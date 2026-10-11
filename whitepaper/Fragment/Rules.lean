module

public import Fragment.Env

@[expose] public section

/-!
# The rules: a relational description of the checker

Three mutually inductive relations over the terms, indexed
by the environment and a **context** `Γ` (the types of the bound
variables, innermost first; `bvar i` has type `Γ[i]` lifted over the
`i + 1` binders in between):

* `Red env Γ e e'` — **head reduction**: β at every binder with no
  certificate, δ, ι, closed under `appFn` and `trans` (and `refl`).
* `DefEq env Γ a b` — **definitional equality**, the checker's verdict
  `true`: `refl`, `symm`, reduce-the-left-side, sorts by the level
  oracle, constants, congruence for `app`/`lam`/`pi`, η, proof
  irrelevance; λ-congruence and η compare the bodies' types, except
  where the bodies' point-ness cannot vary with the variable (a
  propositional domain, bodies that do not use it) or the two sides
  are compared at a known type (`appIn`).  **No `trans`** — see the
  docstring of `DefEq`.
* `DefEqIn env Γ T a b` — **comparison at a known type** `T` (task
  #345): the arguments of an application whose head's type the
  checker has; λ-congruence and η there need neither the bodies'
  types nor the domains' comparison.
* `Infer env Γ e T` — **type inference**, one grade, Lean's rules.

The terms carry no binder annotations (task #344), so no rule reads
one: the regime of a binder is the model's business (`Interp.lean`).

They mirror the six relations of `ConLeche/Rules/Rel.lean` (task
#305) restricted to the fragment: one inference grade instead of two
(no `appSkip`, no `proofFast`), no projections, literals, rescues or
structure η, and the certificate walks (`Certs`, `DefEqList`) folded
into the rules that use them (`Red.iota`).  Each constructor's
docstring names the constructor of `Rel.lean` it corresponds to.

**Premise discipline** (as in `Rel.lean`).  A rule's premises are the
certificates the checker runs at that site — the sub-runs and the
guards that determine the shape of the conclusion.  Well-formedness of
the subjects is NOT a premise anywhere: it is semantic (the invariant
`WellDenoted` of `WellDenoted.lean`) and enters only the soundness
theorems (`Sound.lean`), whose statements assume the conclusion's
terms well-denoted and CONCLUDE it of every term a rule produces.
-/

namespace Fragment

open Expr

variable [LevelOracle]

mutual

/-- **Reduction**: the head steps of the checker's `whnf`, chained. -/
inductive Red (env : Env) : List Expr → Expr → Expr → Prop where
  /-- No step (`Red.refl`, `Rel.lean:101`). -/
  | refl {Γ : List Expr} {e : Expr} : Red env Γ e e
  /-- Chaining (`Red.trans`, `Rel.lean:106`).  A reduction is a
  denotation identity, so chaining costs nothing semantically. -/
  | trans {Γ : List Expr} {e₁ e₂ e₃ : Expr} :
      Red env Γ e₁ e₂ → Red env Γ e₂ e₃ → Red env Γ e₁ e₃
  /-- Head reduction inside an application (`Red.appFn`,
  `Rel.lean:111`): the head is reduced before a redex is looked for. -/
  | appFn {Γ : List Expr} {f f' a : Expr} :
      Red env Γ f f' → Red env Γ (app f a) (app f' a)
  /-- **β, uniform**: at every binder, with **no certificate** — no
  inference of the argument, no comparison with the binder's domain.
  Con-leche's checker still runs the certified step where the body may
  be a proposition (`Red.beta`, `Rel.lean:126`) and the free one only
  at a `never` gate (`Red.betaGate`, `Rel.lean:121`); the fragment's
  model needs neither (`Sound.lean`, `Red.beta_sound`): a reduction
  claims nothing of a redex that denotes the point, and a redex that
  does not has a λ that does not, so a graph, which determines its
  domain. -/
  | beta {Γ : List Expr} {A b a : Expr} :
      Red env Γ (app (lam A b) a) (b.inst a)
  /-- **δ** (`Red.delta`, `Rel.lean:132`): a definition unfolds to its
  value, at the use's level instantiation.  (With `appFn`, an applied
  definition unfolds at its head.) -/
  | delta {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo} {v : Expr} :
      env.find? c = some ci → ci.value? = some v →
      ls.length = ci.lparams.length →
      Red env Γ (const c ls) (v.instL ci.lparams ls)
  /-- **ι** (`Red.iota`, `Rel.lean:184`): a stored recursor applied to
  exactly its telescope — `numParams` parameters, `numMotives` motives,
  `numMinors` minor premises, `numIndices` indices and the major
  premise — whose major reduces to a constructor application with a
  rule, fires the rule: the rule's right-hand side, at the use's
  levels, applied to the parameters, motives and minors, then to the
  constructor's fields (its arguments after the parameters).  The rule
  is one of the block's own constructors' (no stored instantiation,
  `RecRule.inst`); an auxiliary recursor's rule fires by
  `Red.iotaNested`.

  The two **telescope certificates** are `Rel.lean`'s `Certs` walks
  (`:576-587`) folded in: the recursor's argument spine (with the
  reduced major) and the constructor's argument spine are each typed
  against the stored type's `Π`-telescope — every argument's type is
  inferred and found definitionally equal to the binder domain it
  meets (`Expr.piDomains`), and the stored type has the spine's
  length of syntactic binders (`Expr.hasPis`; a generated type does).
  They are what makes the environment's ι law (`EnvModel.lean`,
  `RecRuleLaw`) applicable: they put every argument in its domain.

  The **three comparisons** after them are `Rel.lean`'s too
  (`:206-231`): the constructor's levels are the recursor's (its last
  `usj.length` ones — a large eliminator carries one extra level in
  front), the constructor's parameters are definitionally the
  recursor's, and the constructor's residual type
  (`Expr.piResidual`: the family at the constructor's own parameters
  and index expressions, with the fields substituted in) has index
  expressions definitionally equal to the recursor's index arguments.
  In the model they matter exactly when the family is a proposition:
  there the major denotes the one point, the certificates say only
  that the fibre is inhabited, and the fields the rule's right-hand
  side receives can be related to the recursor's own parameters and
  indices through these comparisons alone (`Install.lean`). -/
  | iota {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
      {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
      {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
      {cij : ConstInfo} {margs : List Expr} {rl : RecRule}
      {doms tys doms' tys' : List Expr}
      {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr} :
      env.find? c = some ci →
      ci.kind = .recursor numParams numMotives numMinors numIndices rules →
      us.length = ci.lparams.length →
      args.length = numParams + numMotives + numMinors + numIndices + 1 →
      ci.type.hasPis (numParams + numMotives + numMinors + numIndices + 1) = true →
      Red env Γ (args.getD (numParams + numMotives + numMinors + numIndices) (bvar 0))
        major →
      major = mkAppN (const cj usj) margs →
      rl ∈ rules → rl.ctor = cj → rl.inst = none →
      env.find? cj = some cij →
      usj.length = cij.lparams.length →
      margs.length = numParams + rl.nfields →
      cij.type.hasPis (numParams + rl.nfields) = true →
      -- the recursor's telescope certificate, on the spine with the reduced major
      piDomains (ci.type.instL ci.lparams us)
        (args.take (numParams + numMotives + numMinors + numIndices) ++ [major]) = some doms →
      tys.length = doms.length →
      (∀ p ∈ (args.take (numParams + numMotives + numMinors + numIndices) ++ [major]).zip tys,
        Infer env Γ p.1 p.2) →
      (∀ p ∈ tys.zip doms, DefEq env Γ p.1 p.2) →
      -- the constructor's telescope certificate
      piDomains (cij.type.instL cij.lparams usj) margs = some doms' →
      tys'.length = doms'.length →
      (∀ p ∈ margs.zip tys', Infer env Γ p.1 p.2) →
      (∀ p ∈ tys'.zip doms', DefEq env Γ p.1 p.2) →
      -- the constructor's levels, parameters and residual indices against the recursor's
      Level.eqList usj (us.drop (us.length - usj.length)) = true →
      (∀ p ∈ (margs.take numParams).zip (args.take numParams), DefEq env Γ p.1 p.2) →
      piResidual (cij.type.instL cij.lparams usj) margs = some residual →
      residual = mkAppN (const I lsI) (rps ++ ridx) →
      rps.length = numParams →
      (∀ p ∈ ridx.zip ((args.take (numParams + numMotives + numMinors + numIndices)).drop
        (numParams + numMotives + numMinors)), DefEq env Γ p.1 p.2) →
      Red env Γ (mkAppN (const c us) args)
        (mkAppN (rl.rhs.instL ci.lparams us)
          (args.take (numParams + numMotives + numMinors) ++ margs.drop numParams))
  /-- **ι, nested** (con-leche's `.nested`-certified rules, task #48):
  a rule of an auxiliary recursor fires on a constructor of the
  block's *container*, whose parameters are not the recursor's.  The
  rule stores the constructor's expected levels (over the recursor's
  level parameters) and expected parameters (terms under the
  recursor's parameter binders, `RecRule.inst`); the three
  comparisons of `Red.iota` become: the constructor's levels are the
  stored ones at the use's levels, its parameters are definitionally
  the stored ones at the recursor's parameter arguments
  (`Expr.instChain`), and the residual's index expressions are
  definitionally the recursor's index arguments.  The constructor's
  own parameter count comes from its record.  The telescope
  certificates are as in `Red.iota`. -/
  | iotaNested {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
      {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
      {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
      {cij : ConstInfo} {I' : Name} {nPc nfj : Nat} {margs : List Expr} {rl : RecRule}
      {lvs : List Level} {pinst : List Expr}
      {doms tys doms' tys' : List Expr}
      {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr} :
      env.find? c = some ci →
      ci.kind = .recursor numParams numMotives numMinors numIndices rules →
      us.length = ci.lparams.length →
      args.length = numParams + numMotives + numMinors + numIndices + 1 →
      ci.type.hasPis (numParams + numMotives + numMinors + numIndices + 1) = true →
      Red env Γ (args.getD (numParams + numMotives + numMinors + numIndices) (bvar 0))
        major →
      major = mkAppN (const cj usj) margs →
      rl ∈ rules → rl.ctor = cj → rl.inst = some (lvs, pinst) →
      env.find? cj = some cij →
      cij.kind = .ctor I' nPc nfj →
      usj.length = cij.lparams.length →
      margs.length = nPc + rl.nfields →
      cij.type.hasPis (nPc + rl.nfields) = true →
      piDomains (ci.type.instL ci.lparams us)
        (args.take (numParams + numMotives + numMinors + numIndices) ++ [major]) = some doms →
      tys.length = doms.length →
      (∀ p ∈ (args.take (numParams + numMotives + numMinors + numIndices) ++ [major]).zip tys,
        Infer env Γ p.1 p.2) →
      (∀ p ∈ tys.zip doms, DefEq env Γ p.1 p.2) →
      piDomains (cij.type.instL cij.lparams usj) margs = some doms' →
      tys'.length = doms'.length →
      (∀ p ∈ margs.zip tys', Infer env Γ p.1 p.2) →
      (∀ p ∈ tys'.zip doms', DefEq env Γ p.1 p.2) →
      -- the constructor's levels and parameters against the stored instantiation
      Level.eqList usj (lvs.map (Level.subst ci.lparams us)) = true →
      pinst.length = nPc →
      (∀ p ∈ (margs.take nPc).zip
        (pinst.map fun e => instChain (e.instL ci.lparams us) (args.take numParams)),
        DefEq env Γ p.1 p.2) →
      piResidual (cij.type.instL cij.lparams usj) margs = some residual →
      residual = mkAppN (const I lsI) (rps ++ ridx) →
      rps.length = nPc →
      (∀ p ∈ ridx.zip ((args.take (numParams + numMotives + numMinors + numIndices)).drop
        (numParams + numMotives + numMinors)), DefEq env Γ p.1 p.2) →
      Red env Γ (mkAppN (const c us) args)
        (mkAppN (rl.rhs.instL ci.lparams us)
          (args.take (numParams + numMotives + numMinors) ++ margs.drop nPc))

/-- **Definitional equality**: the verdict `true` of the checker's
`isDefEq`.

**There is no `trans` rule, deliberately** (`Rel.lean:310-333`, task
#309).  The relation is the checker's verdict on two terms that are
well-formed *together*, a fact no rule states because well-formedness
is semantic (`WellDenoted`) and may not enter this inductive.  Every
rule respects one discipline instead: **the subject of each `DefEq`
premise is a subterm of the conclusion or is produced by a `Red` or
`Infer` premise** (a reduct, an inferred type), so the soundness proof
always has the premise's terms — and their invariant — in hand.  A
`trans` rule is the unique rule that would break it: its middle term
comes from nowhere, so nothing supplies its invariant, and the
induction has nothing to apply the hypothesis to.  In the real checker
the rule is not merely unprovable but unsound (`fvar`s carry
annotations `DefEq.fvar` does not compare while `DefEq.proofFast`
reads; `trans` lets the two meet).  The one sound chaining is "reduce,
then continue": `redL`. -/
inductive DefEq (env : Env) : List Expr → Expr → Expr → Prop where
  /-- The syntactic fast path (`DefEq.refl`, `Rel.lean:338`). -/
  | refl {Γ : List Expr} {a : Expr} : DefEq env Γ a a
  /-- Symmetry (`DefEq.symm`, `Rel.lean:341`).  Not a checker move: the
  constructor from which every right-hand variant of a one-sided rule
  is derived. -/
  | symm {Γ : List Expr} {a b : Expr} : DefEq env Γ a b → DefEq env Γ b a
  /-- **Reduce the left side, then continue** (`DefEq.redL`,
  `Rel.lean:346`): the recursive structure of `isDefEq` — head
  normalisation of either side (with `symm`) and every lazy-δ
  continuation. -/
  | redL {Γ : List Expr} {a a' b : Expr} :
      Red env Γ a a' → DefEq env Γ a' b → DefEq env Γ a b
  /-- Two sorts, by the level oracle (`DefEq.sort`, `Rel.lean:349`). -/
  | sort {Γ : List Expr} {u v : Level} :
      LevelOracle.eq u v = true → DefEq env Γ (sort u) (sort v)
  /-- Two constants of the same name at oracle-equal levels
  (`DefEq.const`, `Rel.lean:360`). -/
  | const {Γ : List Expr} {c : Name} {ls ls' : List Level} :
      Level.eqList ls ls' = true → DefEq env Γ (const c ls) (const c ls')
  /-- `∀`-congruence (`DefEq.forallE`, `Rel.lean:373`): domains, then
  bodies under the RIGHT domain, and nothing else (task #344).  A
  `∀`'s value is a function of its domain's and its fibres' values
  (`SetLib.piV`: the propositional product exactly when every fibre is
  a truth value), and both are types, never the point, so the
  premises' claims apply everywhere (`Sound.lean`, `DefEq.pi_sound`). -/
  | pi {Γ : List Expr} {A₁ B₁ A₂ B₂ : Expr} :
      DefEq env Γ A₁ A₂ → DefEq env (A₂ :: Γ) B₁ B₂ →
      DefEq env Γ (pi A₁ B₁) (pi A₂ B₂)
  /-- λ-congruence (`DefEq.lam`, `Rel.lean:380`): domains, then
  bodies under the RIGHT domain — and, **typed** (task #344), the two
  bodies' inferred types under that domain are definitionally equal.
  A λ's value is the point exactly when every body value is
  (`SetLib.lamV`), and a body may be a proof at some values of the
  variable and not at others (a large elimination into a family whose
  fibres are truth values at some indices); the claim on the bodies
  says nothing where one of them is the point, so the two bodies must
  lie in one type, whose members are all the point or none
  (`Sound.lean`, `DefEq.lam_sound`; without the premise the rule is
  unsound in this model, `Unannot.lean`, `lam_congr_untyped_unsound`). -/
  | lam {Γ : List Expr} {A₁ b₁ A₂ b₂ t₁ t₂ : Expr} :
      DefEq env Γ A₁ A₂ → DefEq env (A₂ :: Γ) b₁ b₂ →
      Infer env (A₂ :: Γ) b₁ t₁ → Infer env (A₂ :: Γ) b₂ t₂ → DefEq env (A₂ :: Γ) t₁ t₂ →
      DefEq env Γ (lam A₁ b₁) (lam A₂ b₂)
  /-- **λ-congruence over a propositional domain** (task #345): no
  comparison of the bodies' types.  The domain is a truth value, so it
  has at most one member, and a body's point-ness cannot vary with
  the variable: a λ that is not the point has its one body value not
  the point, and the bodies' claim applies there (`Sound.lean`,
  `DefEq.lamProp_sound`).  The checker infers the domain's sort, not
  the bodies' types. -/
  | lamProp {Γ : List Expr} {A₁ b₁ A₂ b₂ s : Expr} {u : Level} :
      DefEq env Γ A₁ A₂ → DefEq env (A₂ :: Γ) b₁ b₂ →
      Infer env Γ A₂ s → Red env Γ s (sort u) → LevelOracle.eq u .zero = true →
      DefEq env Γ (lam A₁ b₁) (lam A₂ b₂)
  /-- **λ-congruence of two constant bodies** (task #345): neither body
  uses the bound variable, so each body's value, and its point-ness,
  is the same at every value of the variable; a λ that is not the
  point has a body that is not the point anywhere (`Sound.lean`,
  `DefEq.lamConst_sound`).  One constant body is not enough: the right
  body of `lam_congr_untyped_unsound` is the constant `n`. -/
  | lamConst {Γ : List Expr} {A₁ b₁ A₂ b₂ : Expr} :
      DefEq env Γ A₁ A₂ → DefEq env (A₂ :: Γ) b₁ b₂ →
      b₁.usesVar 0 = false → b₂.usesVar 0 = false →
      DefEq env Γ (lam A₁ b₁) (lam A₂ b₂)
  /-- **Application congruence at the head's type** (task #345): the
  heads are equal and the head's type reduces to a `∀` whose domain
  `S` is the arguments' common type, so the arguments are compared
  *at* `S` (`DefEqIn`) — λ-congruence and η between them need neither
  the bodies' types nor a domain comparison (`Sound.lean`,
  `DefEq.appIn_sound`).  The checker has the head's type for free when
  the head is a constant or a variable (con-leche's arguments of a
  constant-headed spine: the stored type instantiated along the
  earlier arguments). -/
  | appIn {Γ : List Expr} {f₁ a₁ f₂ a₂ tf S B : Expr} :
      DefEq env Γ f₁ f₂ → Infer env Γ f₁ tf → Red env Γ tf (pi S B) →
      DefEqIn env Γ S a₁ a₂ →
      DefEq env Γ (app f₁ a₁) (app f₂ a₂)
  /-- Application congruence (`DefEq.app`, `Rel.lean:390`). -/
  | app {Γ : List Expr} {f₁ a₁ f₂ a₂ : Expr} :
      DefEq env Γ f₁ f₂ → DefEq env Γ a₁ a₂ →
      DefEq env Γ (app f₁ a₁) (app f₂ a₂)
  /-- **η** (`DefEq.eta`, `Rel.lean:400`): a λ against a term `b`
  whose inferred type reduces to a `∀` with a definitionally equal
  domain, when the λ's body is `b` applied to the variable — and,
  **typed** as λ-congruence is (task #344), the λ's body's inferred
  type is definitionally equal to the `∀`'s body, so that the λ's body
  and `b` applied lie in one type.  Sound because a member of a
  product is the abstraction of its applications
  (`SetLib.lamV_eta`). -/
  | eta {Γ : List Expr} {A₁ b₁ b tb A₂ B t₁ : Expr} :
      Infer env Γ b tb → Red env Γ tb (pi A₂ B) →
      DefEq env Γ A₂ A₁ →
      DefEq env (A₁ :: Γ) b₁ (app (b.liftN 1) (bvar 0)) →
      Infer env (A₁ :: Γ) b₁ t₁ → DefEq env (A₁ :: Γ) t₁ B →
      DefEq env Γ (lam A₁ b₁) b
  /-- **Proof irrelevance** (`DefEq.proofIrrel`, `Rel.lean:417`): both
  sides' inferred types have sort `Prop`.  **The two types are never
  compared**: the model justifies that, because every proof denotes the
  one point. -/
  | proofIrrel {Γ : List Expr} {a ta tta b tb ttb : Expr} {u v : Level} :
      Infer env Γ a ta → Infer env Γ ta tta → Red env Γ tta (sort u) →
      LevelOracle.eq u .zero = true →
      Infer env Γ b tb → Infer env Γ tb ttb → Red env Γ ttb (sort v) →
      LevelOracle.eq v .zero = true →
      DefEq env Γ a b

/-- **Comparison at a known type** (task #345): `a` and `b` are both
members of `T` — the caller knows it, the relation does not check it —
and the checker calls them definitionally equal.  Its claim is
unconditional (`DefEqInSem`): a type's members are all the point or
none, so the point needs no exception.  A λ against a λ, or against
anything by η, is compared through the `∀` the type reduces to, at
its body: the λs' domains are that `∀`'s (a graph in a function space
has its domain), and the bodies lie in its fibres — no inference, no
comparison of domains or of bodies' types. -/
inductive DefEqIn (env : Env) : List Expr → Expr → Expr → Expr → Prop where
  /-- Any definitional equality, read at the common type. -/
  | of {Γ : List Expr} {T a b : Expr} : DefEq env Γ a b → DefEqIn env Γ T a b
  /-- Symmetry. -/
  | symm {Γ : List Expr} {T a b : Expr} : DefEqIn env Γ T a b → DefEqIn env Γ T b a
  /-- λ-congruence at a `∀`: the bodies at its body. -/
  | lam {Γ : List Expr} {T D E A₁ b₁ A₂ b₂ : Expr} :
      Red env Γ T (pi D E) → DefEqIn env (A₂ :: Γ) E b₁ b₂ →
      DefEqIn env Γ T (lam A₁ b₁) (lam A₂ b₂)
  /-- η at a `∀`: the λ's body against `b` applied, at its body. -/
  | eta {Γ : List Expr} {T D E A₁ b₁ b : Expr} :
      Red env Γ T (pi D E) → DefEqIn env (A₁ :: Γ) E b₁ (app (b.liftN 1) (bvar 0)) →
      DefEqIn env Γ T (lam A₁ b₁) b

/-- **Type inference.** -/
inductive Infer (env : Env) : List Expr → Expr → Expr → Prop where
  /-- A bound variable's type is its context entry, lifted over the
  binders in between (`Infer.fvar`, `Rel.lean:492`; the real checker
  reads the type off the free variable). -/
  | bvar {Γ : List Expr} {i : Nat} {A : Expr} :
      Γ[i]? = some A → Infer env Γ (bvar i) (A.liftN (i + 1))
  /-- `Sort u : Sort (u + 1)` (`Infer.sort`, `Rel.lean:488`). -/
  | sort {Γ : List Expr} {u : Level} :
      Infer env Γ (sort u) (sort (.succ u))
  /-- A stored constant at the right number of levels has its
  declared type, instantiated (`Infer.const`, `Rel.lean:496`). -/
  | const {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo} :
      env.find? c = some ci → ls.length = ci.lparams.length →
      Infer env Γ (const c ls) (ci.type.instL ci.lparams ls)
  /-- **`∀`-formation** (`Infer.forallE`, `Rel.lean:515`): the domain's
  type reduces to a sort `u`, the body's type (under the domain)
  reduces to a sort `v`, the result is `Sort (imax u v)`.  Nothing is
  checked beyond Lean's own rule. -/
  | pi {Γ : List Expr} {A B s t : Expr} {u v : Level} :
      Infer env Γ A s → Red env Γ s (sort u) →
      Infer env (A :: Γ) B t → Red env (A :: Γ) t (sort v) →
      Infer env Γ (pi A B) (sort (.imax u v))
  /-- **λ** (`Infer.lam`, `Rel.lean:530`): the domain's type reduces to
  a sort, the body is inferred under the domain, and the result is the
  `∀` of the body's type — Lean's own rule.  The body's type's sort is
  not computed (con-leche computes it to check the binder's datum, of
  which there is none here): an inferred type is a type
  (`InferSem`), which is all the `∀`'s invariant asks of it. -/
  | lam {Γ : List Expr} {A b s bt : Expr} {u : Level} :
      Infer env Γ A s → Red env Γ s (sort u) →
      Infer env (A :: Γ) b bt →
      Infer env Γ (lam A b) (pi A bt)
  /-- **Application** (`Infer.app`, `Rel.lean:544`): the head's type
  reduces to a `∀`, and the argument's inferred type is definitionally
  equal to its domain.  This is where a syntactic proof would need
  Π-injectivity and the semantic one does not: the `∀` the head's type
  reduces to *is* a function space, and membership in it is what the
  model needs (`Sound.lean`, `infer_sound`'s `app` case). -/
  | app {Γ : List Expr} {f a tf A B ta : Expr} :
      Infer env Γ f tf → Red env Γ tf (pi A B) →
      Infer env Γ a ta → DefEq env Γ ta A →
      Infer env Γ (app f a) (B.inst a)

end

end Fragment
