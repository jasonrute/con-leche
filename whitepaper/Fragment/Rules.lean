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
  premise, ζ, δ, ι, closed under `appFn` and `trans` (and `refl`).
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

A binder carries its domain alone (task #344), and no rule reads a
regime: the regime of a binder is the model's business (`Interp.lean`).

They mirror the six relations of `ConLeche/Rules/Rel.lean` (task
#305) restricted to the fragment: one inference grade instead of two
(no `appSkip`, no `proofFast`), no projections, literals, rescues or
structure η, and the certificate walks (`CertsF`, `DefEqList`) folded
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
  /-- No step (`Red.refl`, `Rel.lean:106`). -/
  | refl {Γ : List Expr} {e : Expr} : Red env Γ e e
  /-- Chaining (`Red.trans`, `Rel.lean:111`).  A reduction is a
  denotation identity, so chaining costs nothing semantically. -/
  | trans {Γ : List Expr} {e₁ e₂ e₃ : Expr} :
      Red env Γ e₁ e₂ → Red env Γ e₂ e₃ → Red env Γ e₁ e₃
  /-- Head reduction inside an application (`Red.appFn`,
  `Rel.lean:116`): the head is reduced before a redex is looked for. -/
  | appFn {Γ : List Expr} {f f' a : Expr} :
      Red env Γ f f' → Red env Γ (app f a) (app f' a)
  /-- **β**: at every binder, with **no premise** — no
  inference of the argument, no comparison with the binder's domain.
  This is Lean's own β (`whnf_core`).  The model needs no premise
  (`Sound.lean`, `Red.beta_sound`): a reduction claims nothing of a
  redex that denotes the point, and a redex that does not has a lambda that
  does not, so a graph, which determines its domain: the argument lies
  in the lambda's domain because it lies in the domain of the slot the
  semantic invariant gives the application.
  -/
  | beta {Γ : List Expr} {A b a : Expr} :
      Red env Γ (app (lam A b) a) (b.inst a)
  /-- **ζ**: a `let` reduces to its body with the value
  substituted, with no certificate, as β (con-leche's `whnfCore` on
  `.letE`, S0's `inst1M b v`; official `whnf_core`).  Unlike β it
  needs no case split on the point: the `let` and its reduct denote
  alike at every environment (`interp_zeta`). -/
  | zeta {Γ : List Expr} {T v b : Expr} :
      Red env Γ (letE T v b) (b.inst v)
  /-- **δ** (`Red.delta`, `Rel.lean:140`): a definition unfolds to its
  value, at the use's level instantiation.  (With `appFn`, an applied
  definition unfolds at its head.) -/
  | delta {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo} {v : Expr} :
      env.find? c = some ci → ci.value? = some v →
      ls.length = ci.lparams.length →
      Red env Γ (const c ls) (v.instL ci.lparams ls)
  /-- **ι** (`Red.iota`, `Rel.lean:200`): a stored recursor applied to
  exactly its telescope — `numParams` parameters, `numMotives` motives,
  `numMinors` minor premises, `numIndices` indices and the major
  premise — whose major reduces to a constructor application with a
  rule, fires the rule: the rule's right-hand side, at the use's
  levels, applied to the parameters, motives and minors, then to the
  constructor's fields (its arguments after the parameters).  The rule
  is one of the block's own constructors' (no stored instantiation,
  `RecRule.inst`); an auxiliary recursor's rule fires by
  `Red.iotaNested`.

  The **certificates** are the fragment's form of `Rel.lean`'s `CertsF`
  and `piResidual` premises (`:227-236`).  The recursor's spine before the
  major needs none: a reduction claims nothing of a redex that is the
  point, and a redex that is not the point fits the recursor's telescope
  by the invariant's application slots (`teleFit_of_ne_pt`).  The reduced
  major's slot is certified — its type inferred and found definitionally
  equal to the domain the recursor's telescope leaves after the spine
  (`Expr.piResidual`) — and so is the constructor's argument spine against
  its stored type's `Π`-telescope (`Expr.piDomains`; the stored types have
  the spine's length of syntactic binders, `Expr.hasPis`).  Both are
  needed only where the major may denote the point (a family that may be a
  proposition): where the major's domain is strict, `iota_core_strict`
  (`Sound.lean`) needs neither; where the constructor's family is a
  proposition at every valuation, `Red.iotaProp` needs no slot
  certificate.  They make the environment's ι law (`EnvModel.lean`,
  `RecRuleLaw`) applicable: they put every argument in its domain.

  The **three comparisons** after them are `Rel.lean`'s too (`:213-241`,
  there in the certified case only): the constructor's levels are the
  recursor's (its last `usj.length` ones — a large eliminator carries
  one extra level in front), the constructor's parameters are
  definitionally the recursor's, and the constructor's residual type
  (`Expr.piResidual`: the family at the constructor's own parameters and
  index expressions, with the fields substituted in) has index
  expressions definitionally equal to the recursor's index arguments. In
  the model they matter exactly when the family is a proposition: there
  the major denotes the one point, the certificates say only that the
  fibre is inhabited, and the fields the rule's right-hand side receives
  can be related to the recursor's own parameters and indices through
  these comparisons alone (`Install.lean`). -/
  | iota {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
      {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
      {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
      {cij : ConstInfo} {margs : List Expr} {rl : RecRule}
      {dM bM tM : Expr} {doms' tys' : List Expr}
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
      -- the major's slot certificate (the recursor's spine before it needs none)
      piResidual (ci.type.instL ci.lparams us)
        (args.take (numParams + numMotives + numMinors + numIndices)) = some (pi dM bM) →
      Infer env Γ major tM → DefEq env Γ tM dM →
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
  /-- **ι on a family in `Prop`, with no major-slot certificate**
  (the checker's certified case of ι).  `Red.iota` without the reduced
  major's slot certificate, for a constructor whose family's sort
  evaluates to zero at every valuation: the family `I` the
  constructor's residual type is headed by is stored, its type walked
  along the residual's parameters and indices leaves `Sort u`, and the
  oracle decides `u = 0`.  The constructor's telescope certificate stays
  at the full grade (every parameter and field), and so do the
  three comparisons.  Why the slot needs nothing: the unreduced major
  lies in the slot whenever the redex is not the point, and where it is
  the point so is the reduced constructor application
  (`ctorApp_eq_pt_of_sortZero`, `Red.iota_core_prop`).  This covers the
  families that are always propositions (`Acc`); a family that may be
  a proposition at some valuations only (`Quot.{u}`, `PUnit.{u}`) also
  goes by `Red.iotaSlot`, which reads the environment's fibre law at the
  others. -/
  | iotaProp {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
      {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
      {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
      {cij : ConstInfo} {margs : List Expr} {rl : RecRule}
      {dM bM : Expr} {doms' tys' : List Expr}
      {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
      {Ii : ConstInfo} {u : Level} :
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
      -- the major's slot, located but not certified
      piResidual (ci.type.instL ci.lparams us)
        (args.take (numParams + numMotives + numMinors + numIndices)) = some (pi dM bM) →
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
      -- the constructor's family is a proposition at every valuation
      env.find? I = some Ii →
      lsI.length = Ii.lparams.length →
      Ii.type.hasPis (rps ++ ridx).length = true →
      piResidual (Ii.type.instL Ii.lparams lsI) (rps ++ ridx) = some (sort u) →
      LevelOracle.eq u .zero = true →
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
      {dM bM tM : Expr} {doms' tys' : List Expr}
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
      piResidual (ci.type.instL ci.lparams us)
        (args.take (numParams + numMotives + numMinors + numIndices)) = some (pi dM bM) →
      Infer env Γ major tM → DefEq env Γ tM dM →
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

  /-- **ι with no major-slot certificate and no level test** (the
  checker's certified case of ι).  `Red.iota`
  without the reduced major's slot certificate, for any family: the
  constructor's telescope certificate stays at the full grade (every
  parameter and field), and so do the three comparisons; nothing
  else is tested.  Why the slot needs nothing: where the unreduced
  major is not the point its reduction claim gives the reduct; where it
  is, the environment's slot law (`EnvModel.rec_rules_slot`) makes
  the constructor application the point too, given the redex is not
  (`Sound.lean`, `slot_of_law`, `iota_core_slot`).  On the generated
  recursors that law holds because the major's domain is the
  constructor's own family at the recursor's levels, a fibre holding the
  point is a truth value there, and the constructor of a family in
  `Prop` is the point (`IndSpec.rec_rule_slot`).  No premise links the
  major's domain to the constructor's family: the installation proves
  the slot law of every generated rule (`InstallIota.lean`).  This
  is the rule for a family that is a proposition at some valuations
  only (`Quot.{u}`, `PUnit.{u}`). -/
  | iotaSlot {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
      {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
      {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
      {cij : ConstInfo} {margs : List Expr} {rl : RecRule}
      {dM bM : Expr} {doms' tys' : List Expr}
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
      -- the major's slot, located but not certified
      piResidual (ci.type.instL ci.lparams us)
        (args.take (numParams + numMotives + numMinors + numIndices)) = some (pi dM bM) →
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
  /-- **ι, nested, with no major-slot certificate**:
  `Red.iotaNested` without the reduced major's slot certificate, with
  no further premise: the slot law of an auxiliary recursor's rule
  (`IndSpec.rec_rule_slot1N`) holds because a nested block is a
  proposition only where its eliminator is. -/
  | iotaNestedSlot {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
      {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
      {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
      {cij : ConstInfo} {I' : Name} {nPc nfj : Nat} {margs : List Expr} {rl : RecRule}
      {lvs : List Level} {pinst : List Expr}
      {dM bM : Expr} {doms' tys' : List Expr}
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
      piResidual (ci.type.instL ci.lparams us)
        (args.take (numParams + numMotives + numMinors + numIndices)) = some (pi dM bM) →
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
  /-- **ι, case 2** (the checker's ι case test): `Red.iota`
  with **no certificate at all** — no major slot, no constructor
  telescope — where the major's domain (what the recursor's telescope
  leaves after the spine, `Expr.piResidual`) is a stored inductive
  family applied to its parameters and indices whose stored sort is
  **never `Prop`** at the use: one level test, `1 ≤ u` at every
  valuation (`LevelOracle.le`, con-leche's `sortZ` read as `never`).
  The environment law `EnvModel.ind_fib` makes that domain strict,
  so a redex that is not the point has a major that is not the point;
  its reduction claim then applies, and the reduced constructor
  application fits the constructor's telescope with no certificate
  (`Sound.lean`, `iota_core_strict`).  The three comparisons are
  `Red.iota`'s, unchanged. -/
  | iotaStrict {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
      {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
      {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
      {cij : ConstInfo} {margs : List Expr} {rl : RecRule}
      {dM bM : Expr} {I₀ : Name} {ls₀ : List Level} {dargs : List Expr} {ci₀ : ConstInfo}
      {nP₀ nI₀ : Nat} {cs₀ : List Name} {S₀ : IndSpec}
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
      -- case 2: the major's domain is a stored family whose sort is never `Prop` at the use
      piResidual (ci.type.instL ci.lparams us)
        (args.take (numParams + numMotives + numMinors + numIndices)) = some (pi dM bM) →
      dM = mkAppN (const I₀ ls₀) dargs →
      env.find? I₀ = some ci₀ → ci₀.kind = .induct nP₀ nI₀ cs₀ S₀ →
      ls₀.length = ci₀.lparams.length → dargs.length = nP₀ + nI₀ →
      ci₀.type.hasPis (nP₀ + nI₀) = true →
      LevelOracle.le (.succ .zero) (S₀.sort.subst ci₀.lparams ls₀) = true →
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
  /-- **ι, nested, case 2**: `Red.iotaNested` with no
  certificate, under `Red.iotaStrict`'s level test on the major's
  domain. -/
  | iotaNestedStrict {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
      {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
      {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
      {cij : ConstInfo} {I' : Name} {nPc nfj : Nat} {margs : List Expr} {rl : RecRule}
      {lvs : List Level} {pinst : List Expr}
      {dM bM : Expr} {I₀ : Name} {ls₀ : List Level} {dargs : List Expr} {ci₀ : ConstInfo}
      {nP₀ nI₀ : Nat} {cs₀ : List Name} {S₀ : IndSpec}
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
      -- case 2: the major's domain is a stored family whose sort is never `Prop` at the use
      piResidual (ci.type.instL ci.lparams us)
        (args.take (numParams + numMotives + numMinors + numIndices)) = some (pi dM bM) →
      dM = mkAppN (const I₀ ls₀) dargs →
      env.find? I₀ = some ci₀ → ci₀.kind = .induct nP₀ nI₀ cs₀ S₀ →
      ls₀.length = ci₀.lparams.length → dargs.length = nP₀ + nI₀ →
      ci₀.type.hasPis (nP₀ + nI₀) = true →
      LevelOracle.le (.succ .zero) (S₀.sort.subst ci₀.lparams ls₀) = true →
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
  /-- **ι by K** (Lean's
  `to_cnstr_when_K`): a recursor whose rule is flagged K
  (`RecRule.k`: one family, always a proposition, one constructor
  with no fields — `Eq`, `HEq`, `True`) reduces on its major **as it
  stands**, with no constructor in sight, to the rule's right-hand
  side at the recursor's parameters, motives and minors.  There is no
  certificate, no level, parameter or index comparison, and the major
  is not reduced.  What stays is K's **type check**, as in Lean: the
  major's inferred type reduces to a family application
  `I.{lsI} targs`, the constructor fabricated at its parameters
  `rl.ctor.{lsI} (targs.take numParams)` has a type `tF`, and
  `tF ≡ I.{lsI} targs`.  That check decides whether the step is taken
  (a verdict test); no claim consumes it.  Soundness is the
  environment's K law (`EnvModel.rec_rules_k`, proved in the
  installer by inversion of the least fixed point) with
  `Red.iotaK_core_sem`: a redex that is not the point fits the
  recursor's telescope, the major included, and the law needs nothing
  more. -/
  | iotaK {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
      {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
      {args : List Expr} {rl : RecRule} {tM : Expr} {I : Name} {lsI : List Level}
      {targs : List Expr} {tF : Expr} :
      env.find? c = some ci →
      ci.kind = .recursor numParams numMotives numMinors numIndices rules →
      us.length = ci.lparams.length →
      args.length = numParams + numMotives + numMinors + numIndices + 1 →
      ci.type.hasPis (numParams + numMotives + numMinors + numIndices + 1) = true →
      rl ∈ rules → rl.k = true →
      -- K's type check on the major as it stands (a verdict test, consumed by no claim)
      Infer env Γ (args.getD (numParams + numMotives + numMinors + numIndices) (bvar 0)) tM →
      Red env Γ tM (mkAppN (const I lsI) targs) →
      Infer env Γ (mkAppN (const rl.ctor lsI) (targs.take numParams)) tF →
      DefEq env Γ tF (mkAppN (const I lsI) targs) →
      Red env Γ (mkAppN (const c us) args)
        (mkAppN (rl.rhs.instL ci.lparams us) (args.take (numParams + numMotives + numMinors)))

/-- **Definitional equality**: the verdict `true` of the checker's
`isDefEq`.

**There is no `trans` rule, deliberately** (`Rel.lean:334-357`).
The relation is the checker's verdict on two terms that are
well-formed *together*, a fact no rule states because well-formedness
is semantic (`WellDenoted`) and may not enter this inductive.  Every
rule respects one discipline instead: **the subject of each `DefEq`
premise is a subterm of the conclusion or is produced by a `Red` or
`Infer` premise** (a reduct, an inferred type), so the soundness proof
always has the premise's terms — and their invariant — in hand.  A
`trans` rule is the unique rule that would break it: its middle term
comes from nowhere, so nothing supplies its invariant, and the
induction has nothing to apply the hypothesis to.  Nor does the
checker chain through an arbitrary middle term: every comparison it
makes is one of the rules below, and its one way to chain is
"reduce, then continue": `redL`.
-/
inductive DefEq (env : Env) : List Expr → Expr → Expr → Prop where
  /-- The syntactic fast path (`DefEq.refl`, `Rel.lean:362`). -/
  | refl {Γ : List Expr} {a : Expr} : DefEq env Γ a a
  /-- Symmetry (`DefEq.symm`, `Rel.lean:365`).  Not a checker move: the
  constructor from which every right-hand variant of a one-sided rule
  is derived. -/
  | symm {Γ : List Expr} {a b : Expr} : DefEq env Γ a b → DefEq env Γ b a
  /-- **Reduce the left side, then continue** (`DefEq.redL`,
  `Rel.lean:370`): the recursive structure of `isDefEq` — head
  normalisation of either side (with `symm`) and every lazy-δ
  continuation. -/
  | redL {Γ : List Expr} {a a' b : Expr} :
      Red env Γ a a' → DefEq env Γ a' b → DefEq env Γ a b
  /-- Two sorts, by the level oracle (`DefEq.sort`, `Rel.lean:373`). -/
  | sort {Γ : List Expr} {u v : Level} :
      LevelOracle.eq u v = true → DefEq env Γ (sort u) (sort v)
  /-- Two constants of the same name at oracle-equal levels
  (`DefEq.const`, `Rel.lean:384`). -/
  | const {Γ : List Expr} {c : Name} {ls ls' : List Level} :
      Level.eqList ls ls' = true → DefEq env Γ (const c ls) (const c ls')
  /-- `∀`-congruence (`DefEq.forallE`, `Rel.lean:399`): domains, then
  bodies under the RIGHT domain, and nothing else.  A
  `∀`'s value is a function of its domain's and its fibres' values
  (`SetLib.piV`: the propositional function space exactly when every fibre is
  a truth value), and both are types, never the point, so the
  premises' claims apply everywhere (`Sound.lean`, `DefEq.pi_sound`). -/
  | pi {Γ : List Expr} {A₁ B₁ A₂ B₂ : Expr} :
      DefEq env Γ A₁ A₂ → DefEq env (A₂ :: Γ) B₁ B₂ →
      DefEq env Γ (pi A₁ B₁) (pi A₂ B₂)
  /-- Lambda congruence (`DefEq.lams`, `Rel.lean:407`): domains, then
  bodies under the RIGHT domain — and, **typed**, the two
  bodies' inferred types under that domain are definitionally equal.
  A lambda's value is the point exactly when every body value is
  (`SetLib.lamV`), and a body may be a proof at some values of the
  variable and not at others (a large elimination into a family whose
  fibres are truth values at some indices); the claim on the bodies
  says nothing where one of them is the point, so the two bodies must
  lie in one type, whose members are all the point or none
  (`Sound.lean`, `DefEq.lam_sound`; without the premise the rule is
  unsound in this model, `ValueReading.lean`, `lam_congr_untyped_unsound`). -/
  | lam {Γ : List Expr} {A₁ b₁ A₂ b₂ t₁ t₂ : Expr} :
      DefEq env Γ A₁ A₂ → DefEq env (A₂ :: Γ) b₁ b₂ →
      Infer env (A₂ :: Γ) b₁ t₁ → Infer env (A₂ :: Γ) b₂ t₂ → DefEq env (A₂ :: Γ) t₁ t₂ →
      DefEq env Γ (lam A₁ b₁) (lam A₂ b₂)
  /-- **Lambda congruence over a propositional domain**: no
  comparison of the bodies' types.  The domain is a truth value, so it
  has at most one member, and a body's point-ness cannot vary with
  the variable: a lambda that is not the point has its one body value not
  the point, and the bodies' claim applies there (`Sound.lean`,
  `DefEq.lamProp_sound`).  The checker infers the domain's sort, not
  the bodies' types. -/
  | lamProp {Γ : List Expr} {A₁ b₁ A₂ b₂ s : Expr} {u : Level} :
      DefEq env Γ A₁ A₂ → DefEq env (A₂ :: Γ) b₁ b₂ →
      Infer env Γ A₂ s → Red env Γ s (sort u) → LevelOracle.eq u .zero = true →
      DefEq env Γ (lam A₁ b₁) (lam A₂ b₂)
  /-- **Lambda congruence of two constant bodies**: neither body
  uses the bound variable, so each body's value, and its point-ness,
  is the same at every value of the variable; a lambda that is not the
  point has a body that is not the point anywhere (`Sound.lean`,
  `DefEq.lamConst_sound`).  One constant body is not enough: the right
  body of `lam_congr_untyped_unsound` is the constant `n`. -/
  | lamConst {Γ : List Expr} {A₁ b₁ A₂ b₂ : Expr} :
      DefEq env Γ A₁ A₂ → DefEq env (A₂ :: Γ) b₁ b₂ →
      b₁.usesVar 0 = false → b₂.usesVar 0 = false →
      DefEq env Γ (lam A₁ b₁) (lam A₂ b₂)
  /-- **η over a propositional domain**: `DefEq.eta`
  without the lambda's body's type, for the reason of `lamProp`: over a
  domain with at most one member, the lambda and `b` that are not the point
  have their one body value not the point (`Sound.lean`,
  `DefEq.etaProp_sound`). -/
  | etaProp {Γ : List Expr} {A₁ b₁ b tb A₂ B s : Expr} {u : Level} :
      Infer env Γ b tb → Red env Γ tb (pi A₂ B) →
      DefEq env Γ A₂ A₁ →
      DefEq env (A₁ :: Γ) b₁ (app (b.liftN 1) (bvar 0)) →
      Infer env Γ A₁ s → Red env Γ s (sort u) → LevelOracle.eq u .zero = true →
      DefEq env Γ (lam A₁ b₁) b
  /-- **Application congruence at the head's type**: the
  heads are equal and the head's type reduces to a `∀` whose domain
  `S` is the arguments' common type, so the arguments are compared
  *at* `S` (`DefEqIn`) — lambda congruence and η between them need neither
  the bodies' types nor a domain comparison (`Sound.lean`,
  `DefEq.appIn_sound`).  The checker has the head's type for free when
  the head is a constant or a variable (con-leche's arguments of a
  constant-headed spine: the stored type instantiated along the
  earlier arguments). -/
  | appIn {Γ : List Expr} {f₁ a₁ f₂ a₂ tf S B : Expr} :
      DefEq env Γ f₁ f₂ → Infer env Γ f₁ tf → Red env Γ tf (pi S B) →
      DefEqIn env Γ S a₁ a₂ →
      DefEq env Γ (app f₁ a₁) (app f₂ a₂)
  /-- Application congruence (`DefEq.app`, `Rel.lean:412`). -/
  | app {Γ : List Expr} {f₁ a₁ f₂ a₂ : Expr} :
      DefEq env Γ f₁ f₂ → DefEq env Γ a₁ a₂ →
      DefEq env Γ (app f₁ a₁) (app f₂ a₂)
  /-- **η** (`DefEq.eta`, `Rel.lean:430`): a lambda against a term `b`
  whose inferred type reduces to a `∀` with a definitionally equal
  domain, when the lambda's body is `b` applied to the variable — and,
  **typed** as lambda congruence is, the lambda's body's inferred
  type is definitionally equal to the `∀`'s body, so that the lambda's body
  and `b` applied lie in one type.  Sound because a member of a
  function space is the abstraction of its applications
  (`SetLib.lamV_eta`). -/
  | eta {Γ : List Expr} {A₁ b₁ b tb A₂ B t₁ : Expr} :
      Infer env Γ b tb → Red env Γ tb (pi A₂ B) →
      DefEq env Γ A₂ A₁ →
      DefEq env (A₁ :: Γ) b₁ (app (b.liftN 1) (bvar 0)) →
      Infer env (A₁ :: Γ) b₁ t₁ → DefEq env (A₁ :: Γ) t₁ B →
      DefEq env Γ (lam A₁ b₁) b
  /-- **Proof irrelevance** (`DefEq.proofIrrel`, `Rel.lean:452`): both
  sides' inferred types have sort `Prop`.  **The two types are never
  compared**: the model justifies that, because every proof denotes the
  one point. -/
  | proofIrrel {Γ : List Expr} {a ta tta b tb ttb : Expr} {u v : Level} :
      Infer env Γ a ta → Infer env Γ ta tta → Red env Γ tta (sort u) →
      LevelOracle.eq u .zero = true →
      Infer env Γ b tb → Infer env Γ tb ttb → Red env Γ ttb (sort v) →
      LevelOracle.eq v .zero = true →
      DefEq env Γ a b
  /-- **Lambda telescope congruence**: a pair of lambda telescopes
  compared level by level, the bodies' types compared only at the
  innermost level (`DefEqLams`).  The checker's two-lambda arm skips the
  bodies' types exactly when both opened bodies are syntactically lambdas. -/
  | lams {Γ : List Expr} {a b : Expr} : DefEqLams env Γ a b → DefEq env Γ a b

/-- **Lambda telescope congruence, typed at the innermost level only**.
Two lambda telescopes are compared level by level: the domains
at every level, the bodies' types only where the comparison stops
descending through two lambdas.

*Why the outer levels need no type comparison.*  Syntactically: the
type of `fun x : A => fun y : B => c` is `∀ x : A, ∀ y : B, T` where
`T` is `c`'s type, so for two telescopes compared with equal domains,
each outer level's bodies' types are `∀`s over the domain the next
level compares, with the next level's bodies' types as codomains; equal
innermost bodies' types give equal bodies' types at every level, by
`∀`-congruence.  Semantically (`Sound.lean`, `DefEqLams.outer_sound`):
the type comparison is what makes lambda congruence's claim
**unconditional** — `DefEq`'s claim says nothing where a side is the
point, and two bodies in one type are both the point or neither — and
an unconditional equality of the bodies at every value of the variable
is an equality of the lambdas, with no type at all.  So the claim of this
relation, `LamsSem`, is unconditional, and it propagates outward
through any number of levels.

*Unequal depth, and reduction between levels.*  The descent continues
only through two **syntactic** lambdas (`outer`'s premise is this relation
itself, which has no reduction rule).  Where one body is not a lambda — the
comparison ends in η, or in any other rule, possibly after δ or whnf
steps — that level is the innermost one (`inner`), and its bodies'
types are inferred and compared at the full grade.  A δ or whnf step
between levels therefore resets the accounting: the δ-witness `d :=
fun x => (fun h => h) n` (`Probe.lean`, `lam_congr_sorts_unsound`)
puts the reduction inside `inner`'s untyped premise `DefEq … b₁ b₂`,
where the type comparison is still required.  Syntactically equal
lambdas (`refl`) are equal outright. -/
inductive DefEqLams (env : Env) : List Expr → Expr → Expr → Prop where
  /-- Syntactically equal sides (the checker's `a == b` fast path). -/
  | refl {Γ : List Expr} {a : Expr} : DefEqLams env Γ a a
  /-- The innermost level: `DefEq.lam`'s premises — domains, bodies,
  and the bodies' inferred types. -/
  | inner {Γ : List Expr} {A₁ b₁ A₂ b₂ t₁ t₂ : Expr} :
      DefEq env Γ A₁ A₂ → DefEq env (A₂ :: Γ) b₁ b₂ →
      Infer env (A₂ :: Γ) b₁ t₁ → Infer env (A₂ :: Γ) b₂ t₂ → DefEq env (A₂ :: Γ) t₁ t₂ →
      DefEqLams env Γ (lam A₁ b₁) (lam A₂ b₂)
  /-- An outer level: the domains, and the bodies by this relation —
  no inference, no type comparison. -/
  | outer {Γ : List Expr} {A₁ b₁ A₂ b₂ : Expr} :
      DefEq env Γ A₁ A₂ → DefEqLams env (A₂ :: Γ) b₁ b₂ →
      DefEqLams env Γ (lam A₁ b₁) (lam A₂ b₂)

/-- **Comparison at a known type**: `a` and `b` are both
members of `T` — the caller knows it, the relation does not check it —
and the checker calls them definitionally equal.  Its claim is
unconditional (`DefEqInSem`): a type's members are all the point or
none, so the point needs no exception.  A lambda against a lambda, or against
anything by η, is compared through the `∀` the type reduces to, at
its body: the lambdas' domains are that `∀`'s (a graph in a function space
has its domain), and the bodies lie in its fibres — no inference, no
comparison of domains or of bodies' types. -/
inductive DefEqIn (env : Env) : List Expr → Expr → Expr → Expr → Prop where
  /-- Any definitional equality, read at the common type. -/
  | of {Γ : List Expr} {T a b : Expr} : DefEq env Γ a b → DefEqIn env Γ T a b
  /-- Symmetry. -/
  | symm {Γ : List Expr} {T a b : Expr} : DefEqIn env Γ T a b → DefEqIn env Γ T b a
  /-- Lambda congruence at a `∀`: the bodies at its body. -/
  | lam {Γ : List Expr} {T D E A₁ b₁ A₂ b₂ : Expr} :
      Red env Γ T (pi D E) → DefEqIn env (A₂ :: Γ) E b₁ b₂ →
      DefEqIn env Γ T (lam A₁ b₁) (lam A₂ b₂)
  /-- η at a `∀`: the lambda's body against `b` applied, at its body. -/
  | eta {Γ : List Expr} {T D E A₁ b₁ b : Expr} :
      Red env Γ T (pi D E) → DefEqIn env (A₁ :: Γ) E b₁ (app (b.liftN 1) (bvar 0)) →
      DefEqIn env Γ T (lam A₁ b₁) b

/-- **Type inference.** -/
inductive Infer (env : Env) : List Expr → Expr → Expr → Prop where
  /-- A bound variable's type is its context entry, lifted over the
  binders in between (`Infer.fvar`, `Rel.lean:555`; the real checker
  reads the type off the free variable). -/
  | bvar {Γ : List Expr} {i : Nat} {A : Expr} :
      Γ[i]? = some A → Infer env Γ (bvar i) (A.liftN (i + 1))
  /-- `Sort u : Sort (u + 1)` (`Infer.sort`, `Rel.lean:551`). -/
  | sort {Γ : List Expr} {u : Level} :
      Infer env Γ (sort u) (sort (.succ u))
  /-- A stored constant at the right number of levels has its
  declared type, instantiated (`Infer.const`, `Rel.lean:559`). -/
  | const {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo} :
      env.find? c = some ci → ls.length = ci.lparams.length →
      Infer env Γ (const c ls) (ci.type.instL ci.lparams ls)
  /-- **`∀`-formation** (`Infer.forallE`, `Rel.lean:576`): the domain's
  type reduces to a sort `u`, the body's type (under the domain)
  reduces to a sort `v`, the result is `Sort (imax u v)`.  Nothing is
  checked beyond Lean's own rule. -/
  | pi {Γ : List Expr} {A B s t : Expr} {u v : Level} :
      Infer env Γ A s → Red env Γ s (sort u) →
      Infer env (A :: Γ) B t → Red env (A :: Γ) t (sort v) →
      Infer env Γ (pi A B) (sort (.imax u v))
  /-- **Lambda** (`Infer.lam`, `Rel.lean:589`): the domain's type reduces to
  a sort, the body is inferred under the domain, and the result is the
  `∀` of the body's type — Lean's own rule.  The body's type's sort is
  not computed: an inferred type is a type (`InferSem`), which is all
  the `∀`'s invariant asks of it, and the body's value is read by the
  interpretation, not by its sort. -/
  | lam {Γ : List Expr} {A b s bt : Expr} {u : Level} :
      Infer env Γ A s → Red env Γ s (sort u) →
      Infer env (A :: Γ) b bt →
      Infer env Γ (lam A b) (pi A bt)
  /-- **Application** (`Infer.app`, `Rel.lean:617`): the head's type
  reduces to a `∀`, and the argument's inferred type is definitionally
  equal to its domain.  This is where a syntactic proof would need
  Π-injectivity and the semantic one does not: the `∀` the head's type
  reduces to *is* a function space, and membership in it is what the
  model needs (`Sound.lean`, `infer_sound`'s `app` case). -/
  | app {Γ : List Expr} {f a tf A B ta : Expr} :
      Infer env Γ f tf → Red env Γ tf (pi A B) →
      Infer env Γ a ta → DefEq env Γ ta A →
      Infer env Γ (app f a) (B.inst a)
  /-- **`let`, by substitution** (official `infer_let`
  with the body instantiated rather than opened at a let-variable, as
  the checker does): the type's type reduces to a
  sort, the value's inferred type is definitionally equal to the type,
  and the result is the inferred type of the body with the value
  substituted.  The two checks on the value are Lean's (they reject
  `let x : T := v; b` with `v : T` false even where the body ignores
  `x`); the soundness proof does not use them (`Sound.lean`,
  `Infer.letE_sound`), because `interp` reads no type and the body is
  inferred at the value itself. -/
  | letE {Γ : List Expr} {T v b s tv B : Expr} {u : Level} :
      Infer env Γ T s → Red env Γ s (sort u) →
      Infer env Γ v tv → DefEq env Γ tv T →
      Infer env Γ (b.inst v) B →
      Infer env Γ (letE T v b) B

end

end Fragment
