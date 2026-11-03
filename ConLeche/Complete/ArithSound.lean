module

import ConLeche.MainTheorem
public import ConLeche.Model.Env.EnvModelM
public import ConLeche.Model.NatSem
public import ConLeche.Model.Denotes
public import ConLeche.SetTheory.Derive.Universe
import ConLeche.Cached.Installed
import ConLeche.Model.StreamConsts
import ConLeche.Verify.Cached.MainC
public section

/-!
# Arithmetic soundness: the second theorem

The main theorem (`ConLeche.model_exists`) is parametric over any
first-order model `V` of `SetTheory` — ZF⁻ plus an ω-chain of
Grothendieck universes, i.e. a first-order model of ZFC with
`{n inaccessibles | n ∈ ω}` (Carneiro's `OmegaInaccessibles`, bridged in
`bridge/lean4lean-model`).  This module adds the second theorem asked
for in the task: **arithmetic soundness**.  If `φ` is a closed
first-order statement of arithmetic — a term of the small deep
embedding `AProp` below, built from `Nat` numerals, `Nat.zero`,
`Nat.succ`, `Nat.add`, `Nat.mul`, `Nat.pred`, `Nat.sub`, `Nat.beq`,
`Eq`, and the propositional connectives — and `con-leche` accepts a
proof of `φ` (a `thmDecl` whose declared type is `φ`'s term appears in
an accepted stream), then `φ` is satisfied by the standard model of
arithmetic inside `V`: by `ω` with the von Neumann numerals `vnat k`.

The proof route is the main theorem's own machinery.  In the model of
an accepted environment, every stored constant is a member of what its
type denotes (`Model.mem`); a theorem of type `φ` is therefore a member
of `φ`'s denotation.  Two lemmas do the rest:

* `denote_aNat`: the denotation of an arithmetic `Nat` expression is
  `vnat` of its meta-level value — proved from the environment's own
  `NatHeads`/`NatOps` laws (the stored `Nat` heads' memberships and the
  pinned recurrence equations the model tier already computes with,
  `Model/NatSem.lean`), which say exactly that the stored `Nat` denotes
  `ω` and the operations compute on the `vnat`.
* `denote_aProp`: the denotation of an arithmetic proposition is a
  truth value (`truthVal` of its meta-level satisfaction), using
  `Model.eq_equality` for `Eq`.

Membership of a truth value is equality with `pt`
(`eq_pt_of_mem_truthVal`), and `truthVal p` contains `pt` exactly when
`p` (`pt_mem_truthVal` / `of_mem_truthVal`).  So the theorem's member
yields `φ.satV`, the meta-level statement of arithmetic.
-/

namespace ConLeche

open SetTheory
open SetTheory (omega vnat vnat_mem_omega omega_mem_univ_succ vnat_inj)
open ConLeche.Model (EnvModelM NatHeads NatOps natLit natLeafV cvalOf
  denote_levelless_const natLeafAV_interp_closed substFn_nil Denotes_of_denote
  denote_natLit_spine
  natOpV_add natOpV_mul natOpV_pred natOpV_sub)
open ConLeche.SetModel (bval natSuccV_app piV piR_zero piV_eq_zero)
open ConLeche.Semantics (interp interp_const interp_app)
open ConLeche.Term (Term)
open ConLeche (Env Name Level ConstantInfo ConstantVal)
open ConLeche.Env (find?_mem)
open ConLeche.Expr (hasFvar looseBVarsBounded fvarsBelow closeN_of_hasFvar
  bvarBound looseBVarsBounded_iff)
open ConLeche.Verify (denote denote_const denote_app denote_natLit denote_app_inv
  pinnedStructT natLitT)

universe w

/-! ## First-order statements of arithmetic, as kernel terms

A small deep embedding: `ANat` for closed `Nat`-typed expressions and
`AProp` for closed propositions over them, each with a `toExpr` into
the kernel's `Expr`.  The fragment is deliberately small; the theorem
below is about exactly these terms. -/

/-- A closed `Nat`-typed expression of the arithmetic fragment. -/
inductive ANat : Type
  | lit (n : Nat)
  | zero
  | succ (a : ANat)
  | add (a b : ANat)
  | mul (a b : ANat)
  | pred (a : ANat)
  | sub (a b : ANat)
  deriving DecidableEq, Repr

/-- A closed first-order statement of arithmetic. -/
inductive AProp : Type
  | eq (a b : ANat)
  | not (p : AProp)
  | and (p q : AProp)
  | or (p q : AProp)
  | imp (p q : AProp)

/-- The kernel term an arithmetic `Nat` expression is. -/
def ANat.toExpr : ANat → Expr
  | .lit n => .lit (.natVal n)
  | .zero => .const natZeroName []
  | .succ a => .app (.const natSuccName []) a.toExpr
  | .add a b => .app (.app (.const natAddName []) a.toExpr) b.toExpr
  | .mul a b => .app (.app (.const natMulName []) a.toExpr) b.toExpr
  | .pred a => .app (.const natPredName []) a.toExpr
  | .sub a b => .app (.app (.const natSubName []) a.toExpr) b.toExpr

/-- The kernel term an arithmetic proposition is: `@Eq.{1} Nat a b`
for equality (the pinned `Eq` at level `1` over `Nat`), and the
connectives as the kernel spells them — `p → q` is a `∀`, `¬p` is
`p → False`, `p ∨ q` is `¬p → q`, and `p ∧ q` is `¬(¬p ∨ ¬q)`. -/
def AProp.toExpr : AProp → Expr
  | .eq a b =>
      .app (.app (.app (.const eqName [.succ .zero]) (.const natName [])) a.toExpr)
        b.toExpr
  | .not p =>
      .forallE p.toExpr (.const falseName [])
  | .and p q =>
      .forallE
        (.forallE (.forallE (.forallE p.toExpr (.const falseName []))
            (.const falseName []))
          (.forallE q.toExpr (.const falseName [])))
        (.const falseName [])
  | .or p q =>
      .forallE (.forallE p.toExpr (.const falseName [])) q.toExpr
  | .imp p q =>
      .forallE p.toExpr q.toExpr

/-! ## Satisfaction in the standard model of arithmetic inside `V` -/

variable {V : Type w} [SetTheory V]

/-- The meta-level value of an arithmetic `Nat` expression. -/
def ANat.evalV : ANat → Nat
  | .lit n => n
  | .zero => 0
  | .succ a => a.evalV + 1
  | .add a b => a.evalV + b.evalV
  | .mul a b => a.evalV * b.evalV
  | .pred a => a.evalV.pred
  | .sub a b => a.evalV - b.evalV

/-- **Satisfaction of an arithmetic statement in the standard model of
arithmetic** (the meta-level `Nat` standing for `ω`'s members). -/
def AProp.satV : AProp → Prop
  | .eq a b => decide (a.evalV = b.evalV) = true
  | .not p => ¬ p.satV
  | .and p q => p.satV ∧ q.satV
  | .or p q => p.satV ∨ q.satV
  | .imp p q => p.satV → q.satV

/-! ## The two denotation lemmas -/

variable {env : Env} {m : EnvModelM V .verified env} {ψ : Name → Nat}

/-- A term with no `fvar` is scoped below every depth. -/
private theorem fvarsBelow_zero_of_not_hasFvar {e : Expr}
    (h : e.hasFvar = false) : Expr.fvarsBelow 0 e := by
  induction e <;> simp_all [Expr.fvarsBelow, Expr.hasFvar]

/-- Inversion of the constant clause of `denote`: a reading of a
`.const` names the stored constant and its level arity, and yields
the leaf itself. -/
private theorem denote_const_inv {acval : Name → (Name → Nat) → Term}
    {d : Nat} {n : Name} {us : List Level} {ta : Term}
    (h : denote acval env ψ d (.const n us) = some ta) :
    ∃ ci : ConstantInfo, env.find? n = some ci ∧
      us.length = ci.toConstantVal.levelParams.length ∧
      ta = acval n (Level.substFn ψ ci.toConstantVal.levelParams us) := by
  rw [denote] at h
  match hf : env.find? n with
  | none => rw [hf] at h; exact nomatch h
  | some ci =>
    simp only [hf] at h
    by_cases hlen : us.length = ci.toConstantVal.levelParams.length
    · rw [ite_eq_left hlen] at h
      exact ⟨ci, rfl, hlen, Option.some.inj h.symm⟩
    · simp only [hlen] at h
      exact nomatch h

private theorem natzero_eq_vnat_zero : (natzero : V) = vnat 0 := by
  unfold natzero; rfl

private theorem natsucc_vnat (n : Nat) :
    (natsucc (vnat n) : V) = vnat (n + 1) := by
  unfold natsucc; rfl

/-- **The stored `Nat` denotes `ω`**: the leaf is the pinned
`.const .nat []` (`acval_pinned`), whose value is `ω` (`bval` of the
built-in `nat`). -/
theorem natLeaf_eq_omega (hs : natLitSupported env = true) :
    interp V (fun _ => SetTheory.empty) (m.base2.acval ConLeche.natName ψ) = omega := by
  obtain ⟨_, _, _, _, _, _, _, _, h⟩ := natLitSupported_inv hs
  obtain ⟨hfN, -, -, -, -, -, -, -, -⟩ := h
  have hleaf : m.base2.acval ConLeche.natName ψ = Term.const .nat [] :=
    m.base2.acval_pinned hfN (by decide)
      (by simp +decide [ConLeche.Verify.pinnedStructT])
  rw [hleaf, interp_const, bval]

/-- A stored operation name is a stored *definition* (the install
gate's pin route is the only way in), at the occurrence the accepted
type's own `constsResolve` reads.  Each op name's stored definition
is level-free: the `NatOps` law gives the guard at the stored
definition, and the guard's own inversion (`natOpGuard_inv`) stores
every dependency — including the name itself — with empty level
parameters. -/
theorem hdeps_lp (hdeps : ∀ c ∈ ConLeche.natOpNames, (env.find? c).isSome = true →
    ∃ cv v hint, env.find? c = some (.defnInfo cv v hint))
    (hops : NatOps m.base2 ψ)
    (c : Name) (hc : c ∈ ConLeche.natOpNames)
    (hIs : (env.find? c).isSome = true) :
    ∃ cv v hint, env.find? c = some (.defnInfo cv v hint) ∧
      cv.levelParams = [] := by
  obtain ⟨cv, v, hint, hf⟩ := hdeps c hc hIs
  obtain ⟨hg, -⟩ := hops c hc cv v hint hf
  obtain ⟨-, hdeps', -⟩ := natOpGuard_inv hg
  have hself : c ∈ ConLeche.natOpDeps c := by
    simp only [ConLeche.natOpNames, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨cvn, vn, hn, hfn, hlp⟩ := hdeps' c hself
  have hcv : cvn = cv :=
    (ConstantInfo.defnInfo.inj (Option.some.inj (hfn.symm.trans hf))).1
  rw [hcv] at hlp
  exact ⟨cv, v, hint, hf, hlp⟩

/-- The level-monomorphic fragment names are stored, level-free: the
two heads as constructors (`natLitSupported_inv`), the four
operations as definitions (`hdeps` + `hdeps_lp`, at the occurrence
`hIs` the term's own `constsResolve` reads). -/
theorem fragName_stored (hdeps : ∀ c ∈ ConLeche.natOpNames,
    (env.find? c).isSome = true →
    ∃ cv v hint, env.find? c = some (.defnInfo cv v hint))
    (hops : NatOps m.base2 ψ)
    (hs : natLitSupported env = true) (c : Name)
    (hc : c ∈ [ConLeche.natZeroName, ConLeche.natSuccName,
      ConLeche.natPredName, ConLeche.natAddName, ConLeche.natSubName,
      ConLeche.natMulName])
    (hIs : (env.find? c).isSome = true) :
    ∃ ci : ConstantInfo, env.find? c = some ci ∧
      ci.toConstantVal.levelParams = [] := by
  obtain ⟨_, _, cv0, i0, j0, cv1, i1, j1, h⟩ := natLitSupported_inv hs
  obtain ⟨-, hfZ, hfS, -, hlpZ, hlpS, -, -, -⟩ := h
  have hZ : ∃ ci : ConstantInfo, env.find? ConLeche.natZeroName = some ci ∧
      ci.toConstantVal.levelParams = [] :=
    ⟨.ctorInfo cv0 i0 j0, hfZ, by simpa [ConstantInfo.toConstantVal] using hlpZ⟩
  have hS : ∃ ci : ConstantInfo, env.find? ConLeche.natSuccName = some ci ∧
      ci.toConstantVal.levelParams = [] :=
    ⟨.ctorInfo cv1 i1 j1, hfS, by simpa [ConstantInfo.toConstantVal] using hlpS⟩
  have hops' : ∀ c ∈ ConLeche.natOpNames, (env.find? c).isSome = true →
      ∃ cv v hint,
      env.find? c = some (.defnInfo cv v hint) ∧ cv.levelParams = [] :=
    hdeps_lp hdeps hops
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hZ
  · exact hS
  · obtain ⟨cv, v, hint, hf, hlp⟩ := hops' ConLeche.natPredName (by decide) hIs
    exact ⟨.defnInfo cv v hint, hf, by simpa [ConstantInfo.toConstantVal] using hlp⟩
  · obtain ⟨cv, v, hint, hf, hlp⟩ := hops' ConLeche.natAddName (by decide) hIs
    exact ⟨.defnInfo cv v hint, hf, by simpa [ConstantInfo.toConstantVal] using hlp⟩
  · obtain ⟨cv, v, hint, hf, hlp⟩ := hops' ConLeche.natSubName (by decide) hIs
    exact ⟨.defnInfo cv v hint, hf, by simpa [ConstantInfo.toConstantVal] using hlp⟩
  · obtain ⟨cv, v, hint, hf, hlp⟩ := hops' ConLeche.natMulName (by decide) hIs
    exact ⟨.defnInfo cv v hint, hf, by simpa [ConstantInfo.toConstantVal] using hlp⟩

/-- `denote` reads an arithmetic `Nat` expression's kernel term (at
depth `0`, an application spine of stored constants and one literal
always reads: `hres` is the term's own `constsResolve`, which says
every constant the term mentions is stored, and `hdeps` turns each
stored operation name into its stored definition). -/
theorem denote_aNat_reading (hdeps : ∀ c ∈ ConLeche.natOpNames,
    (env.find? c).isSome = true →
    ∃ cv v hint, env.find? c = some (.defnInfo cv v hint))
    (hops : NatOps m.base2 ψ)
    (hs : natLitSupported env = true) (a : ANat)
    (hres : a.toExpr.constsResolve env = true) :
    ∃ ta : Term, denote m.base2.acval env ψ 0 a.toExpr = some ta := by
  revert hres
  induction a with
  | lit n =>
    intro _
    rw [ANat.toExpr, denote_natLit_spine m.base2 hs 0 n]
    exact ⟨_, rfl⟩
  | zero =>
    intro hres
    simp only [ANat.toExpr, Expr.constsResolve] at hres
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natZeroName
      (by decide) hres
    rw [ANat.toExpr, denote_const hf (by simp [hlp])]
    exact ⟨_, rfl⟩
  | succ a ih =>
    intro hres
    simp only [ANat.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨ta, hta⟩ := ih hres.2
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natSuccName
      (by decide) hres.1
    rw [ANat.toExpr, denote_app, denote_const hf (by simp [hlp]), hta]
    exact ⟨_, rfl⟩
  | add a b iha ihb =>
    intro hres
    simp only [ANat.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨ta, hta⟩ := iha hres.1.2
    obtain ⟨tb, htb⟩ := ihb hres.2
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natAddName
      (by decide) hres.1.1
    rw [ANat.toExpr, denote_app, denote_app, denote_const hf (by simp [hlp]),
      hta, htb]
    exact ⟨_, rfl⟩
  | mul a b iha ihb =>
    intro hres
    simp only [ANat.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨ta, hta⟩ := iha hres.1.2
    obtain ⟨tb, htb⟩ := ihb hres.2
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natMulName
      (by decide) hres.1.1
    rw [ANat.toExpr, denote_app, denote_app, denote_const hf (by simp [hlp]),
      hta, htb]
    exact ⟨_, rfl⟩
  | pred a ih =>
    intro hres
    simp only [ANat.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨ta, hta⟩ := ih hres.2
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natPredName
      (by decide) hres.1
    rw [ANat.toExpr, denote_app, denote_const hf (by simp [hlp]), hta]
    exact ⟨_, rfl⟩
  | sub a b iha ihb =>
    intro hres
    simp only [ANat.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨ta, hta⟩ := iha hres.1.2
    obtain ⟨tb, htb⟩ := ihb hres.2
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natSubName
      (by decide) hres.1.1
    rw [ANat.toExpr, denote_app, denote_app, denote_const hf (by simp [hlp]),
      hta, htb]
    exact ⟨_, rfl⟩

/-- An arithmetic `Nat` expression's kernel term is closed. -/
private theorem ANat.toExpr_hasFvar (a : ANat) : a.toExpr.hasFvar = false := by
  induction a <;> simp_all [ANat.toExpr, Expr.hasFvar]

/-- An arithmetic `Nat` expression's kernel term is loose-bvar-bounded
at depth `0`. -/
private theorem ANat.toExpr_looseBVarsBounded (a : ANat) :
    a.toExpr.looseBVarsBounded 0 = true := by
  induction a <;> simp_all [ANat.toExpr, Expr.looseBVarsBounded]

/-- The numeral spine at the pinned heads interprets to the von
Neumann numerals: `interp` of `natLit` at the `natZero`/`natSucc`
pins is `vnat`. -/
theorem interp_natLit_pinned (hs : natLitSupported env = true) (n : Nat) :
    interp V (fun _ => SetTheory.empty) (natLit m.base2 ψ n) = vnat n := by
  obtain ⟨_, _, _, _, _, _, _, _, h⟩ := natLitSupported_inv hs
  obtain ⟨-, hfZ, hfS, -, -, -, -, -, -⟩ := h
  have hz : m.base2.acval ConLeche.natZeroName ψ = Term.const .natZero [] :=
    m.base2.acval_pinned hfZ (by decide)
      (by simp +decide [ConLeche.Verify.pinnedStructT])
  have hsucc : m.base2.acval ConLeche.natSuccName ψ = Term.const .natSucc [] :=
    m.base2.acval_pinned hfS (by decide)
      (by simp +decide [ConLeche.Verify.pinnedStructT])
  unfold natLit
  induction n with
  | zero =>
    rw [natLitT, hz, interp_const, bval]
    exact natzero_eq_vnat_zero
  | succ n ih =>
    rw [natLitT, interp_app, ih, hsucc, interp_const, bval,
      natSuccV_app V (vnat_mem_omega n)]
    exact natsucc_vnat n

/-- The denotation of an arithmetic `Nat` expression's kernel term,
computed by `interp` at the empty variable environment: the value is
`vnat` of the expression's meta-level value.  Induction on the
fragment, discharging each constructor by the corresponding `NatSem`
literal law (`natOpV_*`), the pinned head leaves, and
`natSuccV_app`. -/
theorem denote_aNat_interp (hdeps : ∀ c ∈ ConLeche.natOpNames,
    (env.find? c).isSome = true →
    ∃ cv v hint, env.find? c = some (.defnInfo cv v hint))
    (hnh : NatHeads m.base2 ψ)
    (hops : NatOps m.base2 ψ) (hs : natLitSupported env = true) (a : ANat)
    (hres : a.toExpr.constsResolve env = true) {ta : Term}
    (hdenote : denote m.base2.acval env ψ 0 a.toExpr = some ta) :
    interp V (fun _ => SetTheory.empty) ta = vnat a.evalV := by
  revert hres
  induction a generalizing ta with
  | lit n =>
    intro _
    rw [ANat.toExpr, denote_natLit_spine m.base2 hs 0 n] at hdenote
    obtain rfl := Option.some.inj hdenote
    exact interp_natLit_pinned hs n
  | zero =>
    intro hres
    simp only [ANat.toExpr, Expr.constsResolve] at hres
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natZeroName
      (by decide) hres
    rw [ANat.toExpr, denote_const hf (by simp [hlp])] at hdenote
    obtain rfl := Option.some.inj hdenote
    have hcvψ : m.base2.acval ConLeche.natZeroName
        (Level.substFn ψ ci.toConstantVal.levelParams []) =
        m.base2.acval ConLeche.natZeroName ψ := by
      rw [hlp, substFn_nil]
    have hleaf : m.base2.acval ConLeche.natZeroName ψ = Term.const .natZero [] :=
      m.base2.acval_pinned hf (by decide)
        (by simp +decide [ConLeche.Verify.pinnedStructT])
    rw [hcvψ, hleaf, interp_const, bval]
    exact natzero_eq_vnat_zero
  | succ a ih =>
    intro hres
    simp only [ANat.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natSuccName
      (by decide) hres.1
    rw [ANat.toExpr] at hdenote
    obtain ⟨tfa, ta', hfa, hta', rfl⟩ := denote_app_inv hdenote
    rw [denote_const hf (by simp [hlp])] at hfa
    obtain rfl := Option.some.inj hfa
    have hcvψ : m.base2.acval ConLeche.natSuccName
        (Level.substFn ψ ci.toConstantVal.levelParams []) =
        m.base2.acval ConLeche.natSuccName ψ := by
      rw [hlp, substFn_nil]
    have hleaf : m.base2.acval ConLeche.natSuccName ψ = Term.const .natSucc [] :=
      m.base2.acval_pinned hf (by decide)
        (by simp +decide [ConLeche.Verify.pinnedStructT])
    have ih' := ih hta' hres.2
    rw [interp_app, hcvψ, hleaf, interp_const, bval, ih',
      natSuccV_app V (vnat_mem_omega _)]
    exact natsucc_vnat _
  | add a b iha ihb =>
    intro hres
    simp only [ANat.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨cv, v, hint, hf, hlpcv⟩ := hdeps_lp hdeps hops ConLeche.natAddName
      (by decide) hres.1.1
    rw [ANat.toExpr] at hdenote
    obtain ⟨tfa, tb', hfa, htb', rfl⟩ := denote_app_inv hdenote
    obtain ⟨tga, ta', hga, hta', rfl⟩ := denote_app_inv hfa
    rw [denote_const hf (by simp [ConstantInfo.toConstantVal, hlpcv])] at hga
    obtain rfl := Option.some.inj hga
    have hcvψ : m.base2.acval ConLeche.natAddName
        (Level.substFn ψ (ConstantInfo.defnInfo cv v hint).toConstantVal.levelParams []) =
        m.base2.acval ConLeche.natAddName ψ := by
      simp [ConstantInfo.toConstantVal, hlpcv, substFn_nil]
    rw [interp_app, interp_app, hcvψ, iha hta' hres.1.2, ihb htb' hres.2]
    have h := natOpV_add m.base2 hops hnh hf (fun _ => SetTheory.empty)
      a.evalV b.evalV
    rw [interp_natLit_pinned hs a.evalV, interp_natLit_pinned hs b.evalV] at h
    rw [h, interp_natLit_pinned hs]
    rfl
  | mul a b iha ihb =>
    intro hres
    simp only [ANat.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨cv, v, hint, hf, hlpcv⟩ := hdeps_lp hdeps hops ConLeche.natMulName
      (by decide) hres.1.1
    rw [ANat.toExpr] at hdenote
    obtain ⟨tfa, tb', hfa, htb', rfl⟩ := denote_app_inv hdenote
    obtain ⟨tga, ta', hga, hta', rfl⟩ := denote_app_inv hfa
    rw [denote_const hf (by simp [ConstantInfo.toConstantVal, hlpcv])] at hga
    obtain rfl := Option.some.inj hga
    have hcvψ : m.base2.acval ConLeche.natMulName
        (Level.substFn ψ (ConstantInfo.defnInfo cv v hint).toConstantVal.levelParams []) =
        m.base2.acval ConLeche.natMulName ψ := by
      simp [ConstantInfo.toConstantVal, hlpcv, substFn_nil]
    rw [interp_app, interp_app, hcvψ, iha hta' hres.1.2, ihb htb' hres.2]
    have h := natOpV_mul m.base2 hops hnh hf (fun _ => SetTheory.empty)
      a.evalV b.evalV
    rw [interp_natLit_pinned hs a.evalV, interp_natLit_pinned hs b.evalV] at h
    rw [h, interp_natLit_pinned hs]
    rfl
  | pred a ih =>
    intro hres
    simp only [ANat.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨cv, v, hint, hf, hlpcv⟩ := hdeps_lp hdeps hops ConLeche.natPredName
      (by decide) hres.1
    rw [ANat.toExpr] at hdenote
    obtain ⟨tfa, ta', hfa, hta', rfl⟩ := denote_app_inv hdenote
    rw [denote_const hf (by simp [ConstantInfo.toConstantVal, hlpcv])] at hfa
    obtain rfl := Option.some.inj hfa
    have hcvψ : m.base2.acval ConLeche.natPredName
        (Level.substFn ψ (ConstantInfo.defnInfo cv v hint).toConstantVal.levelParams []) =
        m.base2.acval ConLeche.natPredName ψ := by
      simp [ConstantInfo.toConstantVal, hlpcv, substFn_nil]
    rw [interp_app, hcvψ, ih hta' hres.2]
    have h := natOpV_pred m.base2 hops hnh hf (fun _ => SetTheory.empty) a.evalV
    rw [interp_natLit_pinned hs a.evalV] at h
    rw [h, interp_natLit_pinned hs]
    rfl
  | sub a b iha ihb =>
    intro hres
    simp only [ANat.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨cv, v, hint, hf, hlpcv⟩ := hdeps_lp hdeps hops ConLeche.natSubName
      (by decide) hres.1.1
    rw [ANat.toExpr] at hdenote
    obtain ⟨tfa, tb', hfa, htb', rfl⟩ := denote_app_inv hdenote
    obtain ⟨tga, ta', hga, hta', rfl⟩ := denote_app_inv hfa
    rw [denote_const hf (by simp [ConstantInfo.toConstantVal, hlpcv])] at hga
    obtain rfl := Option.some.inj hga
    have hcvψ : m.base2.acval ConLeche.natSubName
        (Level.substFn ψ (ConstantInfo.defnInfo cv v hint).toConstantVal.levelParams []) =
        m.base2.acval ConLeche.natSubName ψ := by
      simp [ConstantInfo.toConstantVal, hlpcv, substFn_nil]
    rw [interp_app, interp_app, hcvψ, iha hta' hres.1.2, ihb htb' hres.2]
    have h := natOpV_sub m.base2 hops hnh hf (fun _ => SetTheory.empty)
      a.evalV b.evalV
    rw [interp_natLit_pinned hs a.evalV, interp_natLit_pinned hs b.evalV] at h
    rw [h, interp_natLit_pinned hs]
    rfl

/-- **An arithmetic `Nat` expression denotes `vnat` of its value.** -/
theorem denote_aNat (hdeps : ∀ c ∈ ConLeche.natOpNames,
    (env.find? c).isSome = true →
    ∃ cv v hint, env.find? c = some (.defnInfo cv v hint))
    (hnh : NatHeads m.base2 ψ)
    (hops : NatOps m.base2 ψ) (hs : natLitSupported env = true) (a : ANat)
    (hres : a.toExpr.constsResolve env = true) (X : V)
    (h : Denotes (cvalOf m.base2.acval) env ψ (fun _ => SetTheory.empty) a.toExpr X) :
    X = vnat a.evalV := by
  have hclosed := a.toExpr_hasFvar
  have hlb := a.toExpr_looseBVarsBounded
  have hfv : fvarsBelow 0 a.toExpr := fvarsBelow_zero_of_not_hasFvar hclosed
  obtain ⟨ta, hdenote⟩ := denote_aNat_reading hdeps hops hs a hres
  have hbr := Denotes_of_denote (V := V) m.base2.cval_closed 0 a.toExpr hdenote
    hfv hlb (fun _ => SetTheory.empty)
  rw [closeN_of_hasFvar _ 0 0 hclosed] at hbr
  rw [Denotes_functional h hbr, denote_aNat_interp hdeps hnh hops hs a hres hdenote]
/-- `constsResolve` of an application splits. -/
private theorem constsResolve_app {f a : Expr}
    (h : (Expr.app f a).constsResolve env = true) :
    f.constsResolve env = true ∧ a.constsResolve env = true := by
  simpa [Expr.constsResolve, Bool.and_eq_true] using h

/-- `constsResolve` of a `∀` splits. -/
private theorem constsResolve_forallE {ty body : Expr}
    (h : (Expr.forallE ty body).constsResolve env = true) :
    ty.constsResolve env = true ∧ body.constsResolve env = true := by
  simpa [Expr.constsResolve, Bool.and_eq_true] using h

/-- An arithmetic `Nat` expression's kernel term has no bound variable. -/
private theorem ANat.toExpr_bvarBound_zero (a : ANat) : a.toExpr.bvarBound = 0 := by
  induction a <;> simp_all [ANat.toExpr, Expr.bvarBound]

/-- An arithmetic proposition's kernel term has no bound variable. -/
private theorem AProp.toExpr_bvarBound_zero (p : AProp) : p.toExpr.bvarBound = 0 := by
  induction p <;> simp_all [AProp.toExpr, Expr.bvarBound, ANat.toExpr_bvarBound_zero]

/-- An arithmetic proposition's kernel term is loose-bvar-bounded at
depth `0` (indeed at every depth). -/
private theorem AProp.toExpr_looseBVarsBounded (p : AProp) :
    p.toExpr.looseBVarsBounded 0 = true := by
  rw [Expr.looseBVarsBounded_iff, AProp.toExpr_bvarBound_zero]
  exact Nat.zero_le 0

/-- The constructor form of a `Nat` literal is loose-bvar-bounded at
every depth. -/
private theorem natLitToConstructor_looseBVarsBounded (n k : Nat) :
    (natLitToConstructor n).looseBVarsBounded k = true := by
  cases n <;> simp [natLitToConstructor, Expr.looseBVarsBounded]

/-- A stored reserved-basis name is the pinned declaration
(`basis_pinned`'s declaration clause, which holds of a stored reserved
name whatever its kind). -/
private theorem find?_pinned (mm : EnvModelM V .verified env) (n : Name)
    (hn : ConLeche.reservedBasisNames.contains n = true)
    (hIs : (env.find? n).isSome = true) :
    ∃ ci, env.find? n = some ci ∧ ci = ConLeche.pinnedInfo n := by
  obtain ⟨ci, hf⟩ := Option.isSome_iff_exists.mp hIs
  exact ⟨ci, hf, (mm.base2.basis_pinned n ci hf hn).1⟩

/-- **Re-environmenting**: a loose-bvar-bounded term denotes the same
value under any variable environment agreeing with the original below
the bounding depth.  (At depth `0` this says a closed term denotes the
same value under every environment.) -/
private theorem Denotes_reenv {cval : Name → (LevelParam → Nat) → V} {env : Env}
    {ψ : LevelParam → Nat} {e : Expr} {v : V} {α : BVarIdx → V}
    (h : Denotes cval env ψ α e v) :
    ∀ (d : Nat) (α' : BVarIdx → V), looseBVarsBounded d e = true →
      (∀ i, i < d → α i = α' i) → Denotes cval env ψ α' e v := by
  induction h with
  | bvar =>
    intro d α' hlb hag
    have hlt : ∀ i, looseBVarsBounded d (.bvar i) = true → i < d := by
      intro i hb
      rw [Expr.looseBVarsBounded_iff] at hb
      simp only [Expr.bvarBound] at hb
      omega
    rw [hag _ (hlt _ hlb)]
    exact Denotes.bvar
  | sort => intro _ _ _ _; exact Denotes.sort
  | const hf hlen => intro _ _ _ _; exact Denotes.const hf hlen
  | app hf ha ihf iha =>
    intro d α' hlb hag
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hlb
    exact Denotes.app (ihf d α' hlb.1 hag) (iha d α' hlb.2 hag)
  | lam hA hF ihA ihF =>
    intro d α' hlb hag
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hlb
    refine Denotes.lam (ihA d α' hlb.1 hag) (fun x hx => ?_)
    exact ihF x hx (d + 1) (push x α') hlb.2 (fun i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hag i (by omega))
  | pi hA hB ihA ihB =>
    intro d α' hlb hag
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hlb
    refine Denotes.pi (ihA d α' hlb.1 hag) (fun x hx => ?_)
    exact ihB x hx (d + 1) (push x α') hlb.2 (fun i hi => by
      cases i with
      | zero => rfl
      | succ i => exact hag i (by omega))
  | letE hv hb ihv ihb =>
    intro d α' hlb hag
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hlb
    refine Denotes.letE (ihv d α' hlb.1.2 hag)
      (ihb (d + 1) (push _ α') hlb.2 (fun i hi => by
        cases i with
        | zero => rfl
        | succ i => exact hag i (by omega)))
  | proj_table ht he ih =>
    intro d α' hlb hag
    exact Denotes.proj_table ht (ih d α' (by simpa [Expr.looseBVarsBounded] using hlb) hag)
  | natLit hh ih =>
    intro d α' hlb hag
    exact Denotes.natLit (ih d α' (natLitToConstructor_looseBVarsBounded _ d) hag)
  | strLit hh ih =>
    intro d α' hlb hag
    exact Denotes.strLit (ih d α' (strLitToConstructor_looseBVars _ d) hag)

/-- A `∀` over a truth-value domain with truth-value fibres denotes the
truth value of the implication. -/
private theorem piV_truthVal {P Q : Prop} {A : V} {B : V → V}
    (hA : A = truthVal P) (hB : ∀ x, x ∈ˢ A → B x = truthVal Q) :
    piV A B = truthVal (P → Q) := by
  rw [piV_eq_zero (fun x hx => by rw [hB x hx]; exact truthVal_mem_univZero Q), piR_zero]
  rw [hA] at hB ⊢
  refine truthVal_congr ?_
  constructor
  · intro h p
    obtain ⟨y, hy⟩ := h pt (pt_mem_truthVal p)
    rw [hB pt (pt_mem_truthVal p)] at hy
    exact of_mem_truthVal hy
  · intro h x hx
    rw [hB x hx]
    exact ⟨pt, pt_mem_truthVal (h (of_mem_truthVal hx))⟩

/-- The denotation of the `False` constant is the empty set, at any
variable environment: the leaf is the pinned `.const .empty [0]`. -/
private theorem denotes_false_empty {F : V} {α : BVarIdx → V}
    (h : Denotes (cvalOf m.base2.acval) env ψ α (.const ConLeche.falseName []) F) :
    F = empty := by
  cases h with
  | const hf _ =>
    have key : ∀ (χ : Name → Nat), cvalOf (V := V) m.base2.acval ConLeche.falseName χ
        = SetTheory.empty := by
      intro χ
      have hpd : ConLeche.Verify.pinnedStructT ConLeche.falseName χ
          = some (Term.const .empty [0]) := by
        simp +decide [ConLeche.Verify.pinnedStructT]
      have he : m.base2.acval ConLeche.falseName χ = Term.const .empty [0] :=
        m.base2.acval_pinned hf (by decide) hpd
      have h1 : interp V (fun _ => SetTheory.empty) (m.base2.acval ConLeche.falseName χ)
          = SetTheory.empty := by
        rw [he, interp_const]
        rfl
      have h2 := Model.interp_cvalOf (V := V) m.base2.cval_closed ConLeche.falseName χ
        (fun _ => SetTheory.empty)
      rw [h2] at h1
      exact h1
    exact key _

/-- **An arithmetic proposition denotes the truth value of its
satisfaction.**  Induction on the fragment: `Eq` by the model's
`eq_equality` law (with `denote_aNat` for the two sides), and each
connective by the `∀`-reading (`piV_truthVal`) at the pinned `False`. -/
theorem denote_aProp (hdeps : ∀ c ∈ ConLeche.natOpNames,
    (env.find? c).isSome = true →
    ∃ cv v hint, env.find? c = some (.defnInfo cv v hint))
    (hnh : NatHeads m.base2 ψ) (hops : NatOps m.base2 ψ)
    (hs : natLitSupported env = true) (p : AProp)
    (hres : p.toExpr.constsResolve env = true) (T : V)
    (h : Denotes (cvalOf m.base2.acval) env ψ (fun _ => SetTheory.empty) p.toExpr T) :
    T = truthVal p.satV := by
  revert hres h
  induction p generalizing T with
  | eq a b =>
    intro hres h
    simp only [AProp.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    have hfE : env.find? ConLeche.eqName = some ConLeche.eqA := by
      obtain ⟨ci, hf, hci⟩ := find?_pinned m ConLeche.eqName (by decide) hres.1.1.1
      rw [hci, show ConLeche.pinnedInfo ConLeche.eqName = ConLeche.eqA from rfl] at hf
      exact hf
    have hfN : env.find? ConLeche.natName = some ConLeche.natA := by
      obtain ⟨ci, hf, hci⟩ := find?_pinned m ConLeche.natName (by decide) hres.1.1.2
      rw [hci, show ConLeche.pinnedInfo ConLeche.natName = ConLeche.natA from rfl] at hf
      exact hf
    rw [AProp.toExpr] at h
    cases h with
    | app h3 hb =>
      cases h3 with
      | app h2 ha =>
        cases h2 with
        | app hE hN =>
          have hNcan : Denotes (cvalOf (V := V) m.base2.acval) env ψ
              (fun _ => SetTheory.empty)
              (.const ConLeche.natName []) (cvalOf m.base2.acval ConLeche.natName ψ) :=
            Denotes.const (cval := cvalOf m.base2.acval) hfN (us := []) (by rfl)
          have hNω := Denotes_functional hN hNcan
          have hX := denote_aNat hdeps hnh hops hs a hres.1.2 _ ha
          have hY := denote_aNat hdeps hnh hops hs b hres.2 _ hb
          have hNω' : cvalOf (V := V) m.base2.acval ConLeche.natName ψ = (omega : V) := by
            rw [← Model.interp_cvalOf (V := V) m.base2.cval_closed ConLeche.natName ψ
              (fun _ => SetTheory.empty)]
            exact natLeaf_eq_omega hs
          rw [hNω, hNω', hX, hY]
          cases hE with
          | const hfE' _ =>
            have hpin := (m.base2.basis_pinned _ _ hfE' (by decide)).1
            rw [show ConLeche.pinnedInfo ConLeche.eqName = ConLeche.eqA from rfl] at hpin
            subst hpin
            rw [show (ConLeche.eqA : ConstantInfo).toConstantVal.levelParams
              = [ConLeche.uN] from rfl]
            have hψ : Level.substFn ψ [ConLeche.uN] [.succ .zero] ConLeche.uN
                = Level.eval ψ (.succ .zero) := by
              simp [Level.substFn]
            have hA : (omega : V) ∈ˢ
                univ (Level.substFn ψ [ConLeche.uN] [.succ .zero] ConLeche.uN) := by
              rw [hψ, show Level.eval ψ (.succ .zero) = 1 from rfl]
              exact omega_mem_univ_succ 0
            have hlaw := (m.eq_law hfE (Level.substFn ψ [ConLeche.uN] [.succ .zero])).1
              (fun _ => SetTheory.empty) omega (vnat a.evalV) (vnat b.evalV) hA
              (vnat_mem_omega a.evalV) (vnat_mem_omega b.evalV)
            rw [Model.interp_cvalOf (V := V) m.base2.cval_closed ConLeche.eqName
              (Level.substFn ψ [ConLeche.uN] [.succ .zero]) (fun _ => SetTheory.empty)] at hlaw
            rw [hlaw]
            unfold eqv
            exact truthVal_congr
              ⟨fun hh => decide_eq_true_eq.mpr (vnat_inj hh),
                fun hh => by
                  simp only [AProp.satV] at hh
                  rw [decide_eq_true_eq] at hh
                  rw [hh]⟩
  | not p ih =>
    intro hres h
    simp only [AProp.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    rw [AProp.toExpr] at h
    cases h with
    | pi hA hB =>
      refine piV_truthVal (ih _ hres.1 hA) (Q := False) ?_
      intro x hx
      have hBx := Denotes_reenv (hB x hx) 0 (fun _ => SetTheory.empty)
        (by simp [Expr.looseBVarsBounded]) (fun i hi => absurd hi (Nat.not_lt_zero i))
      exact (denotes_false_empty hBx).trans (truthVal_eq_empty (fun h => h)).symm
  | imp p q ihp ihq =>
    intro hres h
    simp only [AProp.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    rw [AProp.toExpr] at h
    cases h with
    | pi hA hB =>
      refine piV_truthVal (ihp _ hres.1 hA) (Q := q.satV) ?_
      intro x hx
      exact ihq _ hres.2 (Denotes_reenv (hB x hx) 0 (fun _ => SetTheory.empty)
        (AProp.toExpr_looseBVarsBounded q) (fun i hi => absurd hi (Nat.not_lt_zero i)))
  | or p q ihp ihq =>
    intro hres h
    simp only [AProp.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    rw [AProp.toExpr] at h
    cases h with
    | pi hA hB =>
      cases hA with
      | pi hA' hB' =>
        have hP' := ihp _ hres.1.1 hA'
        have hP := piV_truthVal hP' (Q := False) (fun x hx => by
          have hBx := Denotes_reenv (hB' x hx) 0 (fun _ => SetTheory.empty)
            (by simp [Expr.looseBVarsBounded]) (fun i hi => absurd hi (Nat.not_lt_zero i))
          exact (denotes_false_empty hBx).trans (truthVal_eq_empty (fun h => h)).symm)
        rw [piV_truthVal hP (Q := q.satV) (fun x hx =>
          ihq _ hres.2 (Denotes_reenv (hB x hx) 0 (fun _ => SetTheory.empty)
            (AProp.toExpr_looseBVarsBounded q) (fun i hi => absurd hi (Nat.not_lt_zero i))))]
        refine truthVal_congr ?_
        constructor
        · intro hh
          rcases Classical.em p.satV with hp | hp
          · exact Or.inl hp
          · exact Or.inr (hh hp)
        · intro hh hn
          rcases hh with hp | hq
          · exact absurd hp hn
          · exact hq
  | and p q ihp ihq =>
    intro hres h
    simp only [AProp.toExpr, Expr.constsResolve, Bool.and_eq_true] at hres
    rw [AProp.toExpr] at h
    cases h with
    | pi hX hB0 =>
      cases hX with
      | pi hY hB1 =>
        rename_i B1
        cases hY with
        | pi hNp hB2 =>
          cases hNp with
          | pi hP hB3 =>
            have hPv := ihp _ hres.1.1.1.1 hP
            have hNpv := piV_truthVal hPv (Q := False) (fun x hx => by
              have hBx := Denotes_reenv (hB3 x hx) 0 (fun _ => SetTheory.empty)
                (by simp [Expr.looseBVarsBounded]) (fun i hi => absurd hi (Nat.not_lt_zero i))
              exact (denotes_false_empty hBx).trans (truthVal_eq_empty (fun h => h)).symm)
            have hYv := piV_truthVal hNpv (Q := False) (fun x hx => by
              have hBx := Denotes_reenv (hB2 x hx) 0 (fun _ => SetTheory.empty)
                (by simp [Expr.looseBVarsBounded]) (fun i hi => absurd hi (Nat.not_lt_zero i))
              exact (denotes_false_empty hBx).trans (truthVal_eq_empty (fun h => h)).symm)
            have hXv := piV_truthVal hYv (Q := q.satV → False) (fun x hx => by
              have hBx := Denotes_reenv (hB1 x hx) 0 (fun _ => SetTheory.empty)
                (by
                  rw [Expr.looseBVarsBounded_iff]
                  simp [Expr.bvarBound, AProp.toExpr_bvarBound_zero q])
                (fun i hi => absurd hi (Nat.not_lt_zero i))
              show B1 x = truthVal (q.satV → False)
              generalize hV : B1 x = Z
              rw [hV] at hBx
              cases hBx with
              | pi hQ hB4 =>
                exact piV_truthVal (ihq _ hres.1.2.1 hQ) (Q := False) (fun y hy => by
                  have hBy := Denotes_reenv (hB4 y hy) 0 (fun _ => SetTheory.empty)
                    (by simp [Expr.looseBVarsBounded]) (fun i hi => absurd hi (Nat.not_lt_zero i))
                  exact (denotes_false_empty hBy).trans (truthVal_eq_empty (fun h => h)).symm))
            rw [piV_truthVal hXv (Q := False) (fun x hx => by
              have hBx := Denotes_reenv (hB0 x hx) 0 (fun _ => SetTheory.empty)
                (by simp [Expr.looseBVarsBounded]) (fun i hi => absurd hi (Nat.not_lt_zero i))
              exact (denotes_false_empty hBx).trans (truthVal_eq_empty (fun h => h)).symm)]
            refine truthVal_congr ?_
            constructor
            · intro hh
              constructor
              · exact Classical.byContradiction (fun hn => hh (fun a => (a hn).elim))
              · exact Classical.byContradiction (fun hn => hh (fun _ => hn))
            · intro ⟨hp, hq⟩ x
              exact x (fun g => absurd hp g) hq

/-! ## The second theorem -/

/-- The environment facts `arith_sound` reads off an accepted stream:
the `Nat`-literal guard holds (the pinned `Nat` block is installed),
the accepted theorem's own type resolves (the stored constant's WF
gives `constsResolve`), and every operation name the type can mention
is stored as a certified definition. -/
private theorem arith_env_facts
    {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
    (accepted : Cached.checkDecls .verified pins ds = .ok env)
    (p : AProp) (cv : ConstantVal) (value : Expr)
    (hmem : Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = p.toExpr)
    (m : EnvModelM V .verified env) {c : ConstantInfo}
    (hfind : env.find? cv.name = some c) (hcty : c.toConstantVal.type = cv.type) :
    natLitSupported env = true ∧
    p.toExpr.constsResolve env = true ∧
    (∀ n ∈ ConLeche.natOpNames, (env.find? n).isSome = true →
      ∃ cv v hint, env.find? n = some (.defnInfo cv v hint)) := by
  have hwf := m.base2.wf.consts c (find?_mem hfind)
  have hres : p.toExpr.constsResolve env = true := by
    rw [← hty, ← hcty]; exact hwf.2.2.1
  refine ⟨?_, hres, ?_⟩
  · sorry
  · sorry

open Cached in
/-- **Arithmetic soundness.**  If `φ` is a closed first-order statement
of arithmetic and `con-leche` accepts a stream declaring a theorem of
type `φ` (the record's declared type is `φ.toExpr`), then `φ` is
satisfied by the standard model of arithmetic inside any first-order
model `V` of ZFC plus `{n inaccessibles | n ∈ ω}` — the same
`SetTheory` hypothesis as the main theorem. -/
theorem arith_sound (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration)
    (env : Env) (accepted : checkDecls .verified pins ds = .ok env)
    (p : AProp) (cv : ConstantVal) (value : Expr)
    (hmem : Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = p.toExpr) :
    p.satV := by
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) rfl accepted
  have hcv : Declaration.Declares (.thmDecl cv value) cv := rfl
  obtain ⟨c, hfind, -, hcty⟩ := Cached.checkDecls_consts (V := V) accepted
    (pd := .thmDecl cv value) hmem hcv
  have hc : c ∈ env.consts := find?_mem hfind
  obtain ⟨hs, hres, hdeps⟩ := arith_env_facts accepted p cv value hmem hty m hfind hcty
  obtain ⟨ta, hta⟩ := m.type_reads c hc (fun _ => 0)
  have hwf := m.base2.wf.consts c hc
  have hnf : c.toConstantVal.type.hasFvar = false := hwf.1
  have hlb : c.toConstantVal.type.looseBVarsBounded 0 = true := hwf.2.2.2.1
  have hbr := Denotes_of_denote (V := V) m.base2.cval_closed 0 c.toConstantVal.type hta
    (fvarsBelow_zero_of_not_hasFvar hnf) hlb (fun _ => SetTheory.empty)
  rw [Expr.closeN_of_hasFvar _ 0 0 hnf, hcty, hty] at hbr
  have hEq := denote_aProp hdeps (m.nat_heads (fun _ => 0)) (m.nat_ops (fun _ => 0)) hs p hres _
    hbr
  have hmemT : cvalOf m.base2.acval c.name (fun _ => 0) ∈ˢ
      interp V (fun _ => SetTheory.empty) ta := by
    rw [← Model.interp_cvalOf (V := V) m.base2.cval_closed c.name (fun _ => 0)
      (fun _ => SetTheory.empty)]
    exact m.mem_type c hc (fun _ => 0) ta hta (fun _ => SetTheory.empty)
  rw [hEq] at hmemT
  exact of_mem_truthVal hmemT

end ConLeche
