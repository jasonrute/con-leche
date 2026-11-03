module

public import ConLeche.MainTheorem
public import ConLeche.Model.Env.EnvModelM
public import ConLeche.Model.NatSem
public import ConLeche.Model.Denotes
public import ConLeche.SetTheory.Derive.Universe
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
open SetTheory (omega vnat vnat_mem_omega)
open ConLeche.Model (EnvModelM NatHeads NatOps natLit natLeafV cvalOf
  denote_levelless_const natLeafAV_interp_closed substFn_nil Denotes_of_denote
  denote_natLit_spine
  natOpV_add natOpV_mul natOpV_pred natOpV_sub)
open ConLeche.SetModel (bval natSuccV_app)
open ConLeche.Semantics (interp interp_const interp_app)
open ConLeche.Term (Term)
open ConLeche (Env Name Level ConstantInfo ConstantVal)
open ConLeche.Env (find?_mem)
open ConLeche.Expr (hasFvar looseBVarsBounded fvarsBelow closeN_of_hasFvar)
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
  | forallNat (p : ANat → AProp)

/-- The kernel term an arithmetic `Nat` expression is. -/
def ANat.toExpr : ANat → Expr
  | .lit n => .lit (.natVal n)
  | .zero => .const natZeroName []
  | .succ a => .app (.const natSuccName []) a.toExpr
  | .add a b => .app (.app (.const natAddName []) a.toExpr) b.toExpr
  | .mul a b => .app (.app (.const natMulName []) a.toExpr) b.toExpr
  | .pred a => .app (.const natPredName []) a.toExpr
  | .sub a b => .app (.app (.const natSubName []) a.toExpr) b.toExpr

/-- The kernel term an arithmetic proposition is: `@Eq Nat a b` for
equality (the pinned `Eq` at level `1` over `Nat`), and `Prop`-valued
formers for the connectives. -/
def AProp.toExpr : AProp → Expr
  | .eq a b =>
      .app (.app (.app (.const eqName [.succ .zero]) (.const natName [])) a.toExpr)
        b.toExpr
  | .not p =>
      .app (.const eqName [.succ .zero])
        (.app (.app (.const eqName [.zero]) p.toExpr) (.const falseName []))
  | .and p q =>
      .app (.app (.const andName []) p.toExpr) q.toExpr
  | .or p q =>
      .app (.app (.const eqName [.succ .zero])
        (.app (.app (.const eqName [.zero]) p.toExpr) (.const falseName [])))
        (.app (.app (.const eqName [.zero]) q.toExpr) (.const falseName []))
  | .imp p q =>
      .app (.app (.const eqName [.succ .zero])
        (.app (.app (.const eqName [.zero]) p.toExpr) (.const falseName []))) q.toExpr
  | .forallNat p =>
      .forallE (.const natName []) ((p (ANat.lit 0)).toExpr)

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
  | .forallNat p => ∀ n : Nat, (p (.lit n)).satV

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

/-- The fragment's operation names are stored as definitions.  In an
accepted environment this is read off the accepted theorem type's own
reading (every constant the type mentions is stored); `NatOps` then
hands back the guard at that stored definition. -/
theorem hdepsOf (hdeps : ∀ c ∈ ConLeche.natOpNames, ∃ cv v hint,
    env.find? c = some (.defnInfo cv v hint)) (c : Name)
    (hc : c ∈ ConLeche.natOpNames) :
    ∃ cv v hint, env.find? c = some (.defnInfo cv v hint) :=
  hdeps c hc

/-- Each op name's stored definition is level-free: the `NatOps` law
gives the guard at the stored definition, and the guard's own
inversion (`natOpGuard_inv`) stores every dependency — including the
name itself — with empty level parameters. -/
theorem hdeps_lp (hdeps : ∀ c ∈ ConLeche.natOpNames, ∃ cv v hint,
    env.find? c = some (.defnInfo cv v hint)) (hops : NatOps m.base2 ψ)
    (c : Name) (hc : c ∈ ConLeche.natOpNames) :
    ∃ cv v hint, env.find? c = some (.defnInfo cv v hint) ∧
      cv.levelParams = [] := by
  obtain ⟨cv, v, hint, hf⟩ := hdeps c hc
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
operations as definitions (`hdeps` + `hdeps_lp`). -/
theorem fragName_stored (hdeps : ∀ c ∈ ConLeche.natOpNames, ∃ cv v hint,
    env.find? c = some (.defnInfo cv v hint)) (hops : NatOps m.base2 ψ)
    (hs : natLitSupported env = true) (c : Name)
    (hc : c ∈ [ConLeche.natZeroName, ConLeche.natSuccName,
      ConLeche.natPredName, ConLeche.natAddName, ConLeche.natSubName,
      ConLeche.natMulName]) :
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
  have hops' : ∀ c ∈ ConLeche.natOpNames, ∃ cv v hint,
      env.find? c = some (.defnInfo cv v hint) ∧ cv.levelParams = [] :=
    hdeps_lp hdeps hops
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hZ
  · exact hS
  · obtain ⟨cv, v, hint, hf, hlp⟩ := hops' ConLeche.natPredName (by decide)
    exact ⟨.defnInfo cv v hint, hf, by simpa [ConstantInfo.toConstantVal] using hlp⟩
  · obtain ⟨cv, v, hint, hf, hlp⟩ := hops' ConLeche.natAddName (by decide)
    exact ⟨.defnInfo cv v hint, hf, by simpa [ConstantInfo.toConstantVal] using hlp⟩
  · obtain ⟨cv, v, hint, hf, hlp⟩ := hops' ConLeche.natSubName (by decide)
    exact ⟨.defnInfo cv v hint, hf, by simpa [ConstantInfo.toConstantVal] using hlp⟩
  · obtain ⟨cv, v, hint, hf, hlp⟩ := hops' ConLeche.natMulName (by decide)
    exact ⟨.defnInfo cv v hint, hf, by simpa [ConstantInfo.toConstantVal] using hlp⟩

/-- `denote` reads an arithmetic `Nat` expression's kernel term (at
depth `0`, an application spine of stored constants and one literal
always reads, since every name in the fragment is stored under the
literal guard). -/
theorem denote_aNat_reading (hdeps : ∀ c ∈ ConLeche.natOpNames, ∃ cv v hint,
    env.find? c = some (.defnInfo cv v hint)) (hops : NatOps m.base2 ψ)
    (hs : natLitSupported env = true) (a : ANat) :
    ∃ ta : Term, denote m.base2.acval env ψ 0 a.toExpr = some ta := by
  induction a with
  | lit n =>
    rw [ANat.toExpr, denote_natLit_spine m.base2 hs 0 n]
    exact ⟨_, rfl⟩
  | zero =>
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natZeroName
      (by decide)
    rw [ANat.toExpr, denote_const hf (by simp [hlp])]
    exact ⟨_, rfl⟩
  | succ a ih =>
    obtain ⟨ta, hta⟩ := ih
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natSuccName
      (by decide)
    rw [ANat.toExpr, denote_app, denote_const hf (by simp [hlp]), hta]
    exact ⟨_, rfl⟩
  | add a b iha ihb =>
    obtain ⟨ta, hta⟩ := iha
    obtain ⟨tb, htb⟩ := ihb
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natAddName
      (by decide)
    rw [ANat.toExpr, denote_app, denote_app, denote_const hf (by simp [hlp]),
      hta, htb]
    exact ⟨_, rfl⟩
  | mul a b iha ihb =>
    obtain ⟨ta, hta⟩ := iha
    obtain ⟨tb, htb⟩ := ihb
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natMulName
      (by decide)
    rw [ANat.toExpr, denote_app, denote_app, denote_const hf (by simp [hlp]),
      hta, htb]
    exact ⟨_, rfl⟩
  | pred a ih =>
    obtain ⟨ta, hta⟩ := ih
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natPredName
      (by decide)
    rw [ANat.toExpr, denote_app, denote_const hf (by simp [hlp]), hta]
    exact ⟨_, rfl⟩
  | sub a b iha ihb =>
    obtain ⟨ta, hta⟩ := iha
    obtain ⟨tb, htb⟩ := ihb
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natSubName
      (by decide)
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
theorem denote_aNat_interp (hdeps : ∀ c ∈ ConLeche.natOpNames, ∃ cv v hint,
    env.find? c = some (.defnInfo cv v hint)) (hnh : NatHeads m.base2 ψ)
    (hops : NatOps m.base2 ψ) (hs : natLitSupported env = true) (a : ANat) {ta : Term}
    (hdenote : denote m.base2.acval env ψ 0 a.toExpr = some ta) :
    interp V (fun _ => SetTheory.empty) ta = vnat a.evalV := by
  induction a generalizing ta with
  | lit n =>
    rw [ANat.toExpr, denote_natLit_spine m.base2 hs 0 n] at hdenote
    obtain rfl := Option.some.inj hdenote
    exact interp_natLit_pinned hs n
  | zero =>
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natZeroName
      (by decide)
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
    obtain ⟨ci, hf, hlp⟩ := fragName_stored hdeps hops hs ConLeche.natSuccName
      (by decide)
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
    have ih' := ih hta'
    rw [interp_app, hcvψ, hleaf, interp_const, bval, ih',
      natSuccV_app V (vnat_mem_omega _)]
    exact natsucc_vnat _
  | add a b iha ihb =>
    obtain ⟨cv, v, hint, hf, hlpcv⟩ := hdeps_lp hdeps hops ConLeche.natAddName
      (by decide)
    rw [ANat.toExpr] at hdenote
    obtain ⟨tfa, tb', hfa, htb', rfl⟩ := denote_app_inv hdenote
    obtain ⟨tga, ta', hga, hta', rfl⟩ := denote_app_inv hfa
    rw [denote_const hf (by simp [ConstantInfo.toConstantVal, hlpcv])] at hga
    obtain rfl := Option.some.inj hga
    have hcvψ : m.base2.acval ConLeche.natAddName
        (Level.substFn ψ (ConstantInfo.defnInfo cv v hint).toConstantVal.levelParams []) =
        m.base2.acval ConLeche.natAddName ψ := by
      simp [ConstantInfo.toConstantVal, hlpcv, substFn_nil]
    rw [interp_app, interp_app, hcvψ, iha hta', ihb htb']
    have h := natOpV_add m.base2 hops hnh hf (fun _ => SetTheory.empty)
      a.evalV b.evalV
    rw [interp_natLit_pinned hs a.evalV, interp_natLit_pinned hs b.evalV] at h
    rw [h, interp_natLit_pinned hs]
    rfl
  | mul a b iha ihb =>
    obtain ⟨cv, v, hint, hf, hlpcv⟩ := hdeps_lp hdeps hops ConLeche.natMulName
      (by decide)
    rw [ANat.toExpr] at hdenote
    obtain ⟨tfa, tb', hfa, htb', rfl⟩ := denote_app_inv hdenote
    obtain ⟨tga, ta', hga, hta', rfl⟩ := denote_app_inv hfa
    rw [denote_const hf (by simp [ConstantInfo.toConstantVal, hlpcv])] at hga
    obtain rfl := Option.some.inj hga
    have hcvψ : m.base2.acval ConLeche.natMulName
        (Level.substFn ψ (ConstantInfo.defnInfo cv v hint).toConstantVal.levelParams []) =
        m.base2.acval ConLeche.natMulName ψ := by
      simp [ConstantInfo.toConstantVal, hlpcv, substFn_nil]
    rw [interp_app, interp_app, hcvψ, iha hta', ihb htb']
    have h := natOpV_mul m.base2 hops hnh hf (fun _ => SetTheory.empty)
      a.evalV b.evalV
    rw [interp_natLit_pinned hs a.evalV, interp_natLit_pinned hs b.evalV] at h
    rw [h, interp_natLit_pinned hs]
    rfl
  | pred a ih =>
    obtain ⟨cv, v, hint, hf, hlpcv⟩ := hdeps_lp hdeps hops ConLeche.natPredName
      (by decide)
    rw [ANat.toExpr] at hdenote
    obtain ⟨tfa, ta', hfa, hta', rfl⟩ := denote_app_inv hdenote
    rw [denote_const hf (by simp [ConstantInfo.toConstantVal, hlpcv])] at hfa
    obtain rfl := Option.some.inj hfa
    have hcvψ : m.base2.acval ConLeche.natPredName
        (Level.substFn ψ (ConstantInfo.defnInfo cv v hint).toConstantVal.levelParams []) =
        m.base2.acval ConLeche.natPredName ψ := by
      simp [ConstantInfo.toConstantVal, hlpcv, substFn_nil]
    rw [interp_app, hcvψ, ih hta']
    have h := natOpV_pred m.base2 hops hnh hf (fun _ => SetTheory.empty) a.evalV
    rw [interp_natLit_pinned hs a.evalV] at h
    rw [h, interp_natLit_pinned hs]
    rfl
  | sub a b iha ihb =>
    obtain ⟨cv, v, hint, hf, hlpcv⟩ := hdeps_lp hdeps hops ConLeche.natSubName
      (by decide)
    rw [ANat.toExpr] at hdenote
    obtain ⟨tfa, tb', hfa, htb', rfl⟩ := denote_app_inv hdenote
    obtain ⟨tga, ta', hga, hta', rfl⟩ := denote_app_inv hfa
    rw [denote_const hf (by simp [ConstantInfo.toConstantVal, hlpcv])] at hga
    obtain rfl := Option.some.inj hga
    have hcvψ : m.base2.acval ConLeche.natSubName
        (Level.substFn ψ (ConstantInfo.defnInfo cv v hint).toConstantVal.levelParams []) =
        m.base2.acval ConLeche.natSubName ψ := by
      simp [ConstantInfo.toConstantVal, hlpcv, substFn_nil]
    rw [interp_app, interp_app, hcvψ, iha hta', ihb htb']
    have h := natOpV_sub m.base2 hops hnh hf (fun _ => SetTheory.empty)
      a.evalV b.evalV
    rw [interp_natLit_pinned hs a.evalV, interp_natLit_pinned hs b.evalV] at h
    rw [h, interp_natLit_pinned hs]
    rfl

/-- **An arithmetic `Nat` expression denotes `vnat` of its value.** -/
theorem denote_aNat (hdeps : ∀ c ∈ ConLeche.natOpNames, ∃ cv v hint,
    env.find? c = some (.defnInfo cv v hint)) (hnh : NatHeads m.base2 ψ)
    (hops : NatOps m.base2 ψ) (hs : natLitSupported env = true) (a : ANat) (X : V)
    (h : Denotes (cvalOf m.base2.acval) env ψ (fun _ => SetTheory.empty) a.toExpr X) :
    X = vnat a.evalV := by
  have hclosed := a.toExpr_hasFvar
  have hlb := a.toExpr_looseBVarsBounded
  have hfv : fvarsBelow 0 a.toExpr := fvarsBelow_zero_of_not_hasFvar hclosed
  obtain ⟨ta, hdenote⟩ := denote_aNat_reading hdeps hops hs a
  have hbr := Denotes_of_denote (V := V) m.base2.cval_closed 0 a.toExpr hdenote
    hfv hlb (fun _ => SetTheory.empty)
  rw [closeN_of_hasFvar _ 0 0 hclosed] at hbr
  rw [Denotes_functional h hbr, denote_aNat_interp hdeps hnh hops hs a hdenote]

/-- **An arithmetic proposition denotes the truth value of its
satisfaction.** -/
theorem denote_aProp (m' : ConLeche.Model V env)
    (hnh : NatHeads m.base2 ψ) (hops : NatOps m.base2 ψ)
    (p : AProp) (T : V)
    (h : Denotes m'.cval env ψ (fun _ => SetTheory.empty) p.toExpr T) :
    T = truthVal p.satV := by
  sorry

/-! ## The second theorem -/

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
  obtain ⟨c, hfind, -, hcty⟩ := Cached.checkDecls_consts (V := V) accepted
    (pd := .thmDecl cv value) (cv := cv) hmem rfl
  have hc : c ∈ env.consts := find?_mem hfind
  obtain ⟨T, hT, hmemT⟩ := (Model.Model.ofEnvModelM m).mem c hc (fun _ => 0)
    (fun _ => SetTheory.empty)
  rw [hcty, hty] at hT
  rw [denote_aProp (Model.Model.ofEnvModelM m) (m.nat_heads (fun _ => 0))
    (m.nat_ops (fun _ => 0)) p T hT] at hmemT
  exact of_mem_truthVal hmemT

end ConLeche
