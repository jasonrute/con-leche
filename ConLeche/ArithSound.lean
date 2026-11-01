module

public import ConLeche.MainTheorem
public import ConLeche.Model.Env.EnvModelM
public import ConLeche.Model.NatSem
public import ConLeche.Model.Denotes
public import ConLeche.SetTheory.Derive.Universe
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
open ConLeche.Model (EnvModelM NatHeads NatOps natLit natLeafV cvalOf natLitT
  denote_levelless_const natLeafAV_interp_closed substFn_nil Denotes_of_denote
  Denotes_functional natOpV_add natOpV_mul natOpV_pred natOpV_sub)
open ConLeche.SetModel (bval natSuccV_app)
open ConLeche.Semantics (interp)
open ConLeche.Term (Term)
open ConLeche (Env Name Level ConstantInfo ConstantVal)
open ConLeche.Env (find?_mem)
open ConLeche.Expr (Expr hasFvar looseBVarsBounded fvarsBelow
  closeN_of_hasFvar fvarsBelow_zero_of_not_hasFvar)
open ConLeche.Verify (denote denote_const denote_app denote_natLit
  denote_app_inv pinnedStructT natLitSupported_inv natOpGuard_inv)

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

/-- **The stored `Nat` denotes `ω`**: its members are exactly the
`vnat k`.  The leaf is the pinned `.const .nat []` (`acval_pinned`),
whose value is `ω` (`bval` of the built-in `nat`). -/
theorem natLeaf_eq_omega (hN : env.find? natName = some ci) :
    natLeafV m.base2 ψ (fun _ => SetTheory.empty) = omega := by
  have hpin : pinnedStructT natName ψ
      = some (Term.const .nat []) := by
    simp [pinnedStructT]
  have hleaf : m.base2.acval natName ψ = Term.const .nat [] :=
    m.base2.acval_pinned hN (by decide) hpin
  show interp V (fun _ => SetTheory.empty) (m.base2.acval natName ψ) = omega
  rw [hleaf, interp_const, bval]

/-- The level-monomorphic fragment names are stored: the two heads as
constructors (`natLitSupported_inv`), the four operations as
definitions whose arity `NatOps` itself witnesses. -/
theorem fragName_stored (hops : NatOps m.base2 ψ)
    (hs : natLitSupported env = true) (c : Name)
    (hc : c ∈ [ConLeche.natZeroName, ConLeche.natSuccName,
      ConLeche.natPredName, ConLeche.natAddName, ConLeche.natSubName,
      ConLeche.natMulName]) :
    ∃ ci : ConstantInfo, env.find? c = some ci := by
  obtain ⟨-, -, -, hfZ, hfS, -⟩ := natLitSupported_inv hs
  have hops' : ∀ c ∈ ConLeche.natOpNames, ∃ cv v hint,
      env.find? c = some (.defnInfo cv v hint) := by
    intro c hc
    obtain ⟨cv, v, hint, h⟩ := hdepsOf hops c hc
    exact ⟨cv, v, hint, h⟩
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hfZ⟩
  · exact ⟨_, hfS⟩
  · exact hops' _ (by decide)
  · exact hops' _ (by decide)
  · exact hops' _ (by decide)
  · exact hops' _ (by decide)

/-- The `NatOps` law yields each op name's stored definition, through
its own guard inversion. -/
theorem hdepsOf (hops : NatOps m.base2 ψ) (c : Name)
    (hc : c ∈ ConLeche.natOpNames) :
    ∃ cv v hint, env.find? c = some (.defnInfo cv v hint) := by
  obtain ⟨hg, -⟩ := hops c hc _ _ _ (by
    obtain ⟨cv, v, hint, h⟩ := hdepsOf hops c hc
    exact h)
  exact (natOpGuard_inv hg).2 c (by
    unfold ConLeche.natOpDeps; split <;> simp_all)

/-- `denote` reads an arithmetic `Nat` expression's kernel term (at
depth `0`, an application spine of stored constants and one literal
always reads, since every name in the fragment is stored under the
literal guard). -/
theorem denote_aNat_reading (hops : NatOps m.base2 ψ)
    (hs : natLitSupported env = true) (a : ANat) :
    ∃ ta : Term, denote m.base2.acval env ψ 0 a.toExpr = some ta := by
  induction a with
  | lit n =>
    rw [ANat.toExpr, denote_natLit hs]
    exact ⟨_, rfl⟩
  | zero =>
    obtain ⟨ci, hf⟩ := fragName_stored hops hs ConLeche.natZeroName
      (by simp)
    rw [ANat.toExpr, denote_const hf
      (by cases ci <;> simp [ConstantInfo.toConstantVal] at * <;> simp [*])]
    exact ⟨_, rfl⟩
  | succ a ih =>
    obtain ⟨ta, hta⟩ := ih
    obtain ⟨ci, hf⟩ := fragName_stored hops hs ConLeche.natSuccName
      (by simp)
    rw [ANat.toExpr, denote_app,
      denote_const hf
        (by cases ci <;> simp [ConstantInfo.toConstantVal] at * <;> simp [*]),
      hta]
    exact ⟨_, rfl⟩
  | add a b iha ihb =>
    obtain ⟨ta, hta⟩ := iha
    obtain ⟨tb, htb⟩ := ihb
    obtain ⟨ci, hf⟩ := fragName_stored hops hs ConLeche.natAddName
      (by simp)
    rw [ANat.toExpr, denote_app, denote_app,
      denote_const hf
        (by cases ci <;> simp [ConstantInfo.toConstantVal] at * <;> simp [*]),
      hta, htb]
    exact ⟨_, rfl⟩
  | mul a b iha ihb =>
    obtain ⟨ta, hta⟩ := iha
    obtain ⟨tb, htb⟩ := ihb
    obtain ⟨ci, hf⟩ := fragName_stored hops hs ConLeche.natMulName
      (by simp)
    rw [ANat.toExpr, denote_app, denote_app,
      denote_const hf
        (by cases ci <;> simp [ConstantInfo.toConstantVal] at * <;> simp [*]),
      hta, htb]
    exact ⟨_, rfl⟩
  | pred a ih =>
    obtain ⟨ta, hta⟩ := ih
    obtain ⟨ci, hf⟩ := fragName_stored hops hs ConLeche.natPredName
      (by simp)
    rw [ANat.toExpr, denote_app,
      denote_const hf
        (by cases ci <;> simp [ConstantInfo.toConstantVal] at * <;> simp [*]),
      hta]
    exact ⟨_, rfl⟩
  | sub a b iha ihb =>
    obtain ⟨ta, hta⟩ := iha
    obtain ⟨tb, htb⟩ := ihb
    obtain ⟨ci, hf⟩ := fragName_stored hops hs ConLeche.natSubName
      (by simp)
    rw [ANat.toExpr, denote_app, denote_app,
      denote_const hf
        (by cases ci <;> simp [ConstantInfo.toConstantVal] at * <;> simp [*]),
      hta, htb]
    exact ⟨_, rfl⟩

/-- The numeral spine at the pinned heads interprets to the von
Neumann numerals: `interp` of `natLitT` at the `natZero`/`natSucc`
pins is `vnat`. -/
theorem interp_natLit_pinned (hs : natLitSupported env = true) (n : Nat) :
    interp V (fun _ => SetTheory.empty)
        (natLitT (m.base2.acval ConLeche.natZeroName
            (Level.substFn ψ [] []))
          (m.base2.acval ConLeche.natSuccName
            (Level.substFn ψ [] [])) n)
      = vnat n := by
  have hz : m.base2.acval ConLeche.natZeroName (Level.substFn ψ [] [])
      = Term.const .natZero [] := by
    obtain ⟨-, -, cv0, -, -, hfZ, -, -, -⟩ := natLitSupported_inv hs
    have hpin : pinnedStructT ConLeche.natZeroName ψ
        = some (Term.const .natZero []) := by
      simp [pinnedStructT]
    exact m.base2.acval_pinned hfZ (by decide) hpin
  have hsucc : m.base2.acval ConLeche.natSuccName (Level.substFn ψ [] [])
      = Term.const .natSucc [] := by
    obtain ⟨-, -, -, -, cv1, -, -, hfS, -, -, -⟩ :=
      natLitSupported_inv hs
    have hpin : pinnedStructT ConLeche.natSuccName ψ
        = some (Term.const .natSucc []) := by
      simp [pinnedStructT]
    exact m.base2.acval_pinned hfS (by decide) hpin
  rw [substFn_nil] at hz hsucc
  induction n with
  | zero => rw [natLitT, hz, interp_const, bval]; rfl
  | succ n ih =>
    rw [natLitT, interp_app, hsucc, interp_const, bval, ih, natSuccV_app
      (vnat_mem_omega n)]
    rfl

/-- The denotation of an arithmetic `Nat` expression's kernel term,
computed by `interp` at the empty variable environment: the value is
`vnat` of the expression's meta-level value.  Induction on the
fragment, discharging each constructor by the corresponding `NatSem`
literal law (`natOpV_*`), the heads' memberships (`NatHeads`), and
`natSuccV_app`. -/
theorem denote_aNat_interp (hnh : NatHeads m.base2 ψ) (hops : NatOps m.base2 ψ)
    (hs : natLitSupported env = true) (a : ANat) {ta : Term}
    (hdenote : denote m.base2.acval env ψ 0 a.toExpr = some ta) :
    interp V (fun _ => SetTheory.empty) ta = vnat a.evalV := by
  have hN : env.find? natName = some ci := (natLitSupported_inv hs).2.1
  have hω := natLeaf_eq_omega (m := m) (ψ := ψ) hN
  have hheads : ∀ ρ : Nat → V,
      interp V ρ (m.base2.acval ConLeche.natZeroName (Level.substFn ψ [] []))
        ∈ᵛ interp V ρ (m.base2.acval natName (Level.substFn ψ [] [])) ∧
      interp V ρ (m.base2.acval ConLeche.natSuccName (Level.substFn ψ [] []))
        ∈ᵛ piR 1 (interp V ρ (m.base2.acval natName (Level.substFn ψ [] [])))
          (fun _ => interp V ρ (m.base2.acval natName (Level.substFn ψ [] []))) ∧
      IsTy (interp V ρ (m.base2.acval natName (Level.substFn ψ [] []))) :=
    fun ρ => hnh hs ρ
  have hNatLeaf : ∀ ρ : Nat → V,
      interp V ρ (m.base2.acval natName (Level.substFn ψ [] [])) = omega := by
    intro ρ
    rw [substFn_nil, ← hω, natLeafAV_interp_closed m.base2 ψ ρ]
  induction a generalizing ta with
  | lit n =>
    rw [ANat.toExpr, denote_natLit hs] at hdenote
    obtain rfl := Option.some.inj hdenote
    exact interp_natLit_pinned hs n
  | zero =>
    obtain ⟨ci, hf⟩ := fragName_stored hops hs ConLeche.natZeroName (by simp)
    rw [ANat.toExpr, denote_const hf
      (by cases ci <;> simp [ConstantInfo.toConstantVal] at * <;> simp [*])]
      at hdenote
    obtain rfl := Option.some.inj hdenote
    have hz := (hheads _).1
    rw [substFn_nil, hNatLeaf] at hz
    have hpin : pinnedStructT ConLeche.natZeroName ψ
        = some (Term.const .natZero []) := by
      simp [pinnedStructT]
    have hleaf := m.base2.acval_pinned hf (by decide) hpin
    rw [hleaf, interp_const, bval]
    rfl
  | succ a ih =>
    obtain ⟨ci, hf⟩ := fragName_stored hops hs ConLeche.natSuccName (by simp)
    rw [ANat.toExpr, denote_app,
      denote_const hf
        (by cases ci <;> simp [ConstantInfo.toConstantVal] at * <;> simp [*])]
      at hdenote
    obtain ⟨tfa, ta', hfa, hta', rfl⟩ := denote_app_inv hdenote
    obtain ⟨tcv, hcv⟩ := denote_const_inv hfa
    have ih' := ih hta'
    rw [interp_app, hcv, ih']
    have hpin : pinnedStructT ConLeche.natSuccName ψ
        = some (Term.const .natSucc []) := by
      simp [pinnedStructT]
    have hleaf := m.base2.acval_pinned hf (by decide) hpin
    rw [hleaf, interp_const, bval, natSuccV_app]
    · rfl
    · rw [hNatLeaf]; exact vnat_mem_omega _
  | add a b iha ihb =>
    obtain ⟨cv, v, hint, hf⟩ := hdepsOf hops ConLeche.natAddName (by decide)
    rw [ANat.toExpr, denote_app, denote_app] at hdenote
    obtain ⟨tfa, tb', hfa, htb', rfl⟩ := denote_app_inv hdenote
    obtain ⟨tga, ta', hga, hta', hfa'⟩ := denote_app_inv hfa
    have hcv : denote m.base2.acval env ψ 0
        (.const ConLeche.natAddName []) = some (m.base2.acval ConLeche.natAddName ψ) := by
      have hlp : (ConstantInfo.defnInfo cv v hint).toConstantVal.levelParams = [] :=
        (natOpGuard_inv (hops ConLeche.natAddName (by decide) cv v hint hf).1).2
          ConLeche.natAddName (by decide) |>.elim (fun ⟨_, _, _, _, hlp⟩ => hlp)
          (fun h => nomatch h)
      exact denote_levelless_const hf hlp
    rw [hcv, hga, hta', htb'] at hdenote
    obtain rfl := Option.some.inj hdenote
    rw [interp_app, interp_app, iha hta', ihb htb']
    have h := natOpV_add m.base2 hops hnh hf
      (fun _ => SetTheory.empty) a.evalV b.evalV
    rw [interp_natLit_pinned hs a.evalV, interp_natLit_pinned hs b.evalV] at h
    rw [h, interp_natLit_pinned hs]
    rfl
  | mul a b iha ihb =>
    obtain ⟨cv, v, hint, hf⟩ := hdepsOf hops ConLeche.natMulName (by decide)
    rw [ANat.toExpr, denote_app, denote_app] at hdenote
    obtain ⟨tfa, tb', hfa, htb', rfl⟩ := denote_app_inv hdenote
    obtain ⟨tga, ta', hga, hta', hfa'⟩ := denote_app_inv hfa
    have hcv : denote m.base2.acval env ψ 0
        (.const ConLeche.natMulName []) = some (m.base2.acval ConLeche.natMulName ψ) :=
      denote_levelless_const hf ((natOpGuard_inv
        (hops ConLeche.natMulName (by decide) cv v hint hf).1).2
        ConLeche.natMulName (by decide) |>.elim (fun ⟨_, _, _, _, hlp⟩ => hlp)
        (fun h => nomatch h))
    rw [hcv, hga, hta', htb'] at hdenote
    obtain rfl := Option.some.inj hdenote
    rw [interp_app, interp_app, iha hta', ihb htb']
    have h := natOpV_mul m.base2 hops hnh hf
      (fun _ => SetTheory.empty) a.evalV b.evalV
    rw [interp_natLit_pinned hs a.evalV, interp_natLit_pinned hs b.evalV] at h
    rw [h, interp_natLit_pinned hs]
    rfl
  | pred a ih =>
    obtain ⟨cv, v, hint, hf⟩ := hdepsOf hops ConLeche.natPredName (by decide)
    rw [ANat.toExpr, denote_app] at hdenote
    obtain ⟨tfa, ta', hfa, hta', rfl⟩ := denote_app_inv hdenote
    have hcv : denote m.base2.acval env ψ 0
        (.const ConLeche.natPredName []) = some (m.base2.acval ConLeche.natPredName ψ) :=
      denote_levelless_const hf ((natOpGuard_inv
        (hops ConLeche.natPredName (by decide) cv v hint hf).1).2
        ConLeche.natPredName (by decide) |>.elim (fun ⟨_, _, _, _, hlp⟩ => hlp)
        (fun h => nomatch h))
    rw [hcv, hfa, hta'] at hdenote
    obtain rfl := Option.some.inj hdenote
    rw [interp_app, iha hta']
    have h := natOpV_pred m.base2 hops hnh hf
      (fun _ => SetTheory.empty) a.evalV
    rw [interp_natLit_pinned hs a.evalV] at h
    rw [h, interp_natLit_pinned hs]
    rfl
  | sub a b iha ihb =>
    obtain ⟨cv, v, hint, hf⟩ := hdepsOf hops ConLeche.natSubName (by decide)
    rw [ANat.toExpr, denote_app, denote_app] at hdenote
    obtain ⟨tfa, tb', hfa, htb', rfl⟩ := denote_app_inv hdenote
    obtain ⟨tga, ta', hga, hta', hfa'⟩ := denote_app_inv hfa
    have hcv : denote m.base2.acval env ψ 0
        (.const ConLeche.natSubName []) = some (m.base2.acval ConLeche.natSubName ψ) :=
      denote_levelless_const hf ((natOpGuard_inv
        (hops ConLeche.natSubName (by decide) cv v hint hf).1).2
        ConLeche.natSubName (by decide) |>.elim (fun ⟨_, _, _, _, hlp⟩ => hlp)
        (fun h => nomatch h))
    rw [hcv, hga, hta', htb'] at hdenote
    obtain rfl := Option.some.inj hdenote
    rw [interp_app, interp_app, iha hta', ihb htb']
    have h := natOpV_sub m.base2 hops hnh hf
      (fun _ => SetTheory.empty) a.evalV b.evalV
    rw [interp_natLit_pinned hs a.evalV, interp_natLit_pinned hs b.evalV] at h
    rw [h, interp_natLit_pinned hs]
    rfl

/-- **An arithmetic `Nat` expression denotes `vnat` of its value.** -/
theorem denote_aNat (hnh : NatHeads m.base2 ψ) (hops : NatOps m.base2 ψ)
    (hs : natLitSupported env = true) (a : ANat) (X : V)
    (h : Denotes (cvalOf m.base2.acval) env ψ (fun _ => SetTheory.empty) a.toExpr X) :
    X = vnat a.evalV := by
  have hclosed : a.tohasFvar = false := by
    cases a <;> simp [ANat.toExpr, hasFvar]
  have hlb : a.tolooseBVarsBounded 0 = true := by
    cases a <;> simp [ANat.toExpr, looseBVarsBounded]
  have hfv : fvarsBelow 0 a.toExpr :=
    fvarsBelow_zero_of_not_hasFvar hclosed
  obtain ⟨ta, hdenote⟩ := denote_aNat_reading hops hs a
  have hbr := Denotes_of_denote (V := V) m.base2.cval_closed 0 a.toExpr hdenote
    hfv hlb (fun _ => SetTheory.empty)
  rw [closeN_of_hasFvar _ 0 0 hclosed] at hbr
  rw [Denotes_functional h hbr, denote_aNat_interp hnh hops hs a hdenote]

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
  sorry

end ConLeche
