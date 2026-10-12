module

public import ConLeche.Model.BasisCons
public import ConLeche.Semantics.EqTower

public section

/-!
# The hand-built basis towers, `Eq` family (task #161)

`pinnedStructT` has no entry for `Eq`, `Eq.refl` or `Eq.rec`, and
`BConst` has no such constructors, so `acval_basis_pinned` — which
unlocks the other blocks' leaves — is *empty* on `eqK`.  The leaves are
built by hand: `Semantics/EqTower.lean`'s `eqValT`/`eqReflValT`/
`eqRecValT`, and here their semantic-syntax towers.

The binders carry no regime: `interp` reads it off the values
(`lamV`).  `Eq`'s innermost body is a truth value, never the point, so
its tower is a graph wherever its domains are inhabited; `Eq.refl`'s
body is the proof, so its tower is the point.  Each inhabits its
pinned type's (value-read) reading by `lamV_mem`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (ITerm eqValT eqReflValT eqRecValT)
open ConLeche (Name)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The towers -/

/-- `Eq`'s valuation: `eqValT` in the semantic syntax. -/
@[expose] def eqValAV (ψ : Name → Nat) : ITerm :=
  .lam (.sort (ψ uN)) (.lam (.bvar 0) (.lam (.bvar 1)
    (.eqE (.bvar 1) (.bvar 0))))

/-- `Eq.refl`'s valuation: `.prf` under two binders (`Eq α a a` is a
proposition, so the tower reads as the point). -/
@[expose] def eqReflValAV (ψ : Name → Nat) : ITerm :=
  .lam (.sort (ψ uN)) (.lam (.bvar 0) .prf)

/-- `Eq.rec`'s valuation: the minor premise, returned, under six
binders. -/
@[expose] def eqRecValAV (ψ : Name → Nat) : ITerm :=
  .lam (.sort (ψ uN))
    (.lam (.bvar 0)
      (.lam (.pi (.bvar 1)
          (.pi (ITerm.mkAppN (eqValAV ψ) [.bvar 2, .bvar 1, .bvar 0])
            (.sort (ψ u1N))))
        (.lam (.app (.app (.bvar 0) (.bvar 1))
            (ITerm.mkAppN (eqReflValAV ψ) [.bvar 2, .bvar 1]))
          (.lam (.bvar 3)
            (.lam (ITerm.mkAppN (eqValAV ψ) [.bvar 4, .bvar 3, .bvar 0])
              (.bvar 2))))))

/-! ### Erasure: the towers project onto the `Term` towers -/

@[simp] theorem eqValAV_erase (ψ : Name → Nat) :
    (eqValAV ψ).erase = eqValT ψ := rfl

@[simp] theorem eqReflValAV_erase (ψ : Name → Nat) :
    (eqReflValAV ψ).erase = eqReflValT ψ := rfl

@[simp] theorem eqRecValAV_erase (ψ : Name → Nat) :
    (eqRecValAV ψ).erase = eqRecValT ψ := rfl

/-! ### The towers read the assignment only at their own level names -/

theorem eqValAV_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uN = ψ₂ uN) :
    eqValAV ψ₁ = eqValAV ψ₂ := by rw [eqValAV, eqValAV, h]

theorem eqReflValAV_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uN = ψ₂ uN) :
    eqReflValAV ψ₁ = eqReflValAV ψ₂ := by rw [eqReflValAV, eqReflValAV, h]

/-! ## `Eq`'s tower, interpreted -/

/-- **`Eq`'s tower, interpreted**: a three-deep `lamV` over the
truth-set former. -/
theorem eqValAV_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqValAV ψ)
      = lamV (univ (ψ uN))
        (fun a => lamV a (fun x => lamV a (fun y => eqv x y))) := by
  simp [eqValAV, cons]

/-- **The full spine's value** — `EqLaw`'s first conjunct at the tower:
three `app_lamV`, one per binder, each on its domain. -/
theorem eqValAV_app₃ (ψ : Name → Nat) (ρ : Nat → V) (A a b : V)
    (hA : A ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ A) (hb : b ∈ˢ A) :
    SetTheory.app (SetTheory.app (SetTheory.app
        (interp V ρ (eqValAV ψ)) A) a) b = eqv a b := by
  rw [eqValAV_interp, app_lamV hA, app_lamV ha, app_lamV hb]

/-- The tower inhabits the `Eq` former's function-space tower. -/
theorem eqValAV_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqValAV ψ) ∈ˢ piV (univ (ψ uN) : V)
      (fun a => piV a (fun _ => piV a (fun _ => univZero))) := by
  rw [eqValAV_interp]
  exact lamV_mem (fun _a _ => lamV_mem (fun _x _ =>
    lamV_mem (fun _y _ => eqv_mem_univZero _ _) (fun _ _ => IsTy_univZero))
    (fun _ _ => IsTy_piV)) (fun _ _ => IsTy_piV)

/-- The tower is graded (`WellDenoted`), at every environment. -/
theorem eqValAV_wellDenoted (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenoted V ρ (eqValAV ψ) := by
  refine ⟨trivial, IsTy_univ _, fun A hA => ⟨trivial, IsTy_of_mem_univ hA,
    fun a _ => ⟨trivial, IsTy_of_mem_univ hA,
    fun b _ => ⟨trivial, trivial⟩, ?_⟩, ?_⟩, ?_⟩
  · exact ⟨fun _ => univZero, fun _ _ => eqv_mem_univZero _ _,
      fun _ _ => IsTy_univZero⟩
  · exact ⟨fun _ => piV A (fun _ => univZero),
      fun _ _ => lamV_mem (fun _ _ => eqv_mem_univZero _ _) (fun _ _ => IsTy_univZero),
      fun _ _ => IsTy_piV⟩
  · exact ⟨fun x => piV x (fun _ => piV x (fun _ => univZero)),
      fun _ _ => lamV_mem (fun _ _ =>
        lamV_mem (fun _ _ => eqv_mem_univZero _ _) (fun _ _ => IsTy_univZero))
        (fun _ _ => IsTy_piV),
      fun _ _ => IsTy_piV⟩

/-! ## `Eq.refl`'s tower, interpreted: the point -/

/-- **`Eq.refl`'s tower, interpreted**: `pt`, because its body is the
proof at every value. -/
theorem eqReflValAV_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqReflValAV ψ) = (pt : V) := by
  simp only [eqReflValAV, interp_lam, interp_prf]
  exact lamV_eq_pt fun A _ => lamV_eq_pt fun _ _ => rfl

/-- The tower inhabits `Eq.refl`'s function-space tower: both fibres
are truth values, so it is `pt_mem_piR_zero_of` twice, bottoming at
`pt_mem_eqv_self`. -/
theorem eqReflValAV_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqReflValAV ψ) ∈ˢ piV (univ (ψ uN) : V)
      (fun a => piV a (fun x => eqv x x)) := by
  rw [eqReflValAV_interp, piV_eq_zero fun A _ => by
    rw [piV_eq_zero fun x _ => eqv_mem_univZero x x]; exact piR_zero_mem_univZero]
  exact pt_mem_piR_zero_of fun A _ => by
    rw [piV_eq_zero fun x _ => eqv_mem_univZero x x]
    exact pt_mem_piR_zero_of fun x _ => pt_mem_eqv_self x

theorem eqReflValAV_wellDenoted (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenoted V ρ (eqReflValAV ψ) := by
  refine ⟨trivial, IsTy_univ _, fun A hA => ⟨trivial, IsTy_of_mem_univ hA,
    fun _a _ => trivial, ?_⟩, ?_⟩
  · exact ⟨fun x => eqv x x, fun x _ => pt_mem_eqv_self x,
      fun x _ => IsTy_eqv x x⟩
  · exact ⟨fun x => piV x (fun y => eqv y y),
      fun _ _ => lamV_mem (fun y _ => pt_mem_eqv_self y) (fun y _ => IsTy_eqv y y),
      fun _ _ => IsTy_piV⟩

/-! ## `EqLaw`, discharged from the tower

`eqK`'s whole content, and the reason `eqLaw_cons_fresh` is structurally unavailable at this block
(its side condition is `eqName ≠ c₀.name` and the cons *is* `Eq`).
Both conjuncts come off `eqValAV` directly:

* the **value** clause is `eqValAV_app₃` — three `app_lamV`, one
  per binder, each on its own domain (the consumers read the
  three-fold form);
* the **grading** clause is the `WellDenoted` `.app` chain over
  `eqValAV_mem` (each slot read off the `piV` membership), plus
  `eqv_mem_univZero` for the propositionhood half. -/

/-- **The `Eq` spine over the tower is graded, and is a proposition.**
`EqLaw`'s second conjunct, factored out: the `Eq.refl` and `Eq.rec`
type readings both mention the spine directly, not through the
field. -/
theorem eqValAV_app₃_okP (ψ : Name → Nat) (ρ : Nat → V)
    {Aa la ra : ITerm} (hAa : WellDenoted V ρ Aa) (hla : WellDenoted V ρ la)
    (hra : WellDenoted V ρ ra)
    (hA : interp V ρ Aa ∈ˢ (univ (ψ uN) : V))
    (ha : interp V ρ la ∈ˢ interp V ρ Aa)
    (hb : interp V ρ ra ∈ˢ interp V ρ Aa) :
    WellDenoted V ρ (.app (.app (.app (eqValAV ψ) Aa) la) ra) ∧
      interp V ρ (.app (.app (.app (eqValAV ψ) Aa) la) ra)
        ∈ˢ (univZero : V) := by
  have hmem := eqValAV_mem (V := V) ψ ρ
  have h1 : SetTheory.app (interp V ρ (eqValAV ψ)) (interp V ρ Aa)
      ∈ˢ piV (interp V ρ Aa)
        (fun _ => piV (interp V ρ Aa) (fun _ => univZero)) :=
    app_mem_piV hmem hA
  have h2 : SetTheory.app (SetTheory.app (interp V ρ (eqValAV ψ))
        (interp V ρ Aa)) (interp V ρ la)
      ∈ˢ piV (interp V ρ Aa) (fun _ => univZero) :=
    app_mem_piV h1 ha
  have hAty : IsTy (interp V ρ Aa) := IsTy_of_mem_univ hA
  -- the application slot, read off a `piV` membership (`propN`)
  have slot : ∀ {f a A : V} {B : V → V}, f ∈ˢ piV A B → a ∈ˢ A → IsTy A →
      ∃ (v : Nat) (A' : V) (B' : V → V), f ∈ˢ piR v A' B' ∧ a ∈ˢ A' ∧
        (v = 0 → ∀ x, x ∈ˢ A' → B' x ∈ˢ (univZero : V)) ∧ (v ≠ 0 → IsTy A') :=
    fun {_ _ A B} hf ha hT => ⟨propN A B, A, B, hf, ha, propN_eq_zero.mp, fun _ => hT⟩
  refine ⟨⟨⟨⟨eqValAV_wellDenoted ψ ρ, hAa, slot hmem hA (IsTy_univ _)⟩,
      hla, slot h1 ha hAty⟩, hra, slot h2 hb hAty⟩, ?_⟩
  rw [interp_app, interp_app, interp_app,
    eqValAV_app₃ ψ ρ _ _ _ hA ha hb]
  exact eqv_mem_univZero _ _

/-- **`EqLaw` from the tower.**  Any environment carrier whose `Eq`
leaf is the annotated tower satisfies the field. -/
theorem eqLaw_of_tower {env : ConLeche.Env} (m : EnvModel V env)
    (hleaf : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValAV ψ) :
    EqLaw m := by
  intro _hf ψ
  refine ⟨fun ρ A a b hA ha hb => ?_, fun ρ Aa la ra hAa hla hra
    hA ha hb => ?_⟩
  · rw [hleaf]; exact eqValAV_app₃ ψ ρ A a b hA ha hb
  · rw [hleaf]
    exact eqValAV_app₃_okP ψ ρ hAa hla hra hA ha hb

end ConLeche.Model
