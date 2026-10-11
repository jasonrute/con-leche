module

public import Fragment.Uniform.Model
public import Fragment.Tele

@[expose] public section

/-!
# Uniform β: telescopes, terms and values (task #339)

The bridges of `Tele.lean`, read by `interpU` — the term-level fit
`TeleFitU`, its value form `TeleFitVU`, the residual and the
substitution chain, spines and their typed application chains
(`SpineOkU`) — and three facts about walking a telescope along values
that the uniform ι step needs (`mem_piBodyV`, `WDU_piBodyV`,
`teleFitVU_snoc`): the head applied to a fitting prefix lies in the
residual, the residual is well-denoted, and the last value meets the
residual's first binder.
-/

namespace Fragment.Uniform

open SetLib UnivLib PtLib

universe u

variable {V : Type u} [PtLib V] (M : Name → List Nat → V) (φ : Name → Nat)

/-- **A spine fitting a telescope**, read by `interpU` (`TeleFit`). -/
def TeleFitU (ρ : Nat → V) : Expr → List Expr → Prop
  | _, [] => True
  | .pi A _ B, a :: as => interpU M φ ρ a ∈ˢ interpU M φ ρ A ∧ TeleFitU ρ (B.inst a) as
  | _, _ :: _ => False

theorem interpU_mkAppN_appList (ρ : Nat → V) (f : Expr) (args : List Expr) :
    interpU M φ ρ (Expr.mkAppN f args) = appList (interpU M φ ρ f) (args.map (interpU M φ ρ)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => simp [ih]

theorem interpU_instChain (ρ : Nat → V) :
    ∀ (as : List Expr) (e : Expr),
      interpU M φ ρ (Expr.instChain e as) =
        interpU M φ (consList (as.map (interpU M φ ρ)).reverse ρ) e
  | [], e => rfl
  | a :: as, e => by
    rw [Expr.instChain_cons, interpU_instChain ρ as, interpU_inst]
    have hlen : (as.map (interpU M φ ρ)).reverse.length = as.length := by simp
    rw [← hlen, shiftE_consList, instE_consList]
    simp [consList_append]

theorem piBodyV_instU (a : Expr) : ∀ (vs : List V) (e : Expr) (k : Nat) (ρ : Nat → V)
    {B' : Expr} {ρ' : Nat → V},
    piBodyV (instE k (interpU M φ (shiftE k 0 ρ) a) ρ) e vs = some (B', ρ') →
    ∃ ρ'', piBodyV ρ (e.inst a k) vs = some (B'.inst a (k + vs.length), ρ'')
  | [], e, k, ρ, B', ρ', h => by
    simp [piBodyV] at h
    exact ⟨ρ, by simp [piBodyV, h.1]⟩
  | v :: vs, .pi A pw B, k, ρ, B', ρ', h => by
    simp only [piBodyV] at h
    have h' : piBodyV (instE (k + 1) (interpU M φ (shiftE (k + 1) 0 (cons v ρ)) a) (cons v ρ))
        B vs = some (B', ρ') := by
      rw [shiftE_succ_cons, ← cons_instE]; exact h
    obtain ⟨ρ'', h''⟩ := piBodyV_instU a vs B (k + 1) (cons v ρ) h'
    refine ⟨ρ'', ?_⟩
    simp only [Expr.inst_pi, piBodyV, List.length_cons, h'']
    congr 3
    omega
  | _ :: _, .bvar _, _, _, _, _, h => by simp [piBodyV] at h
  | _ :: _, .sort _, _, _, _, _, h => by simp [piBodyV] at h
  | _ :: _, .const _ _, _, _, _, _, h => by simp [piBodyV] at h
  | _ :: _, .app _ _, _, _, _, _, h => by simp [piBodyV] at h
  | _ :: _, .lam _ _ _, _, _, _, _, h => by simp [piBodyV] at h

/-- The residual is the substitution chain of the body the values
leave (`piResidual_of_piBodyV`). -/
theorem piResidual_of_piBodyVU (ρ : Nat → V) :
    ∀ {as : List Expr} {T R B : Expr} {ρ' : Nat → V},
      Expr.piResidual T as = some R →
      piBodyV ρ T (as.map (interpU M φ ρ)) = some (B, ρ') → R = Expr.instChain B as
  | [], T, R, B, _, h1, h2 => by
    rw [List.map_nil, piBodyV_nil] at h2
    simp only [Expr.piResidual_nil, Option.some.injEq] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    rw [← h1, h2.1]; rfl
  | a :: as, .pi A pw B₀, R, B, ρ', h1, h2 => by
    rw [Expr.piResidual_pi_cons] at h1
    simp only [List.map_cons, piBodyV] at h2
    rw [← instE_zero, ← shiftE_zero_zero (ρ := ρ)] at h2
    obtain ⟨ρ'', h''⟩ := piBodyV_instU M φ a _ B₀ 0 ρ h2
    rw [List.length_map, Nat.zero_add] at h''
    rw [piResidual_of_piBodyVU ρ h1 h'']
    rfl
  | _ :: _, .bvar _, _, _, _, h, _ => by simp [Expr.piResidual] at h
  | _ :: _, .sort _, _, _, _, h, _ => by simp [Expr.piResidual] at h
  | _ :: _, .const _ _, _, _, _, h, _ => by simp [Expr.piResidual] at h
  | _ :: _, .app _ _, _, _, _, h, _ => by simp [Expr.piResidual] at h
  | _ :: _, .lam _ _ _, _, _, _, h, _ => by simp [Expr.piResidual] at h

theorem teleFitVU_inst (a : Expr) : ∀ (vs : List V) (e : Expr) (k : Nat) (ρ : Nat → V),
    e.hasPis vs.length = true →
    (TeleFitVU M φ ρ (e.inst a k) vs ↔
      TeleFitVU M φ (instE k (interpU M φ (shiftE k 0 ρ) a) ρ) e vs)
  | [], _, _, _, _ => ⟨fun _ => TeleFitVU_nil M φ _ _, fun _ => TeleFitVU_nil M φ _ _⟩
  | v :: vs, .pi A pw B, k, ρ, h => by
    simp only [Expr.inst_pi, TeleFitVU]
    rw [interpU_inst, teleFitVU_inst a vs B (k + 1) (cons v ρ) (by simpa using h),
      shiftE_succ_cons, cons_instE]
  | _ :: _, .bvar _, _, _, h => by simp [Expr.hasPis] at h
  | _ :: _, .sort _, _, _, h => by simp [Expr.hasPis] at h
  | _ :: _, .const _ _, _, _, h => by simp [Expr.hasPis] at h
  | _ :: _, .app _ _, _, _, h => by simp [Expr.hasPis] at h
  | _ :: _, .lam _ _ _, _, _, h => by simp [Expr.hasPis] at h

/-- Terms fit when their values do (`teleFitV_of_teleFit`). -/
theorem teleFitVU_of_teleFitU (ρ : Nat → V) :
    ∀ {as : List Expr} {T : Expr}, T.hasPis as.length = true →
      TeleFitU M φ ρ T as → TeleFitVU M φ ρ T (as.map (interpU M φ ρ))
  | [], _, _, _ => TeleFitVU_nil M φ _ _
  | a :: as, .pi A pw B, hp, h => by
    obtain ⟨hmem, hfit⟩ := h
    refine ⟨hmem, ?_⟩
    have hp' : B.hasPis as.length = true := by simpa using hp
    have := teleFitVU_of_teleFitU ρ (Expr.hasPis_inst a B 0 _ hp') hfit
    rw [teleFitVU_inst M φ a _ B 0 ρ (by simpa using hp'), shiftE_zero_zero, instE_zero] at this
    exact this
  | _ :: _, .bvar _, _, h => h.elim
  | _ :: _, .sort _, _, h => h.elim
  | _ :: _, .const _ _, _, h => h.elim
  | _ :: _, .app _ _, _, h => h.elim
  | _ :: _, .lam _ _ _, _, h => h.elim

/-- The invariant of a spine gives the invariant of its head and of
every argument. -/
theorem WDU_mkAppN {ρ : Nat → V} :
    ∀ {f : Expr} {args : List Expr}, WDU M φ ρ (Expr.mkAppN f args) →
      WDU M φ ρ f ∧ ∀ a ∈ args, WDU M φ ρ a
  | _, [], h => ⟨h, by simp⟩
  | f, a :: args, h => by
    rw [Expr.mkAppN_cons] at h
    obtain ⟨h1, h2⟩ := WDU_mkAppN h
    rw [WDU_app] at h1
    refine ⟨h1.1, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h1.2.1
    · exact h2 b hb

/-- A spine is well-denoted when its head and arguments are and their
values form a typed application chain. -/
theorem WDU_mkAppN_of_spineOkU (ρ : Nat → V) :
    ∀ {f : Expr} {args : List Expr}, WDU M φ ρ f → (∀ a ∈ args, WDU M φ ρ a) →
      SpineOkU (interpU M φ ρ f) (args.map (interpU M φ ρ)) → WDU M φ ρ (Expr.mkAppN f args)
  | _, [], hf, _, _ => hf
  | f, a :: args, hf, has, hok => by
    obtain ⟨⟨p, A, B, hslot, hmem, hB, hT⟩, hrest⟩ := hok
    rw [Expr.mkAppN_cons]
    refine WDU_mkAppN_of_spineOkU ρ ?_ (fun b hb => has b (List.mem_cons_of_mem a hb)) hrest
    rw [WDU_app]
    exact ⟨hf, has a List.mem_cons_self, p, A, B, hslot, hmem, hB, hT⟩

/-! ## Walking a telescope along values -/

/-- The head applied to a fitting prefix lies in the residual. -/
theorem mem_piBodyV :
    ∀ {vs : List V} {T B : Expr} {ρ ρ' : Nat → V} {f : V},
      f ∈ˢ interpU M φ ρ T → TeleFitVU M φ ρ T vs → piBodyV ρ T vs = some (B, ρ') →
      appList f vs ∈ˢ interpU M φ ρ' B
  | [], T, B, ρ, ρ', f, hf, _, h => by
    simp only [piBodyV_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hf
  | v :: vs, .pi A pw B₀, B, ρ, ρ', f, hf, hfit, h => by
    obtain ⟨hv, hfit'⟩ := hfit
    simp only [piBodyV] at h
    rw [interpU_pi] at hf
    rw [appList_cons]
    exact mem_piBodyV (app_mem_piR hf hv) hfit' h
  | _ :: _, .bvar _, _, _, _, _, _, h, _ => h.elim
  | _ :: _, .sort _, _, _, _, _, _, h, _ => h.elim
  | _ :: _, .const _ _, _, _, _, _, _, h, _ => h.elim
  | _ :: _, .app _ _, _, _, _, _, _, h, _ => h.elim
  | _ :: _, .lam _ _ _, _, _, _, _, _, h, _ => h.elim

/-- The residual of a well-denoted telescope walked along fitting values
is well-denoted. -/
theorem WDU_piBodyV :
    ∀ {vs : List V} {T B : Expr} {ρ ρ' : Nat → V},
      WDU M φ ρ T → TeleFitVU M φ ρ T vs → piBodyV ρ T vs = some (B, ρ') → WDU M φ ρ' B
  | [], T, B, ρ, ρ', hT, _, h => by
    simp only [piBodyV_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hT
  | v :: vs, .pi A pw B₀, B, ρ, ρ', hT, hfit, h => by
    obtain ⟨hv, hfit'⟩ := hfit
    simp only [piBodyV] at h
    rw [WDU_pi] at hT
    exact WDU_piBodyV (hT.2.2.1 v hv) hfit' h
  | _ :: _, .bvar _, _, _, _, _, h, _ => h.elim
  | _ :: _, .sort _, _, _, _, _, h, _ => h.elim
  | _ :: _, .const _ _, _, _, _, _, h, _ => h.elim
  | _ :: _, .app _ _, _, _, _, _, h, _ => h.elim
  | _ :: _, .lam _ _ _, _, _, _, _, h, _ => h.elim

/-- A fit of a prefix and one more value: the prefix leaves a binder,
whose domain the last value meets. -/
theorem teleFitVU_snoc :
    ∀ {vs : List V} {v : V} {T : Expr} {ρ : Nat → V},
      TeleFitVU M φ ρ T (vs ++ [v]) →
      ∃ (A : Expr) (pw : PropWhen) (B : Expr) (ρ' : Nat → V),
        piBodyV ρ T vs = some (.pi A pw B, ρ') ∧ TeleFitVU M φ ρ T vs ∧
          v ∈ˢ interpU M φ ρ' A
  | [], v, .pi A pw B, ρ, h => ⟨A, pw, B, ρ, by simp [piBodyV], TeleFitVU_nil M φ _ _, h.1⟩
  | w :: vs, v, .pi A₀ pw₀ B₀, ρ, h => by
    obtain ⟨hw, h'⟩ := h
    obtain ⟨A, pw, B, ρ', hb, hfit, hv⟩ := teleFitVU_snoc h'
    exact ⟨A, pw, B, ρ', by simpa [piBodyV] using hb, ⟨hw, hfit⟩, hv⟩
  | [], _, .bvar _, _, h => h.elim
  | [], _, .sort _, _, h => h.elim
  | [], _, .const _ _, _, h => h.elim
  | [], _, .app _ _, _, h => h.elim
  | [], _, .lam _ _ _, _, h => h.elim
  | _ :: _, _, .bvar _, _, h => h.elim
  | _ :: _, _, .sort _, _, h => h.elim
  | _ :: _, _, .const _ _, _, h => h.elim
  | _ :: _, _, .app _ _, _, h => h.elim
  | _ :: _, _, .lam _ _ _, _, h => h.elim

end Fragment.Uniform
