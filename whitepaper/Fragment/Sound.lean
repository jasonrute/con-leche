module

public import Fragment.Motive
public import Fragment.Tele

public section

/-!
# Soundness: derivation ⇒ claim

**One mutual structural induction over the three relations**
(`red_sound`/`defeq_sound`/`infer_sound` at the end of this file);
every case is one lemma about one rule, stated over the environment's
laws (`EnvModel`) and the library (`SetLib`), never over an
implementation.  This is the shape of `ConLeche/Model/Rules/Sound.lean`
and its per-rule lemma files, on the fragment.

The case split proof/non-proof is in the proof and only there.  A
reduction claims nothing of a subject that denotes the point; on one
that does not, β is sound at *every* binder: the redex is not the
point, so its λ is not (`app pt _ = pt`), so the λ's annotation does
not hold at this valuation and the λ is a graph, which determines its
domain (`Red.beta_sound`).  Whether a subject denotes the point is
never decided by the checker: the definitional-equality claim is about
two sides that do not, and the typed invariant makes the proof-ness of
the two sides of every sub-comparison agree (a graph-regime slot's
domain is a type, so its members are all the point or none of it,
`DefEq.app_sound`).  Inferred types are types (`InferSem`), hence never
the point, so the reductions of types that inference runs are sound
outright.

The cases the paper dwells on, each its own lemma:

* `Red.beta_sound` — β at every binder, with no certificate;
* `Red.iota_core` and `major_eq` — ι with no β certificate on the
  major, even on a recursion over proofs: the major's binder domain is
  a type, so the major and its reduct are both the point or neither is;
* `DefEq.eta_sound` — η, from the library's η law;
* `DefEq.proofIrrel_sound` — proof irrelevance claims nothing: two
  proofs are the point, and the claim is about non-proofs;
* `Infer.app_sound` — the application rule, where no Π-injectivity is
  needed.
-/

namespace Fragment
open SetLib

universe u

variable {V : Type u} [SetLib V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## Small facts -/

/-- The oracle's `eq` is `eval`-equality at the valuation. -/
theorem eval_eq_of_oracle [LevelOracle] {u v : Level} (h : LevelOracle.eq u v = true) :
    Level.eval φ u = Level.eval φ v :=
  (LevelOracle.eq_iff u v).mp h φ

/-- A checked annotation reads `true` exactly where the sort is zero. -/
theorem holds_of_zeroness {v : Level} {pw : PropWhen} (h : Level.zeroness v = pw) :
    pw.holds φ = true ↔ Level.eval φ v = 0 := by
  subst h; exact Level.holds_zeroness φ v

/-- A list of length `n + 1` is its first `n` elements and its last. -/
theorem List.take_append_getD {α : Type} (d : α) :
    ∀ (l : List α) (n : Nat), l.length = n + 1 → l = l.take n ++ [l.getD n d]
  | [], _, h => by simp at h
  | _ :: l, 0, h => by
    simp at h
    simp [h]
  | a :: l, n + 1, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.take_succ_cons, List.getD_cons_succ, List.cons_append]
    rw [← take_append_getD d l n h]

/-- The head of an application that is not the point is not the point. -/
theorem fn_ne_pt {f a : Expr} {ρ : Nat → V}
    (h : interp m.M φ ρ (.app f a) ≠ pt) : interp m.M φ ρ f ≠ pt := by
  intro hf; apply h; rw [interp_app, hf, app_pt]

/-! ## Reduction -/

namespace Red

theorem refl_sound {Γ : List Expr} {e : Expr} : RedSem m φ Γ e e :=
  fun _ _ h _ => ⟨h, rfl⟩

theorem trans_sound {Γ : List Expr} {e₁ e₂ e₃ : Expr}
    (h₁ : RedSem m φ Γ e₁ e₂) (h₂ : RedSem m φ Γ e₂ e₃) : RedSem m φ Γ e₁ e₃ := by
  intro ρ hs hw hn
  obtain ⟨hw₁, he₁⟩ := h₁ ρ hs hw hn
  obtain ⟨hw₂, he₂⟩ := h₂ ρ hs hw₁ (he₁ ▸ hn)
  exact ⟨hw₂, he₁.trans he₂⟩

theorem appFn_sound {Γ : List Expr} {f f' a : Expr} (h : RedSem m φ Γ f f') :
    RedSem m φ Γ (.app f a) (.app f' a) := by
  intro ρ hs hw hn
  rw [WellDenoted_app] at hw
  obtain ⟨hf, ha, p, A, B, hslot, hmem, hB, hT⟩ := hw
  obtain ⟨hf', he⟩ := h ρ hs hf (fn_ne_pt hn)
  refine ⟨?_, by simp [he]⟩
  rw [WellDenoted_app]
  exact ⟨hf', ha, p, A, B, he ▸ hslot, hmem, hB, hT⟩

/-- **β at every binder, with no certificate** — `beta_of_ne_pt`.  The
redex is not the point, so neither is its λ; a λ whose annotation held
here would be the point; so it does not hold, the λ is a graph, and the
graph's domain is the slot's: the argument is in it. -/
theorem beta_sound {Γ : List Expr} {A b a : Expr} {pw : PropWhen} :
    RedSem m φ Γ (.app (.lam A pw b) a) (b.inst a) := by
  intro ρ _ hw hn
  rw [WellDenoted_app] at hw
  obtain ⟨hl, ha, p, A', B', hslot, hmem, -, -⟩ := hw
  rw [WellDenoted_lam] at hl
  obtain ⟨-, -, hbody, B, hfib, -⟩ := hl
  have hlam := fn_ne_pt hn
  have hpw : pw.holds φ = false := by
    cases h : pw.holds φ
    · rfl
    · exact absurd (by rw [interp_lam, h, lamR_true]) hlam
  have hval : interp m.M φ ρ (.lam A pw b) =
      lamR false (interp m.M φ ρ A) (fun x => interp m.M φ (cons x ρ) b) := by
    rw [interp_lam, hpw]
  have hp : p = false := by
    cases p
    · rfl
    · exact absurd (eq_pt_of_mem_piR_true hslot) hlam
  subst hp
  have hown : interp m.M φ ρ (.lam A pw b) ∈ˢ piR false (interp m.M φ ρ A) B := by
    rw [hval]; exact lamR_mem hfib fun h => nomatch h
  have haA : interp m.M φ ρ a ∈ˢ interp m.M φ ρ A := by
    rw [piR_dom_unique hown hslot]; exact hmem
  refine ⟨(WellDenoted_inst0 m.M φ ha).mpr (hbody _ haA), ?_⟩
  rw [interp_app, hval, app_lamR_false haA, interp_inst0]

theorem delta_sound {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo} {v : Expr}
    (hfind : env.find? c = some ci) (hv : ci.value? = some v)
    (hls : ls.length = ci.lparams.length) :
    RedSem m φ Γ (.const c ls) (v.instL ci.lparams ls) := by
  intro ρ _ _ _
  obtain ⟨hw, he⟩ := m.unfold c ci v hfind hv φ ρ ls hls
  exact ⟨hw, by rw [interp_const, he]⟩

end Red

/-! ## Definitional equality -/

namespace DefEq

theorem refl_sound {Γ : List Expr} {a : Expr} : DefEqSem m φ Γ a a :=
  fun _ _ _ _ _ _ => rfl

theorem symm_sound {Γ : List Expr} {a b : Expr} (h : DefEqSem m φ Γ a b) :
    DefEqSem m φ Γ b a :=
  fun ρ hs hb ha hnb hna => (h ρ hs ha hb hna hnb).symm

/-- Reduce, then continue — sound with no typing: the side is not the
point, so its reduction is. -/
theorem redL_sound {Γ : List Expr} {a a' b : Expr}
    (hr : RedSem m φ Γ a a') (h : DefEqSem m φ Γ a' b) : DefEqSem m φ Γ a b := by
  intro ρ hs ha hb hna hnb
  obtain ⟨ha', he⟩ := hr ρ hs ha hna
  exact he.trans (h ρ hs ha' hb (he ▸ hna) hnb)

theorem sort_sound [LevelOracle] {Γ : List Expr} {u v : Level} (h : LevelOracle.eq u v = true) :
    DefEqSem m φ Γ (.sort u) (.sort v) :=
  fun _ _ _ _ _ _ => by simp [eval_eq_of_oracle h]

theorem const_sound [LevelOracle] {Γ : List Expr} {c : Name} {ls ls' : List Level}
    (h : Level.eqList ls ls' = true) : DefEqSem m φ Γ (.const c ls) (.const c ls') :=
  fun _ _ _ _ _ _ => by simp [(Level.eqList_iff ls ls').mp h φ]

/-- `∀`-congruence: domains and fibres are types, never the point. -/
theorem pi_sound {Γ : List Expr} {A₁ B₁ A₂ B₂ : Expr} {pw : PropWhen}
    (hA : DefEqSem m φ Γ A₁ A₂) (hB : DefEqSem m φ (A₂ :: Γ) B₁ B₂) :
    DefEqSem m φ Γ (.pi A₁ pw B₁) (.pi A₂ pw B₂) := by
  intro ρ hs h₁ h₂ _ _
  rw [WellDenoted_pi] at h₁ h₂
  have heA := hA ρ hs h₁.1 h₂.1 h₁.2.1.ne_pt h₂.2.1.ne_pt
  simp only [interp_pi]
  rw [heA]
  apply piR_congr
  intro x hx
  have hx₁ : x ∈ˢ interp m.M φ ρ A₁ := by rw [heA]; exact hx
  exact hB (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hs, h₂.1, h₂.2.1, hx⟩) (h₁.2.2.1 x hx₁)
    (h₂.2.2.1 x hx) (h₁.2.2.2 x hx₁).ne_pt (h₂.2.2.2 x hx).ne_pt

/-- A λ that is not the point is in the graph regime, and its body's
values are in strict fibres: never the point. -/
theorem lam_body_ne_pt {A b : Expr} {pw : PropWhen} {ρ : Nat → V}
    (hw : WellDenoted m.M φ ρ (.lam A pw b)) (hn : interp m.M φ ρ (.lam A pw b) ≠ pt)
    {x : V} (hx : x ∈ˢ interp m.M φ ρ A) : interp m.M φ (cons x ρ) b ≠ pt := by
  rw [WellDenoted_lam] at hw
  obtain ⟨-, -, -, B, hfib, hreg⟩ := hw
  have hpw : pw.holds φ = false := by
    cases h : pw.holds φ
    · rfl
    · exact absurd (by rw [interp_lam, h, lamR_true]) hn
  have := hreg x hx
  rw [hpw] at this
  exact ne_pt_of_mem_strict this (hfib x hx)

theorem lam_sound {Γ : List Expr} {A₁ b₁ A₂ b₂ : Expr} {pw : PropWhen}
    (hA : DefEqSem m φ Γ A₁ A₂) (hb : DefEqSem m φ (A₂ :: Γ) b₁ b₂) :
    DefEqSem m φ Γ (.lam A₁ pw b₁) (.lam A₂ pw b₂) := by
  intro ρ hs h₁ h₂ hn₁ hn₂
  have h₁' := h₁
  have h₂' := h₂
  rw [WellDenoted_lam] at h₁' h₂'
  have heA := hA ρ hs h₁'.1 h₂'.1 h₁'.2.1.ne_pt h₂'.2.1.ne_pt
  simp only [interp_lam]
  rw [heA]
  apply lamR_congr
  intro x hx
  have hx₁ : x ∈ˢ interp m.M φ ρ A₁ := by rw [heA]; exact hx
  exact hb (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hs, h₂'.1, h₂'.2.1, hx⟩) (h₁'.2.2.1 x hx₁)
    (h₂'.2.2.1 x hx) (lam_body_ne_pt h₁ hn₁ hx₁) (lam_body_ne_pt h₂ hn₂ hx)

/-- An application that is not the point is in the graph regime, and
its slot's domain is a type. -/
theorem app_slot {f a : Expr} {ρ : Nat → V} (hw : WellDenoted m.M φ ρ (.app f a))
    (hn : interp m.M φ ρ (.app f a) ≠ pt) :
    ∃ (A : V) (B : V → V), interp m.M φ ρ f ∈ˢ piSet A B ∧ interp m.M φ ρ a ∈ˢ A ∧ IsTy A := by
  rw [WellDenoted_app] at hw
  obtain ⟨-, -, p, A, B, hslot, hmem, -, hT⟩ := hw
  cases p
  · exact ⟨A, B, hslot, hmem, hT rfl⟩
  · exact absurd (eq_pt_of_mem_piR_true hslot) (fn_ne_pt hn)

/-- **Application congruence**: the two heads are equal graphs, so the
two arguments lie in one domain, which is a type — both arguments are
the point, or neither is. -/
theorem app_sound {Γ : List Expr} {f₁ a₁ f₂ a₂ : Expr}
    (hf : DefEqSem m φ Γ f₁ f₂) (ha : DefEqSem m φ Γ a₁ a₂) :
    DefEqSem m φ Γ (.app f₁ a₁) (.app f₂ a₂) := by
  intro ρ hs h₁ h₂ hn₁ hn₂
  obtain ⟨A₁, B₁, hs₁, hm₁, hT₁⟩ := app_slot h₁ hn₁
  obtain ⟨A₂, B₂, hs₂, hm₂, -⟩ := app_slot h₂ hn₂
  have h₁' := h₁
  have h₂' := h₂
  rw [WellDenoted_app] at h₁' h₂'
  have heF := hf ρ hs h₁'.1 h₂'.1 (fn_ne_pt hn₁) (fn_ne_pt hn₂)
  rw [← heF] at hs₂
  have hA : A₁ = A₂ := piSet_dom_unique hs₁ hs₂
  rw [← hA] at hm₂
  have heA : interp m.M φ ρ a₁ = interp m.M φ ρ a₂ := by
    rcases hT₁ with hT | hT
    · rw [eq_pt_of_mem_univ_zero hT hm₁, eq_pt_of_mem_univ_zero hT hm₂]
    · exact ha ρ hs h₁'.2.1 h₂'.2.1 (ne_pt_of_mem_strict hT hm₁) (ne_pt_of_mem_strict hT hm₂)
  simp only [interp_app]
  rw [heF, heA]

end DefEq

/-! ## Inference, and the two rules that use it -/

namespace Infer

theorem bvar_sound {Γ : List Expr} {i : Nat} {A : Expr} (h : Γ[i]? = some A) :
    InferSem m φ Γ (.bvar i) (A.liftN (i + 1)) := by
  intro ρ hs
  obtain ⟨hw, hT, hmem⟩ := Sat_get m.M φ hs h
  refine ⟨trivial, ?_, ?_, ?_⟩
  · rw [WellDenoted_liftN]; exact hw
  · rw [interp_liftN]; exact hT
  · rw [interp_bvar, interp_liftN]; exact hmem

theorem sort_sound {Γ : List Expr} {u : Level} :
    InferSem m φ Γ (.sort u) (.sort (.succ u)) :=
  fun _ _ => ⟨trivial, trivial, Or.inr (strict_typeU _), by
    simp only [interp_sort, Level.eval_succ]; exact typeU_mem_typeU_succ _⟩

theorem const_sound {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo}
    (hfind : env.find? c = some ci) (hls : ls.length = ci.lparams.length) :
    InferSem m φ Γ (.const c ls) (ci.type.instL ci.lparams ls) := by
  intro ρ _
  obtain ⟨hw, hT, hmem⟩ := m.type_ok c ci hfind φ ρ ls hls
  exact ⟨trivial, hw, hT, hmem⟩

/-- A type whose type reduces to `Sort u` is a member of `typeU u`. -/
theorem mem_typeU_of {Γ : List Expr} {A s : Expr} {u : Level} {ρ : Nat → V}
    (hA : InferSem m φ Γ A s) (hu : RedSem m φ Γ s (.sort u)) (hs : Sat m.M φ Γ ρ) :
    WellDenoted m.M φ ρ A ∧ interp m.M φ ρ A ∈ˢ typeU (Level.eval φ u) := by
  obtain ⟨hwA, hws, hTs, hmem⟩ := hA ρ hs
  obtain ⟨-, hes⟩ := hu ρ hs hws hTs.ne_pt
  rw [hes, interp_sort] at hmem
  exact ⟨hwA, hmem⟩

/-- The regime of the annotation is the regime of the sort it checks. -/
theorem fib_of_zeroness {v : Level} {pw : PropWhen} (hz : Level.zeroness v = pw) {X : V}
    (h : X ∈ˢ typeU (Level.eval φ v)) : Fib (pw.holds φ) X := by
  have hzero := holds_of_zeroness (φ := φ) hz
  have hf := Fib_of_mem_typeU h
  cases hp : pw.holds φ
  · have : Level.eval φ v ≠ 0 := fun h0 => by rw [hzero.mpr h0] at hp; exact nomatch hp
    simpa [this] using hf
  · simpa [hzero.mp hp] using hf

theorem pi_sound {Γ : List Expr} {A B s t : Expr} {u v : Level} {pw : PropWhen}
    (hA : InferSem m φ Γ A s) (hu : RedSem m φ Γ s (.sort u))
    (hB : InferSem m φ (A :: Γ) B t) (hv : RedSem m φ (A :: Γ) t (.sort v))
    (hz : Level.zeroness v = pw) :
    InferSem m φ Γ (.pi A pw B) (.sort (.imax u v)) := by
  intro ρ hs
  obtain ⟨hwA, hmemA⟩ := mem_typeU_of hA hu hs
  have hTA := IsTy_of_mem_typeU hmemA
  have hbody : ∀ x, x ∈ˢ interp m.M φ ρ A →
      WellDenoted m.M φ (cons x ρ) B ∧ interp m.M φ (cons x ρ) B ∈ˢ typeU (Level.eval φ v) :=
    fun x hx => mem_typeU_of hB hv ((Sat_cons m.M φ).mpr ⟨hs, hwA, hTA, hx⟩)
  have hzero := holds_of_zeroness (φ := φ) hz
  refine ⟨?_, trivial, Or.inr (strict_typeU _), ?_⟩
  · rw [WellDenoted_pi]
    exact ⟨hwA, hTA, fun x hx => (hbody x hx).1, fun x hx => fib_of_zeroness hz (hbody x hx).2⟩
  · rw [interp_pi, interp_sort, Level.eval_imax]
    exact piR_mem_typeU hzero hmemA fun x hx => (hbody x hx).2

theorem lam_sound {Γ : List Expr} {A b s bt btt : Expr} {u v : Level} {pw : PropWhen}
    (hA : InferSem m φ Γ A s) (hu : RedSem m φ Γ s (.sort u))
    (hb : InferSem m φ (A :: Γ) b bt)
    (hbt : InferSem m φ (A :: Γ) bt btt) (hv : RedSem m φ (A :: Γ) btt (.sort v))
    (hz : Level.zeroness v = pw) :
    InferSem m φ Γ (.lam A pw b) (.pi A pw bt) := by
  intro ρ hs
  obtain ⟨hwA, hmemA⟩ := mem_typeU_of hA hu hs
  have hTA := IsTy_of_mem_typeU hmemA
  have hbody : ∀ x, x ∈ˢ interp m.M φ ρ A →
      WellDenoted m.M φ (cons x ρ) b ∧ WellDenoted m.M φ (cons x ρ) bt ∧
      interp m.M φ (cons x ρ) b ∈ˢ interp m.M φ (cons x ρ) bt ∧
      Fib (pw.holds φ) (interp m.M φ (cons x ρ) bt) := by
    intro x hx
    have hs' : Sat m.M φ (A :: Γ) (cons x ρ) := (Sat_cons m.M φ).mpr ⟨hs, hwA, hTA, hx⟩
    obtain ⟨hwb, -, -, hmemb⟩ := hb (cons x ρ) hs'
    obtain ⟨hwbt, hmembt⟩ := mem_typeU_of hbt hv hs'
    exact ⟨hwb, hwbt, hmemb, fib_of_zeroness hz hmembt⟩
  refine ⟨?_, ?_, IsTy_piR, ?_⟩
  · rw [WellDenoted_lam]
    exact ⟨hwA, hTA, fun x hx => (hbody x hx).1,
      fun x => interp m.M φ (cons x ρ) bt, fun x hx => (hbody x hx).2.2.1,
      fun x hx => (hbody x hx).2.2.2⟩
  · rw [WellDenoted_pi]
    exact ⟨hwA, hTA, fun x hx => (hbody x hx).2.1, fun x hx => (hbody x hx).2.2.2⟩
  · rw [interp_lam, interp_pi]
    refine lamR_mem (fun x hx => (hbody x hx).2.2.1) fun hp x hx => ?_
    have := (hbody x hx).2.2.2
    rwa [hp] at this

theorem app_sound {Γ : List Expr} {f a tf A B ta : Expr} {pw : PropWhen}
    (hf : InferSem m φ Γ f tf) (hr : RedSem m φ Γ tf (.pi A pw B))
    (ha : InferSem m φ Γ a ta) (hd : DefEqSem m φ Γ ta A) :
    InferSem m φ Γ (.app f a) (B.inst a) := by
  intro ρ hs
  obtain ⟨hwf, hwtf, hTtf, hmemf⟩ := hf ρ hs
  obtain ⟨hwpi, hepi⟩ := hr ρ hs hwtf hTtf.ne_pt
  rw [hepi, interp_pi] at hmemf
  have hwpi' := hwpi
  rw [WellDenoted_pi] at hwpi'
  obtain ⟨hwA, hTA, hwB, hfib⟩ := hwpi'
  obtain ⟨hwa, hwta, hTta, hmema⟩ := ha ρ hs
  rw [hd ρ hs hwta hwA hTta.ne_pt hTA.ne_pt] at hmema
  refine ⟨?_, (WellDenoted_inst0 m.M φ hwa).mpr (hwB _ hmema), ?_, ?_⟩
  · rw [WellDenoted_app]
    refine ⟨hwf, hwa, pw.holds φ, _, _, hmemf, hmema, fun hp x hx => ?_, fun _ => hTA⟩
    have := hfib x hx
    rwa [hp] at this
  · rw [interp_inst0]; exact IsTy_of_Fib (hfib _ hmema)
  · rw [interp_app, interp_inst0]
    exact app_mem_piR hmemf hmema

end Infer

namespace DefEq

/-- **η**: the λ is not the point, so `b`'s type is in the graph regime
and `b` applied is never the point either. -/
theorem eta_sound {Γ : List Expr} {A₁ b₁ b tb A₂ B : Expr} {pw : PropWhen}
    (htb : InferSem m φ Γ b tb) (hr : RedSem m φ Γ tb (.pi A₂ pw B))
    (hA : DefEqSem m φ Γ A₂ A₁)
    (hbody : DefEqSem m φ (A₁ :: Γ) b₁ (.app (b.liftN 1) (.bvar 0))) :
    DefEqSem m φ Γ (.lam A₁ pw b₁) b := by
  intro ρ hs hlam hwb hnl _
  obtain ⟨-, hwtb, hTtb, hmemb⟩ := htb ρ hs
  obtain ⟨hwpi, hepi⟩ := hr ρ hs hwtb hTtb.ne_pt
  rw [hepi, interp_pi] at hmemb
  rw [WellDenoted_pi] at hwpi
  have hlam' := hlam
  rw [WellDenoted_lam] at hlam'
  have heA := hA ρ hs hwpi.1 hlam'.1 hwpi.2.1.ne_pt hlam'.2.1.ne_pt
  have hpw : pw.holds φ = false := by
    cases h : pw.holds φ
    · rfl
    · exact absurd (by rw [interp_lam, h, lamR_true]) hnl
  have hsh : ∀ x, shiftE 1 0 (cons x ρ) = ρ := by
    intro x; funext i; simp [shiftE]
  have hlift : ∀ x, interp m.M φ (cons x ρ) (b.liftN 1) = interp m.M φ ρ b := by
    intro x; rw [interp_liftN, hsh]
  have hpt : ∀ x, x ∈ˢ interp m.M φ ρ A₁ →
      interp m.M φ (cons x ρ) b₁ = SetLib.app (interp m.M φ ρ b) x := by
    intro x hx
    have hx₂ : x ∈ˢ interp m.M φ ρ A₂ := by rw [heA]; exact hx
    have happ : WellDenoted m.M φ (cons x ρ) (.app (b.liftN 1) (.bvar 0)) := by
      rw [WellDenoted_app]
      refine ⟨(WellDenoted_liftN m.M φ 1 b 0 (cons x ρ)).mpr (by rw [hsh]; exact hwb), trivial,
        pw.holds φ, interp m.M φ ρ A₂, fun y => interp m.M φ (cons y ρ) B,
        by rw [hlift]; exact hmemb, hx₂, fun hp => ?_, fun _ => hwpi.2.1⟩
      rw [hpw] at hp; exact nomatch hp
    have hfibx := hwpi.2.2.2 x hx₂
    rw [hpw] at hfibx
    have hne : interp m.M φ (cons x ρ) (.app (b.liftN 1) (.bvar 0)) ≠ pt := by
      rw [interp_app, interp_bvar, cons_zero, hlift]
      exact ne_pt_of_mem_strict hfibx (app_mem_piR hmemb hx₂)
    have := hbody (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hs, hlam'.1, hlam'.2.1, hx⟩)
      (hlam'.2.2.1 x hx) happ (lam_body_ne_pt hlam hnl hx) hne
    rw [this, interp_app, interp_bvar, cons_zero, hlift]
  rw [interp_lam, lamR_congr hpt, ← heA]
  exact lamR_eta hmemb

/-- **Proof irrelevance claims nothing**: a side whose type's sort is
`Prop` is the point, and the claim is about sides that are not. -/
theorem proofIrrel_sound [LevelOracle] {Γ : List Expr} {a ta tta b : Expr} {u : Level}
    (hta : InferSem m φ Γ a ta) (htta : InferSem m φ Γ ta tta)
    (hu : RedSem m φ Γ tta (.sort u)) (hu0 : LevelOracle.eq u .zero = true) :
    DefEqSem m φ Γ a b := by
  intro ρ hs _ _ hna _
  obtain ⟨-, hmemT⟩ := Infer.mem_typeU_of htta hu hs
  obtain ⟨-, -, -, hmem⟩ := hta ρ hs
  rw [eval_eq_of_oracle hu0, Level.eval_zero, mem_typeU_zero] at hmemT
  exact absurd (eq_pt_of_mem_univ_zero hmemT hmem) hna

end DefEq


/-! ## ι -/

/-- **Certificates give fit**: arguments typed against the telescope's
domains fit it.  The inferred types are types, and the domains are
(`WellDenoted` records it), so neither side of a certificate's comparison is
the point and the conditional claim applies. -/
theorem teleFit_of_certs {Γ : List Expr} {ρ : Nat → V} (hs : Sat m.M φ Γ ρ) :
    ∀ {T : Expr} {spine tys doms : List Expr},
      WellDenoted m.M φ ρ T → (∀ a ∈ spine, WellDenoted m.M φ ρ a) →
      Expr.piDomains T spine = some doms → tys.length = doms.length →
      (∀ p ∈ spine.zip tys, InferSem m φ Γ p.1 p.2) →
      (∀ p ∈ tys.zip doms, DefEqSem m φ Γ p.1 p.2) →
      TeleFit m.M φ ρ T spine
  | _, [], _, _, _, _, _, _, _, _ => trivial
  | .pi A _ B, a :: as, tys, _, hT, hsp, hdoms, hlen, hI, hD => by
    simp only [Expr.piDomains, Option.map_eq_some_iff] at hdoms
    obtain ⟨ds, hds, rfl⟩ := hdoms
    cases tys with
    | nil => simp at hlen
    | cons ta ts =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [WellDenoted_pi] at hT
      have hwa := hsp a List.mem_cons_self
      obtain ⟨-, hwta, hTta, hmem⟩ := hI (a, ta) (by simp) ρ hs
      rw [hD (ta, A) (by simp) ρ hs hwta hT.1 hTta.ne_pt hT.2.1.ne_pt] at hmem
      refine ⟨hmem, ?_⟩
      refine teleFit_of_certs hs ((WellDenoted_inst0 m.M φ hwa).mpr (hT.2.2.1 _ hmem))
        (fun b hb => hsp b (List.mem_cons_of_mem a hb)) hds hlen ?_ ?_
      · intro p hp
        exact hI p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp)
      · intro p hp
        exact hD p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp)
  | .bvar _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h
  | .sort _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h
  | .const _ _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h
  | .app _ _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h
  | .lam _ _ _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h

/-- The residual of a well-denoted telescope along a fitting spine is
well-denoted. -/
theorem WellDenoted_piResidual {ρ : Nat → V} :
    ∀ {T : Expr} {as : List Expr} {R : Expr},
      WellDenoted m.M φ ρ T → (∀ a ∈ as, WellDenoted m.M φ ρ a) →
      TeleFit m.M φ ρ T as → Expr.piResidual T as = some R → WellDenoted m.M φ ρ R
  | T, [], _, hT, _, _, h => by simp at h; subst h; exact hT
  | .pi A _ B, a :: as, R, hT, has, hfit, h => by
    rw [Expr.piResidual_pi_cons] at h
    obtain ⟨hmem, hfit'⟩ := hfit
    rw [WellDenoted_pi] at hT
    exact WellDenoted_piResidual
      ((WellDenoted_inst0 m.M φ (has a List.mem_cons_self)).mpr (hT.2.2.1 _ hmem))
      (fun b hb => has b (List.mem_cons_of_mem a hb)) hfit' h
  | .bvar _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .sort _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .const _ _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .app _ _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .lam _ _ _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h

/-- **The major premise needs no β certificate.**  In an application of
a head `f` of type `T` to a spine `xs` and a major `maj` that is not the
point, with a reduct `maj'` of the major that meets the major's binder:
the two denote alike.  The head applied to `xs` is not the point, so it
is a graph, whose domain is the binder's — a type.  If the major is not
the point, its reduction's claim applies; if it is, the binder's domain
holds the point, so it is a truth value, and the reduct is the point
too.  This is the case of a recursion on proofs (`Acc`-style), where
the fragment's ι needs the certified β to reduce the major. -/
theorem major_eq {Γ : List Expr} {ρ : Nat → V} {T f maj maj' : Expr} {xs : List Expr}
    (hs : Sat m.M φ Γ ρ) (hT : WellDenoted m.M φ ρ T) (hf : interp m.M φ ρ f ∈ˢ interp m.M φ ρ T)
    (hw : WellDenoted m.M φ ρ (.app (Expr.mkAppN f xs) maj))
    (hn : interp m.M φ ρ (.app (Expr.mkAppN f xs) maj) ≠ pt)
    (hred : RedSem m φ Γ maj maj')
    (hfit : TeleFitV m.M φ ρ T ((xs ++ [maj']).map (interp m.M φ ρ))) :
    interp m.M φ ρ maj = interp m.M φ ρ maj' := by
  rw [List.map_append, List.map_singleton] at hfit
  obtain ⟨A, pw, B, ρ', hb, hfitxs, hv⟩ := teleFitV_snoc m.M φ hfit
  have hmemB := mem_piBodyV m.M φ hf hfitxs hb
  have hwB := WellDenoted_piBodyV m.M φ hT hfitxs hb
  rw [WellDenoted_pi] at hwB
  rw [interp_pi] at hmemB
  rw [WellDenoted_app] at hw
  obtain ⟨-, hwmaj, p, A', B', hslot, hmaj, -, -⟩ := hw
  have hF := fn_ne_pt hn
  rw [interp_mkAppN_appList] at hslot hF
  have hp : p = false := by
    cases p
    · rfl
    · exact absurd (eq_pt_of_mem_piR_true hslot) hF
  have hpw : pw.holds φ = false := by
    cases h : pw.holds φ
    · rfl
    · rw [h] at hmemB; exact absurd (eq_pt_of_mem_piR_true hmemB) hF
  subst hp
  rw [hpw] at hmemB
  have hA : A' = interp m.M φ ρ' A := piR_dom_unique hslot hmemB
  rw [hA] at hmaj
  by_cases hmp : interp m.M φ ρ maj = pt
  · rcases hwB.2.1 with hT0 | hTs
    · rw [hmp, eq_pt_of_mem_univ_zero hT0 hv]
    · exact absurd (hmp ▸ hmaj) hTs.2
  · exact (hred ρ hs hwmaj hmp).2

/-- The conditional comparisons of a spine, on values. -/
theorem cmp_vals {Γ : List Expr} {ρ : Nat → V} (hs : Sat m.M φ Γ ρ) {as bs : List Expr}
    (ha : ∀ a ∈ as, WellDenoted m.M φ ρ a) (hb : ∀ b ∈ bs, WellDenoted m.M φ ρ b)
    (h : ∀ p ∈ as.zip bs, DefEqSem m φ Γ p.1 p.2) :
    ∀ p ∈ (as.map (interp m.M φ ρ)).zip (bs.map (interp m.M φ ρ)),
      p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2 := by
  intro p hp h1 h2
  rw [List.zip_map] at hp
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hp
  exact h (a, b) hab ρ hs (ha a (List.of_mem_zip hab).1) (hb b (List.of_mem_zip hab).2) h1 h2

namespace Red

/-- **ι, the common part** of `iota_sound` and
`iotaNested_sound`, at the constructor's parameter count `nP` and a
right-hand side `rhs`, given the environment's law in the form both ι
laws take once instantiated (`hlaw`).  The certificates give the two
telescope fits and, through their inferences, the invariant of the
reduced major and of the constructor's arguments; the index comparisons
are passed on in their conditional form; the major's denotation is its
reduct's with no β certificate (`major_eq`). -/
theorem iota_core {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {margs : List Expr} {rhs : Expr}
    {doms tys doms' tys' : List Expr} {nP numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore ≤ majorIdx)
    (hfind : env.find? c = some ci)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hcij : env.find? cj = some cij)
    (husj : usj.length = cij.lparams.length)
    (hpis' : cij.type.hasPis margs.length = true)
    (hdoms : Expr.piDomains (ci.type.instL ci.lparams us) (args.take majorIdx ++ [major]) = some doms)
    (htys : tys.length = doms.length)
    (hI : ∀ p ∈ (args.take majorIdx ++ [major]).zip tys, InferSem m φ Γ p.1 p.2)
    (hD : ∀ p ∈ tys.zip doms, DefEqSem m φ Γ p.1 p.2)
    (hdoms' : Expr.piDomains (cij.type.instL cij.lparams usj) margs = some doms')
    (htys' : tys'.length = doms'.length)
    (hI' : ∀ p ∈ margs.zip tys', InferSem m φ Γ p.1 p.2)
    (hD' : ∀ p ∈ tys'.zip doms', DefEqSem m φ Γ p.1 p.2)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = nP)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2)
    (hlaw : ∀ ρ : Nat → V, Sat m.M φ Γ ρ → (∀ a ∈ args, WellDenoted m.M φ ρ a) →
      (∀ a ∈ margs, WellDenoted m.M φ ρ a) →
      TeleFitV m.M φ ρ (ci.type.instL ci.lparams us)
        ((args.take majorIdx).map (interp m.M φ ρ) ++
          [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) →
      TeleFitV m.M φ ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) →
      (∀ (B : Expr) (ρ' : Nat → V) (I : Name) (lsI : List Level) (rps ridx : List Expr),
        piBodyV ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) = some (B, ρ') →
        B = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = nP →
        ∀ p ∈ (ridx.map (interp m.M φ ρ')).zip
          (((args.take majorIdx).map (interp m.M φ ρ)).drop numBefore),
          p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) →
      appList (m.M c (us.map (Level.eval φ)))
          ((args.take majorIdx).map (interp m.M φ ρ) ++
            [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) ≠ pt →
      appList (m.M c (us.map (Level.eval φ)))
          ((args.take majorIdx).map (interp m.M φ ρ) ++
            [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))])
        = appList (interp m.M φ ρ rhs)
            (((args.take majorIdx).map (interp m.M φ ρ)).take numBefore ++
              (margs.map (interp m.M φ ρ)).drop nP) ∧
      WellDenoted m.M φ ρ rhs ∧
      SpineOk (interp m.M φ ρ rhs)
        (((args.take majorIdx).map (interp m.M φ ρ)).take numBefore ++
          (margs.map (interp m.M φ ρ)).drop nP)) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN rhs (args.take numBefore ++ margs.drop nP)) := by
  intro ρ hs hw hn
  subst hmeq
  obtain ⟨-, hargs⟩ := WellDenoted_mkAppN m.M φ hw
  have hsplit := List.take_append_getD (Expr.bvar 0) args _ hlen
  have hwxs : ∀ a ∈ args.take majorIdx, WellDenoted m.M φ ρ a :=
    fun a ha => hargs a (List.mem_of_mem_take ha)
  -- the certificates' inferences give the invariant of the reduced major and of its arguments
  have hwmajor : WellDenoted m.M φ ρ (Expr.mkAppN (Expr.const cj usj) margs) := by
    have hl : (args.take majorIdx ++ [Expr.mkAppN (Expr.const cj usj) margs]).length
        = tys.length := by
      rw [htys, Expr.length_of_piDomains hdoms]
    have hlt : (args.take majorIdx).length < tys.length := by
      simp only [List.length_append, List.length_singleton] at hl; omega
    have hmem := List.getElem_mem (l := (args.take majorIdx
        ++ [Expr.mkAppN (Expr.const cj usj) margs]).zip tys)
      (n := (args.take majorIdx).length)
      (by simp only [List.length_zip, List.length_append, List.length_singleton]; omega)
    exact (hI _ (by simpa using hmem) ρ hs).1
  have hmargs : ∀ a ∈ margs, WellDenoted m.M φ ρ a := (WellDenoted_mkAppN m.M φ hwmajor).2
  -- the two telescope fits, from the certificates
  have hfit := teleFit_of_certs hs (m.type_ok c ci hfind φ ρ us hus).1
    (fun a ha => by
      rcases List.mem_append.mp ha with ha | ha
      · exact hwxs a ha
      · rw [List.mem_singleton.mp ha]; exact hwmajor)
    hdoms htys hI hD
  have hfit' := teleFit_of_certs hs (m.type_ok _ cij hcij φ ρ usj husj).1 hmargs
    hdoms' htys' hI' hD'
  have hmajv : interp m.M φ ρ (Expr.mkAppN (Expr.const cj usj) margs)
      = appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ)) := by
    rw [interp_mkAppN_appList, interp_const]
  have hlenmaj : (args.take majorIdx ++ [Expr.mkAppN (Expr.const cj usj) margs]).length
      = majorIdx + 1 := by
    simp only [List.length_append, List.length_take, List.length_singleton, hlen]; omega
  have hfitV₀ := teleFitV_of_teleFit m.M φ ρ
    (by rw [Expr.hasPis_instL, hlenmaj]; exact hpis) hfit
  have hfitV' := teleFitV_of_teleFit m.M φ ρ (by rw [Expr.hasPis_instL]; exact hpis') hfit'
  -- the major denotes its reduct, with no β certificate
  have hsub : Expr.mkAppN (Expr.const c us) args =
      .app (Expr.mkAppN (Expr.const c us) (args.take majorIdx)) (args.getD majorIdx (Expr.bvar 0)) := by
    conv => lhs; rw [hsplit]
    rw [Expr.mkAppN_append]; rfl
  have hemaj := major_eq (f := Expr.const c us) hs (m.type_ok c ci hfind φ ρ us hus).1
    (by rw [interp_const]; exact (m.type_ok c ci hfind φ ρ us hus).2.2) (hsub ▸ hw) (hsub ▸ hn)
    hmaj hfitV₀
  have hfitV := hfitV₀
  rw [List.map_append, List.map_singleton, hmajv] at hfitV
  -- the index comparisons, in their conditional form
  have hwres : WellDenoted m.M φ ρ residual :=
    WellDenoted_piResidual (m.type_ok _ cij hcij φ ρ usj husj).1 hmargs hfit' hres
  rw [hshape] at hwres
  obtain ⟨-, hwridx⟩ := WellDenoted_mkAppN m.M φ hwres
  have hX' : ∀ (B : Expr) (ρ' : Nat → V) (I' : Name) (lsI' : List Level) (rps' ridx' : List Expr),
      piBodyV ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) = some (B, ρ') →
      B = Expr.mkAppN (.const I' lsI') (rps' ++ ridx') → rps'.length = nP →
      ∀ p ∈ (ridx'.map (interp m.M φ ρ')).zip
        (((args.take majorIdx).map (interp m.M φ ρ)).drop numBefore),
        p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2 := by
    intro B ρ' I' lsI' rps' ridx' hB hBs hrps'
    have hRB := piResidual_of_piBodyV m.M φ ρ hres hB
    rw [hshape, hBs, Expr.instChain_mkAppN, Expr.instChain_const] at hRB
    obtain ⟨-, -, hargs_eq⟩ := Expr.mkAppN_const_inj hRB
    rw [List.map_append] at hargs_eq
    have hridx : ridx = ridx'.map (Expr.instChain · margs) :=
      List.append_inj_right hargs_eq (by simp [hrps, hrps'])
    rw [piBodyV_env hB]
    have hmap : ridx'.map (interp m.M φ (consList (margs.map (interp m.M φ ρ)).reverse ρ))
        = ridx.map (interp m.M φ ρ) := by
      rw [hridx, List.map_map]
      apply List.map_congr_left
      intro r _
      simp [Function.comp, interp_instChain]
    rw [hmap, ← List.map_drop]
    exact cmp_vals hs (fun a ha => hwridx a (List.mem_append_right _ ha))
      (fun a ha => hwxs a (List.mem_of_mem_drop ha)) hX
  -- the environment's ι law
  have hvsub : interp m.M φ ρ (Expr.mkAppN (Expr.const c us) args)
      = appList (m.M c (us.map (Level.eval φ)))
        ((args.take majorIdx).map (interp m.M φ ρ)
          ++ [appList (m.M cj (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ))]) := by
    conv => lhs; rw [hsplit]
    rw [interp_mkAppN_appList, interp_const, List.map_append, List.map_singleton, hemaj, hmajv]
  obtain ⟨heq, hwrhs, hspine⟩ :=
    hlaw ρ hs hargs hmargs hfitV hfitV' hX' (hvsub ▸ hn)
  have hvals : (args.take numBefore ++ margs.drop nP).map (interp m.M φ ρ)
      = ((args.take majorIdx).map (interp m.M φ ρ)).take numBefore
        ++ (margs.map (interp m.M φ ρ)).drop nP := by
    rw [List.map_append, ← List.map_take, ← List.map_drop, List.take_take,
      Nat.min_eq_left hnB]
  refine ⟨?_, ?_⟩
  · apply WellDenoted_mkAppN_of_spineOk m.M φ ρ hwrhs
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hargs a (List.mem_of_mem_take ha)
      · exact hmargs a (List.mem_of_mem_drop ha)
    · rw [hvals]; exact hspine
  · rw [hvsub, interp_mkAppN_appList, hvals]
    exact heq

/-- **ι**: `iota_core` with the environment's `RecRuleLaw`;
the parameter comparisons are passed on in their conditional form. -/
theorem iota_sound [LevelOracle] {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {margs : List Expr} {rl : RecRule}
    {doms tys doms' tys' : List Expr} {numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore = numParams + numMotives + numMinors)
    (hmI : majorIdx = numParams + numMotives + numMinors + numIndices)
    (hfind : env.find? c = some ci)
    (hkind : ci.kind = .recursor numParams numMotives numMinors numIndices rules)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hrl : rl ∈ rules) (hctor : rl.ctor = cj) (hinst : rl.inst = none)
    (hcij : env.find? cj = some cij)
    (husj : usj.length = cij.lparams.length)
    (hmlen : margs.length = numParams + rl.nfields)
    (hpis' : cij.type.hasPis (numParams + rl.nfields) = true)
    (hdoms : Expr.piDomains (ci.type.instL ci.lparams us) (args.take majorIdx ++ [major]) = some doms)
    (htys : tys.length = doms.length)
    (hI : ∀ p ∈ (args.take majorIdx ++ [major]).zip tys, InferSem m φ Γ p.1 p.2)
    (hD : ∀ p ∈ tys.zip doms, DefEqSem m φ Γ p.1 p.2)
    (hdoms' : Expr.piDomains (cij.type.instL cij.lparams usj) margs = some doms')
    (htys' : tys'.length = doms'.length)
    (hI' : ∀ p ∈ margs.zip tys', InferSem m φ Γ p.1 p.2)
    (hD' : ∀ p ∈ tys'.zip doms', DefEqSem m φ Γ p.1 p.2)
    (hlv : Level.eqList usj (us.drop (us.length - usj.length)) = true)
    (hP : ∀ p ∈ (margs.take numParams).zip (args.take numParams), DefEqSem m φ Γ p.1 p.2)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = numParams)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us) (args.take numBefore ++ margs.drop numParams)) := by
  subst hnB hmI hctor
  refine iota_core (by omega) hfind hus hlen hpis hmaj hmeq hcij husj (by rw [hmlen]; exact hpis')
    hdoms htys hI hD hdoms' htys' hI' hD' hres hshape hrps hX ?_
  intro ρ hs hargs hmargs hfitV hfitV' hX' hn
  have hP' : ∀ p ∈ ((margs.map (interp m.M φ ρ)).take numParams).zip
      (((args.take (numParams + numMotives + numMinors + numIndices)).map
        (interp m.M φ ρ)).take numParams), p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2 := by
    rw [← List.map_take, ← List.map_take, List.take_take, Nat.min_eq_left (by omega)]
    exact cmp_vals hs (fun a ha => hmargs a (List.mem_of_mem_take ha))
      (fun a ha => hargs a (List.mem_of_mem_take ha)) hP
  exact m.rec_rules c ci numParams numMotives numMinors numIndices rules
    hfind hkind rl hrl hinst cij hcij φ ρ us usj _ _ hus husj
    (by simp only [List.length_map, List.length_take, hlen]; omega) (by simp [hmlen])
    hfitV hfitV' ((Level.eqList_iff _ _).mp hlv φ) hP' hX' hn

/-- **ι, nested**: `iota_core` at the constructor's own
parameter count, with the environment's `RecRuleLawN`. -/
theorem iotaNested_sound [LevelOracle] {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {I' : Name} {nPc nfj : Nat} {margs : List Expr} {rl : RecRule}
    {lvs : List Level} {pinst : List Expr}
    {doms tys doms' tys' : List Expr} {numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore = numParams + numMotives + numMinors)
    (hmI : majorIdx = numParams + numMotives + numMinors + numIndices)
    (hfind : env.find? c = some ci)
    (hkind : ci.kind = .recursor numParams numMotives numMinors numIndices rules)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hrl : rl ∈ rules) (hctor : rl.ctor = cj) (hinst : rl.inst = some (lvs, pinst))
    (hcij : env.find? cj = some cij) (hcijk : cij.kind = .ctor I' nPc nfj)
    (husj : usj.length = cij.lparams.length)
    (hmlen : margs.length = nPc + rl.nfields)
    (hpis' : cij.type.hasPis (nPc + rl.nfields) = true)
    (hdoms : Expr.piDomains (ci.type.instL ci.lparams us) (args.take majorIdx ++ [major]) = some doms)
    (htys : tys.length = doms.length)
    (hI : ∀ p ∈ (args.take majorIdx ++ [major]).zip tys, InferSem m φ Γ p.1 p.2)
    (hD : ∀ p ∈ tys.zip doms, DefEqSem m φ Γ p.1 p.2)
    (hdoms' : Expr.piDomains (cij.type.instL cij.lparams usj) margs = some doms')
    (htys' : tys'.length = doms'.length)
    (hI' : ∀ p ∈ margs.zip tys', InferSem m φ Γ p.1 p.2)
    (hD' : ∀ p ∈ tys'.zip doms', DefEqSem m φ Γ p.1 p.2)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = nPc)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us) (args.take numBefore ++ margs.drop nPc)) := by
  subst hnB hmI hctor
  refine iota_core (by omega) hfind hus hlen hpis hmaj hmeq hcij husj (by rw [hmlen]; exact hpis')
    hdoms htys hI hD hdoms' htys' hI' hD' hres hshape hrps hX ?_
  intro ρ _ _ _ hfitV hfitV' hX' hn
  exact m.rec_rules_nested c ci numParams numMotives numMinors numIndices rules hfind hkind rl hrl
    lvs pinst hinst cij I' nPc nfj hcij hcijk φ ρ us usj _ _ hus husj
    (by simp only [List.length_map, List.length_take, hlen]; omega) (by simp [hmlen])
    hfitV hfitV' hX' hn

end Red

/-! ## The master induction -/

mutual

theorem red_sound [LevelOracle] : ∀ {Γ : List Expr} {e e' : Expr},
    Red env Γ e e' → RedSem m φ Γ e e'
  | _, _, _, .refl => Red.refl_sound
  | _, _, _, .trans h₁ h₂ => Red.trans_sound (red_sound h₁) (red_sound h₂)
  | _, _, _, .appFn h => Red.appFn_sound (red_sound h)
  | _, _, _, .beta => Red.beta_sound
  | _, _, _, .delta hfind hv hls => Red.delta_sound hfind hv hls
  | _, _, _, .iota hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij husj hmlen hpis' hdoms htys
      hI hD hdoms' htys' hI' hD' hlv hP hres hshape hrps hX =>
    Red.iota_sound rfl rfl hfind hkind hus hlen hpis (red_sound hmaj) hmeq hrl hctor hinst hcij husj
      hmlen hpis' hdoms htys (fun p hp => infer_sound (hI p hp)) (fun p hp => defeq_sound (hD p hp))
      hdoms' htys' (fun p hp => infer_sound (hI' p hp)) (fun p hp => defeq_sound (hD' p hp))
      hlv (fun p hp => defeq_sound (hP p hp)) hres hshape hrps
      (fun p hp => defeq_sound (hX p hp))
  | _, _, _, .iotaNested hfind hkind hus hlen hpis hmaj hmeq hrl hctor hinst hcij hcijk husj hmlen
      hpis' hdoms htys hI hD hdoms' htys' hI' hD' _ _ _ hres hshape hrps hX =>
    Red.iotaNested_sound rfl rfl hfind hkind hus hlen hpis (red_sound hmaj) hmeq hrl hctor hinst
      hcij hcijk husj hmlen hpis' hdoms htys (fun p hp => infer_sound (hI p hp))
      (fun p hp => defeq_sound (hD p hp)) hdoms' htys' (fun p hp => infer_sound (hI' p hp))
      (fun p hp => defeq_sound (hD' p hp)) hres hshape hrps (fun p hp => defeq_sound (hX p hp))

theorem defeq_sound [LevelOracle] : ∀ {Γ : List Expr} {a b : Expr},
    DefEq env Γ a b → DefEqSem m φ Γ a b
  | _, _, _, .refl => DefEq.refl_sound
  | _, _, _, .symm h => DefEq.symm_sound (defeq_sound h)
  | _, _, _, .redL hr h => DefEq.redL_sound (red_sound hr) (defeq_sound h)
  | _, _, _, .sort h => DefEq.sort_sound h
  | _, _, _, .const h => DefEq.const_sound h
  | _, _, _, .pi hA hB => DefEq.pi_sound (defeq_sound hA) (defeq_sound hB)
  | _, _, _, .lam hA hb => DefEq.lam_sound (defeq_sound hA) (defeq_sound hb)
  | _, _, _, .app hf ha => DefEq.app_sound (defeq_sound hf) (defeq_sound ha)
  | _, _, _, .eta htb hr hA hbody =>
    DefEq.eta_sound (infer_sound htb) (red_sound hr) (defeq_sound hA) (defeq_sound hbody)
  | _, _, _, .proofIrrel hta htta hu hu0 _ _ _ _ =>
    DefEq.proofIrrel_sound (infer_sound hta) (infer_sound htta) (red_sound hu) hu0

theorem infer_sound [LevelOracle] : ∀ {Γ : List Expr} {e T : Expr},
    Infer env Γ e T → InferSem m φ Γ e T
  | _, _, _, .bvar h => Infer.bvar_sound h
  | _, _, _, .sort => Infer.sort_sound
  | _, _, _, .const hfind hls => Infer.const_sound hfind hls
  | _, _, _, .pi hA hu hB hv hz =>
    Infer.pi_sound (infer_sound hA) (red_sound hu) (infer_sound hB) (red_sound hv) hz
  | _, _, _, .lam hA hu hb hbt hv hz =>
    Infer.lam_sound (infer_sound hA) (red_sound hu) (infer_sound hb) (infer_sound hbt)
      (red_sound hv) hz
  | _, _, _, .app hf hr ha hd =>
    Infer.app_sound (infer_sound hf) (red_sound hr) (infer_sound ha) (defeq_sound hd)

end

/-! ## The theorem -/

/-- **Soundness of the fragment.**  At every model of the environment
and every valuation: a reduction — β included, at every binder, with
no certificate — keeps the invariant and the denotation of a subject
that is not the point; two well-denoted sides that are not the point
and that the checker calls definitionally equal have equal
denotations; an inferred term and its type are well-denoted, the type
is a type, and the term's denotation is a member of the type's. -/
theorem soundness [LevelOracle] (m : EnvModel V env) (φ : Name → Nat) :
    (∀ {Γ : List Expr} {e e' : Expr}, Red env Γ e e' → RedSem m φ Γ e e') ∧
    (∀ {Γ : List Expr} {a b : Expr}, DefEq env Γ a b → DefEqSem m φ Γ a b) ∧
    (∀ {Γ : List Expr} {e T : Expr}, Infer env Γ e T → InferSem m φ Γ e T) :=
  ⟨red_sound, defeq_sound, infer_sound⟩

/-- **The closed corollary**: a closed term the checker types is a
member of its type, under every model, valuation and environment. -/
theorem closed_infer [LevelOracle] (m : EnvModel V env) (φ : Name → Nat) {e T : Expr}
    (h : Infer env [] e T) (ρ : Nat → V) :
    interp m.M φ ρ e ∈ˢ interp m.M φ ρ T :=
  (infer_sound (m := m) (φ := φ) h ρ (Sat_nil m.M φ ρ)).2.2.2

end Fragment
