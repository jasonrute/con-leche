module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.DefEqSoundKit
import ConLeche.Model.Rules.EtaSoundKit
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Semantics.DefEqStep
import ConLeche.Semantics.LitStep
import ConLeche.Model.Annot.BitShift
import ConLeche.Model.Annot.BitClosed

public section

/-!
# The soundness of the definitional-equality rules (task #305)

One lemma per constructor of `DefEq`: the structural rules, the
recursive-structure rule, η, the two proof-irrelevance arms, and the
capability rules `structEta`, `structUnit`.

Two sets of lemmas (task #342, L9, L11).  The `…_soundU` lemmas are the
**interim unconditional** proofs: their conclusion is `DefEqSemU` at
one valuation (`CtxOkS`/`LeavesGr`, no point condition), and the side
induction (`Model/Rules/Sound.lean`) reads them.  The `…_sound` lemmas
(the last section) prove the rules at the conditional motive
`DefEqSem`; λ-congruence, η and structure η have none yet (the
section's note says why), so the conditional induction takes them from
the side induction.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

theorem DefEq.refl_soundU {d : Nat} {a : Expr} : DefEqSemU m φ d a a := by
  intro _ _ Δa aa ba _ _ haa hba _ _ _ _ _ _
  rw [haa] at hba
  cases hba
  rfl

theorem DefEq.symm_soundU {d : Nat} {a b : Expr} (h : DefEqSemU m φ d a b) :
    DefEqSemU m φ d b a := by
  intro hfb hfa Δa ba aa hCb hCa hba haa ρ hρ hLb hLa hwb hwa
  exact (h hfa hfb hCa hCb haa hba ρ hρ hLa hLb hwa hwb).symm

/-- **The recursive-structure rule is sound**: the reduct reads, is
graded and framed (`RedSemU`), so the continuation's motive applies at
it. -/
theorem DefEq.redL_soundU {d : Nat} {a a' b : Expr}
    (ha : RedSemU m φ d a a') (hb : DefEqSemU m φ d a' b) :
    DefEqSemU m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb
  obtain ⟨hfa', hsub, aa', haa', hs⟩ := ha hfa hCa haa
  obtain ⟨hwaa', heq⟩ := hs ρ hρ hLa hwa
  rw [heq]
  exact hb hfa' hfb (hCa.of_subset hsub) hCb haa' hba ρ hρ
    (hLa.of_subset hsub) hLb hwaa' hwb

/-- Equivalent levels, equal sorts. -/
theorem DefEq.sort_soundU {d : Nat} {u v : Level}
    (h : Level.isEquiv u v = some true) :
    DefEqSemU m φ d (.sort u) (.sort v) := by
  intro _ _ Δa aa ba _ _ haa hba _ _ _ _ _ _
  rw [denoteMeta_sort] at haa hba
  obtain rfl : aa = AnnotTerm.sort (u.eval φ) := (Option.some.inj haa).symm
  obtain rfl : ba = AnnotTerm.sort (v.eval φ) := (Option.some.inj hba).symm
  rw [Level.isEquiv_sound h φ]

/-- The `fvar` arm: the reading ignores the annotation. -/
theorem DefEq.fvar_soundU {d i : Nat} {ty₁ ty₂ : Expr} :
    DefEqSemU m φ d (.fvar i ty₁) (.fvar i ty₂) := by
  intro _ _ Δa aa ba _ _ haa hba _ _ _ _ _ _
  rw [denoteMeta_fvar] at haa hba
  obtain rfl : aa = AnnotTerm.bvar (d - 1 - i) := (Option.some.inj haa).symm
  obtain rfl : ba = AnnotTerm.bvar (d - 1 - i) := (Option.some.inj hba).symm
  rfl

/-- `acval_const_congr'` with `AcvalParams`
(`Model/Annot/EnvModel.lean`, `acvalParams m`). -/
theorem DefEq.const_soundU {d : Nat} {n : Name} {us us' : List Level}
    (h : Level.isEquivList us us' = some true) :
    DefEqSemU m φ d (.const n us) (.const n us') := by
  intro _ _ Δa aa ba _ _ haa hba _ _ _ _ _ _
  obtain rfl : aa = ba := acval_const_congr' (acvalParams m) h haa hba
  rfl

/-- `denoteMetaNatZeroConst`: the literal `0` reads as `Nat.zero`. -/
theorem DefEq.natZero_soundU {d : Nat} :
    DefEqSemU m φ d (.lit (.natVal 0)) (.const natZeroName []) := by
  intro _ _ Δa aa ba _ _ haa hba _ _ _ _ _ _
  obtain ⟨hg, rfl⟩ := denoteMeta_natLit_inv haa
  rw [denoteMetaNatZeroConst hg] at hba
  obtain rfl : ba = m.acval ConLeche.natZeroName (Level.substFn φ [] []) :=
    (Option.some.inj hba).symm
  rfl

/-- `denoteMetaNatSuccConst`: the packed
successor reads as `succ` applied to the packed predecessor. -/
theorem DefEq.natSucc_soundU {d : Nat} {k : Nat} {x : Expr}
    (h : DefEqSemU m φ d (.lit (.natVal k)) x) :
    DefEqSemU m φ d (.lit (.natVal (k + 1))) (.app (.const natSuccName []) x) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb
  obtain ⟨hg, rfl⟩ := denoteMeta_natLit_inv haa
  obtain ⟨fa, xa, hfa', hxa, rfl⟩ := denoteMeta_app_inv hba
  rw [denoteMetaNatSuccConst hg] at hfa'
  obtain rfl : fa = m.acval ConLeche.natSuccName (Level.substFn φ [] []) :=
    (Option.some.inj hfa').symm
  refine deqStep_appCong rfl (h (Frame.of_not_hasFvar rfl rfl) hfb.app_arg
    (CtxOkS.of_fvarLeaves_nil hCa.length (by simp [Expr.fvarLeaves]))
    hCb.app_arg (denoteMeta_natLit hg) hxa ρ hρ
    (LeavesGr.of_fvarLeaves_nil (by simp [Expr.fvarLeaves]))
    hLb.app_arg ?_ hwb.app_arg)
  simp only [natLitAV] at hwa
  exact hwa.app_arg

/-- Binder congruence: equal domains, equal
bodies opened at the right domain, equal bits (`piR_zero_agree`). -/
theorem DefEq.forallE_soundU {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr}
    {m₁ m₂ : BinderMeta}
    (hty : DefEqSemU m φ d ty₁ ty₂)
    (hbody : DefEqSemU m φ (d + 1) (body₁.instantiate1 (.fvar d ty₂))
      (body₂.instantiate1 (.fvar d ty₂)))
    (hpw : m₁.pw = m₂.pw) :
    DefEqSemU m φ d (.forallE ty₁ body₁ m₁) (.forallE ty₂ body₂ m₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb
  obtain ⟨ta₁, ba₁, hta₁, hva₁, rfl⟩ := denoteMeta_forallE_inv haa
  obtain ⟨ta₂, ba₂, hta₂, hva₂, rfl⟩ := denoteMeta_forallE_inv hba
  have hdom : interp V ρ ta₁ = interp V ρ ta₂ :=
    hty hfa.forallE_ty hfb.forallE_ty hCa.forallE_ty hCb.forallE_ty hta₁ hta₂
      ρ hρ hLa.forallE_ty hLb.forallE_ty hwa.pi_dom.1 hwb.pi_dom.1
  rw [hpw]
  refine deqStep_piCong hdom (fun x hx => ?_)
  exact hbody (hfa.forallE_open hfb.forallE_ty) (hfb.forallE_open hfb.forallE_ty)
    (CtxOkS.openS hCb.forallE_ty hCa.forallE_body hta₂)
    (CtxOkS.openS hCb.forallE_ty hCb.forallE_body hta₂)
    (denoteMeta_open_rename hva₁) hva₂
    (cons x ρ) (Sat_cons V hρ (hdom ▸ hx))
    (LeavesGr.open hCb.forallE_ty hCa.forallE_body hLb.forallE_ty hLa.forallE_body
      hta₂ hwb.pi_dom)
    (LeavesGr.open hCb.forallE_ty hCb.forallE_body hLb.forallE_ty hLb.forallE_body
      hta₂ hwb.pi_dom)
    (hwa.pi_body x hx) (hwb.pi_body x (hdom ▸ hx))

/-- Binder congruence, the λ half. -/
theorem DefEq.lam_soundU {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr}
    {m₁ m₂ : BinderMeta}
    (hty : DefEqSemU m φ d ty₁ ty₂)
    (hbody : DefEqSemU m φ (d + 1) (body₁.instantiate1 (.fvar d ty₂))
      (body₂.instantiate1 (.fvar d ty₂)))
    (hpw : m₁.pw = m₂.pw) :
    DefEqSemU m φ d (.lam ty₁ body₁ m₁) (.lam ty₂ body₂ m₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb
  obtain ⟨ta₁, ba₁, hta₁, hva₁, rfl⟩ := denoteMeta_lam_inv haa
  obtain ⟨ta₂, ba₂, hta₂, hva₂, rfl⟩ := denoteMeta_lam_inv hba
  have hdom : interp V ρ ta₁ = interp V ρ ta₂ :=
    hty hfa.lam_ty hfb.lam_ty hCa.lam_ty hCb.lam_ty hta₁ hta₂
      ρ hρ hLa.lam_ty hLb.lam_ty hwa.lam_dom.1 hwb.lam_dom.1
  rw [hpw]
  refine deqStep_lamCong hdom (fun x hx => ?_)
  exact hbody (hfa.lam_open hfb.lam_ty) (hfb.lam_open hfb.lam_ty)
    (CtxOkS.openS hCb.lam_ty hCa.lam_body hta₂)
    (CtxOkS.openS hCb.lam_ty hCb.lam_body hta₂)
    (denoteMeta_open_rename hva₁) hva₂
    (cons x ρ) (Sat_cons V hρ (hdom ▸ hx))
    (LeavesGr.open hCb.lam_ty hCa.lam_body hLb.lam_ty hLa.lam_body
      hta₂ hwb.lam_dom)
    (LeavesGr.open hCb.lam_ty hCb.lam_body hLb.lam_ty hLb.lam_body
      hta₂ hwb.lam_dom)
    (hwa.lam_body x hx) (hwb.lam_body x (hdom ▸ hx))

/-- Per-node congruence of an application. -/
theorem DefEq.app_soundU {d : Nat} {f₁ a₁ f₂ a₂ : Expr}
    (hf : DefEqSemU m φ d f₁ f₂) (ha : DefEqSemU m φ d a₁ a₂) :
    DefEqSemU m φ d (.app f₁ a₁) (.app f₂ a₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb
  obtain ⟨fa₁, xa₁, hf₁, hx₁, rfl⟩ := denoteMeta_app_inv haa
  obtain ⟨fa₂, xa₂, hf₂, hx₂, rfl⟩ := denoteMeta_app_inv hba
  exact deqStep_appCong
    (hf hfa.app_fn hfb.app_fn hCa.app_fn hCb.app_fn hf₁ hf₂ ρ hρ
      hLa.app_fn hLb.app_fn hwa.app_fn hwb.app_fn)
    (ha hfa.app_arg hfb.app_arg hCa.app_arg hCb.app_arg hx₁ hx₂ ρ hρ
      hLa.app_arg hLb.app_arg hwa.app_arg hwb.app_arg)

/-- Congruence under a projection. -/
theorem DefEq.proj_soundU {d : Nat} {s : Name} {i : Nat} {e₁ e₂ : Expr}
    (h : DefEqSemU m φ d e₁ e₂) :
    DefEqSemU m φ d (.proj s i e₁) (.proj s i e₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb
  obtain ⟨ia₁, he₁, hrd₁⟩ := denoteMeta_proj_inv haa
  obtain ⟨ia₂, he₂, hrd₂⟩ := denoteMeta_proj_inv hba
  rcases hrd₁ with ⟨entry, hfe, rfl⟩ | ⟨hnt, hdec₁⟩
  · rcases hrd₂ with ⟨entry', hfe', rfl⟩ | ⟨hnt', -⟩
    · obtain rfl : entry = entry' := Option.some.inj (hfe.symm.trans hfe')
      exact ProjAV.interp_congr (h hfa.proj_arg hfb.proj_arg hCa.proj_arg
        hCb.proj_arg he₁ he₂ ρ hρ hLa.proj_arg hLb.proj_arg
        (ProjAV.hoistV hwa) (ProjAV.hoistV hwb))
    · rw [hnt'] at hfe; exact nomatch hfe
  · rcases hrd₂ with ⟨entry', hfe', -⟩ | ⟨-, hdec₂⟩
    · rw [hnt] at hfe'; exact nomatch hfe'
    · rcases AnnotTerm.projPair?_cases₂ hdec₁ hdec₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact deqStep_fstCong (h hfa.proj_arg hfb.proj_arg hCa.proj_arg
          hCb.proj_arg he₁ he₂ ρ hρ hLa.proj_arg hLb.proj_arg
          hwa.fst_arg hwb.fst_arg)
      · exact deqStep_sndCong (h hfa.proj_arg hfb.proj_arg hCa.proj_arg
          hCb.proj_arg he₁ he₂ ρ hρ hLa.proj_arg hLb.proj_arg
          hwa.snd_arg hwb.snd_arg)

/-- η (`lamR_eta`, regime-uniform). -/
theorem DefEq.eta_soundU {d : Nat}
    {ty₁ body₁ b tb ty₂ B : Expr} {m₁ m₂ : BinderMeta}
    (htb : InferSemIO m φ d b tb) (hwtb : RedSemU m φ d tb (.forallE ty₂ B m₂))
    (hty : DefEqSemU m φ d ty₂ ty₁)
    (hbody : DefEqSemU m φ (d + 1) (body₁.instantiate1 (.fvar d ty₁))
      (.app b (.fvar d ty₁)))
    (hpw : m₁.pw = m₂.pw) :
    DefEqSemU m φ d (.lam ty₁ body₁ m₁) b := by
  intro hfa hfb Δa aa ba hCa hCb hda hdb ρ hρ hLa hLb hokA hokB
  obtain ⟨hwF1, hbF1, hLF1⟩ := hfa
  obtain ⟨hwF2, hbF2, hLF2⟩ := hfb
  simp only [Expr.WScoped] at hwF1
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbF1
  have hLty : Expr.LeavesBounded ty₁ := fun l hl =>
    hLF1 l (by simp [Expr.fvarLeaves, hl])
  have hLbd : Expr.LeavesBounded body₁ := fun l hl =>
    hLF1 l (by simp [Expr.fvarLeaves, hl])
  have hfty : Frame d ty₁ := ⟨hwF1.1, hbF1.1, hLty⟩
  have hCty : CtxOkS m φ d Δa ty₁ := hCa.lam_ty
  have hCbd : CtxOkS m φ d Δa body₁ := hCa.lam_body
  have hLtyρ : LeavesGr m φ d ty₁ ρ := hLa.lam_ty
  have hLbdρ : LeavesGr m φ d body₁ ρ := hLa.lam_body
  -- the λ's own reading, and its grading at ρ
  obtain ⟨ta, bda, hta, hbda, rfl⟩ := denoteMeta_lam_inv hda
  have hokTa : WellDenotedTy V ρ ta := hokA.lam_dom
  -- `b`'s inferred type, its reduct, and both readings
  obtain ⟨hftb, hsubtb, tba, htba, hX⟩ := htb ⟨hwF2, hbF2, hLF2⟩ hCb hdb
  obtain ⟨hokTb, hmemB⟩ := hX ρ hρ hLb hokB
  have hCtb : CtxOkS m φ d Δa tb := hCb.of_subset hsubtb
  have hLtbρ : LeavesGr m φ d tb ρ := hLb.of_subset hsubtb
  obtain ⟨hfW, hsubW, wtba, hwtba, hY⟩ := hwtb hftb hCtb htba
  obtain ⟨hokW, heqW⟩ := hY ρ hρ hLtbρ hokTb.1
  have hCwr : CtxOkS m φ d Δa (Expr.forallE ty₂ B m₂) := hCtb.of_subset hsubW
  have hLwρ : LeavesGr m φ d (Expr.forallE ty₂ B m₂) ρ := hLtbρ.of_subset hsubW
  obtain ⟨ta₂, ba₂, hta₂, -, rfl⟩ := denoteMeta_forallE_inv hwtba
  have hokTa₂ : WellDenotedTy V ρ ta₂ := hokW.pi_dom
  -- premise one: the two domains agree
  have hdom : interp V ρ ta₂ = interp V ρ ta :=
    hty hfW.forallE_ty hfty hCwr.forallE_ty hCty hta₂ hta ρ hρ
      hLwρ.forallE_ty hLtyρ hokTa₂.1 hokTa.1
  -- premise two: `b` inhabits the product the ∀-type names
  have hmem : interp V ρ ba ∈ˢ piR (pwBit φ m₂.pw) (interp V ρ ta₂)
      (fun x => interp V (cons x ρ) ba₂) := by
    have h := hmemB
    rw [heqW, interp_pi] at h
    exact h
  -- premise three: the two bits are equal (the rule's own `pw` premise)
  have hbit : pwBit φ m₁.pw = pwBit φ m₂.pw := by rw [hpw]
  -- premise four: the λ's fibre is `app ⟦b⟧`
  have hdbUp : denoteMeta m.acval env φ (d + 1) b = some ba.lift := by
    rw [denoteMeta_weaken_top m.acval_closed hwF2, hdb]; rfl
  have hdapp : denoteMeta m.acval env φ (d + 1) (.app b (.fvar d ty₁))
      = some (.app ba.lift (.bvar 0)) := by
    rw [denoteMeta, hdbUp, denoteMeta_fvar]
    simp
  have hCfvar : CtxOkS m φ (d + 1) (ta :: Δa) (.fvar d ty₁) := by
    have := CtxOkS.openS (body := Expr.bvar 0) hCty
      (CtxOkS.of_fvarLeaves_nil hCa.length (by simp [Expr.fvarLeaves])) hta
    simpa [Expr.instantiate1] using this
  have hCapp : CtxOkS m φ (d + 1) (ta :: Δa) (.app b (.fvar d ty₁)) :=
    CtxOkS.app (CtxOkS.weakenTop hCb) hCfvar
  have hokApp : ∀ x, x ∈ˢ interp V ρ ta →
      WellDenotedV V (cons x ρ) (.app ba.lift (.bvar 0)) := by
    intro x hx
    have hok0 : WellDenotedV V (cons x ρ) ba.lift :=
      (WellDenotedV_liftN V 1 ba 0 (cons x ρ)).mpr (by rw [shiftE_zero]; exact hokB)
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨hok0.1, by simp, pwBit φ m₂.pw,
        interp V ρ ta₂, (fun y => interp V (cons y ρ) ba₂), ?_, ?_, ?_⟩
      · rw [interp_lift]; exact hmem
      · show x ∈ˢ _
        rw [hdom]; exact hx
      · exact ⟨((AnnotValid_pi V ρ 0 (pwBit φ m₂.pw) ta₂ ba₂) ▸ hokW.2).2.2,
          fun _ => hokTa₂.2⟩
    · rw [AnnotValid_app]
      exact ⟨hok0.2, by simp⟩
  have hfopen : Frame (d + 1) (body₁.instantiate1 (.fvar d ty₁)) :=
    Frame.open_body hfty hwF1.2 hbF1.2 hLbd
  have hfapp : Frame (d + 1) (.app b (.fvar d ty₁)) := by
    refine ⟨?_, by simp [Expr.looseBVarsBounded, hbF2], fun l hl => ?_⟩
    · simp only [Expr.WScoped]
      exact ⟨Expr.WScoped.mono (by omega) hwF2, by omega,
        Expr.WScoped.mono (by omega) hwF1.1⟩
    · rw [ConLeche.Expr.fvarLeaves] at hl
      rcases List.mem_append.mp hl with h2 | h2
      · exact hLF2 l h2
      · rw [ConLeche.Expr.fvarLeaves] at h2
        rcases List.mem_cons.mp h2 with rfl | h3
        · exact hbF1.1
        · exact hLty l h3
  have hLopenBody : ∀ x : V, LeavesGr m φ (d + 1)
      (body₁.instantiate1 (.fvar d ty₁)) (cons x ρ) := fun _ =>
    LeavesGr.open hCty hCbd hLtyρ hLbdρ hta hokTa
  have hLfvar : ∀ x : V, LeavesGr m φ (d + 1) (.fvar d ty₁) (cons x ρ) := by
    intro x
    have := LeavesGr.open (body := Expr.bvar 0) (x := x) hCty
      (CtxOkS.of_fvarLeaves_nil hCa.length (by simp [Expr.fvarLeaves]))
      hLtyρ (LeavesGr.of_fvarLeaves_nil (by simp [Expr.fvarLeaves])) hta hokTa
    simpa [Expr.instantiate1] using this
  have hLapp : ∀ x : V, LeavesGr m φ (d + 1) (.app b (.fvar d ty₁)) (cons x ρ) :=
    fun x => LeavesGr.app (LeavesGr.weakenTop (ρ := cons x ρ) hCb hLb) (hLfvar x)
  have hbodyEqAt : ∀ x, x ∈ˢ interp V ρ ta →
      interp V (cons x ρ) bda = interp V (cons x ρ) (.app ba.lift (.bvar 0)) :=
    fun x hx => hbody hfopen hfapp (CtxOkS.openS hCty hCbd hta) hCapp
      hbda hdapp (cons x ρ) (Sat_cons V hρ hx)
      (hLopenBody x) (hLapp x) (hokA.lam_body x hx) (hokApp x hx)
  -- η: `lamR_eta`, regime-uniform
  have hpt : ∀ x, x ∈ˢ interp V ρ ta →
      interp V (cons x ρ) bda = SetTheory.app (interp V ρ ba) x := by
    intro x hx
    rw [hbodyEqAt x hx, interp_app, interp_lift_cons, interp_bvar]
    rfl
  rw [interp_lam, lamR_congr hpt, hbit]
  exact lamR_eta (by rw [← hdom]; exact hmem)

/-- `prf_of_isProofFast` twice. -/
theorem DefEq.proofFast_soundU (hin : RulesInputs V m φ) {d : Nat} {a b : Expr}
    (ha : ConLeche.isProofFast env.find? a = true)
    (hb : ConLeche.isProofFast env.find? b = true) :
    DefEqSemU m φ d a b := by
  intro _ _ Δa aa ba hCa hCb haa hba ρ hρ hLa hLb _ _
  rw [prf_of_isProofFast hin.const_ty ha hCa haa ρ hρ hLa,
    prf_of_isProofFast hin.const_ty hb hCb hba ρ hρ hLb]

/-- `prop_side_pt'` twice: a term whose type's
sort is zero-equivalent interprets to the point. -/
theorem DefEq.proofIrrel_soundU {d : Nat}
    {a ta tta b tb ttb : Expr} {u v : Level}
    (hta : InferSemIO m φ d a ta) (htta : InferSemIO m φ d ta tta)
    (hu : RedSemU m φ d tta (.sort u)) (hu0 : Level.isEquiv u .zero = some true)
    (htb : InferSemIO m φ d b tb) (httb : InferSemIO m φ d tb ttb)
    (hv : RedSemU m φ d ttb (.sort v)) (hv0 : Level.isEquiv v .zero = some true) :
    DefEqSemU m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb
  rw [prop_side_pt' hta htta hu.cond hu0 hfa hCa haa ρ hρ hLa hwa,
    prop_side_pt' htb httb hv.cond hv0 hfb hCb hba ρ hρ hLb hwb]

/-- Structure η, unconditionally (the interim side induction): the
stuck side is the η constructor at its type's arguments and its own
projections (`etaSide`; the type's spine fits the former's telescope
because the type is a type, "not pt" source (1)), and the two
comparisons are equations. -/
theorem DefEq.structEta_soundU (hin : RulesInputs V m φ) {d : Nat}
    {a b tb wtb : Expr} {c : Name} {us : List Level} {cvc : ConstantVal}
    {cnP cnF : Nat} {T : Name} {us' : List Level} {cvT : ConstantVal}
    {caps : IndCaps}
    (htb : InferSemIO m φ d b tb) (hwtb : RedSemU m φ d tb wtb)
    (hhead : a.getAppFn = .const c us)
    (hctor : env.find? c = some (.ctorInfo cvc cnP cnF))
    (_hlen : a.getAppArgs.length = cnP + cnF)
    (hthead : wtb.getAppFn = .const T us')
    (hind : env.find? T = some (.indInfo cvT caps))
    (heta : caps.eta = true) (hetaCtor : caps.etaCtor = c)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (hresc : ConLeche.reservedBasisNames.contains c = false)
    (htlen : wtb.getAppArgs.length = caps.etaParams)
    (hlv : us'.length = cvT.levelParams.length)
    (hlps : cvc.levelParams = cvT.levelParams)
    (_hslots : (ConLeche.towerSlotsAll env T caps.etaFields ||
      ConLeche.recSlotsAll env T caps.etaFields) = true)
    (hus : Level.isEquivList us us' = some true)
    (hproj : ConLeche.towerSlotsAll env T caps.etaFields = false →
      EtaProjCertsSem m φ d T us' wtb.getAppArgs b cvT.levelParams
        (List.range caps.etaFields))
    (hparams : DefEqListSemU m φ d (a.getAppArgs.take caps.etaParams)
      wtb.getAppArgs)
    (hfields : DefEqListSemU m φ d (a.getAppArgs.drop caps.etaParams)
      (ConLeche.etaProjs env T us' wtb.getAppArgs b caps.etaFields)) :
    DefEqSemU m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb hda hdb ρ hρ hLa hLb hokA hokB
  -- the stuck side's inferred type, reduced, with its reading
  obtain ⟨hftb, hsubtb, tba, htba, hX⟩ := htb hfb hCb hdb
  obtain ⟨hokTb, hmemB0⟩ := hX ρ hρ hLb hokB
  have hCtb : CtxOkS m φ d Δa tb := hCb.of_subset hsubtb
  have hLtbρ : LeavesGr m φ d tb ρ := hLb.of_subset hsubtb
  obtain ⟨hfW, hsubW, wtba, hwtba, hY⟩ := hwtb hftb hCtb htba
  obtain ⟨hokW, heqW⟩ := hY ρ hρ hLtbρ hokTb.1
  have hCr : CtxOkS m φ d Δa wtb := hCtb.of_subset hsubW
  have hLrρ : LeavesGr m φ d wtb ρ := hLtbρ.of_subset hsubW
  have hmemB : interp V ρ ba ∈ˢ interp V ρ wtba := by rw [← heqW]; exact hmemB0
  -- the reduced type is the family applied to its parameters
  rw [show wtb = Expr.mkAppN wtb.getAppFn wtb.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp wtb).symm, hthead] at hwtba
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteMeta_mkAppN_inv hwtba
  rw [denoteMeta, hind] at hvT
  dsimp only at hvT
  split at hvT
  case isFalse => exact nomatch hvT
  case isTrue =>
  obtain rfl : vT = m.acval T (Level.substFn φ cvT.levelParams us') :=
    (Option.some.inj hvT).symm
  -- the constructor side is the constructor applied to its arguments
  rw [show a = Expr.mkAppN a.getAppFn a.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp a).symm, hhead] at hda
  obtain ⟨vf, asa, hvf, hspa, rfl⟩ := denoteMeta_mkAppN_inv hda
  rw [denoteMeta, hctor] at hvf
  dsimp only at hvf
  split at hvf
  case isFalse => exact nomatch hvf
  case isTrue =>
  obtain rfl : vf = m.acval c (Level.substFn φ cvc.levelParams us) :=
    (Option.some.inj hvf).symm
  -- the two instantiations agree
  have hψc : Level.substFn φ cvc.levelParams us
      = Level.substFn φ cvT.levelParams us' := by
    rw [hlps]
    exact ConLeche.Level.substFn_congr
      (ConLeche.Level.isEquivList_sound hus φ)
  -- the stuck side: the η law and its projections
  obtain ⟨ps, hsps, hfps, _, -, hside⟩ := etaSide hin hind heta hresT
    (by rw [hetaCtor]; exact hresc) (by rw [hetaCtor]; exact hctor) hlv htlen hproj
    hfb hCb (frame_spine hfW hCr) hdb hspt
  have hneW : interp V ρ (AnnotTerm.mkAppN
      (m.acval T (Level.substFn φ cvT.levelParams us')) tsa) ≠ pt := by
    rw [← heqW]; exact hokTb.2.ne_pt
  obtain ⟨hLps, hokps, hb, -⟩ :=
    hside ρ hρ hLb (leavesGr_spine hLrρ) hokW hneW hokB hmemB
  obtain ⟨-, hoA⟩ := hoist_spineV asa hokA
  obtain ⟨-, hoT⟩ := hoist_spineV tsa hokW
  -- the two comparisons, unconditionally
  have htake : (asa.take caps.etaParams).map (interp V ρ) = tsa.map (interp V ρ) :=
    hparams.2
      (fun x hx => frame_spine hfa hCa x (List.mem_of_mem_take hx))
      (frame_spine hfW hCr) (hspa.take caps.etaParams) hspt ρ hρ
      (fun x hx => leavesGr_spine hLa x (List.mem_of_mem_take hx))
      (leavesGr_spine hLrρ)
      (fun x hx => hoA x (List.mem_of_mem_take hx)) hoT
  have hdrop : (asa.drop caps.etaParams).map (interp V ρ) = ps.map (interp V ρ) :=
    hfields.2
      (fun x hx => frame_spine hfa hCa x (List.mem_of_mem_drop hx))
      (fun x hx => ⟨(hfps x hx).1, (hfps x hx).2.1⟩) (hspa.drop caps.etaParams) hsps ρ hρ
      (fun x hx => leavesGr_spine hLa x (List.mem_of_mem_drop hx))
      hLps (fun x hx => hoA x (List.mem_of_mem_drop hx)) hokps
  have hfold : ∀ (l : List AnnotTerm) (x : V),
      l.foldl (fun r y => SetTheory.app r (interp V ρ y)) x
        = (l.map (interp V ρ)).foldl SetTheory.app x := by
    intro l x; rw [List.foldl_map]
  rw [hb, interp_mkAppN, hfold, hψc, ← hetaCtor,
    ← List.take_append_drop caps.etaParams asa, List.map_append, htake, hdrop,
    List.map_append]

/-- Unit-like structure: the stored unit-like law. -/
theorem DefEq.structUnit_soundU (hin : RulesInputs V m φ) {d : Nat}
    {a ta wta b tb wtb : Expr} {T : Name} {us' : List Level}
    {cvT : ConstantVal} {caps : IndCaps}
    (hta : InferSemIO m φ d a ta) (hwta : RedSemU m φ d ta wta)
    (hthead : wta.getAppFn = .const T us')
    (hind : env.find? T = some (.indInfo cvT caps))
    (hunit : caps.unitlike = true)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (htlen : wta.getAppArgs.length = caps.unitParams)
    (hlv : us'.length = cvT.levelParams.length)
    (htb : InferSemIO m φ d b tb) (hwtb : RedSemU m φ d tb wtb)
    (hd : DefEqSemU m φ d wta wtb) :
    DefEqSemU m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb hda hdb ρ hρ hLa hLb hokA hokB
  -- the two sides' inferred types, reduced, with their readings
  obtain ⟨hfta, hsuba, taa, htaa, hXA⟩ := hta hfa hCa hda
  obtain ⟨hokTa, hmemA⟩ := hXA ρ hρ hLa hokA
  have hCta : CtxOkS m φ d Δa ta := hCa.of_subset hsuba
  have hLtaρ : LeavesGr m φ d ta ρ := hLa.of_subset hsuba
  obtain ⟨hfWA, hsubWA, wtaa, hwtaa, hYA⟩ := hwta hfta hCta htaa
  obtain ⟨hokWA, heqWA⟩ := hYA ρ hρ hLtaρ hokTa.1
  have hCwa : CtxOkS m φ d Δa wta := hCta.of_subset hsubWA
  have hLwaρ : LeavesGr m φ d wta ρ := hLtaρ.of_subset hsubWA
  obtain ⟨hftb, hsubb, tba, htba, hXB⟩ := htb hfb hCb hdb
  obtain ⟨hokTb, hmemB⟩ := hXB ρ hρ hLb hokB
  have hCtb : CtxOkS m φ d Δa tb := hCb.of_subset hsubb
  have hLtbρ : LeavesGr m φ d tb ρ := hLb.of_subset hsubb
  obtain ⟨hfWB, hsubWB, wtba, hwtba, hYB⟩ := hwtb hftb hCtb htba
  obtain ⟨hokWB, heqWB⟩ := hYB ρ hρ hLtbρ hokTb.1
  have hCwb : CtxOkS m φ d Δa wtb := hCtb.of_subset hsubWB
  have hLwbρ : LeavesGr m φ d wtb ρ := hLtbρ.of_subset hsubWB
  have hmemAW : interp V ρ aa ∈ˢ interp V ρ wtaa := by rw [← heqWA]; exact hmemA
  have hmemBW : interp V ρ ba ∈ˢ interp V ρ wtba := by rw [← heqWB]; exact hmemB
  -- the certificate's defeq identifies the two family instances
  have hEq : interp V ρ wtaa = interp V ρ wtba :=
    hd hfWA hfWB hCwa hCwb hwtaa hwtba ρ hρ hLwaρ hLwbρ hokWA hokWB
  -- side a's reduct is the family applied to its parameters
  rw [show wta = Expr.mkAppN wta.getAppFn wta.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp wta).symm, hthead] at hwtaa
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteMeta_mkAppN_inv hwtaa
  rw [denoteMeta, hind] at hvT
  dsimp only at hvT
  split at hvT
  case isFalse => exact nomatch hvT
  case isTrue =>
  obtain rfl : vT = m.acval T (Level.substFn φ cvT.levelParams us') :=
    (Option.some.inj hvT).symm
  -- the former's telescope arity, from the environment invariant
  have hstrip : (cvT.type.stripPis caps.unitParams).isSome = true :=
    (m.wf.indCaps hind).1 hunit
  -- the (repaired) unit law, and its carried reading at depth `d`
  obtain ⟨TVa, hTVa, -, hlaw⟩ :=
    hin.caps_ok.2 T cvT caps hind hunit hresT φ us' hlv
  -- the parameter spine fits the former's telescope: the reduct is a
  -- type, not the point ("not pt" source (1))
  obtain ⟨resta, hfitT⟩ := formerFit hin hind hlv hstrip htlen hspt hTVa ρ hokWA
    (by rw [← heqWA]; exact hokTa.2.ne_pt)
  have hfold : ∀ (l : List AnnotTerm) (x : V),
      l.foldl (fun r y => SetTheory.app r (interp V ρ y)) x
        = (l.map (interp V ρ)).foldl SetTheory.app x := by
    intro l x; rw [List.foldl_map]
  have hmx : interp V ρ aa
      ∈ˢ (tsa.map (interp V ρ)).foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ cvT.levelParams us'))) := by
    have h := hmemAW
    rwa [interp_mkAppN, hfold] at h
  have hmy : interp V ρ ba
      ∈ˢ (tsa.map (interp V ρ)).foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ cvT.levelParams us'))) := by
    have h := hEq ▸ hmemBW
    rwa [interp_mkAppN, hfold] at h
  have hlenTs : (tsa.map (interp V ρ)).length = caps.unitParams := by
    rw [List.length_map, ← hspt.length, htlen]
  exact hlaw ρ (tsa.map (interp V ρ)) resta (interp V ρ aa)
    (interp V ρ ba) hlenTs hfitT hmx hmy

/-! ## The conditional rules (task #342, L11)

The rules at the conditional motive `DefEqSem`: two graded sides are
equal at a valuation where neither is the point.  Every step that uses
"not the point" names its source (`_tmp/port/COMMON.md`'s proof rule):
(1) the subject is a type; (2) the hypothesis of the conditional claim
(a head, a projected subject of a non-point is not the point, since the
point applied or projected is the point); (3) membership in a type
whose members are all the point or none of them (`IsTy.eq_of_ne_pt`).

λ-congruence, η and structure η are NOT here: they stay on the interim
side induction (`Model/Rules/Sound.lean`).  λ and η compare the two
bodies at every value of the bound variable, and a body may be the
point at one value while the other is not; under the annotated reading
nothing types the two bodies alike (the body-type check arrives with
the value reading, task #342 S4).  Structure η compares the
constructor side's parameters and fields with the stuck side's
projections, and nothing at the rules tier places both spines in one
telescope of types (the DESIGN record of task #342 L11). -/

/-- The slot of a graded application whose head is not the point: the
graph regime, and a domain that is a type. -/
theorem appSlot_of_ne_pt {ρ : Nat → V} {f x : AnnotTerm}
    (hw : WellDenotedV V ρ (.app f x)) (hn : interp V ρ f ≠ pt) :
    ∃ (v : Nat) (A : V) (B : V → V), v ≠ 0 ∧
      interp V ρ f ∈ˢ piR v A B ∧ interp V ρ x ∈ˢ A ∧ IsTy A := by
  have h := hw.1
  rw [WellDenoted_app] at h
  obtain ⟨-, -, v, A, B, hf, hx, -, hT⟩ := h
  have hv : v ≠ 0 := by
    rintro rfl; exact hn (eq_pt_of_mem_piR_zero hf)
  exact ⟨v, A, B, hv, hf, hx, hT hv⟩

/-- A graded Π-type's fibres are types. -/
theorem _root_.ConLeche.Model.WellDenotedV.pi_fib {ρ : Nat → V} {u v : Nat}
    {A B : AnnotTerm} (h : WellDenotedV V ρ (.pi u v A B)) :
    ∀ x, x ∈ˢ interp V ρ A → IsTy (interp V (cons x ρ) B) := fun x hx =>
  ((WellDenoted_pi V ρ u v A B) ▸ h.1).2.2.2 x hx

theorem DefEq.refl_sound {d : Nat} {a : Expr} : DefEqSem m φ d a a :=
  DefEq.refl_soundU.cond

theorem DefEq.symm_sound {d : Nat} {a b : Expr} (h : DefEqSem m φ d a b) :
    DefEqSem m φ d b a := by
  intro hfb hfa Δa ba aa hCb hCa hba haa ρ hρ hLb hLa hwb hwa hnb hna
  exact (h hfa hfb hCa hCb haa hba ρ hρ hLa hLb hwa hwb hna hnb).symm

/-- The recursive-structure rule: the reduct is graded and equal to the
subject where the subject is not the point ("not pt" source (2)), so it
is not the point there either and the continuation's claim applies. -/
theorem DefEq.redL_sound {d : Nat} {a a' b : Expr}
    (ha : RedSem m φ d a a') (hb : DefEqSem m φ d a' b) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb hna hnb
  obtain ⟨hfa', hsub, aa', haa', hs⟩ := ha hfa hCa haa
  obtain ⟨hwaa', heq⟩ := hs ρ hρ hLa hwa hna
  rw [heq] at hna ⊢
  exact hb hfa' hfb (hCa.of_subset hsub) hCb haa' hba ρ hρ
    (hLa.of_subset hsub) hLb hwaa' hwb hna hnb

theorem DefEq.sort_sound {d : Nat} {u v : Level}
    (h : Level.isEquiv u v = some true) :
    DefEqSem m φ d (.sort u) (.sort v) :=
  (DefEq.sort_soundU h).cond

theorem DefEq.fvar_sound {d i : Nat} {ty₁ ty₂ : Expr} :
    DefEqSem m φ d (.fvar i ty₁) (.fvar i ty₂) :=
  DefEq.fvar_soundU.cond

theorem DefEq.const_sound {d : Nat} {n : Name} {us us' : List Level}
    (h : Level.isEquivList us us' = some true) :
    DefEqSem m φ d (.const n us) (.const n us') :=
  (DefEq.const_soundU h).cond

theorem DefEq.natZero_sound {d : Nat} :
    DefEqSem m φ d (.lit (.natVal 0)) (.const natZeroName []) :=
  DefEq.natZero_soundU.cond

/-- The packed successor: the two arguments are members of `Nat`, a
type ("not pt" source (3)).  The literal's membership is
`natLit_factsAV`; the other argument's comes from its slot, whose head
is the successor, a member of a graph-regime Π-type and so never the
point, so its domain is `Nat` (`piR_dom_unique`). -/
theorem DefEq.natSucc_sound (hin : RulesInputs V m φ) {d : Nat} {k : Nat} {x : Expr}
    (h : DefEqSem m φ d (.lit (.natVal k)) x) :
    DefEqSem m φ d (.lit (.natVal (k + 1))) (.app (.const natSuccName []) x) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb _ _
  obtain ⟨hg, rfl⟩ := denoteMeta_natLit_inv haa
  obtain ⟨fa, xa, hfa', hxa, rfl⟩ := denoteMeta_app_inv hba
  rw [denoteMetaNatSuccConst hg] at hfa'
  obtain rfl : fa = m.acval ConLeche.natSuccName (Level.substFn φ [] []) :=
    (Option.some.inj hfa').symm
  obtain ⟨hz, hs, hT⟩ := hin.nat_heads hg ρ
  have hmk := (natLit_factsAV (m.acval_wellDenoted _ _ ρ) (m.acval_wellDenoted _ _ ρ)
    hz hs hT k).2
  have hw := hwb.1
  rw [WellDenoted_app] at hw
  obtain ⟨-, -, v, A, B, hfm, hxm, -, -⟩ := hw
  have hv : v ≠ 0 := by
    rintro rfl
    exact (mem_piR_pos Nat.one_ne_zero hs).2.2.2 (eq_pt_of_mem_piR_zero hfm)
  have hA := piR_dom_unique Nat.one_ne_zero hv hs hfm
  rw [← hA] at hxm
  have hwk : WellDenotedV V ρ (natLitAV (m.acval natZeroName (Level.substFn φ [] []))
      (m.acval natSuccName (Level.substFn φ [] [])) k) := by
    simp only [natLitAV] at hwa
    exact hwa.app_arg
  refine deqStep_appCong rfl (hT.eq_of_ne_pt hmk hxm fun hn₁ hn₂ =>
    h (Frame.of_not_hasFvar rfl rfl) hfb.app_arg
      (CtxOkS.of_fvarLeaves_nil hCa.length (by simp [Expr.fvarLeaves]))
      hCb.app_arg (denoteMeta_natLit hg) hxa ρ hρ
      (LeavesGr.of_fvarLeaves_nil (by simp [Expr.fvarLeaves]))
      hLb.app_arg hwk hwb.app_arg hn₁ hn₂)

/-- Π-congruence.  Both sides are types: the domains and every fibre are
types, never the point ("not pt" source (1)), so the premises' claims
apply with no condition. -/
theorem DefEq.forallE_sound {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr}
    {m₁ m₂ : BinderMeta}
    (hty : DefEqSem m φ d ty₁ ty₂)
    (hbody : DefEqSem m φ (d + 1) (body₁.instantiate1 (.fvar d ty₂))
      (body₂.instantiate1 (.fvar d ty₂)))
    (hpw : m₁.pw = m₂.pw) :
    DefEqSem m φ d (.forallE ty₁ body₁ m₁) (.forallE ty₂ body₂ m₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb _ _
  obtain ⟨ta₁, ba₁, hta₁, hva₁, rfl⟩ := denoteMeta_forallE_inv haa
  obtain ⟨ta₂, ba₂, hta₂, hva₂, rfl⟩ := denoteMeta_forallE_inv hba
  have hdom : interp V ρ ta₁ = interp V ρ ta₂ :=
    hty hfa.forallE_ty hfb.forallE_ty hCa.forallE_ty hCb.forallE_ty hta₁ hta₂
      ρ hρ hLa.forallE_ty hLb.forallE_ty hwa.pi_dom.1 hwb.pi_dom.1
      hwa.pi_dom.ne_pt hwb.pi_dom.ne_pt
  rw [hpw]
  refine deqStep_piCong hdom (fun x hx => ?_)
  have hx₂ : x ∈ˢ interp V ρ ta₂ := hdom ▸ hx
  exact hbody (hfa.forallE_open hfb.forallE_ty) (hfb.forallE_open hfb.forallE_ty)
    (CtxOkS.openS hCb.forallE_ty hCa.forallE_body hta₂)
    (CtxOkS.openS hCb.forallE_ty hCb.forallE_body hta₂)
    (denoteMeta_open_rename hva₁) hva₂
    (cons x ρ) (Sat_cons V hρ hx₂)
    (LeavesGr.open hCb.forallE_ty hCa.forallE_body hLb.forallE_ty hLa.forallE_body
      hta₂ hwb.pi_dom)
    (LeavesGr.open hCb.forallE_ty hCb.forallE_body hLb.forallE_ty hLb.forallE_body
      hta₂ hwb.pi_dom)
    (hwa.pi_body x hx) (hwb.pi_body x hx₂)
    (hwa.pi_fib x hx).ne_pt (hwb.pi_fib x hx₂).ne_pt

/-- Application congruence.  The heads of two applications that are not
the point are not the point ("not pt" source (2)), so they are equal;
their slots are in the graph regime, so the two domains are the one
domain of the equal heads (`piR_dom_unique`), a type: the arguments are
both the point or neither is ("not pt" source (3)). -/
theorem DefEq.app_sound {d : Nat} {f₁ a₁ f₂ a₂ : Expr}
    (hf : DefEqSem m φ d f₁ f₂) (ha : DefEqSem m φ d a₁ a₂) :
    DefEqSem m φ d (.app f₁ a₁) (.app f₂ a₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb hna hnb
  obtain ⟨fa₁, xa₁, hf₁, hx₁, rfl⟩ := denoteMeta_app_inv haa
  obtain ⟨fa₂, xa₂, hf₂, hx₂, rfl⟩ := denoteMeta_app_inv hba
  have hn₁ : interp V ρ fa₁ ≠ pt := by
    intro h; apply hna; rw [interp_app, h, app_pt]
  have hn₂ : interp V ρ fa₂ ≠ pt := by
    intro h; apply hnb; rw [interp_app, h, app_pt]
  have heF := hf hfa.app_fn hfb.app_fn hCa.app_fn hCb.app_fn hf₁ hf₂ ρ hρ
    hLa.app_fn hLb.app_fn hwa.app_fn hwb.app_fn hn₁ hn₂
  obtain ⟨v₁, A₁, B₁, hv₁, hs₁, hm₁, hT₁⟩ := appSlot_of_ne_pt hwa hn₁
  obtain ⟨v₂, A₂, B₂, hv₂, hs₂, hm₂, -⟩ := appSlot_of_ne_pt hwb hn₂
  rw [← heF] at hs₂
  have hA : A₁ = A₂ := piR_dom_unique hv₁ hv₂ hs₁ hs₂
  rw [← hA] at hm₂
  exact deqStep_appCong heF (hT₁.eq_of_ne_pt hm₁ hm₂ fun h₁ h₂ =>
    ha hfa.app_arg hfb.app_arg hCa.app_arg hCb.app_arg hx₁ hx₂ ρ hρ
      hLa.app_arg hLb.app_arg hwa.app_arg hwb.app_arg h₁ h₂)

/-- Congruence under a projection: a projection of the point is the
point (`projS_pt`, `sfst_pt`, `ssnd_pt`), so the projected subjects of
two projections that are not the point are not the point ("not pt"
source (2)). -/
theorem DefEq.proj_sound {d : Nat} {s : Name} {i : Nat} {e₁ e₂ : Expr}
    (h : DefEqSem m φ d e₁ e₂) :
    DefEqSem m φ d (.proj s i e₁) (.proj s i e₂) := by
  intro hfa hfb Δa aa ba hCa hCb haa hba ρ hρ hLa hLb hwa hwb hna hnb
  obtain ⟨ia₁, he₁, hrd₁⟩ := denoteMeta_proj_inv haa
  obtain ⟨ia₂, he₂, hrd₂⟩ := denoteMeta_proj_inv hba
  rcases hrd₁ with ⟨entry, hfe, rfl⟩ | ⟨hnt, hdec₁⟩
  · rcases hrd₂ with ⟨entry', hfe', rfl⟩ | ⟨hnt', -⟩
    · obtain rfl : entry = entry' := Option.some.inj (hfe.symm.trans hfe')
      have hn₁ : interp V ρ ia₁ ≠ pt := by
        intro h; apply hna; rw [projAV_interp, h, ConLeche.SetTheory.Tower.projS_pt]
      have hn₂ : interp V ρ ia₂ ≠ pt := by
        intro h; apply hnb; rw [projAV_interp, h, ConLeche.SetTheory.Tower.projS_pt]
      exact ProjAV.interp_congr (h hfa.proj_arg hfb.proj_arg hCa.proj_arg
        hCb.proj_arg he₁ he₂ ρ hρ hLa.proj_arg hLb.proj_arg
        (ProjAV.hoistV hwa) (ProjAV.hoistV hwb) hn₁ hn₂)
    · rw [hnt'] at hfe; exact nomatch hfe
  · rcases hrd₂ with ⟨entry', hfe', -⟩ | ⟨-, hdec₂⟩
    · rw [hnt] at hfe'; exact nomatch hfe'
    · rcases AnnotTerm.projPair?_cases₂ hdec₁ hdec₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hn₁ : interp V ρ ia₁ ≠ pt := by
          intro h; apply hna; rw [interp_fst, h, sfst_pt]
        have hn₂ : interp V ρ ia₂ ≠ pt := by
          intro h; apply hnb; rw [interp_fst, h, sfst_pt]
        exact deqStep_fstCong (h hfa.proj_arg hfb.proj_arg hCa.proj_arg
          hCb.proj_arg he₁ he₂ ρ hρ hLa.proj_arg hLb.proj_arg
          hwa.fst_arg hwb.fst_arg hn₁ hn₂)
      · have hn₁ : interp V ρ ia₁ ≠ pt := by
          intro h; apply hna; rw [interp_snd, h, ssnd_pt]
        have hn₂ : interp V ρ ia₂ ≠ pt := by
          intro h; apply hnb; rw [interp_snd, h, ssnd_pt]
        exact deqStep_sndCong (h hfa.proj_arg hfb.proj_arg hCa.proj_arg
          hCb.proj_arg he₁ he₂ ρ hρ hLa.proj_arg hLb.proj_arg
          hwa.snd_arg hwb.snd_arg hn₁ hn₂)

/-- Both sides are the point (`prf_of_isProofFast`): vacuous at the
conditional motive. -/
theorem DefEq.proofFast_sound (hin : RulesInputs V m φ) {d : Nat} {a b : Expr}
    (ha : ConLeche.isProofFast env.find? a = true)
    (_hb : ConLeche.isProofFast env.find? b = true) :
    DefEqSem m φ d a b := by
  intro _ _ Δa aa ba hCa hCb haa _ ρ hρ hLa _ _ _ hna _
  exact absurd (prf_of_isProofFast hin.const_ty ha hCa haa ρ hρ hLa) hna

/-- Both sides are the point (`prop_side_pt'`): vacuous at the
conditional motive. -/
theorem DefEq.proofIrrel_sound {d : Nat}
    {a ta tta b tb ttb : Expr} {u v : Level}
    (hta : InferSemIO m φ d a ta) (htta : InferSemIO m φ d ta tta)
    (hu : RedSem m φ d tta (.sort u)) (hu0 : Level.isEquiv u .zero = some true)
    (_htb : InferSemIO m φ d b tb) (_httb : InferSemIO m φ d tb ttb)
    (_hv : RedSem m φ d ttb (.sort v)) (_hv0 : Level.isEquiv v .zero = some true) :
    DefEqSem m φ d a b := by
  intro hfa _ Δa aa ba hCa _ haa _ ρ hρ hLa _ hwa _ hna _
  exact absurd (prop_side_pt' hta htta hu hu0 hfa hCa haa ρ hρ hLa hwa) hna

set_option maxHeartbeats 800000 in
/-- **Structure η at the conditional motive** (task #342 L11b).  Neither
side is the point.  The stuck side's type is a type ("not pt" source
(1)), so its reduct is graded and equal, and `etaSide` gives the η law
and the coherence law: `tsa ++ ps` fits the η constructor's telescope.
The constructor side is graded and not the point, so its spine fits the
same telescope ("not pt" source (2), `teleFitPA_of_graded_ne_pt`).  The
telescope's domains are types, so the two comparisons, conditional on
the point, make the spines equal (`teleFit_eq_of_cond`, L11's finding
2).  The type application's certificate is not read. -/
theorem DefEq.structEta_sound (hin : RulesInputs V m φ) {d : Nat}
    {a b tb wtb : Expr} {c : Name} {us : List Level} {cvc : ConstantVal}
    {cnP cnF : Nat} {T : Name} {us' : List Level} {cvT : ConstantVal}
    {caps : IndCaps}
    (htb : InferSemIO m φ d b tb) (hwtb : RedSem m φ d tb wtb)
    (hhead : a.getAppFn = .const c us)
    (hctor : env.find? c = some (.ctorInfo cvc cnP cnF))
    (_hlen : a.getAppArgs.length = cnP + cnF)
    (hthead : wtb.getAppFn = .const T us')
    (hind : env.find? T = some (.indInfo cvT caps))
    (heta : caps.eta = true) (hetaCtor : caps.etaCtor = c)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (hresc : ConLeche.reservedBasisNames.contains c = false)
    (htlen : wtb.getAppArgs.length = caps.etaParams)
    (hlv : us'.length = cvT.levelParams.length)
    (hlps : cvc.levelParams = cvT.levelParams)
    (_hslots : (ConLeche.towerSlotsAll env T caps.etaFields ||
      ConLeche.recSlotsAll env T caps.etaFields) = true)
    (hus : Level.isEquivList us us' = some true)
    (hproj : ConLeche.towerSlotsAll env T caps.etaFields = false →
      EtaProjCertsSem m φ d T us' wtb.getAppArgs b cvT.levelParams
        (List.range caps.etaFields))
    (hparams : DefEqListSem m φ d (a.getAppArgs.take caps.etaParams)
      wtb.getAppArgs)
    (hfields : DefEqListSem m φ d (a.getAppArgs.drop caps.etaParams)
      (ConLeche.etaProjs env T us' wtb.getAppArgs b caps.etaFields)) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb hda hdb ρ hρ hLa hLb hokA hokB hneA _
  -- the stuck side's inferred type, reduced: a type
  obtain ⟨hftb, hsubtb, tba, htba, hX⟩ := htb hfb hCb hdb
  obtain ⟨hokTb, hmemB0⟩ := hX ρ hρ hLb hokB
  have hCtb : CtxOkS m φ d Δa tb := hCb.of_subset hsubtb
  have hLtbρ : LeavesGr m φ d tb ρ := hLb.of_subset hsubtb
  obtain ⟨hfW, hsubW, wtba, hwtba, hY⟩ := hwtb hftb hCtb htba
  obtain ⟨hokW, heqW⟩ := hY ρ hρ hLtbρ hokTb.1 hokTb.ne_pt
  have hCr : CtxOkS m φ d Δa wtb := hCtb.of_subset hsubW
  have hLrρ : LeavesGr m φ d wtb ρ := hLtbρ.of_subset hsubW
  have hmemB : interp V ρ ba ∈ˢ interp V ρ wtba := by rw [← heqW]; exact hmemB0
  have hneW : interp V ρ wtba ≠ pt := by rw [← heqW]; exact hokTb.ne_pt
  -- the reduced type is the family applied to its parameters
  rw [show wtb = Expr.mkAppN wtb.getAppFn wtb.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp wtb).symm, hthead] at hwtba
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteMeta_mkAppN_inv hwtba
  rw [denoteMeta, hind] at hvT
  dsimp only at hvT
  split at hvT
  case isFalse => exact nomatch hvT
  case isTrue =>
  obtain rfl : vT = m.acval T (Level.substFn φ cvT.levelParams us') :=
    (Option.some.inj hvT).symm
  -- the constructor side is the constructor applied to its arguments
  rw [show a = Expr.mkAppN a.getAppFn a.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp a).symm, hhead] at hda
  obtain ⟨vf, asa, hvf, hspa, rfl⟩ := denoteMeta_mkAppN_inv hda
  rw [denoteMeta, hctor] at hvf
  dsimp only at hvf
  split at hvf
  case isFalse => exact nomatch hvf
  case isTrue =>
  obtain rfl : vf = m.acval c (Level.substFn φ cvc.levelParams us) :=
    (Option.some.inj hvf).symm
  have hψc : Level.substFn φ cvc.levelParams us
      = Level.substFn φ cvT.levelParams us' := by
    rw [hlps]
    exact ConLeche.Level.substFn_congr
      (ConLeche.Level.isEquivList_sound hus φ)
  -- the stuck side: the η law and the coherence law
  obtain ⟨ps, hsps, hfps, TCa, hTCa, hside⟩ := etaSide hin hind heta hresT
    (by rw [hetaCtor]; exact hresc) (by rw [hetaCtor]; exact hctor) hlv htlen hproj
    hfb hCb (frame_spine hfW hCr) hdb hspt
  obtain ⟨hLps, hokps, hb, restC, hfitC⟩ :=
    hside ρ hρ hLb (leavesGr_spine hLrρ) hokW hneW hokB hmemB
  obtain ⟨-, hoA⟩ := hoist_spineV asa hokA
  obtain ⟨-, hoT⟩ := hoist_spineV tsa hokW
  -- the constructor side fits the same telescope: its head inhabits
  -- the constructor's type reading, and it is not the point
  have hlvc : us'.length = cvc.levelParams.length := by rw [hlps]; exact hlv
  obtain ⟨tc, htc, hoktc, hmemC, -, -⟩ :=
    constTy_pkg hin.const_ty hctor rfl (show us'.length = _ from hlvc)
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at htc hmemC
  obtain rfl : TCa = tc := Option.some.inj (hTCa.symm.trans (htc 0))
  have hlenA : asa.length = (tsa ++ ps).length := by
    have h1 := hparams.1
    have h2 := hfields.1
    rw [List.length_take, htlen] at h1
    rw [List.length_drop, hsps.length] at h2
    rw [List.length_append, ← hspt.length, ← hspa.length, htlen]
    omega
  have hpcA : PiChain asa.length TCa := by
    have := piChain_of_teleFit hfitC
    rwa [List.length_map, ← hlenA] at this
  have hmemC' : interp V ρ (m.acval c (Level.substFn φ cvc.levelParams us))
      ∈ˢ interp V ρ TCa := by
    rw [hψc, ← hlps]; exact hmemC ρ
  obtain ⟨restA, hfitA⟩ := teleFitPA_of_graded_ne_pt asa hpcA (hoktc ρ) hmemC' hokA hneA
  have hfitA' := teleFit_of_teleFitPA hpcA hfitA
  -- the two comparisons, conditional on the point
  have htk := hparams.2
    (fun x hx => frame_spine hfa hCa x (List.mem_of_mem_take hx))
    (frame_spine hfW hCr) (hspa.take caps.etaParams) hspt ρ hρ
    (fun x hx => leavesGr_spine hLa x (List.mem_of_mem_take hx))
    (leavesGr_spine hLrρ)
    (fun x hx => hoA x (List.mem_of_mem_take hx)) hoT
  have hdr := hfields.2
    (fun x hx => frame_spine hfa hCa x (List.mem_of_mem_drop hx))
    (fun x hx => ⟨(hfps x hx).1, (hfps x hx).2.1⟩) (hspa.drop caps.etaParams) hsps ρ hρ
    (fun x hx => leavesGr_spine hLa x (List.mem_of_mem_drop hx))
    hLps (fun x hx => hoA x (List.mem_of_mem_drop hx)) hokps
  have htkLen : ((asa.take caps.etaParams).map (interp V ρ)).length
      = (tsa.map (interp V ρ)).length := by
    rw [List.length_map, List.length_map, List.length_take, ← hspt.length, htlen]
    have := hlenA
    rw [List.length_append, ← hspt.length, htlen] at this
    omega
  have hspine : asa.map (interp V ρ) = (tsa ++ ps).map (interp V ρ) := by
    refine teleFit_eq_of_cond (hoktc ρ).1 hfitA' hfitC
      (by rw [List.length_map, List.length_map, hlenA]) fun p hp => ?_
    rw [← List.take_append_drop caps.etaParams asa, List.map_append, List.map_append,
      List.zip_append htkLen] at hp
    rcases List.mem_append.mp hp with hp' | hp'
    · exact htk p hp'
    · exact hdr p hp'
  have hfold : ∀ (l : List AnnotTerm) (x : V),
      l.foldl (fun r y => SetTheory.app r (interp V ρ y)) x
        = (l.map (interp V ρ)).foldl SetTheory.app x := by
    intro l x; rw [List.foldl_map]
  rw [hb, interp_mkAppN, hfold, hspine, hψc, ← hetaCtor]

/-- Unit-like structure: the two inferred types and their reducts are
types ("not pt" source (1)), so their reductions and the certificate's
comparison are equations; the stored unit law then equates any two
members, the point or not. -/
theorem DefEq.structUnit_sound (hin : RulesInputs V m φ) {d : Nat}
    {a ta wta b tb wtb : Expr} {T : Name} {us' : List Level}
    {cvT : ConstantVal} {caps : IndCaps}
    (hta : InferSemIO m φ d a ta) (hwta : RedSem m φ d ta wta)
    (hthead : wta.getAppFn = .const T us')
    (hind : env.find? T = some (.indInfo cvT caps))
    (hunit : caps.unitlike = true)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (htlen : wta.getAppArgs.length = caps.unitParams)
    (hlv : us'.length = cvT.levelParams.length)
    (htb : InferSemIO m φ d b tb) (hwtb : RedSem m φ d tb wtb)
    (hd : DefEqSem m φ d wta wtb) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb hda hdb ρ hρ hLa hLb hokA hokB _ _
  -- the two sides' inferred types, reduced, with their readings
  obtain ⟨hfta, hsuba, taa, htaa, hXA⟩ := hta hfa hCa hda
  obtain ⟨hokTa, hmemA⟩ := hXA ρ hρ hLa hokA
  have hCta : CtxOkS m φ d Δa ta := hCa.of_subset hsuba
  have hLtaρ : LeavesGr m φ d ta ρ := hLa.of_subset hsuba
  obtain ⟨hfWA, hsubWA, wtaa, hwtaa, hYA⟩ := hwta hfta hCta htaa
  obtain ⟨hokWA, heqWA⟩ := hYA ρ hρ hLtaρ hokTa.1 hokTa.ne_pt
  have hCwa : CtxOkS m φ d Δa wta := hCta.of_subset hsubWA
  have hLwaρ : LeavesGr m φ d wta ρ := hLtaρ.of_subset hsubWA
  obtain ⟨hftb, hsubb, tba, htba, hXB⟩ := htb hfb hCb hdb
  obtain ⟨hokTb, hmemB⟩ := hXB ρ hρ hLb hokB
  have hCtb : CtxOkS m φ d Δa tb := hCb.of_subset hsubb
  have hLtbρ : LeavesGr m φ d tb ρ := hLb.of_subset hsubb
  obtain ⟨hfWB, hsubWB, wtba, hwtba, hYB⟩ := hwtb hftb hCtb htba
  obtain ⟨hokWB, heqWB⟩ := hYB ρ hρ hLtbρ hokTb.1 hokTb.ne_pt
  have hCwb : CtxOkS m φ d Δa wtb := hCtb.of_subset hsubWB
  have hLwbρ : LeavesGr m φ d wtb ρ := hLtbρ.of_subset hsubWB
  have hmemAW : interp V ρ aa ∈ˢ interp V ρ wtaa := by rw [← heqWA]; exact hmemA
  have hmemBW : interp V ρ ba ∈ˢ interp V ρ wtba := by rw [← heqWB]; exact hmemB
  -- the certificate's defeq identifies the two family instances: types
  have hEq : interp V ρ wtaa = interp V ρ wtba :=
    hd hfWA hfWB hCwa hCwb hwtaa hwtba ρ hρ hLwaρ hLwbρ hokWA hokWB
      (heqWA ▸ hokTa.ne_pt) (heqWB ▸ hokTb.ne_pt)
  -- side a's reduct is the family applied to its parameters
  rw [show wta = Expr.mkAppN wta.getAppFn wta.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp wta).symm, hthead] at hwtaa
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteMeta_mkAppN_inv hwtaa
  rw [denoteMeta, hind] at hvT
  dsimp only at hvT
  split at hvT
  case isFalse => exact nomatch hvT
  case isTrue =>
  obtain rfl : vT = m.acval T (Level.substFn φ cvT.levelParams us') :=
    (Option.some.inj hvT).symm
  have hstrip : (cvT.type.stripPis caps.unitParams).isSome = true :=
    (m.wf.indCaps hind).1 hunit
  obtain ⟨TVa, hTVa, -, hlaw⟩ :=
    hin.caps_ok.2 T cvT caps hind hunit hresT φ us' hlv
  -- the parameter spine fits the former's telescope: the reduct is a
  -- type, not the point ("not pt" source (1))
  obtain ⟨resta, hfitT⟩ := formerFit hin hind hlv hstrip htlen hspt hTVa ρ hokWA
    (by rw [← heqWA]; exact hokTa.2.ne_pt)
  have hfold : ∀ (l : List AnnotTerm) (x : V),
      l.foldl (fun r y => SetTheory.app r (interp V ρ y)) x
        = (l.map (interp V ρ)).foldl SetTheory.app x := by
    intro l x; rw [List.foldl_map]
  have hmx : interp V ρ aa
      ∈ˢ (tsa.map (interp V ρ)).foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ cvT.levelParams us'))) := by
    have h := hmemAW
    rwa [interp_mkAppN, hfold] at h
  have hmy : interp V ρ ba
      ∈ˢ (tsa.map (interp V ρ)).foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ cvT.levelParams us'))) := by
    have h := hEq ▸ hmemBW
    rwa [interp_mkAppN, hfold] at h
  have hlenTs : (tsa.map (interp V ρ)).length = caps.unitParams := by
    rw [List.length_map, ← hspt.length, htlen]
  exact hlaw ρ (tsa.map (interp V ρ)) resta (interp V ρ aa)
    (interp V ρ ba) hlenTs hfitT hmx hmy

end ConLeche.Model.Rules
