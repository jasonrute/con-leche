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

The rules are proved at the conditional motive `DefEqSem` (task #342,
L9, L11).  A few leaf rules read no claim and are proved unconditionally
(`…_soundU`, `DefEqSemU`) and weakened.  Structure η reads the η
constructor's telescope coherence (task #342 L11b, `EtaSoundKit`).
λ-congruence (`DefEqLams`) and η are the last section
(task #342 S4).
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

/-! ## The conditional rules (task #342, L11)

The rules at the conditional motive `DefEqSem`: two graded sides are
equal at a valuation where neither is the point.  Every step that uses
"not the point" names its source (`_tmp/port/COMMON.md`'s proof rule):
(1) the subject is a type; (2) the hypothesis of the conditional claim
(a head, a projected subject of a non-point is not the point, since the
point applied or projected is the point); (3) membership in a type
whose members are all the point or none of them (`IsTy.eq_of_ne_pt`).

λ-congruence and η compare the two bodies at every value of the bound
variable, and a body may be the point at one value while the other is
not; their rules carry the body-type check (task #342 S4, the last
section).  Structure η compares the constructor side's parameters and
fields with the stuck side's projections, and nothing at the rules tier
places both spines in one telescope of types (the DESIGN record of task
#342 L11): owed to L11b. -/

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
      (body₂.instantiate1 (.fvar d ty₂))) :
    DefEqSem m φ d (.forallE ty₁ body₁ m₁) (.forallE ty₂ body₂ m₂) := by
  -- **owed to task #342 L14a** (the S4 sorry ledger): the rule compares
  -- no binder datum; the annotated reading's two bits need it, the value
  -- reading (`piV`) none
  have hpw : m₁.pw = m₂.pw := sorry
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

/-! ## λ-congruence and η at the value reading (task #342 S4)

`DefEqLams` (task #349) concludes the UNCONDITIONAL `DefEqLamsSem`: the
innermost level's full-grade body types put the two bodies in one type,
whose members are all the point or none, so the bodies' conditional claim
is an equation there; an equation of the bodies at every value of the
variable is an equation of the λs, so `outer` needs no type.  η's typed
premise does the same for the λ's body and `b` applied.  The proofs are
the fragment's (`whitepaper/Fragment/Sound.lean`: `DefEqLams.inner_sound`,
`outer_sound`, `DefEq.eta_sound`) at the value reading; **owed to task
#342 L18** (the S4 sorry ledger). -/

/-- Syntactically equal λs are equal outright. -/
theorem DefEqLams.refl_sound {d : Nat} {a : Expr} : DefEqLamsSem m φ d a a :=
  DefEq.refl_soundU

/-- The innermost level: **owed to task #342 L18**. -/
theorem DefEqLams.inner_sound {d : Nat} {ty₁ body₁ ty₂ body₂ t₁ t₂ : Expr}
    {m₁ m₂ : BinderMeta}
    (_hty : DefEqSem m φ d ty₁ ty₂)
    (_hbody : DefEqSem m φ (d + 1) (body₁.instantiate1 (.fvar d ty₂))
      (body₂.instantiate1 (.fvar d ty₂)))
    (_ht₁ : InferSemFull m φ (d + 1) (body₁.instantiate1 (.fvar d ty₂)) t₁)
    (_ht₂ : InferSemFull m φ (d + 1) (body₂.instantiate1 (.fvar d ty₂)) t₂)
    (_ht : DefEqSem m φ (d + 1) t₁ t₂) :
    DefEqLamsSem m φ d (.lam ty₁ body₁ m₁) (.lam ty₂ body₂ m₂) := sorry

/-- An outer level: **owed to task #342 L18**. -/
theorem DefEqLams.outer_sound {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr}
    {m₁ m₂ : BinderMeta}
    (_hty : DefEqSem m φ d ty₁ ty₂)
    (_hbody : DefEqLamsSem m φ (d + 1) (body₁.instantiate1 (.fvar d ty₂))
      (body₂.instantiate1 (.fvar d ty₂))) :
    DefEqLamsSem m φ d (.lam ty₁ body₁ m₁) (.lam ty₂ body₂ m₂) := sorry

/-- λ-congruence: the telescopes' unconditional claim, weakened. -/
theorem DefEq.lams_sound {d : Nat} {a b : Expr} (h : DefEqLamsSem m φ d a b) :
    DefEqSem m φ d a b :=
  h.cond

/-- η, typed: **owed to task #342 L18** (with the io claim of `b`'s type,
the hereditary `IORel`; the fragment's `etaIO_sound` for atom heads). -/
theorem DefEq.eta_sound {d : Nat}
    {ty₁ body₁ b tb ty₂ B t₁ : Expr} {m₁ m₂ : BinderMeta}
    (_htb : InferSemIO m φ d b tb) (_hwtb : RedSem m φ d tb (.forallE ty₂ B m₂))
    (_hty : DefEqSem m φ d ty₂ ty₁)
    (_hbody : DefEqSem m φ (d + 1) (body₁.instantiate1 (.fvar d ty₁))
      (.app b (.fvar d ty₁)))
    (_ht₁ : InferSemFull m φ (d + 1) (body₁.instantiate1 (.fvar d ty₁)) t₁)
    (_htB : DefEqSem m φ (d + 1) t₁ (B.instantiate1 (.fvar d ty₁))) :
    DefEqSem m φ d (.lam ty₁ body₁ m₁) b := sorry

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

end ConLeche.Model.Rules
