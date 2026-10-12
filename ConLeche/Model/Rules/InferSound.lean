module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Semantics.LitParams
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.WellDenotedTransport
import ConLeche.Semantics.Frame
import ConLeche.Semantics.LitStep
import ConLeche.Semantics.Skeleton
import ConLeche.Model.Rules.RedSoundKit

public section

/-!
# The soundness of the inference rules (task #305)

One lemma per constructor of `Infer`, at the constructor's grade
(`InferSem m φ g …` dispatches to the establishment motive at `.full`
and the consumption motive at `.io`).  The application clause's
`appSkip` is the io grade's gated arm: `io_domain_transfer` against
the subject's own hereditary app slot.

The λ rule's chain case needs the SHAPE of the body's inferred type
(a ∀ at the inner λ's own annotation, `Infer.lam_shape`), which the master induction reads off the premise
derivation and hands in as `hshape`.

The motives are per valuation (task #342, L9): the context discipline
outside `ρ` is the structural `CtxOkS`, and the leaves' grading
(`LeavesGr`), `Sat` and, at the io grade, the subject's grading are
premises at the one valuation `ρ`.  These lemmas are shared by the
interim unconditional side induction and the main one, so they take the
conditional reduction and comparison claims (`RedSem`, `DefEqSem`),
whose subjects here are always types: an inferred type and its weak
head normal form, a Π's domain, a sort.  Their "not the point" premises
are discharged by `WellDenotedTy.ne_pt`.
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

/-! ## The grade kit

The establishment motive is the stronger one: it concludes the
subject's grading where the consumption motive takes it.  A leaf rule
(`sort`, `fvar`, `const`, `natLit`, `strLit`) establishes outright, so
its lemma is proved once at `InferSemFull` and dispatched. -/

/-- Establishment implies consumption: drop the concluded grading. -/
theorem InferSemFull.toIO {d : Nat} {e t : Expr}
    (h : InferSemFull m φ d e t) : InferSemIO m φ d e t := by
  intro hf Δa ea hC hea
  obtain ⟨hft, hsub, ta, hta, hrow⟩ := h hf hC hea
  exact ⟨hft, hsub, ta, hta, fun ρ hρ hL _ => (hrow ρ hρ hL).2⟩

/-- A rule that establishes is sound at either grade. -/
theorem InferSemFull.toSem {g : Grade} {d : Nat} {e t : Expr}
    (h : InferSemFull m φ d e t) : InferSem m φ g d e t := by
  cases g with
  | full => exact h
  | io => exact h.toIO

/-- **The uniform view of the inference motive.**  Both grades
conclude the type's frame, leaf inclusion and reading outside the
valuation, and at each valuation `ρ` where the context is satisfied and
the subject's leaves are graded: the subject's grading, the type's
grading and the membership.  They differ only in where the SUBJECT's
grading at `ρ` sits — a premise at `.io`, a conclusion at `.full`.
Reading a premise derivation's motive through this lemma, and building
the conclusion's through `InferSem.of_uniform`, is what lets one
argument serve both grades. -/
theorem InferSem.apply {g : Grade} {d : Nat} {e t : Expr}
    (h : InferSem m φ g d e t) (hfe : Frame d e) {Δa : List AnnotTerm}
    {ea : AnnotTerm} (hC : CtxOkS m φ d Δa e)
    (hea : denoteMeta m.acval env φ d e = some ea) :
    Frame d t ∧ LeavesSub t e ∧
      ∃ ta, denoteMeta m.acval env φ d t = some ta ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d e ρ →
          (g = .io → WellDenotedV V ρ ea) →
          WellDenotedV V ρ ea ∧ WellDenotedTy V ρ ta ∧
            interp V ρ ea ∈ˢ interp V ρ ta := by
  cases g with
  | full =>
    obtain ⟨hft, hsub, ta, hta, hrow⟩ := h hfe hC hea
    exact ⟨hft, hsub, ta, hta, fun ρ hρ hL _ => hrow ρ hρ hL⟩
  | io =>
    obtain ⟨hft, hsub, ta, hta, hrow⟩ := h hfe hC hea
    exact ⟨hft, hsub, ta, hta, fun ρ hρ hL hg =>
      ⟨hg rfl, hrow ρ hρ hL (hg rfl)⟩⟩

/-- `InferSem.apply`'s converse: the uniform statement builds the
motive at either grade. -/
theorem InferSem.of_uniform {g : Grade} {d : Nat} {e t : Expr}
    (h : ∀ {Δa : List AnnotTerm} {ea : AnnotTerm}, Frame d e →
      CtxOkS m φ d Δa e → denoteMeta m.acval env φ d e = some ea →
      Frame d t ∧ LeavesSub t e ∧
        ∃ ta, denoteMeta m.acval env φ d t = some ta ∧
          ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d e ρ →
            (g = .io → WellDenotedV V ρ ea) →
            WellDenotedV V ρ ea ∧ WellDenotedTy V ρ ta ∧
              interp V ρ ea ∈ˢ interp V ρ ta) :
    InferSem m φ g d e t := by
  cases g with
  | full =>
    intro hfe Δa ea hC hea
    obtain ⟨hft, hsub, ta, hta, hrow⟩ := h hfe hC hea
    exact ⟨hft, hsub, ta, hta, fun ρ hρ hL =>
      hrow ρ hρ hL (fun hg => by simp at hg)⟩
  | io =>
    intro hfe Δa ea hC hea
    obtain ⟨hft, hsub, ta, hta, hrow⟩ := h hfe hC hea
    exact ⟨hft, hsub, ta, hta, fun ρ hρ hL hge =>
      (hrow ρ hρ hL (fun _ => hge)).2⟩

/-- **The sort fact at a grade** (`sortSemAt_of_claims` at the
motives): a subject whose inferred type
reduces to `.sort u` reads into the universe — and is graded, which at
the io grade is the premise and at the full grade the first motive's
conclusion — at every valuation where the context is satisfied and the
subject's leaves are graded.  The totality factor the run version routes
(`InferReads`) is the existence form of `InferSem`. -/
theorem sortSem_of {g : Grade} {d : Nat} {e s : Expr} {u : Level}
    (hs : InferSem m φ g d e s) (hu : RedSem m φ d s (.sort u))
    (hfe : Frame d e) {Δa : List AnnotTerm} {ea : AnnotTerm}
    (hC : CtxOkS m φ d Δa e)
    (hea : denoteMeta m.acval env φ d e = some ea) :
    ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d e ρ →
      (g = .io → WellDenotedV V ρ ea) →
      WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ (univ (u.eval φ) : V) := by
  obtain ⟨hfs, hsub, sa, hsa, hrow⟩ := hs.apply hfe hC hea
  obtain ⟨-, -, ua, hua, hred⟩ := hu hfs (hC.of_subset hsub) hsa
  rw [denoteMeta] at hua
  obtain rfl : ua = .sort (u.eval φ) := (Option.some.inj hua).symm
  intro ρ hρ hL hgr
  obtain ⟨hge, hgs, hm⟩ := hrow ρ hρ hL hgr
  -- "not pt" source (1): the inferred type `sa` is a type
  have heq := (hred ρ hρ (hL.of_subset hsub) hgs.1 hgs.ne_pt).2
  refine ⟨hge, ?_⟩
  rw [heq, interp_sort] at hm
  exact hm

/-- A sort has the successor sort. -/
theorem Infer.sort_sound {g : Grade} {d : Nat} {u : Level} :
    InferSem m φ g d (.sort u) (.sort (.succ u)) := by
  refine InferSemFull.toSem ?_
  intro hf Δa ea hC hea
  rw [denoteMeta] at hea
  obtain rfl : ea = .sort (u.eval φ) := (Option.some.inj hea).symm
  have hty : denoteMeta m.acval env φ d (.sort (.succ u))
      = some (.sort (Level.eval φ (.succ u))) := by rw [denoteMeta]
  refine ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
      fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
    fun l hl => by simp [Expr.fvarLeaves] at hl,
    _, hty, fun ρ _ _ => ⟨⟨by simp, by simp⟩, ⟨⟨by simp, by simp⟩, IsTy_univ _⟩,
      (sound_sort V ρ (u.eval φ)).2⟩⟩

/-- A free variable: `CtxOkS`'s leaf package, the type's grading from
`LeavesGr` at the valuation. -/
theorem Infer.fvar_sound {g : Grade} {d idx : Nat} {ty : Expr} (h : idx < d) :
    InferSem m φ g d (.fvar idx ty) ty := by
  refine InferSemFull.toSem ?_
  intro hf Δa ea hC hea
  obtain ⟨hws, hb, hLb⟩ := hf
  have hleaf : (idx, ty) ∈ (Expr.fvar idx ty).fvarLeaves := by
    simp [Expr.fvarLeaves]
  obtain ⟨-, -, tya, Aa, hden, hi, hlink⟩ :
      idx < d ∧ Expr.fvarsBelow idx ty ∧
        ∃ tya Aa,
          denoteMeta m.acval env φ d ty = some tya ∧
          Δa[d - 1 - idx]? = some Aa ∧
          (∀ ρ : Nat → V, Sat V Δa ρ →
            interp V ρ tya
              = interp V (fun j => ρ (j + (d - 1 - idx) + 1)) Aa) :=
    hC.2 _ hleaf
  rw [denoteMeta] at hea
  obtain rfl : ea = .bvar (d - 1 - idx) := (Option.some.inj hea).symm
  simp only [Expr.WScoped] at hws
  have hmem : ∀ l ∈ ty.fvarLeaves, l ∈ (Expr.fvar idx ty).fvarLeaves := by
    intro l hl
    rw [Expr.fvarLeaves]
    exact List.mem_cons_of_mem _ hl
  refine ⟨⟨hws.2.mono (by omega), hLb (idx, ty) (by simp [Expr.fvarLeaves]),
      fun l hl => hLb l (hmem l hl)⟩,
    hmem, tya, hden, fun ρ hρ hL => ⟨⟨by simp, by simp⟩, hL _ hleaf tya hden, ?_⟩⟩
  rw [interp_bvar, hlink ρ hρ]
  exact hρ (d - 1 - idx) Aa hi

/-- A constant: `ConstType` + `AcvalValid`. -/
theorem Infer.const_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {n : Name} {us : List Level} {ci : ConLeche.ConstantInfo}
    (hf : env.find? n = some ci) (htower : ci.isTowerEntry = false)
    (hus : us.length = ci.toConstantVal.levelParams.length) :
    InferSem m φ g d (.const n us)
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) := by
  refine InferSemFull.toSem ?_
  intro _ Δa ea hC hea
  rw [denoteMeta, hf] at hea
  dsimp only at hea
  rw [ite_eq_left hus] at hea
  obtain rfl : ea = m.acval n
      (Level.substFn φ ci.toConstantVal.levelParams us) :=
    (Option.some.inj hea).symm
  obtain ⟨ta, hta, hok, hmem⟩ := hin.const_ty d n ci us hf htower hus
  obtain ⟨htc, -, -, htb, -⟩ := m.wf _ (Env.find?_mem hf)
  have hnf : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact htc
  exact ⟨⟨Expr.WScoped.of_not_hasFvar hnf,
      by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact htb,
      Expr.LeavesBounded.of_not_hasFvar hnf⟩,
    (fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl; cases hl),
    ta, hta, fun ρ _ _ => ⟨⟨m.acval_wellDenoted n _ ρ, hin.leaf_valid n _ ρ⟩,
      hok ρ, hmem ρ⟩⟩

/-- A `Nat` literal: `NatHeads` + `AcvalValid`. -/
theorem Infer.natLit_sound (hin : RulesInputs V m φ) {g : Grade} {d n : Nat}
    (h : ConLeche.natLitSupported env = true) :
    InferSem m φ g d (.lit (.natVal n)) (.const natName []) := by
  refine InferSemFull.toSem ?_
  intro _ Δa ea _ hea
  rw [denoteMeta, ite_eq_left h] at hea
  obtain rfl : ea = natLitAV
      (m.acval natZeroName (Level.substFn φ [] []))
      (m.acval natSuccName (Level.substFn φ [] [])) n :=
    (Option.some.inj hea).symm
  cases hf : env.find? natName with
  | none =>
    simp only [ConLeche.natLitSupported, Bool.and_eq_true] at h
    obtain ⟨⟨h1, -⟩, -⟩ := h
    rw [hf] at h1
    exact nomatch h1
  | some ci =>
    have hlp : ci.toConstantVal.levelParams = [] :=
      natName_levelParams_nil h hf
    have hta : denoteMeta m.acval env φ d (.const natName [])
        = some (m.acval natName (Level.substFn φ [] [])) := by
      rw [denoteMeta, hf]
      dsimp only
      rw [ite_eq_left (by simp [hlp]), hlp]
    have hrow : ∀ ρ : Nat → V,
        WellDenoted V ρ (natLitAV
            (m.acval natZeroName (Level.substFn φ [] []))
            (m.acval natSuccName (Level.substFn φ [] [])) n) ∧
          interp V ρ (natLitAV
              (m.acval natZeroName (Level.substFn φ [] []))
              (m.acval natSuccName (Level.substFn φ [] [])) n)
            ∈ˢ interp V ρ (m.acval natName (Level.substFn φ [] [])) :=
      fun ρ => natLit_factsAV (m.acval_wellDenoted _ _ ρ)
        (m.acval_wellDenoted _ _ ρ) (hin.nat_heads h ρ).1
        (hin.nat_heads h ρ).2.1 (hin.nat_heads h ρ).2.2 n
    exact ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
        fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
      (fun l hl => by simp [Expr.fvarLeaves] at hl),
      _, hta,
      fun ρ _ _ => ⟨⟨(hrow ρ).1, AnnotValid_natLitAV (hin.leaf_valid _ _ ρ)
          (hin.leaf_valid _ _ ρ) n⟩,
        ⟨⟨m.acval_wellDenoted _ _ ρ, hin.leaf_valid _ _ ρ⟩,
          (hin.nat_heads h ρ).2.2⟩,
        (hrow ρ).2⟩⟩

/-- A string literal: `strLitFacts`. -/
theorem Infer.strLit_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {s : String} (h : ConLeche.strLitSupported env = true) :
    InferSem m φ g d (.lit (.strVal s)) (.const stringName []) := by
  refine InferSemFull.toSem ?_
  intro _ Δa ea _ hea
  obtain ⟨-, ciS, -, -, -, -, -, -, -, -, -, hfS, -,
    -, -, -, -, -, hlpS, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    ConLeche.strLitSupported_inv h
  have hta : denoteMeta m.acval env φ d (.const stringName [])
      = some (m.acval ConLeche.stringName (Level.substFn φ [] [])) := by
    have hc := denoteMeta_const (acval := m.acval) (φ := φ) (d := d)
      (us := []) hfS (by simp [hlpS])
    rwa [hlpS] at hc
  exact ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
      fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
    (fun l hl => by simp [Expr.fvarLeaves] at hl),
    _, hta,
    fun ρ _ _ => ⟨(strLitFacts hin.const_ty hin.leaf_valid hin.nat_heads h hea ρ).1,
      ⟨⟨m.acval_wellDenoted _ _ ρ, hin.leaf_valid _ _ ρ⟩,
        (strLitFacts hin.const_ty hin.leaf_valid hin.nat_heads h hea ρ).2.2⟩,
      (strLitFacts hin.const_ty hin.leaf_valid hin.nat_heads h hea ρ).2.1⟩⟩

/-- A product: the two sort facts (`sortSemAt_of_claims`'s content) and the bit law. -/
theorem Infer.forallE_sound {g : Grade} {d : Nat}
    {ty body s bs : Expr} {u v : Level} {mb : BinderMeta}
    (hs : InferSem m φ g d ty s) (hu : RedSem m φ d s (.sort u))
    (hbs : InferSem m φ g (d + 1) (body.instantiate1 (.fvar d ty)) bs)
    (hv : RedSem m φ (d + 1) bs (.sort v))
    (hz : Level.zeronessOf v = mb.pw) :
    InferSem m φ g d (.forallE ty body mb) (.sort (.imax u v)) := by
  refine InferSem.of_uniform ?_
  intro Δa ea hfr hC hea
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbody
  obtain ⟨tyA, baA, htyA, hbaA, rfl⟩ := denoteMeta_forallE_inv hea
  have hdomU := sortSem_of hs hu ⟨hws.1, hb.1, hLty⟩ hC.forallE_ty htyA
  have hCop : CtxOkS m φ (d + 1) (tyA :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
    CtxOkS.openS hC.forallE_ty hC.forallE_body htyA
  have hcodU := sortSem_of hbs hv ⟨hwopen, hbopen, hLopen⟩ hCop hbaA
  refine ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
      fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
    (fun l hl => by simp [Expr.fvarLeaves] at hl),
    _, by rw [denoteMeta], ?_⟩
  intro ρ hρ hL hgr
  -- the domain: its own sort run; at the io grade off the subject
  have hdom := hdomU ρ hρ hL.forallE_ty (fun hg => (hgr hg).pi_dom.1)
  have hdomTy : WellDenotedTy V ρ tyA := ⟨hdom.1, IsTy_of_mem_univ hdom.2⟩
  -- the codomain, at every point of the domain
  have hcod : ∀ x, x ∈ˢ interp V ρ tyA →
      WellDenotedV V (cons x ρ) baA ∧
        interp V (cons x ρ) baA ∈ˢ (univ (v.eval φ) : V) :=
    fun x hx => hcodU (cons x ρ) (Sat_cons V hρ hx)
      (LeavesGr.open hC.forallE_ty hC.forallE_body hL.forallE_ty
        hL.forallE_body htyA hdomTy)
      (fun hg => (hgr hg).pi_body x hx)
  have hgea : WellDenotedV V ρ (.pi tyA baA) := by
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_pi]
      exact ⟨hdom.1.1, IsTy_of_mem_univ hdom.2, fun x hx => (hcod x hx).1.1,
        fun x hx => IsTy_of_mem_univ (hcod x hx).2⟩
    · rw [AnnotValid_pi]
      refine ⟨hdom.1.2, fun x hx => (hcod x hx).1.2, ?_⟩
      intro hbit x hx
      exact pwBit_zero_mem_univZero hz hbit (hcod x hx).2
  refine ⟨hgea, ⟨⟨by simp, by simp⟩, by exact IsTy_univ _⟩, ?_⟩
  have hrow := sound_pi V (u := u.eval φ) (v := v.eval φ)
    hdom.1.1 (fun x hx => (hcod x hx).1.1) hdom.2
    (fun x hx => (hcod x hx).2)
  have hzag : pwBit φ mb.pw = 0 ↔ v.eval φ = 0 := by
    rw [← hz]; exact pwBit_zeronessOf φ v
  have hbridge :
      interp V ρ (.pi tyA baA)
        = interp V ρ (.pi tyA baA) := by
    rw [interp_pi, interp_pi]
    exact piR_zero_agree hzag fun x _ => rfl
  rw [hbridge]
  exact hrow.2

/-- A λ: the fibre regime fact from the leaf sort run or, at a chain node, from
the copied annotation (`piR_zero_mem_univZero`). -/
theorem Infer.lam_sound {g : Grade} {d : Nat}
    {ty body s bt btt : Expr} {u v : Level} {mb : BinderMeta}
    (hs : g = .full → InferSemFull m φ d ty s)
    (hu : g = .full → RedSem m φ d s (.sort u))
    (hbt : InferSem m φ g (d + 1) (body.instantiate1 (.fvar d ty)) bt)
    (hshape : ∀ tyI bI mbI, body = .lam tyI bI mbI →
      ∃ btI, bt = .forallE (tyI.instantiate1 (.fvar d ty)) btI mbI)
    (hchain : ∀ pwI, body.lamPw = some pwI → mb.pw = pwI)
    (hbtt : body.lamPw = none → InferSemIO m φ (d + 1) bt btt)
    (hv : body.lamPw = none → RedSem m φ (d + 1) btt (.sort v))
    (hz : body.lamPw = none → Level.zeronessOf v = mb.pw) :
    InferSem m φ g d (.lam ty body mb) (.forallE ty (bt.abstract1 d) mb) := by
  refine InferSem.of_uniform ?_
  intro Δa ea hfr hC hea
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading
  rw [denoteMeta] at hea
  rcases htyA : denoteMeta m.acval env φ d ty with _ | tyA
  · rw [htyA] at hea; exact nomatch hea
  rw [htyA] at hea
  rcases hba : denoteMeta m.acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  obtain rfl : ea = .lam tyA ba :=
    (Option.some.inj hea).symm
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbody
  have hCop : CtxOkS m φ (d + 1) (tyA :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
    CtxOkS.openS hC.lam_ty hC.lam_body htyA
  -- the opened body's inferred type
  obtain ⟨hbtf, hbtsub, btA, hbtA, hrowB⟩ :=
    hbt.apply ⟨hwopen, hbopen, hLopen⟩ hCop hba
  obtain ⟨hwbt, hbtb, hLbt⟩ := hbtf
  -- the abstraction round trip, for the ∀-type's reading
  have hleaf : Expr.LeafCond d ty (body.instantiate1 (.fvar d ty)) := by
    intro l hl hd
    rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact absurd hd (by
        have := Expr.fvarLeaves_lt_of_wscoped hws.2 l h2
        omega)
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact rfl
      · exact absurd hd (by
          have := Expr.fvarLeaves_lt_of_wscoped hws.1 l h3
          omega)
  have hcons : Expr.fvarConsistent d ty bt :=
    Expr.fvarConsistent_of_leafCond bt (fun l hl => hleaf l (hbtsub l hl))
  have hround : (bt.abstract1 d).instantiate1 (.fvar d ty) = bt :=
    ConLeche.abstract1_instantiate1 bt 0 hcons hbtb
  have hta : denoteMeta m.acval env φ d (.forallE ty (bt.abstract1 d) mb)
      = some (.pi tyA btA) := by
    rw [denoteMeta, htyA, hround, hbtA]
    rfl
  have hCbt : CtxOkS m φ (d + 1) (tyA :: Δa) bt := hCop.of_subset hbtsub
  -- the fibre regime fact, one `have`, both uses (the meta copy): at a
  -- valuation where the body type's leaves and the body type are graded
  have hzfib : pwBit φ mb.pw = 0 →
      ∀ (ρ' : Nat → V), Sat V (tyA :: Δa) ρ' → LeavesGr m φ (d + 1) bt ρ' →
        WellDenotedV V ρ' btA → interp V ρ' btA ∈ˢ (univZero : V) := by
    intro hb0 ρ' hρ' hL' hg'
    cases hpw : body.lamPw with
    | some pwI =>
      -- chain: no run — impredicativity at the copied meta
      obtain ⟨tyI, bI, mbI, rfl⟩ : ∃ tyI bI mbI, body = .lam tyI bI mbI := by
        cases body <;> simp [Expr.lamPw] at hpw
        exact ⟨_, _, _, rfl⟩
      have hpwEq : mb.pw = mbI.pw := by
        have := hchain pwI hpw
        simp only [Expr.lamPw, Option.some.injEq] at hpw
        rw [this, hpw]
      obtain ⟨btI, rfl⟩ := hshape tyI bI mbI rfl
      obtain ⟨tyIA, btIA, -, -, rfl⟩ := denoteMeta_forallE_inv hbtA
      rw [interp_pi]
      have hinner : pwBit φ mbI.pw = 0 := by rw [← hpwEq]; exact hb0
      rw [hinner]
      exact piR_zero_mem_univZero
    | none =>
      -- leaf: the io sort walk on the body type + the bit law
      exact pwBit_zero_mem_univZero (hz hpw) hb0
        (sortSem_of (g := .io)
          (show InferSem m φ .io (d + 1) bt btt from hbtt hpw) (hv hpw)
          ⟨hwbt, hbtb, hLbt⟩ hCbt hbtA ρ' hρ' hL' (fun _ => hg')).2
  -- the conclusion's frame and leaves
  have hsubT : ∀ l ∈ (Expr.forallE ty (bt.abstract1 d) mb).fvarLeaves,
      l ∈ (Expr.lam ty body mb).fvarLeaves := by
    intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with h2 | h2
    · exact Or.inl h2
    · obtain ⟨hlbt, hlne⟩ := ConLeche.Expr.fvarLeaves_abstract1_ne bt 0 hwbt l h2
      rcases Expr.fvarLeaves_instantiate1 body 0 (hbtsub l hlbt) with h3 | h3
      · exact Or.inr h3
      · rw [Expr.fvarLeaves] at h3
        rcases List.mem_cons.mp h3 with rfl | h4
        · exact absurd rfl hlne
        · exact Or.inl h4
  have hwT : Expr.WScoped d (.forallE ty (bt.abstract1 d) mb) := by
    simp only [Expr.WScoped]
    exact ⟨hws.1, ConLeche.WScoped.abstract1 0 hwbt⟩
  have hbT : (Expr.forallE ty (bt.abstract1 d) mb).looseBVarsBounded 0
      = true := by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hb.1, ConLeche.looseBVarsBounded_abstract1 bt 0 hbtb⟩
  refine ⟨⟨hwT, hbT, fun l hl => hLb l (hsubT l hl)⟩,
    hsubT, _, hta, ?_⟩
  intro ρ hρ hL hgr
  -- the domain's grading: established at the full grade by its own
  -- sort run, consumed at the io grade off the subject (`lam_dom`)
  have hokty : WellDenotedTy V ρ tyA := by
    cases g with
    | full =>
      have h := sortSem_of (g := .full) (hs rfl) (hu rfl) ⟨hws.1, hb.1, hLty⟩
        hC.lam_ty htyA ρ hρ hL.lam_ty (fun hg => by simp at hg)
      exact ⟨h.1, IsTy_of_mem_univ h.2⟩
    | io => exact (hgr rfl).lam_dom
  -- the opened body at every point of the domain
  have hLop : ∀ x, LeavesGr m φ (d + 1) (body.instantiate1 (.fvar d ty))
      (cons x ρ) := fun _ =>
    LeavesGr.open hC.lam_ty hC.lam_body hL.lam_ty hL.lam_body htyA hokty
  have hrow : ∀ x, x ∈ˢ interp V ρ tyA →
      WellDenotedV V (cons x ρ) ba ∧ WellDenotedTy V (cons x ρ) btA ∧
        interp V (cons x ρ) ba ∈ˢ interp V (cons x ρ) btA := fun x hx =>
    hrowB (cons x ρ) (Sat_cons V hρ hx) (hLop x)
      (fun hg => (hgr hg).lam_body x hx)
  have hfib : pwBit φ mb.pw = 0 → ∀ x, x ∈ˢ interp V ρ tyA →
      interp V (cons x ρ) btA ∈ˢ (univZero : V) := fun h0 x hx =>
    hzfib h0 (cons x ρ) (Sat_cons V hρ hx) ((hLop x).of_subset hbtsub)
      (hrow x hx).2.1.1
  refine ⟨?_, ?_, ?_⟩
  · -- the λ's own grading
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_lam]
      exact ⟨hokty.1.1, hokty.2, fun x hx => (hrow x hx).1.1,
        fun x => interp V (cons x ρ) btA,
        fun x hx => (hrow x hx).2.2,
        fun x hx => (hrow x hx).2.1.2,
        hfib⟩
    · rw [AnnotValid_lam]
      exact ⟨hokty.1.2, fun x hx => (hrow x hx).1.2⟩
  · -- the copied ∀-type's grading
    refine ⟨⟨?_, ?_⟩, IsTy_piR _ _ _⟩
    · rw [WellDenoted_pi]
      exact ⟨hokty.1.1, hokty.2, fun x hx => (hrow x hx).2.1.1.1,
        fun x hx => (hrow x hx).2.1.2⟩
    · rw [AnnotValid_pi]
      exact ⟨hokty.1.2, fun x hx => (hrow x hx).2.1.1.2, hfib⟩
  · -- the membership row
    exact (sound_lam V hokty.1.1 hokty.2
      (fun x hx => (hrow x hx).1.1)
      (fun x hx => (hrow x hx).2.2)
      (fun x hx => (hrow x hx).2.1.2) hfib).2

/-- An application, the kept arm. -/
theorem Infer.app_sound {g : Grade} {d : Nat}
    {f a tf ty body ta : Expr} {mt : BinderMeta}
    (htf : InferSem m φ g d f tf) (hw : RedSem m φ d tf (.forallE ty body mt))
    (hta : InferSem m φ g d a ta) (hd : DefEqSem m φ d ta ty) :
    InferSem m φ g d (.app f a) (body.instantiate1 a) := by
  refine InferSem.of_uniform ?_
  intro Δa ea hfr hC hea
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading splits
  rw [denoteMeta] at hea
  rcases hfa : denoteMeta m.acval env φ d f with _ | fa
  · rw [hfa] at hea; exact nomatch hea
  rw [hfa] at hea
  rcases haa : denoteMeta m.acval env φ d a with _ | aa
  · rw [haa] at hea; exact nomatch hea
  rw [haa] at hea
  obtain rfl : ea = .app fa aa := (Option.some.inj hea).symm
  -- the head, its type, and the ∀ it reduces to (readings)
  obtain ⟨htff, htfsub, tfa, htfa, hrowF⟩ :=
    htf.apply ⟨hws.1, hb.1, hLf⟩ hC.app_fn hfa
  obtain ⟨hpif, hpisub, pa, hpa, hredf⟩ :=
    hw htff (hC.app_fn.of_subset htfsub) htfa
  obtain ⟨hwfe, hbfe, hLfe⟩ := hpif
  simp only [Expr.WScoped] at hwfe
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbfe
  have hLty' : Expr.LeavesBounded ty := fun l hl =>
    hLfe l (by simp [Expr.fvarLeaves, hl])
  have hCpi : CtxOkS m φ d Δa (.forallE ty body mt) :=
    (hC.app_fn.of_subset htfsub).of_subset hpisub
  obtain ⟨Aa, Ba, hAa, hBa, rfl⟩ := denoteMeta_forallE_inv hpa
  -- the argument's type (reading)
  obtain ⟨htaf, htasub, tyaA, htyaA, hrowA⟩ :=
    hta.apply ⟨hws.2, hb.2, hLa⟩ hC.app_arg haa
  -- the returned type's reading, `denoteMeta_beta` backwards
  have hcross : denoteMeta m.acval env φ d (body.instantiate1 a)
      = some (Ba.inst aa) := by
    rw [denoteMeta_beta (ty := ty) m.acval_closed
      (acval_inst_self m) hwfe.2.fvarsBelow hws.2 hb.2 haa 0, hBa]
    rfl
  refine ⟨⟨Expr.WScoped.instantiate1_gen hws.2 0 hwfe.2,
      Expr.looseBVarsBounded_instantiate1_gen hb.2 hbfe.2,
      fun l hl => ?_⟩, fun l hl => ?_, _, hcross, ?_⟩
  · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact hLfe l (by simp [Expr.fvarLeaves, h2])
    · exact hLa l h2
  · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · rw [Expr.fvarLeaves]
      exact List.mem_append_left _ (htfsub l (hpisub l
        (by simp [Expr.fvarLeaves, h2])))
    · rw [Expr.fvarLeaves]
      exact List.mem_append_right _ h2
  intro ρ hρ hL hgr
  -- the head at `ρ`, and its type's reduct
  obtain ⟨hgfa, hgtfa, hrowfM⟩ :=
    hrowF ρ hρ hL.app_fn (fun hg => (hgr hg).app_fn)
  have hLtf : LeavesGr m φ d tf ρ := hL.app_fn.of_subset htfsub
  -- "not pt" source (1): the head's inferred type `tfa` is a type
  obtain ⟨hokpa, hredfρ⟩ := hredf ρ hρ hLtf hgtfa.1 hgtfa.ne_pt
  -- the ∀'s reading, split
  have hAty : WellDenotedTy V ρ Aa := hokpa.pi_dom
  have hokBa : ∀ x, x ∈ˢ interp V ρ Aa → WellDenotedV V (cons x ρ) Ba :=
    hokpa.pi_body
  have hcod0 : pwBit φ mt.pw = 0 →
      ∀ x, x ∈ˢ interp V ρ Aa →
        interp V (cons x ρ) Ba ∈ˢ (univZero : V) := by
    intro h0 x hx
    have h2 := hokpa.2
    rw [AnnotValid_pi] at h2
    exact h2.2.2 h0 x hx
  have hBty : ∀ x, x ∈ˢ interp V ρ Aa → IsTy (interp V (cons x ρ) Ba) :=
    ((WellDenoted_pi V ρ _ _ Aa Ba) ▸ hokpa.1).2.2.2
  -- the argument at `ρ`, and the domain agreement
  obtain ⟨hgaa, hgtyaA, hrowaM⟩ :=
    hrowA ρ hρ hL.app_arg (fun hg => (hgr hg).app_arg)
  -- "not pt" source (1): the argument's inferred type `tyaA` is a type
  -- "not pt" source (1): the ∀'s domain `Aa` is a type
  have hdom : interp V ρ tyaA = interp V ρ Aa :=
    hd htaf ⟨hwfe.1, hbfe.1, hLty'⟩ (hC.app_arg.of_subset htasub)
      hCpi.forallE_ty htyaA hAa ρ hρ (hL.app_arg.of_subset htasub)
      (hLtf.of_subset hpisub).forallE_ty hgtyaA.1 hAty.1
      hgtyaA.ne_pt hAty.ne_pt
  have ha2 : interp V ρ aa ∈ˢ interp V ρ Aa := by
    rw [← hdom]
    exact hrowaM
  have hf2 : interp V ρ fa ∈ˢ interp V ρ (.pi Aa Ba) := by
    rw [← hredfρ]
    exact hrowfM
  refine ⟨⟨(sound_app V hgfa.1 hgaa.1 hf2 ha2 hcod0 (fun _ => hAty.2)).1, ?_⟩,
    (WellDenotedTy_inst0 hgaa).mpr ⟨hokBa _ ha2, hBty _ ha2⟩,
    (sound_app V hgfa.1 hgaa.1 hf2 ha2 hcod0 (fun _ => hAty.2)).2⟩
  rw [AnnotValid_app]
  exact ⟨hgfa.2, hgaa.2⟩

/-- **`let`, by substitution**: the body's claim at its value is the
`let`'s (`interp_zeta`).  The value's grading — part of the `let`'s —
is the subject's at the io grade and the value's own full-grade
inference at the full grade (the establishment motive concludes it).
The type's sort and the value/type comparison are not consumed: no
claim reads a `let`'s type, and the body is typed at the value itself. -/
theorem Infer.letE_sound {g : Grade} {d : Nat} {ty v body tv t : Expr}
    (htv : g = .full → InferSemFull m φ d v tv)
    (hb : InferSem m φ g d (body.instantiate1 v) t) :
    InferSem m φ g d (.letE ty v body) t := by
  refine InferSem.of_uniform ?_
  intro Δa ea hfr hC hea
  obtain ⟨-, va, ba, -, hva, hba, rfl⟩ := denoteMeta_letE_inv hea
  obtain ⟨hfr', hsub, hred⟩ := zeta_syntax hfr hva hba
  obtain ⟨hfv, hsubv⟩ := letE_val_frame hfr
  obtain ⟨hft, htsub, ta, hta, hrow⟩ :=
    hb.apply hfr' (hC.of_subset hsub) hred
  refine ⟨hft, fun l hl => hsub l (htsub l hl), ta, hta, ?_⟩
  intro ρ hρ hL hgr
  have hgv : WellDenotedV V ρ va := by
    cases g with
    | io => exact (hgr rfl).letE_val
    | full =>
      obtain ⟨-, -, _, -, hrowv⟩ := htv rfl hfv (hC.of_subset hsubv) hva
      exact (hrowv ρ hρ (hL.of_subset hsubv)).1
  obtain ⟨hge, hgt, hmem⟩ := hrow ρ hρ (hL.of_subset hsub)
    (fun hg => (WellDenotedV_zeta hgv).mp (hgr hg))
  refine ⟨(WellDenotedV_zeta hgv).mpr hge, hgt, ?_⟩
  rw [interp_zeta]
  exact hmem

/-- **The io licence** (the application's gated arm): the skipped
membership from the subject's own hereditary app slot,
`io_domain_transfer` + `piR_dom_unique` at a bit pinned positive by
`pwBit_ne_zero_of_isNever`. -/
theorem Infer.appSkip_sound {d : Nat}
    {f a tf ty body : Expr} {mt : BinderMeta}
    (htf : InferSemIO m φ d f tf) (hw : RedSem m φ d tf (.forallE ty body mt))
    (hnev : mt.pw.isNever = true) :
    InferSemIO m φ d (.app f a) (body.instantiate1 a) := by
  intro hfr Δa ea hC hea
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading splits
  rw [denoteMeta] at hea
  rcases hfa : denoteMeta m.acval env φ d f with _ | fa
  · rw [hfa] at hea; exact nomatch hea
  rw [hfa] at hea
  rcases haa : denoteMeta m.acval env φ d a with _ | aa
  · rw [haa] at hea; exact nomatch hea
  rw [haa] at hea
  obtain rfl : ea = .app fa aa := (Option.some.inj hea).symm
  obtain ⟨htff, htfsub, tfa, htfa, hrowF⟩ :=
    htf ⟨hws.1, hb.1, hLf⟩ hC.app_fn hfa
  obtain ⟨hpif, hpisub, pa, hpa, hredf⟩ :=
    hw htff (hC.app_fn.of_subset htfsub) htfa
  obtain ⟨hwfe, hbfe, hLfe⟩ := hpif
  simp only [Expr.WScoped] at hwfe
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbfe
  obtain ⟨Aa, Ba, hAa, hBa, rfl⟩ := denoteMeta_forallE_inv hpa
  have hcross : denoteMeta m.acval env φ d (body.instantiate1 a)
      = some (Ba.inst aa) := by
    rw [denoteMeta_beta (ty := ty) m.acval_closed
      (acval_inst_self m) hwfe.2.fvarsBelow hws.2 hb.2 haa 0, hBa]
    rfl
  refine ⟨⟨Expr.WScoped.instantiate1_gen hws.2 0 hwfe.2,
      Expr.looseBVarsBounded_instantiate1_gen hb.2 hbfe.2,
      fun l hl => ?_⟩, fun l hl => ?_, _, hcross, ?_⟩
  · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact hLfe l (by simp [Expr.fvarLeaves, h2])
    · exact hLa l h2
  · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · rw [Expr.fvarLeaves]
      exact List.mem_append_left _ (htfsub l (hpisub l
        (by simp [Expr.fvarLeaves, h2])))
    · rw [Expr.fvarLeaves]
      exact List.mem_append_right _ h2
  intro ρ hρ hL hge
  -- **the premise, spent**: the parts' grading and the hereditary slot
  have hokf : WellDenotedV V ρ fa := hge.app_fn
  have hoka : WellDenotedV V ρ aa := hge.app_arg
  have hslot := ((WellDenoted_app V ρ fa aa) ▸ hge.1).2.2
  obtain ⟨hgtfa, hrowfM⟩ := hrowF ρ hρ hL.app_fn hokf
  -- "not pt" source (1): the head's inferred type `tfa` is a type
  obtain ⟨hokpa, hredfρ⟩ :=
    hredf ρ hρ (hL.app_fn.of_subset htfsub) hgtfa.1 hgtfa.ne_pt
  have hAty : IsTy (interp V ρ Aa) := hokpa.pi_dom.2
  have hokBa : ∀ x, x ∈ˢ interp V ρ Aa → WellDenotedV V (cons x ρ) Ba :=
    hokpa.pi_body
  have hcod0 : pwBit φ mt.pw = 0 →
      ∀ x, x ∈ˢ interp V ρ Aa →
        interp V (cons x ρ) Ba ∈ˢ (univZero : V) := by
    intro h0 x hx
    have h2 := hokpa.2
    rw [AnnotValid_pi] at h2
    exact h2.2.2 h0 x hx
  have hBty : ∀ x, x ∈ˢ interp V ρ Aa → IsTy (interp V (cons x ρ) Ba) :=
    ((WellDenoted_pi V ρ _ _ Aa Ba) ▸ hokpa.1).2.2.2
  have hf2 : interp V ρ fa ∈ˢ interp V ρ (.pi Aa Ba) := by
    rw [← hredfρ]
    exact hrowfM
  -- **THE LICENCE**: the skipped membership, from the subject's own
  -- hereditary app slot at a bit pinned positive by the datum
  have ha2 : interp V ρ aa ∈ˢ interp V ρ Aa := by
    have hw0 : pwBit φ mt.pw ≠ 0 := pwBit_ne_zero_of_isNever hnev φ
    obtain ⟨v, A, B, hfslot, haslot, -⟩ := hslot
    have hf' := hf2
    rw [interp_pi] at hf'
    exact io_domain_transfer hw0 hfslot haslot hf'
  exact ⟨(WellDenotedTy_inst0 hoka).mpr ⟨hokBa _ ha2, hBty _ ha2⟩,
    (sound_app V hokf.1 hoka.1 hf2 ha2 hcod0 (fun _ => hAty)).2⟩

/-- A projection: the tower law's typing clause. -/
theorem Infer.proj_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {sn : Name} {i : Nat} {pe tpe te : Expr} {us : List Level}
    {entry : ProjEntry}
    (htpe : InferSem m φ g d pe tpe) (hte : RedSem m φ d tpe te)
    (hhead : te.getAppFn = .const sn us)
    (hent : env.findProj? sn i = some entry)
    (hlen : te.getAppArgs.length = entry.numParams)
    (hus : us.length = entry.levelParams.length)
    (hprop : Level.isEquiv entry.structSort .zero = some true →
      Level.isEquiv (Level.subst entry.levelParams us entry.fieldSort) .zero
        = some true) :
    InferSem m φ g d (.proj sn i pe) (entry.typeAt us te.getAppArgs pe) := by
  refine InferSem.of_uniform ?_
  intro Δa ea hfr hC hea
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOkS m φ d Δa pe := hC.proj_arg
  obtain ⟨vp, hvp, rfl⟩ := denoteMeta_proj_inv_tower hent hea
  -- the scrutinee's inferred type, and its reduct (readings)
  obtain ⟨htpef, htpesub, tpea, htpea, hrowP⟩ :=
    htpe.apply ⟨hws, hb, hLpe⟩ hCpe hvp
  obtain ⟨htef, htesub, tea, htea, hredT⟩ :=
    hte htpef (hCpe.of_subset htpesub) htpea
  obtain ⟨hwte', hbte, hLte⟩ := htef
  -- the tower law's typing clause
  obtain ⟨-, -, -, ⟨cvT, capsT, hfT, hlpsT, -⟩, hO5, _, -, -, hlaw, -⟩ :=
    hin.tower_ok sn i entry hent
  obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlaw us hus
  -- the reduced type's spine, at the former's leaf
  rw [show te = Expr.mkAppN te.getAppFn te.getAppArgs from
    (Expr.mkAppN_getApp te).symm, hhead] at htea
  obtain ⟨vT, vs, hvT, hspt, hteq⟩ := denoteMeta_mkAppN_inv htea
  have hlenT : us.length
      = (ConstantInfo.indInfo cvT capsT).toConstantVal.levelParams.length := by
    show us.length = cvT.levelParams.length
    rw [hlpsT]; exact hus
  rw [denoteMeta_const hfT hlenT] at hvT
  have hvT' : vT = m.acval sn (Level.substFn φ entry.levelParams us) := by
    rw [← hlpsT]; exact (Option.some.inj hvT).symm
  subst hvT'
  subst hteq
  -- the residual: the entry type's peel, read
  have hframes : ∀ x ∈ te.getAppArgs ++ [pe],
      Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact ⟨hwte'.getAppArgs x hx',
        ConLeche.looseBVarsBounded_getAppArgs hbte x hx'⟩
    · rcases List.mem_singleton.mp hx' with rfl
      exact ⟨hws, hb⟩
  obtain ⟨restA, hrest, hpeel⟩ :=
    denoteMeta_typeAt_peel hent hTa hlen hframes (hspt.snoc hvp)
  have hlenVs : vs.length = entry.numParams := by
    rw [← hspt.length]; exact hlen
  -- the returned type's leaves: the spine's or the subject's
  have hleaves : ∀ l ∈ (entry.typeAt us te.getAppArgs pe).fvarLeaves,
      (∃ x ∈ te.getAppArgs, l ∈ x.fvarLeaves) ∨ l ∈ pe.fvarLeaves := by
    intro l hl
    rw [ProjEntry.typeAt_eq_instSpine entry us hlen pe] at hl
    rcases fvarLeaves_instSpine _ hl with hty | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar
        (ConLeche.projEntry_body_hasFvar m.wf hent us)] at hty
      exact nomatch hty
    · rcases List.mem_append.mp ha with ha | ha
      · exact Or.inl ⟨a, ha, hla⟩
      · rcases List.mem_singleton.mp ha with rfl
        exact Or.inr hla
  refine ⟨⟨ConLeche.projEntry_typeAt_WScoped m.wf hent us hlen
      (fun a ha => hwte'.getAppArgs a ha) hws,
    ConLeche.projEntry_typeAt_looseBVars m.wf hent us hlen
      (fun a ha => ConLeche.looseBVarsBounded_getAppArgs hbte a ha) hb,
    fun l hl => ?_⟩, fun l hl => ?_, restA, hrest, ?_⟩
  · rcases hleaves l hl with ⟨x, hx, hlx⟩ | hlx
    · exact hLte l (ConLeche.fvarLeaves_getAppArgs hx l hlx)
    · exact hLpe l hlx
  · rcases hleaves l hl with ⟨x, hx, hlx⟩ | hlx
    · rw [Expr.fvarLeaves]
      exact htpesub l (htesub l (ConLeche.fvarLeaves_getAppArgs hx l hlx))
    · rw [Expr.fvarLeaves]
      exact hlx
  intro σ hσ hL hgr
  have hLpe' : LeavesGr m φ d pe σ := hL.proj_arg
  -- the io grade's premise, hoisted through the projection spelling
  obtain ⟨hokPe, hokTpe, hmemPe⟩ :=
    hrowP σ hσ hLpe' (fun hg => ProjAV.hoistV (hgr hg))
  -- "not pt" source (1): the scrutinee's inferred type `tpea` is a type
  obtain ⟨hokTe, heqTe⟩ :=
    hredT σ hσ (hLpe'.of_subset htpesub) hokTpe.1 hokTpe.ne_pt
  -- the tower law's typing clause
  exact hA (towerGuardAt_of hO5 (fun hp => by
      simp only [beq_iff_eq] at hp ⊢
      exact hprop hp)) σ vs vp restA hlenVs hokTe hokPe
    (heqTe ▸ hmemPe) hpeel

end ConLeche.Model.Rules
