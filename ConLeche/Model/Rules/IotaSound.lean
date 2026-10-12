module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Semantics.DefEqList

public section

/-!
# The soundness of the ι rule and the three stuck-major rescues (task #305, #342 L10)

One lemma per constructor: `Red.iota`, `Red.rescueK`, `Red.rescueEta`,
`Red.rescueAnd`; the master induction (`Sound.lean`) consumes them by
name.  The shared helpers live in `IotaSoundKit.lean`.

**Conditional premises, unconditional conclusions** (task #342, L10).
`Red.iota_sound`, `Red.rescueK_sound` and `Red.rescueAnd_sound` take
their premises' CONDITIONAL claims (`RedSem`, `DefEqSem`,
`DefEqListSem`, `CertsSem`, `CertsFSem`) and conclude the UNCONDITIONAL
`RedSemU`: no step reads that the redex is not the point.  So one lemma
serves both inductions of `Sound.lean`: the conditional one weakens
the conclusion (`RedSemU.cond`), the interim side induction (which
stays while λ-congruence, η and structure η need it, task #342 L11)
weakens its premises.  The ι step's licence is read through the law's
`RecRuleExtra` (`Model/Annot/Laws.lean`): the recursor's spine fits by
its licensed certificate; a K rule fires by the law at the recursor's
own parameters; otherwise the fired constructor application's value is
the major's (by the major's reduction where the major is not the
point, which at case 2 it never is; by the slot law where it is,
case 3), its spine fits (case 3's full-grade certificate, or the graph
regime of a graded application that is not the point,
`teleFitPA_of_graded_ne_pt`), and the comparisons the step ran become
equations (`RecRuleExtra`'s (U)).  The two fabricating rescues (K,
`And`) equate their fabrication with the major through the one type
both inhabit (`IsTy.eq_of_ne_pt`).  `Red.rescueEta_soundU` stays
unconditional: its certificate (`DefEq.structEta`'s) is the
coherence-law lane's (task #342 L11's finding 2).

## Two rule shapes this file relies on

**`Rules.Red.rescueEta` carries the per-field certificates.**  At
`towerSlotsAll env T caps.etaFields = false` the fabricated arguments
are `Expr.mkAppN (.const (projFnName T j) ust) (tmaj.getAppArgs ++
[major])` nodes, so the fabrication READS only if `projFnName T j` is
stored at the family's level arity, and its GRADING needs the slot's
telescope certificate.  Neither follows from the rule's other
premises: the checker has them from inverting the η certificate's own
run (`structEtaCertWith_inv`), and in the rules tier that run is the
opaque `DefEq env d fab major` premise, whose motive `DefEqSemU`
exposes nothing of the kind.  The rule therefore carries the premise
`DefEq.structEta` carries,

    towerSlotsAll env T caps.etaFields = false →
      EtaProjCerts env d T ust tmaj.getAppArgs major cvT.levelParams
        (List.range caps.etaFields)

— premise-exact: it is the certificate `structEtaCertWith` runs at a
projection-function family, which is what the η rescue calls.  Its
motive `EtaProjCertsSem` (`Model/Rules/Motive.lean`) hands back, per
slot, the storage, `cvp.levelParams = lpsT`, the `stripPis` conjunct
and the `CertsSem` that grades the spine — exactly the four facts the
η arm consumes.  The bridge supplies it from the same inversion
(`Verify/Rules/Certs.lean`'s `structEtaCertWith_projCerts_bridge`,
shared with `structEtaCertWith_bridge`).

**`DefEqListSem` concludes the walk's length.**  `Red.iota_sound`'s
`.nested` fire needs `pins.length = RecRule.ctorParams rl` before it
can build the comparand list's read spine at all, and the length is
needed to build the spines the motive's equation is about.
`DefEqListSem` therefore leads with `as.length = bs.length`,
discharged in `CertsSound.lean`'s `DefEqList.nil_sound`/`cons_sound`.
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
set_option linter.unusedVariables false in
/-- **The ι row** (task #342 L10): the stored recursor's fired contract
(`RecRuleLaw`) and its licence facts (`RecRuleExtra`), at the
recursor's licensed telescope certificate over the redex's own spine,
the major prepared by a reduction, and — at case 3 only — the
constructor's full-grade certificate and the index comparison.  The
premises are the CONDITIONAL claims, the conclusion is the
unconditional one: no step reads that the redex is not the point, so
one lemma serves the conditional induction (`RedSemU.cond`) and the
interim side induction.

Per valuation: the recursor's telescope fits the spine (the licensed
certificate).  At a K rule the law at the recursor's own parameters
gives everything; the major is not read.  Otherwise the fired
constructor application's value is the major's — by the major's
reduction where the major is not the point (case 2 always: (S)), by
the slot law where it is (case 3: (P)) — its spine fits (the
full-grade certificate, or a graded application that is not the point
fitting its ∀-telescope), the comparisons the step ran become
equations ((U)), and the law fires. -/
theorem Red.iota_sound (hin : RulesInputs V m φ) {d : Nat} {e : Expr} {c : Name}
    {us : List Level} {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    {major : Expr} {cj : Name} {usj : List Level} {cvj : ConstantVal}
    {cnP cnF : Nat} {rl : RecRule} {residual : Expr}
    (hhead : e.getAppFn = .const c us)
    (hrec : env.find? c = some (.recInfo cv mI rP rules))
    (hlen : e.getAppArgs.length = mI + 1)
    (hus : us.length = cv.levelParams.length)
    (hmajor : RedSem m φ d (e.getAppArgs.getD mI (.bvar 0)) major)
    (hmhead : major.getAppFn = .const cj usj)
    (hctor : env.find? cj = some (.ctorInfo cvj cnP cnF))
    (hrule : rules.find? (fun r' => r'.ctor == cj) = some rl)
    (hmlen : major.getAppArgs.length = rl.ctorParams + rl.nfields)
    (hfire : rl.fire ≠ .inert)
    (hlv : Level.isEquivList usj
      (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
        e.getAppArgs rP).1 = some true)
    (hparams : ConLeche.iotaCompares env.find? rl cvj usj = true →
      DefEqListSem m φ d (major.getAppArgs.take rl.ctorParams)
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).2)
    (hcertR : CertsSem m φ d true (cv.type.instantiateLevelParams cv.levelParams us)
      e.getAppArgs)
    (hcertC : ConLeche.iotaCase3 env.find? rl cvj usj = true →
      CertsFSem m φ d (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs)
    (hres : ConLeche.iotaCase3 env.find? rl cvj usj = true → mI ≠ rP →
      ConLeche.piResidual (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs = some residual)
    (hidx : ConLeche.iotaCase3 env.find? rl cvj usj = true → mI ≠ rP →
      DefEqListSem m φ d (residual.getAppArgs.drop rl.ctorParams)
        ((e.getAppArgs.take mI).drop rP)) :
    RedSemU m φ d e
      (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
        (e.getAppArgs.take rP ++ major.getAppArgs.drop rl.ctorParams)) := by
  intro hf Δa ea hC hea
  have hrmem : rl ∈ rules := List.mem_of_find?_eq_some hrule
  have hrctor : rl.ctor = cj := by
    have := List.find?_some hrule
    simpa using this
  subst hrctor
  -- **the law and its licence facts**, and the fired right-hand side's
  -- reading at every depth
  obtain ⟨hrPle, hlaw0, hextra⟩ := hin.rec_rules c cv mI rP rules hrec rl hrmem hfire
  obtain ⟨Ra, hRa0, hokRa, hpinsOk, hlaw⟩ := hlaw0 us hus
  obtain ⟨hRaD, hRnf, hRbd⟩ := recRhs_depthK hrec hrmem hRa0
  -- the recursor spine, read
  have hfrE := frame_spine hf hC
  have hea' := hea
  rw [show e = Expr.mkAppN e.getAppFn e.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp e).symm, hhead] at hea'
  obtain ⟨vc, xs, hvc, hspx, rfl⟩ := denoteMeta_mkAppN_inv hea'
  rw [denoteMeta_const hrec (show us.length = _ from hus)] at hvc
  obtain rfl : vc = m.acval c (Level.substFn φ cv.levelParams us) :=
    (Option.some.inj hvc).symm
  have hxsLen : xs.length = mI + 1 := by rw [← hspx.length]; exact hlen
  -- the prepared major: read
  have hmIlt : mI < e.getAppArgs.length := by rw [hlen]; omega
  obtain ⟨hfMa, hCMa⟩ := hfrE _ (ConLeche.getD_mem hmIlt)
  have hdMaj : denoteMeta m.acval env φ d (e.getAppArgs.getD mI (.bvar 0))
      = some (xs.getD mI default) := hspx.getD _ mI hmIlt
  obtain ⟨hfmj, hsubmj, vmaj, hvmajSave, hInnerMaj⟩ := hmajor hfMa hCMa hdMaj
  have hCmj : CtxOkS m φ d Δa major := hCMa.of_subset hsubmj
  -- the constructor spine
  have hvmaj := hvmajSave
  rw [show major = Expr.mkAppN major.getAppFn major.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp major).symm, hmhead] at hvmaj
  obtain ⟨vj, ys, hvj, hspy, rfl⟩ := denoteMeta_mkAppN_inv hvmaj
  obtain ⟨hlenUj, rfl⟩ := denoteMeta_const_arityK hctor hvj
  have hfrC := frame_spine hfmj hCmj
  -- the two stored types
  obtain ⟨TVa, hTVaD, hokTVa, hmemR, hnfR, hbdR⟩ :=
    constTy_pkg hin.const_ty hrec rfl (show us.length = _ from hus)
  obtain ⟨TVja, hTVjaD, hokTVja, hmemJ, hnfJ, hbdJ⟩ :=
    constTy_pkg hin.const_ty hctor rfl hlenUj
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTVaD hmemR hnfR hbdR
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTVjaD hmemJ hnfJ hbdJ
  obtain ⟨hfR, hCR⟩ := frame_of_not_hasFvar (m := m) (Δa := Δa) hnfR hbdR hC.1
  obtain ⟨hfJ, hCJ⟩ := frame_of_not_hasFvar (m := m) (Δa := Δa) hnfJ hbdJ hC.1
  -- **the recursor's licensed fit**, over the redex's own spine
  obtain ⟨restR, hfitR⟩ :=
    hcertR (fa := m.acval c (Level.substFn φ cv.levelParams us))
      hfR hCR (hTVaD d) hfrE hspx
  -- the level congruence (currency-free: the comparand reads no arguments)
  have hψ : Level.substFn φ cvj.levelParams usj
      = Level.substFn φ cvj.levelParams
          (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
            [] rP).1 := by
    rw [recFireComparands_fst_nil] at hlv
    exact ConLeche.Level.substFn_congr (ConLeche.Level.isEquivList_sound hlv φ)
  -- the licence facts at the recursor's levels
  obtain ⟨hK, hext⟩ := hextra us hus TVa (hTVaD 0)
  obtain ⟨hstrip, hextNK⟩ := hext cvj cnP cnF hctor
  have hlenYs : ys.length = rl.ctorParams + rl.nfields := by
    rw [← hspy.length, hmlen]
  have hpcC : PiChain ys.length TVja := by
    rw [hlenYs]
    exact piChain_of_stripPis _
      (ConLeche.Expr.stripPis_instantiateLevelParams_isSome _ _ _ hstrip) (hTVjaD d)
  -- the case split the checker ran
  have hcase3_of : rl.k = false →
      ConLeche.iotaCtorLicensed env.find? cvj usj = false →
      ConLeche.iotaCase3 env.find? rl cvj usj = true := by
    intro hk hl
    simp [ConLeche.iotaCase3, hk, hl]
  have hlic_of : rl.k = false →
      ConLeche.iotaCase3 env.find? rl cvj usj = false →
      ConLeche.iotaCtorLicensed env.find? cvj usj = true := by
    intro hk h3
    cases hl : ConLeche.iotaCtorLicensed env.find? cvj usj
    · rw [hcase3_of hk hl] at h3; exact nomatch h3
    · rfl
  -- the reduct: framed, leaf-covered, read, and graded/equal at any ρ
  have hspOut : DenoteMetaSpine m.acval env φ d
      (e.getAppArgs.take rP ++ major.getAppArgs.drop (RecRule.ctorParams rl))
      (xs.take rP ++ ys.drop (RecRule.ctorParams rl)) :=
    (hspx.take rP).append (hspy.drop _)
  refine ⟨frame_mkAppN ⟨ConLeche.Expr.WScoped.of_not_hasFvar hRnf, hRbd,
      ConLeche.Expr.LeavesBounded.of_not_hasFvar hRnf⟩ (fun y hy => ?_),
    leavesSub_mkAppN (leavesSub_of_not_hasFvar hRnf) (fun y hy => ?_),
    _, denoteMeta_mkAppN hspOut (hRaD d), fun ρ hρ hL hg => ?_⟩
  · rcases List.mem_append.mp hy with hy' | hy'
    · exact (hfrE y (List.mem_of_mem_take hy')).1
    · exact (hfrC y (List.mem_of_mem_drop hy')).1
  · rcases List.mem_append.mp hy with hy' | hy'
    · intro l hl
      exact ConLeche.fvarLeaves_getAppArgs (List.mem_of_mem_take hy') l hl
    · intro l hl
      exact ConLeche.fvarLeaves_getAppArgs (ConLeche.getD_mem hmIlt) l
        (hsubmj l (ConLeche.fvarLeaves_getAppArgs (List.mem_of_mem_drop hy') l hl))
  -- **per valuation**
  obtain ⟨-, hoX⟩ := hoist_spineV xs hg
  have hLmajSlot : LeavesGr m φ d (e.getAppArgs.getD mI (.bvar 0)) ρ :=
    leavesGr_spine hL _ (ConLeche.getD_mem hmIlt)
  have hokMajArg : WellDenotedV V ρ (xs.getD mI default) :=
    hoX _ (ConLeche.getD_mem (by rw [← hspx.length]; exact hmIlt))
  have hLmj : LeavesGr m φ d major ρ := hLmajSlot.of_subset hsubmj
  have hLargsC : ∀ x ∈ major.getAppArgs, LeavesGr m φ d x ρ :=
    leavesGr_spine hLmj
  -- the recursor's fit
  obtain ⟨hfitRVal0, -⟩ :=
    hfitR ρ hρ
      (LeavesGr.of_fvarLeaves_nil
        (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfR))
      (leavesGr_spine hL) (hokTVa ρ) hoX (fun _ => ⟨hg, hmemR ρ⟩)
  have hsplit := take_getD_splitAK hxsLen
  have hfitRVal : TeleFitPA V ρ TVa (xs.take mI ++ [xs.getD mI default]) restR := by
    rw [← hsplit]; exact hfitRVal0
  have hoX0 : ∀ x ∈ xs.take mI, WellDenotedV V ρ x :=
    fun x hx => hoX x (List.mem_of_mem_take hx)
  have hxs0len : (xs.take mI).length = mI := by
    rw [List.length_take, hxsLen]; omega
  have hsubj0 : interp V ρ (AnnotTerm.mkAppN
      (m.acval c (Level.substFn φ cv.levelParams us)) xs)
      = interp V ρ (AnnotTerm.mkAppN
        (m.acval c (Level.substFn φ cv.levelParams us))
        (xs.take mI ++ [xs.getD mI default])) := by
    rw [← hsplit]
  by_cases hk : rl.k = true
  · -- **K**: the law at the recursor's own parameters; the major is not read
    obtain ⟨hnf0, hKlaw⟩ := hK hk
    obtain ⟨heqK, htrK⟩ := hKlaw Ra hRa0 ρ (xs.take mI) _ restR hxs0len hfitRVal
    have hysdrop : ys.drop (RecRule.ctorParams rl) = [] :=
      List.drop_of_length_le (by rw [hlenYs, hnf0, Nat.add_zero]; exact Nat.le_refl _)
    have hred : xs.take rP ++ ys.drop (RecRule.ctorParams rl) = (xs.take mI).take rP := by
      rw [hysdrop, List.append_nil, List.take_take, Nat.min_eq_left hrPle]
    rw [hred]
    exact ⟨htrK hoX0, hsubj0.trans heqK⟩
  have hk' : rl.k = false := by simpa using hk
  obtain ⟨hS, hP, hU⟩ := hextNK hk' usj hlenUj hψ TVja (hTVjaD 0)
  -- the case-3 run, at this valuation
  have hC3 : ConLeche.iotaCase3 env.find? rl cvj usj = true →
      (∀ y ∈ ys, WellDenotedV V ρ y) ∧ ∃ restC, TeleFitPA V ρ TVja ys restC := by
    intro h3
    obtain ⟨restC, hC3⟩ := hcertC h3 hfJ hCJ (hTVjaD d) hfrC hspy
    obtain ⟨hoY, hfitC, -⟩ := hC3 ρ hρ
      (LeavesGr.of_fvarLeaves_nil
        (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfJ))
      hLargsC (hokTVja ρ)
    exact ⟨hoY, restC, hfitC⟩
  -- where the major is the point, the redex is a case-3 one: at case 2
  -- the major's domain holds no point (S)
  have hcase3_of_pt : interp V ρ (xs.getD mI default) = pt →
      ConLeche.iotaCase3 env.find? rl cvj usj = true := by
    intro hapt
    cases h3 : ConLeche.iotaCase3 env.find? rl cvj usj
    · exact absurd hapt (hS (hlic_of hk' h3) ρ (xs.take mI) _ restR hxs0len hfitRVal)
    · rfl
  -- **the fired constructor application is the major's value**
  have hcase : interp V ρ (xs.getD mI default)
        = interp V ρ (AnnotTerm.mkAppN
            (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys) ∧
      (∀ y ∈ ys, WellDenotedV V ρ y) ∧
      ∃ restC, TeleFitPA V ρ TVja ys restC := by
    by_cases hapt : interp V ρ (xs.getD mI default) = pt
    · -- case 3 at a `Prop` valuation: the slot law (P)
      obtain ⟨hoY, restC, hfitC⟩ := hC3 (hcase3_of_pt hapt)
      refine ⟨?_, hoY, restC, hfitC⟩
      rw [hapt, hP ρ (xs.take mI) _ restR hxs0len hfitRVal hapt ys restC hfitC hlenYs hoY]
    · -- the major is not the point: its reduction is an equation
      obtain ⟨hokMj, heqAll⟩ := hInnerMaj ρ hρ hLmajSlot hokMajArg hapt
      obtain ⟨-, hoY⟩ := hoist_spineV ys hokMj
      refine ⟨heqAll, hoY, ?_⟩
      exact teleFitPA_of_graded_ne_pt ys hpcC (hokTVja ρ) (hmemJ ρ) hokMj
        (heqAll ▸ hapt)
  obtain ⟨heqA, hoY, restC, hfitC⟩ := hcase
  obtain ⟨restR', hfitR'⟩ := teleFitPA_snoc_congr (xs.take mI) hfitRVal heqA
  have hcase3_of_ptC : interp V ρ (AnnotTerm.mkAppN
      (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys) = pt →
      ConLeche.iotaCase3 env.find? rl cvj usj = true :=
    fun hpt => hcase3_of_pt (heqA.trans hpt)
  -- **the comparisons the step ran, conditional**
  -- the `.plain` parameters
  have hplainC : RecRule.fire rl = .plain →
      (RecRule.paramsBlind rl = false ∨
        interp V ρ (AnnotTerm.mkAppN
          (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys) = pt) →
      ∀ i, i < RecRule.ctorParams rl → i < mI →
        interp V ρ (ys.getD i default) ≠ pt →
        interp V ρ ((xs.take mI).getD i default) ≠ pt →
        interp V ρ (ys.getD i default) = interp V ρ ((xs.take mI).getD i default) := by
    intro hp hor i hi him hy hx
    have hcmp : ConLeche.iotaCompares env.find? rl cvj usj = true := by
      rcases hor with hb | hpt
      · exact ConLeche.iotaCompares_of_compareParams (RecRule.compareParams_plain hp hb)
      · exact ConLeche.iotaCompares_of_case3 (hcase3_of_ptC hpt)
    have hdefP := hparams hcmp
    rw [show (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
        e.getAppArgs rP).2 = e.getAppArgs.take (RecRule.ctorParams rl) from by
      unfold ConLeche.recFireComparands; rw [hp]] at hdefP
    have hz := hdefP.2
      (fun x hx => hfrC x (List.mem_of_mem_take hx))
      (fun x hx => hfrE x (List.mem_of_mem_take hx))
      (hspy.take _) (hspx.take _) ρ hρ
      (fun x hx => hLargsC x (List.mem_of_mem_take hx))
      (fun x hx => leavesGr_spine hL x (List.mem_of_mem_take hx))
      (fun x hx => hoY x (List.mem_of_mem_take hx))
      (fun x hx => hoX x (List.mem_of_mem_take hx))
    have hlt : i < (ys.take (RecRule.ctorParams rl)).length := by
      rw [List.length_take, hlenYs]; omega
    have hlenT : (ys.take (RecRule.ctorParams rl)).length
        = (xs.take (RecRule.ctorParams rl)).length := by
      have h1 := hdefP.1
      have h2 := hspy.length
      have h3 := hspx.length
      simp only [List.length_take] at h1 ⊢
      omega
    have hgi := zip_cond_getD (f := interp V ρ) hlenT hz i hlt
      (by rw [getD_takeAK hi]; exact hy)
      (by rw [getD_takeAK hi]; rw [getD_takeAK him] at hx; exact hx)
    rw [getD_takeAK hi, getD_takeAK hi] at hgi
    rw [getD_takeAK him]
    exact hgi
  -- the `.nested` pins
  have hnestedC : ∀ lvls pins, RecRule.fire rl = .nested lvls pins →
      ∀ i, i < RecRule.ctorParams rl →
      ∀ vpa : AnnotTerm,
        denoteMeta m.acval env φ rP (ConLeche.Verify.openRev 0 rP
          ((pins.getD i default).instantiateLevelParams cv.levelParams us))
          = some vpa →
        interp V ρ (ys.getD i default) ≠ pt →
        interp V ρ (AnnotTerm.instRevChain ((xs.take mI).take rP) vpa) ≠ pt →
        interp V ρ (ys.getD i default)
          = interp V ρ (AnnotTerm.instRevChain ((xs.take mI).take rP) vpa) := by
    intro lvls pins hn i hi vpa hvpa hy hx
    have hdefP' := hparams (ConLeche.iotaCompares_of_compareParams
      (RecRule.compareParams_nested hn))
    obtain ⟨-, -, -, -, -, hrec', -⟩ :=
      m.wf _ (ConLeche.Semantics.Env.find?_mem hrec)
    obtain ⟨-, -, -, -, hnest⟩ := hrec' cv mI rP rules rfl rl hrmem
    obtain ⟨-, -, hpinsWf, -⟩ := hnest lvls pins hn
    have hpinF' : ∀ p ∈ pins,
        (p.instantiateLevelParams cv.levelParams us).hasFvar = false := by
      intro p hp
      obtain ⟨hpinF, -, -, -⟩ := hpinsWf p hp
      rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hpinF
    have hcmp : (ConLeche.recFireComparands rl cv.levelParams us
        cvj.levelParams e.getAppArgs rP).2
        = pins.map (fun p => Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
            (p.instantiateLevelParams cv.levelParams us)) := by
      unfold ConLeche.recFireComparands; rw [hn]
    have hprelen : (e.getAppArgs.take rP).length = rP := by
      rw [List.length_take, hlen]; omega
    have hargsPre : ∀ x ∈ e.getAppArgs.take rP, Expr.WScoped d x ∧
        x.looseBVarsBounded 0 = true := by
      intro x hx
      obtain ⟨⟨hw2, hb2, -⟩, -⟩ := hfrE x (List.mem_of_mem_take hx)
      exact ⟨hw2, hb2⟩
    have hlenPins : pins.length = RecRule.ctorParams rl := by
      have h1 := hdefP'.1
      rw [hcmp, List.length_map, List.length_take, hmlen] at h1
      omega
    -- the frames of the comparand list
    have hfrPin : ∀ (p : Expr), p ∈ pins →
        Frame d (Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
          (p.instantiateLevelParams cv.levelParams us)) ∧
        CtxOkS m φ d Δa (Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
          (p.instantiateLevelParams cv.levelParams us)) := by
      intro p hp
      obtain ⟨hpinF, -, -, hpinB⟩ := hpinsWf p hp
      have hpinF0 : (p.instantiateLevelParams cv.levelParams us).hasFvar
          = false := hpinF' p hp
      have hpinB' : (p.instantiateLevelParams cv.levelParams
          us).looseBVarsBounded (e.getAppArgs.take rP).length = true := by
        rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams, hprelen]
        exact hpinB
      refine ⟨⟨ConLeche.instSpine_WScoped _
          (ConLeche.Expr.WScoped.of_not_hasFvar hpinF0)
          (fun y hy => (hargsPre y hy).1), ?_, fun l hl => ?_⟩,
        ⟨hC.1, fun l hl => ?_⟩⟩
      · rw [show rP - 1 = (e.getAppArgs.take rP).length - 1 from by
          rw [hprelen]]
        exact ConLeche.instSpine_closed (fun y hy => (hargsPre y hy).2) hpinB'
      · rcases ConLeche.fvarLeaves_instSpine _ hl with hl' | ⟨y, hy, hly⟩
        · exact absurd hl' (by
            rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hpinF0]; simp)
        · exact (hfrE y (List.mem_of_mem_take hy)).1.2.2 l hly
      · rcases ConLeche.fvarLeaves_instSpine _ hl with hl' | ⟨y, hy, hly⟩
        · exact absurd hl' (by
            rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hpinF0]; simp)
        · exact ((hfrE y (List.mem_of_mem_take hy)).2).2 l hly
    -- the comparand's LEAVES, graded at this ρ off the recursor's own
    -- prefix (the pin itself is closed)
    have hLComp : ∀ (p : Expr), p ∈ pins →
        LeavesGr m φ d (Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
          (p.instantiateLevelParams cv.levelParams us)) ρ := by
      intro p hp l hl tya hden
      rcases ConLeche.fvarLeaves_instSpine _ hl with hl' | ⟨y, hy, hly⟩
      · exact absurd hl' (by
          rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar (hpinF' p hp)]; simp)
      · exact leavesGr_spine hL y (List.mem_of_mem_take hy) l hly tya hden
    -- each comparand reads, to the pin's open reading chained along the
    -- recursor's parameter prefix
    have hcompRead : ∀ (p : Expr), p ∈ pins →
        denoteMeta m.acval env φ d
            (Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
              (p.instantiateLevelParams cv.levelParams us))
          = (denoteMeta m.acval env φ rP (ConLeche.Verify.openRev 0 rP
              (p.instantiateLevelParams cv.levelParams us))).map
              (AnnotTerm.instRevChain (xs.take rP)) := by
      intro p hp
      have hpinF0 : (p.instantiateLevelParams cv.levelParams us).hasFvar
          = false := hpinF' p hp
      obtain ⟨-, -, -, hpinB⟩ := hpinsWf p hp
      have hpinB' : (p.instantiateLevelParams cv.levelParams
          us).looseBVarsBounded (e.getAppArgs.take rP).length = true := by
        rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams, hprelen]
        exact hpinB
      have hcden := denoteMeta_openRevK m.acval_closed (acval_inst_self m)
        (e.getAppArgs.take rP) hargsPre
        ((ConLeche.Expr.WScoped.of_not_hasFvar (d := d) hpinF0).fvarsBelow)
        hpinB' (hspx.take rP)
      rw [hprelen] at hcden
      have hbase := denoteMeta_openRev_base (env := env) (φ := φ)
        m.acval_closed m.acval_erase m.cval_closed hpinF0
        (by rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
            exact hpinB) d
      rw [hbase] at hcden
      rw [Expr.instSpine_eq_instSeq]
      simpa using hcden
    -- so the comparand list reads, and its readings are graded by the
    -- law's context-guarded pin conjunct
    have hbsRead : ∀ x ∈ pins.map (fun p =>
        Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
          (p.instantiateLevelParams cv.levelParams us)),
        ∃ v, denoteMeta m.acval env φ d x = some v := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      obtain ⟨j, hj, hpj⟩ := mem_getD_index hp
      obtain ⟨vpa', hvpa', -⟩ := hpinsOk lvls pins hn j (by omega)
      rw [hcompRead p hp, ← hpj, hvpa']
      exact ⟨_, rfl⟩
    obtain ⟨bsa, hspB⟩ := DenoteMetaSpine.exists_of_all _ hbsRead
    have hokChain : ∀ (vv : AnnotTerm) (j : Nat), j < pins.length →
        denoteMeta m.acval env φ rP (ConLeche.Verify.openRev 0 rP
          ((pins.getD j default).instantiateLevelParams cv.levelParams us))
          = some vv →
        WellDenotedV V ρ (AnnotTerm.instRevChain (xs.take rP) vv) := by
      intro vv j hj hvv
      obtain ⟨vpa', hvpa', hok'⟩ := hpinsOk lvls pins hn j (by omega)
      obtain rfl : vpa' = vv := Option.some.inj (hvpa'.symm.trans hvv)
      obtain ⟨mid, hmid⟩ := hfitRVal0.take rP
      exact hok' ρ (xs.take rP) TVa mid
        (by rw [List.length_take, hxsLen]; omega)
        (fun v hv => hoX v (List.mem_of_mem_take hv))
        (hTVaD 0) hmid
    have hgetB : ∀ j, j < pins.length →
        denoteMeta m.acval env φ d
            ((pins.map (fun p => Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
              (p.instantiateLevelParams cv.levelParams us))).getD j default)
          = (denoteMeta m.acval env φ rP (ConLeche.Verify.openRev 0 rP
              ((pins.getD j default).instantiateLevelParams cv.levelParams us))).map
              (AnnotTerm.instRevChain (xs.take rP)) := by
      intro j hj
      rw [show (pins.map (fun p => Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
          (p.instantiateLevelParams cv.levelParams us))).getD j default
          = Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
            ((pins.getD j default).instantiateLevelParams cv.levelParams us) from by
        simp [List.getD, List.getElem?_map, List.getElem?_eq_getElem hj]]
      exact hcompRead _ (ConLeche.getD_mem hj)
    have hlenB : pins.length = bsa.length := by
      have := hspB.length
      simpa using this
    have hgB : ∀ x ∈ bsa, WellDenotedV V ρ x := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := mem_getD_index hx
      have hjp : j < pins.length := by omega
      have h1 := hspB.getD (default : Expr) j (by
        rw [List.length_map]; omega)
      rw [hgetB j hjp] at h1
      obtain ⟨vpa', hvpa', -⟩ := hpinsOk lvls pins hn j (by omega)
      rw [hvpa'] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      rw [← h1]
      exact hokChain vpa' j hjp hvpa'
    have hLb2 : ∀ x ∈ pins.map (fun p => Expr.instSpine
        (e.getAppArgs.take rP) (rP - 1)
        (p.instantiateLevelParams cv.levelParams us)),
        LeavesGr m φ d x ρ := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact hLComp p hp
    rw [hcmp] at hdefP'
    have hz := hdefP'.2
      (fun x hx => hfrC x (List.mem_of_mem_take hx))
      (fun x hx => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact hfrPin p hp)
      (hspy.take _) hspB ρ hρ
      (fun x hx => hLargsC x (List.mem_of_mem_take hx))
      hLb2
      (fun x hx => hoY x (List.mem_of_mem_take hx)) hgB
    -- the `i`-th comparand's reading is the chained pin
    have hiB := hspB.getD (default : Expr) i (by
      simp only [List.length_map]; omega)
    rw [hgetB i (by omega), hvpa] at hiB
    simp only [Option.map_some, Option.some.injEq] at hiB
    have hlt : i < (ys.take (RecRule.ctorParams rl)).length := by
      rw [List.length_take, hlenYs]; omega
    have hlenT : (ys.take (RecRule.ctorParams rl)).length = bsa.length := by
      rw [List.length_take, hlenYs, ← hlenB, hlenPins]; omega
    rw [List.take_take, Nat.min_eq_left hrPle] at hx ⊢
    have hgi := zip_cond_getD (f := interp V ρ) hlenT hz i hlt
      (by rw [getD_takeAK hi]; exact hy) (by rw [← hiB]; exact hx)
    rw [getD_takeAK hi, ← hiB] at hgi
    exact hgi
  -- the index pin, where the fired application is the point (case 3)
  have hpinC : interp V ρ (AnnotTerm.mkAppN
      (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys) = pt →
      IotaIndexPinC (V := V) ρ restC (RecRule.ctorParams rl) mI rP (xs.take mI) := by
    intro hpt
    have h3 := hcase3_of_ptC hpt
    by_cases hmr : mI = rP
    · exact ⟨restC, [], rfl, Or.inl hmr, fun i hi => absurd hi (by omega)⟩
    have hpres := hres h3 hmr
    obtain ⟨hfRes, hCRes⟩ := piResidual_frameK hpres hfJ hCJ hfrC
    have hLRes : LeavesGr m φ d residual ρ :=
      piResidual_leavesGrK hpres
        (LeavesGr.of_fvarLeaves_nil
          (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfJ))
        hLargsC
    have hfrRes := frame_spine hfRes hCRes
    have hresC : denoteMeta m.acval env φ d residual = some restC :=
      teleFitPA_residualK m.acval_closed (acval_inst_self m) major.getAppArgs
        hpres hfJ.1 (fun x hx => ⟨(hfrC x hx).1.1, (hfrC x hx).1.2.1⟩)
        (hTVjaD d) hspy hfitC
    rw [show residual = Expr.mkAppN residual.getAppFn residual.getAppArgs from
      (ConLeche.Expr.mkAppN_getApp residual).symm] at hresC
    obtain ⟨Ha, cargsa, -, hspRes, hCeq⟩ := denoteMeta_mkAppN_inv hresC
    -- the residual is graded: the constructor's fit grades its residual
    have hRcA : WellDenotedV V ρ (AnnotTerm.mkAppN Ha cargsa) :=
      hCeq ▸ teleFitPA_rest_graded hfitC (hokTVja ρ) hoY
    obtain ⟨-, hoCargs⟩ := hoist_spineV cargsa hRcA
    have hspIdx : DenoteMetaSpine m.acval env φ d ((e.getAppArgs.take mI).drop rP)
        ((xs.take mI).drop rP) := (hspx.take mI).drop rP
    have hdefI := hidx h3 hmr
    have hzI := hdefI.2
        (fun x hx => hfrRes x (List.mem_of_mem_drop hx))
        (fun x hx => hfrE x (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
        (hspRes.drop _) hspIdx ρ hρ
        (fun x hx => leavesGr_spine hLRes x (List.mem_of_mem_drop hx))
        (fun x hx => leavesGr_spine hL x
          (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
        (fun x hx => hoCargs x (List.mem_of_mem_drop hx))
        (fun x hx => hoX x (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
    have hlen1 := hdefI.1
    have hlenI : (cargsa.drop (RecRule.ctorParams rl)).length
        = ((xs.take mI).drop rP).length := by
      have h2 := hspRes.length
      have h3 := hspx.length
      simp only [List.length_drop, List.length_take] at hlen1 ⊢
      omega
    have hlenDisj : mI = rP ∨
        cargsa.length = RecRule.ctorParams rl + (mI - rP) := by
      simp only [List.length_drop, List.length_take] at hlenI
      rw [hxsLen] at hlenI
      omega
    refine ⟨Ha, cargsa, hCeq, hlenDisj, fun i hi hy hx => ?_⟩
    have hlt : i < (cargsa.drop (RecRule.ctorParams rl)).length := by
      rw [List.length_drop]
      rcases hlenDisj with hh | hh <;> omega
    have hgi := zip_cond_getD (f := interp V ρ) hlenI hzI i hlt
      (by rw [getD_dropAK]; exact hy) (by rw [getD_dropAK]; exact hx)
    rw [getD_dropAK, getD_dropAK] at hgi
    exact hgi
  -- **(U)**: the comparisons are equations
  obtain ⟨hplainU, hnestedU, hpinU⟩ :=
    hU ρ (xs.take mI) ys restR' restC hxs0len hlenYs hfitR' hfitC hoX0 hoY
      hplainC hnestedC hpinC
  -- **fire the law**
  obtain ⟨heqLaw, htrans⟩ := hlaw cvj cnP cnF hctor usj ρ (xs.take mI) ys
    TVa TVja restR' restC hxs0len hlenYs hlenUj hψ hplainU hnestedU hpinU
    (hTVaD 0) (hTVjaD 0) hfitR' hfitC
  rw [List.take_take, Nat.min_eq_left hrPle] at heqLaw htrans
  have hsubj : interp V ρ (AnnotTerm.mkAppN
      (m.acval c (Level.substFn φ cv.levelParams us)) xs)
      = interp V ρ (AnnotTerm.mkAppN
        (m.acval c (Level.substFn φ cv.levelParams us))
        (xs.take mI ++ [AnnotTerm.mkAppN
          (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys])) := by
    rw [hsubj0]
    refine interp_mkAppN_congrK _ _ rfl ?_
    simp only [List.map_append, List.map_cons, List.map_nil, heqA]
  exact ⟨htrans hoX0 hoY, hsubj.trans heqLaw⟩

set_option linter.unusedVariables false in
/-- The K rescue: the fabrication reads and is
graded by the certified constructor telescope (`CertsSem`), and its
type, checked against the major's (`hdt`), is the major's type.  Both
inhabit that one type, so the conditional proof irrelevance (`hpi`)
equates them: where neither is the point it says so, and a type
holding the point holds nothing else (`IsTy.eq_of_ne_pt`).  The
premises are the conditional claims, the conclusion the unconditional
one (task #342 L10).

Several of the rule's premises are consumed by the BRIDGE and not by
the semantics: the recursor's storage, the K flag, the constructor's
result family (`hres`/`hind`), the parameter count and the two
type-check certificates `htf`/`hdt` are what makes the checker take
this branch and build `proofIrrel`'s argument; at the motive the whole
of that argument is the `DefEq fab major` premise.  Hence the linter
option. -/
theorem Red.rescueK_sound (hin : RulesInputs V m φ) {d : Nat}
    {major tm tmaj fab tf : Expr} {recName : Name} {cv : ConstantVal}
    {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat} {T : Name}
    {tus ust : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (hrec : env.find? recName = some (.recInfo cv mI rP [rl]))
    (hk : rl.k = true)
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hres : (cvj.type.piResult).getAppFn = .const T tus)
    (hind : env.find? T = some (.indInfo cvT caps))
    (htm : InferSemIO m φ d major tm) (htmaj : RedSem m φ d tm tmaj)
    (hthead : tmaj.getAppFn = .const T ust)
    (hlv : cvj.levelParams.length = ust.length)
    (hnP : cnP ≤ tmaj.getAppArgs.length)
    (hfab : fab = Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP))
    (hws : fab.wscopedB d = true) (hb : fab.looseBVarsBounded 0 = true)
    (hlv' : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (hcerts : CertsSem m φ d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (tmaj.getAppArgs.take cnP))
    (htf : InferSemIO m φ d fab tf) (hdt : DefEqSem m φ d tmaj tf)
    (hpi : DefEqSem m φ d fab major) :
    RedSemU m φ d major fab := by
  intro hfM Δa ea hCM hea
  -- the fabrication's frame comes with the rule's three scope guards
  have hsub : LeavesSub fab major := fun l hl => by
    have := List.all_eq_true.mp hlv' l hl
    simpa using this
  have hfF : Frame d fab :=
    ⟨Expr.WScoped.of_wscopedB hws, hb, fun l hl => hfM.2.2 l (hsub l hl)⟩
  have hCF : CtxOkS m φ d Δa fab := hCM.of_subset hsub
  -- the major's io-inferred type, reduced, is the family at its spine
  obtain ⟨hfT0, hsubT0, tm0a, htm0a, hInnerTm0⟩ := htm hfM hCM hea
  obtain ⟨hfTm, hsubTm, tmaja, htmaja, hInnerTmaj⟩ :=
    htmaj hfT0 (hCM.of_subset hsubT0) htm0a
  have hCTm : CtxOkS m φ d Δa tmaj :=
    (hCM.of_subset hsubT0).of_subset hsubTm
  have htmajaSave := htmaja
  rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp tmaj).symm, hthead] at htmaja
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteMeta_mkAppN_inv htmaja
  have hfrT := frame_spine hfTm hCTm
  -- the constructor's stored type: read, graded, inhabited, closed
  obtain ⟨TVja, hTVjaD, hokTVja, hmemCj, hnfJ, hbdJ⟩ :=
    constTy_pkg hin.const_ty hctor rfl (show ust.length = _ from hlv.symm)
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTVjaD hmemCj hnfJ hbdJ
  obtain ⟨hfJ, hCJ⟩ := frame_of_not_hasFvar (m := m) (Δa := Δa) hnfJ hbdJ hCM.1
  -- the fabrication reads
  have hheadCj : denoteMeta m.acval env φ d (.const rl.ctor ust)
      = some (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) :=
    denoteMeta_const hctor (show ust.length = _ from hlv.symm)
  have hdF : denoteMeta m.acval env φ d fab
      = some (AnnotTerm.mkAppN
        (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) (tsa.take cnP)) := by
    rw [hfab]; exact denoteMeta_mkAppN (hspt.take cnP) hheadCj
  have hframesTb : ∀ x ∈ tmaj.getAppArgs.take cnP, Frame d x ∧ CtxOkS m φ d Δa x :=
    fun x hx => hfrT x (List.mem_of_mem_take hx)
  obtain ⟨resta, hfit⟩ :=
    hcerts (fa := m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
      hfJ hCJ (hTVjaD d) hframesTb (hspt.take cnP)
  obtain ⟨hfTf, hsubTf, tfa, htfa, hInnerTf⟩ := htf hfF hCF hdF
  have hCTf : CtxOkS m φ d Δa tf := hCF.of_subset hsubTf
  refine ⟨hfF, hsub, _, hdF, fun ρ hρ hL hg => ?_⟩
  have hLfab : LeavesGr m φ d fab ρ := hL.of_subset hsub
  -- per-ρ: the io type grading, transported along the reduction (the
  -- type is not the point: "not pt" source (1))
  obtain ⟨hgT0, hmemM0⟩ := hInnerTm0 ρ hρ hL hg
  obtain ⟨hgTm, heqTm⟩ := hInnerTmaj ρ hρ (hL.of_subset hsubT0) hgT0.1 hgT0.ne_pt
  obtain ⟨-, hoTs⟩ := hoist_spineV tsa hgTm
  have hLtmaj : LeavesGr m φ d tmaj ρ := (hL.of_subset hsubT0).of_subset hsubTm
  have hLTb : ∀ x ∈ tmaj.getAppArgs.take cnP, LeavesGr m φ d x ρ :=
    fun x hx => leavesGr_spine hLtmaj x (List.mem_of_mem_take hx)
  obtain ⟨hfitVal, -⟩ :=
    hfit ρ hρ
      (LeavesGr.of_fvarLeaves_nil
        (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfJ))
      hLTb (hokTVja ρ) (fun x hx => hoTs x (List.mem_of_mem_take hx)) (by simp)
  -- and is graded: its own telescope certificate is the fit
  have hgF : WellDenotedV V ρ (AnnotTerm.mkAppN
      (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) (tsa.take cnP)) :=
    (mkAppN_of_fitA (tsa.take cnP) (hokTVja ρ)
      ⟨m.acval_wellDenoted _ _ ρ, hin.leaf_valid _ _ ρ⟩
      (fun x hx => hoTs x (List.mem_of_mem_take hx)) (hmemCj ρ) hfitVal).1
  -- the fabrication's type is the major's ("not pt" source (1): two types)
  obtain ⟨hgTf, hmemF⟩ := hInnerTf ρ hρ hLfab hgF
  have hneTm : interp V ρ (AnnotTerm.mkAppN vT tsa) ≠ pt := heqTm ▸ hgT0.ne_pt
  have heqT := hdt hfTm hfTf hCTm hCTf htmajaSave htfa ρ hρ hLtmaj
    (hLfab.of_subset hsubTf) hgTm hgTf.1 hneTm hgTf.ne_pt
  have hmemM : interp V ρ ea ∈ˢ interp V ρ tfa := by
    rw [← heqT, ← heqTm]; exact hmemM0
  -- one type holds both: the conditional proof irrelevance is an equation
  refine ⟨hgF, (IsTy.eq_of_ne_pt hgTf.2 hmemF hmemM
    (hpi hfF hfM hCF hCM hdF hea ρ hρ hLfab hL hgF hg)).symm⟩

set_option linter.unusedVariables false in
/-- The structure-η rescue, in its
two slot kinds: at a tower-backed family the fabricated projections
are `.proj T j major` nodes reading to the tower readings and graded
by each entry's typing law; at a projection-function family they are
`mkAppN (.const (projFnName T j) ust) (tmaj.getAppArgs ++ [major])`
nodes, whose storage and telescope fit come from the rule's
`EtaProjCerts` premise (`hproj`) — the same premise `DefEq.structEta`
carries, and the same certificate the checker runs there. -/
theorem Red.rescueEta_soundU (hin : RulesInputs V m φ) {d : Nat}
    {major tm tmaj fab : Expr} {recName : Name} {cv : ConstantVal}
    {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat} {T : Name}
    {tus ust : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (hrec : env.find? recName = some (.recInfo cv mI rP [rl]))
    (heta : rl.eta = true)
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hres : (cvj.type.piResult).getAppFn = .const T tus)
    (hind : env.find? T = some (.indInfo cvT caps))
    (htm : InferSemIO m φ d major tm) (htmaj : RedSemU m φ d tm tmaj)
    (hthead : tmaj.getAppFn = .const T ust)
    (hlen : tmaj.getAppArgs.length = caps.etaParams)
    (hlv : ust.length = cvT.levelParams.length)
    (hnz : ConLeche.capsNeverZero cvT.levelParams ust caps = true)
    (hfab : fab = Expr.mkAppN (.const caps.etaCtor ust)
      (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields))
    (hws : fab.wscopedB d = true) (hb : fab.looseBVarsBounded 0 = true)
    (hlv' : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (hcerts : CertsSem m φ d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields))
    (hproj : ConLeche.towerSlotsAll env T caps.etaFields = false →
      EtaProjCertsSem m φ d T ust tmaj.getAppArgs major cvT.levelParams
        (List.range caps.etaFields))
    (hpi : DefEqSemU m φ d fab major) :
    RedSemU m φ d major fab := by
  intro hfM Δa ea hCM hea
  have hsub : LeavesSub fab major := fun l hl => by
    have := List.all_eq_true.mp hlv' l hl
    simpa using this
  have hfF : Frame d fab :=
    ⟨Expr.WScoped.of_wscopedB hws, hb, fun l hl => hfM.2.2 l (hsub l hl)⟩
  have hCF : CtxOkS m φ d Δa fab := hCM.of_subset hsub
  -- the family's η record: the rule's constructor IS the family's, and
  -- carries the former's level parameters (`RecCtorsStored`)
  obtain ⟨-, hEbits⟩ := ConLeche.recCtors_bits m.rec_ctors hrec
    List.mem_cons_self hctor hres hind
  obtain ⟨hcapseta, hectr, hlpsE⟩ := hEbits heta
  have hlpj : ust.length = cvj.levelParams.length := by
    rw [hlpsE]; exact hlv
  -- the major's io-inferred type, reduced, is the family at its spine
  obtain ⟨hfT0, hsubT0, tm0a, htm0a, hInnerTm0⟩ := htm hfM hCM hea
  obtain ⟨hfTm, hsubTm, tmaja, htmaja, hInnerTmaj⟩ :=
    htmaj hfT0 (hCM.of_subset hsubT0) htm0a
  have hCTm : CtxOkS m φ d Δa tmaj :=
    (hCM.of_subset hsubT0).of_subset hsubTm
  rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp tmaj).symm, hthead] at htmaja
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteMeta_mkAppN_inv htmaja
  have hfrT := frame_spine hfTm hCTm
  have hvT' : vT = m.acval T (Level.substFn φ cvT.levelParams ust) := by
    rw [denoteMeta_const hind (show ust.length
      = (ConLeche.ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
      from hlv)] at hvT
    exact (Option.some.inj hvT).symm
  -- the constructor's stored type: read, graded, inhabited, closed
  obtain ⟨TVja, hTVjaD, hokTVja, hmemCj, hnfJ, hbdJ⟩ :=
    constTy_pkg hin.const_ty hctor rfl (show ust.length = _ from hlpj)
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTVjaD hmemCj hnfJ hbdJ
  obtain ⟨hfJ, hCJ⟩ := frame_of_not_hasFvar (m := m) (Δa := Δa) hnfJ hbdJ hCM.1
  have hheadCj : denoteMeta m.acval env φ d (.const caps.etaCtor ust)
      = some (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) := by
    rw [← hectr]; exact denoteMeta_const hctor (show ust.length = _ from hlpj)
  -- the fabricated projections' frames (a `.proj` node over the major)
  have hprFr : ∀ j, Frame d (Expr.proj T j major) ∧
      CtxOkS m φ d Δa (Expr.proj T j major) := fun j =>
    ⟨⟨by simpa [Expr.WScoped] using hfM.1,
        by simpa [Expr.looseBVarsBounded] using hfM.2.1,
        fun l hl => hfM.2.2 l (by simpa [Expr.fvarLeaves] using hl)⟩,
      hCM.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)⟩
  by_cases htow : ConLeche.towerSlotsAll env T caps.etaFields = true
  · -- TOWER-BACKED SLOTS: the fabricated projections are `.proj T j
    -- major` nodes reading to the tower readings and graded by each
    -- entry's typing law
    have hpfacts : ∀ j ∈ List.range caps.etaFields,
        denoteMeta m.acval env φ d (Expr.proj T j major)
          = some (projAV (j + env.projOff T) ea) := by
      intro j hj
      obtain ⟨entry, hfe⟩ :=
        ConLeche.towerSlotsAll_slot htow j (List.mem_range.mp hj)
      rw [← ConLeche.Env.findProj?_off hfe]
      exact denoteMeta_proj_tower hfe hea
    have hspF : DenoteMetaSpine m.acval env φ d
        (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields)
        (tsa ++ (List.range caps.etaFields).map fun j =>
          projAV (j + env.projOff T) ea) := by
      unfold ConLeche.etaFabArgsE ConLeche.etaProjs
      rw [ite_eq_left htow]
      exact hspt.append (DenoteMetaSpine.map_list _ hpfacts)
    have hfrF : ∀ x ∈ ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major
        caps.etaFields, Frame d x ∧ CtxOkS m φ d Δa x := by
      intro x hx
      unfold ConLeche.etaFabArgsE ConLeche.etaProjs at hx
      rw [ite_eq_left htow] at hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hfrT x hx'
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx'
        exact hprFr j
    have hdF : denoteMeta m.acval env φ d fab
        = some (AnnotTerm.mkAppN
          (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
          (tsa ++ (List.range caps.etaFields).map fun j =>
            projAV (j + env.projOff T) ea)) := by
      rw [hfab]; exact denoteMeta_mkAppN hspF hheadCj
    obtain ⟨resta, hfit⟩ :=
      hcerts (fa := m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
        hfJ hCJ (hTVjaD d) hfrF hspF
    refine ⟨hfF, hsub, _, hdF, fun ρ hρ hL hg => ?_⟩
    obtain ⟨hgT0, hmemM0⟩ := hInnerTm0 ρ hρ hL hg
    obtain ⟨hgTm, heqTm⟩ := hInnerTmaj ρ hρ (hL.of_subset hsubT0) hgT0.1
    have hmemMW : interp V ρ ea ∈ˢ interp V ρ (AnnotTerm.mkAppN vT tsa) :=
      heqTm ▸ hmemM0
    obtain ⟨-, hoTs⟩ := hoist_spineV tsa hgTm
    have hLtmaj : LeavesGr m φ d tmaj ρ := (hL.of_subset hsubT0).of_subset hsubTm
    have hokProj : ∀ j ∈ List.range caps.etaFields,
        WellDenotedV V ρ (projAV (j + env.projOff T) ea) := by
      intro j hj
      obtain ⟨entry, hfe⟩ :=
        ConLeche.towerSlotsAll_slot htow j (List.mem_range.mp hj)
      rw [← ConLeche.Env.findProj?_off hfe]
      obtain ⟨-, -, -, ⟨cvTj, capsTj, hfTj, hlpsTj, himpj⟩, hO5j, cvCj, -, -,
        hlawj, -⟩ := hin.tower_ok T j entry hfe
      have hcvTj : cvTj = cvT := by
        rw [hind] at hfTj
        exact (ConLeche.ConstantInfo.indInfo.inj (Option.some.inj hfTj)).1.symm
      have hcapsTj : capsTj = caps := by
        rw [hind] at hfTj
        exact (ConLeche.ConstantInfo.indInfo.inj (Option.some.inj hfTj)).2.symm
      obtain ⟨hnpj, -, hparj, -⟩ := himpj (by rw [hcapsTj]; exact hcapseta)
      rw [hcapsTj] at hparj
      have hlpe : entry.levelParams = cvT.levelParams := by rw [← hlpsTj, hcvTj]
      have hgj : TowerGuardAt φ entry ust :=
        towerGuardAt_of hO5j (fun hp => by rw [hp] at hnpj; exact nomatch hnpj)
      obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlawj ust (by rw [hlpe]; exact hlv)
      have hTad := (towerEntry_tele_at_depth hfe hTa).1
      have hlenVs : tsa.length = entry.numParams := by
        rw [← hspt.length, hlen, hparj]
      have hpc : PiChain (tsa ++ [ea]).length Ta := by
        rw [List.length_append, List.length_singleton, hlenVs]
        exact piChain_of_stripPis _
          (by rw [ConLeche.projTele_stripPis]; rfl) (hTad d)
      obtain ⟨restj, hpeel⟩ := peelPis_of_piChain _ hpc
      rw [hlpe, ← hvT'] at hA
      exact (hA hgj ρ tsa ea restj hlenVs hgTm hg hmemMW hpeel).1
    have hoksF : ∀ x ∈ (tsa ++ (List.range caps.etaFields).map fun j =>
        projAV (j + env.projOff T) ea), WellDenotedV V ρ x := by
      intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hoTs x hx'
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx'
        exact hokProj j hj
    have hLF : ∀ x ∈ ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major
        caps.etaFields, LeavesGr m φ d x ρ := by
      intro x hx
      unfold ConLeche.etaFabArgsE ConLeche.etaProjs at hx
      rw [ite_eq_left htow] at hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact leavesGr_spine hLtmaj x hx'
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx'
        exact LeavesGr.of_subset hL (fun l hl => by simpa [Expr.fvarLeaves] using hl)
    obtain ⟨hfitVal, -⟩ :=
      hfit ρ hρ
        (LeavesGr.of_fvarLeaves_nil
          (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfJ))
        hLF (hokTVja ρ) hoksF (by simp)
    have hgF : WellDenotedV V ρ (AnnotTerm.mkAppN
        (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (tsa ++ (List.range caps.etaFields).map fun j =>
          projAV (j + env.projOff T) ea)) :=
      (mkAppN_of_fitA _ (hokTVja ρ)
        ⟨m.acval_wellDenoted _ _ ρ, hin.leaf_valid _ _ ρ⟩
        hoksF (hmemCj ρ) hfitVal).1
    exact ⟨hgF, (hpi hfF hfM hCF hCM hdF hea ρ hρ (hL.of_subset hsub) hL hgF hg).symm⟩
  · -- PROJECTION-FUNCTION SLOTS: the fabricated projections are
    -- `mkAppN (.const (projFnName T j) ust) (tmaj.getAppArgs ++
    -- [major])` nodes.  Each slot's storage, its level arity and the
    -- telescope fit that grades the node are the rule's
    -- `EtaProjCerts` premise (`hproj`) — the four facts the checker
    -- reads off `structEtaProjCerts_inv`.
    have htowF : ConLeche.towerSlotsAll env T caps.etaFields = false := by
      cases h : ConLeche.towerSlotsAll env T caps.etaFields
      · rfl
      · exact absurd h htow
    have hslotR := hproj htowF
    -- the spine the per-slot certificates run at
    have hspTb : DenoteMetaSpine m.acval env φ d (tmaj.getAppArgs ++ [major])
        (tsa ++ [ea]) := hspt.append (.cons hea .nil)
    have hsubTb : ∀ x ∈ tmaj.getAppArgs ++ [major], LeavesSub x major := by
      intro x hx l hl
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hsubT0 l (hsubTm l (ConLeche.fvarLeaves_getAppArgs hx' l hl))
      · rcases List.mem_singleton.mp hx' with rfl; exact hl
    have hframeTb : ∀ x ∈ tmaj.getAppArgs ++ [major],
        Frame d x ∧ CtxOkS m φ d Δa x := by
      intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hfrT x hx'
      · rcases List.mem_singleton.mp hx' with rfl
        exact ⟨hfM, hCM⟩
    -- each slot reads: the stored projection function at the family's
    -- level arity, applied to the certified spine
    have hprojden : ∀ j ∈ List.range caps.etaFields,
        denoteMeta m.acval env φ d
            (Expr.mkAppN (.const (projFnName T j) ust)
              (tmaj.getAppArgs ++ [major]))
          = some (AnnotTerm.mkAppN (m.acval (projFnName T j)
              (Level.substFn φ cvT.levelParams ust)) (tsa ++ [ea])) := by
      intro j hj
      obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpj2, -, -⟩ := hslotR j hj
      refine denoteMeta_mkAppN hspTb ?_
      have hden := denoteMeta_const (acval := m.acval) (φ := φ) (d := d) hfp
        (show ust.length = _ from by
          dsimp only [ConLeche.ConstantInfo.toConstantVal]
          rw [hlpj2]; exact hlv)
      dsimp only [ConLeche.ConstantInfo.toConstantVal] at hden
      rw [hlpj2] at hden
      exact hden
    -- the fabricated spine, its frame and its reading
    have hspF : DenoteMetaSpine m.acval env φ d
        (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields)
        (tsa ++ (List.range caps.etaFields).map fun j =>
          AnnotTerm.mkAppN (m.acval (projFnName T j)
            (Level.substFn φ cvT.levelParams ust)) (tsa ++ [ea])) := by
      unfold ConLeche.etaFabArgsE ConLeche.etaProjs
      rw [ite_eq_right htow]
      exact hspt.append (DenoteMetaSpine.map_list _ hprojden)
    have hfrF : ∀ x ∈ ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major
        caps.etaFields, Frame d x ∧ CtxOkS m φ d Δa x := by
      intro x hx
      unfold ConLeche.etaFabArgsE ConLeche.etaProjs at hx
      rw [ite_eq_right htow] at hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hfrT x hx'
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx'
        obtain ⟨hfC0, -⟩ := frame_of_not_hasFvar (m := m) (φ := φ) (Δa := Δa)
          (e := Expr.const (projFnName T j) ust) rfl rfl hCM.1
        exact ⟨frame_mkAppN hfC0 (fun y hy => (hframeTb y hy).1),
          hCM.of_subset (leavesSub_mkAppN
            (leavesSub_of_not_hasFvar rfl) hsubTb)⟩
    have hdF : denoteMeta m.acval env φ d fab
        = some (AnnotTerm.mkAppN
          (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
          (tsa ++ (List.range caps.etaFields).map fun j =>
            AnnotTerm.mkAppN (m.acval (projFnName T j)
              (Level.substFn φ cvT.levelParams ust)) (tsa ++ [ea]))) := by
      rw [hfab]; exact denoteMeta_mkAppN hspF hheadCj
    obtain ⟨resta, hfit⟩ :=
      hcerts (fa := m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
        hfJ hCJ (hTVjaD d) hfrF hspF
    refine ⟨hfF, hsub, _, hdF, fun ρ hρ hL hg => ?_⟩
    obtain ⟨hgT0, -⟩ := hInnerTm0 ρ hρ hL hg
    obtain ⟨hgTm, -⟩ := hInnerTmaj ρ hρ (hL.of_subset hsubT0) hgT0.1
    obtain ⟨-, hoTs⟩ := hoist_spineV tsa hgTm
    have hLtmaj : LeavesGr m φ d tmaj ρ := (hL.of_subset hsubT0).of_subset hsubTm
    have hLTb : ∀ x ∈ tmaj.getAppArgs ++ [major], LeavesGr m φ d x ρ := by
      intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact leavesGr_spine hLtmaj x hx'
      · rcases List.mem_singleton.mp hx' with rfl; exact hL
    have hoksTb : ∀ x ∈ tsa ++ [ea], WellDenotedV V ρ x := by
      intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hoTs x hx'
      · rcases List.mem_singleton.mp hx' with rfl; exact hg
    -- and is graded, by its own telescope's fit
    have hokProj : ∀ j ∈ List.range caps.etaFields,
        WellDenotedV V ρ (AnnotTerm.mkAppN (m.acval (projFnName T j)
          (Level.substFn φ cvT.levelParams ust)) (tsa ++ [ea])) := by
      intro j hj
      obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpj2, -, hicj⟩ := hslotR j hj
      obtain ⟨tpa, htpa, hoktpa, hmemp, hnfp, hbdp⟩ :=
        constTy_pkg hin.const_ty hfp rfl
          (show ust.length = _ from by
            dsimp only [ConLeche.ConstantInfo.toConstantVal]
            rw [hlpj2]; exact hlv)
      dsimp only [ConLeche.ConstantInfo.toConstantVal] at htpa hmemp hnfp hbdp
      obtain ⟨hfP, hCP⟩ := frame_of_not_hasFvar (m := m) (Δa := Δa) hnfp hbdp hCM.1
      obtain ⟨restp, hfitp⟩ :=
        hicj (fa := m.acval (projFnName T j) (Level.substFn φ cvp.levelParams ust))
          hfP hCP (htpa d) hframeTb hspTb
      obtain ⟨hfitpVal, -⟩ :=
        hfitp ρ hρ
          (LeavesGr.of_fvarLeaves_nil
            (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfp))
          hLTb (hoktpa ρ) hoksTb (by simp)
      refine (mkAppN_of_fitA (tsa ++ [ea]) (hoktpa ρ)
        ⟨m.acval_wellDenoted _ _ ρ, hin.leaf_valid _ _ ρ⟩
        hoksTb ?_ hfitpVal).1
      have hmm := hmemp ρ
      rwa [hlpj2] at hmm
    have hoksF : ∀ x ∈ (tsa ++ (List.range caps.etaFields).map fun j =>
        AnnotTerm.mkAppN (m.acval (projFnName T j)
          (Level.substFn φ cvT.levelParams ust)) (tsa ++ [ea])),
        WellDenotedV V ρ x := by
      intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hoTs x hx'
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx'
        exact hokProj j hj
    have hLproj : ∀ j, LeavesGr m φ d (Expr.mkAppN (.const (projFnName T j) ust)
        (tmaj.getAppArgs ++ [major])) ρ := by
      intro j l hl tya hden
      rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
      · simp [Expr.fvarLeaves] at hl'
      · exact hLTb y hy l hly tya hden
    have hLF : ∀ x ∈ ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major
        caps.etaFields, LeavesGr m φ d x ρ := by
      intro x hx
      unfold ConLeche.etaFabArgsE ConLeche.etaProjs at hx
      rw [ite_eq_right htow] at hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact leavesGr_spine hLtmaj x hx'
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx'
        exact hLproj j
    obtain ⟨hfitVal, -⟩ :=
      hfit ρ hρ
        (LeavesGr.of_fvarLeaves_nil
          (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfJ))
        hLF (hokTVja ρ) hoksF (by simp)
    have hgF : WellDenotedV V ρ (AnnotTerm.mkAppN
        (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (tsa ++ (List.range caps.etaFields).map fun j =>
          AnnotTerm.mkAppN (m.acval (projFnName T j)
            (Level.substFn φ cvT.levelParams ust)) (tsa ++ [ea]))) :=
      (mkAppN_of_fitA _ (hokTVja ρ)
        ⟨m.acval_wellDenoted _ _ ρ, hin.leaf_valid _ _ ρ⟩
        hoksF (hmemCj ρ) hfitVal).1
    exact ⟨hgF, (hpi hfF hfM hCF hCM hdF hea ρ hρ (hL.of_subset hsub) hL hgF hg).symm⟩

set_option linter.unusedVariables false in
/-- The `And` rescue: the
fabricated spine is the reduced type's parameters plus the major's two
`.proj` nodes, which read to the tower readings and are graded by the
two stored entries' typing law (`TowerOk`).  As for K, the
fabrication's type, checked against the major's, is the major's type,
so the conditional proof irrelevance (`hpi`) is an equation
(`IsTy.eq_of_ne_pt`); conditional premises, unconditional conclusion
(task #342 L10). -/
theorem Red.rescueAnd_sound (hin : RulesInputs V m φ) {d : Nat}
    {major tm tmaj fab tf : Expr} {recName : Name} {cv : ConstantVal}
    {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat}
    {tus ust : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (hrec : env.find? recName = some (.recInfo cv mI rP [rl]))
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hres : (cvj.type.piResult).getAppFn = .const andName tus)
    (hind : env.find? andName = some (.indInfo cvT caps))
    (htm : InferSemIO m φ d major tm) (htmaj : RedSem m φ d tm tmaj)
    (hthead : tmaj.getAppFn = .const andName ust)
    (hlen : tmaj.getAppArgs.length = cnP)
    (hlv : cvj.levelParams.length = ust.length)
    (hslots : ConLeche.andRescueSlots env rl.ctor cnP ust = true)
    (hfab : fab = Expr.mkAppN (.const rl.ctor ust)
      (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major]))
    (hws : fab.wscopedB d = true) (hb : fab.looseBVarsBounded 0 = true)
    (hlv' : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (hcerts : CertsSem m φ d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major]))
    (htf : InferSemIO m φ d fab tf) (hdt : DefEqSem m φ d tmaj tf)
    (hpi : DefEqSem m φ d fab major) :
    RedSemU m φ d major fab := by
  intro hfM Δa ea hCM hea
  have hsub : LeavesSub fab major := fun l hl => by
    have := List.all_eq_true.mp hlv' l hl
    simpa using this
  have hfF : Frame d fab :=
    ⟨Expr.WScoped.of_wscopedB hws, hb, fun l hl => hfM.2.2 l (hsub l hl)⟩
  have hCF : CtxOkS m φ d Δa fab := hCM.of_subset hsub
  -- the major's io-inferred type, reduced, is `And` at its parameters
  obtain ⟨hfT0, hsubT0, tm0a, htm0a, hInnerTm0⟩ := htm hfM hCM hea
  obtain ⟨hfTm, hsubTm, tmaja, htmaja, hInnerTmaj⟩ :=
    htmaj hfT0 (hCM.of_subset hsubT0) htm0a
  have hCTm : CtxOkS m φ d Δa tmaj :=
    (hCM.of_subset hsubT0).of_subset hsubTm
  have htmajaSave := htmaja
  rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp tmaj).symm, hthead] at htmaja
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteMeta_mkAppN_inv htmaja
  have hfrT := frame_spine hfTm hCTm
  -- the constructor's stored type: read, graded, inhabited, closed
  obtain ⟨TVja, hTVjaD, hokTVja, hmemCj, hnfJ, hbdJ⟩ :=
    constTy_pkg hin.const_ty hctor rfl (show ust.length = _ from hlv.symm)
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTVjaD hmemCj hnfJ hbdJ
  obtain ⟨hfJ, hCJ⟩ := frame_of_not_hasFvar (m := m) (Δa := Δa) hnfJ hbdJ hCM.1
  -- the two pinned slots are stored tower entries; their head data
  -- carries the former's level parameters (`TowerEntryLaw`)
  have hslot := ConLeche.andRescueSlots_inv hslots
  obtain ⟨entry0, hfe0, hctor0, hnP0, -, -⟩ := hslot 0 (by decide)
  obtain ⟨-, -, -, ⟨cvT0, capsT0, hfT0s, hlpsT0, -⟩, -, cvC0, hfC0, hlpsC0, -, -⟩ :=
    hin.tower_ok andName 0 entry0 hfe0
  have hcvT0 : cvT0 = cvT := by
    rw [hind] at hfT0s
    exact (ConLeche.ConstantInfo.indInfo.inj (Option.some.inj hfT0s)).1.symm
  have hcvC0 : cvC0 = cvj := by
    rw [hctor0, hctor] at hfC0
    exact (ConLeche.ConstantInfo.ctorInfo.inj (Option.some.inj hfC0)).1.symm
  have hlenus2 : ust.length = cvT.levelParams.length := by
    rw [← hcvT0, hlpsT0, ← hlpsC0, hcvC0]; exact hlv.symm
  have hvT' : vT = m.acval andName (Level.substFn φ cvT.levelParams ust) := by
    rw [denoteMeta_const hind (show ust.length
      = (ConLeche.ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
      from hlenus2)] at hvT
    exact (Option.some.inj hvT).symm
  -- each projection reads to the tower reading
  have hprojR : ∀ j, j < 2 →
      denoteMeta m.acval env φ d (Expr.proj andName j major)
        = some (projAV (j + env.projOff andName) ea) := by
    intro j hj
    obtain ⟨entry, hfe, -, -, -, -⟩ := hslot j hj
    rw [← ConLeche.Env.findProj?_off hfe]
    exact denoteMeta_proj_tower hfe hea
  -- the fabrication reads
  have hheadCj : denoteMeta m.acval env φ d (.const rl.ctor ust)
      = some (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) :=
    denoteMeta_const hctor (show ust.length = _ from hlv.symm)
  have hspF : DenoteMetaSpine m.acval env φ d
      (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major])
      (tsa ++ [projAV (0 + env.projOff andName) ea,
        projAV (1 + env.projOff andName) ea]) :=
    hspt.append (DenoteMetaSpine.cons (hprojR 0 (by decide))
      (DenoteMetaSpine.cons (hprojR 1 (by decide)) DenoteMetaSpine.nil))
  have hprFr : ∀ j, Frame d (Expr.proj andName j major) ∧
      CtxOkS m φ d Δa (Expr.proj andName j major) := fun j =>
    ⟨⟨by simpa [Expr.WScoped] using hfM.1,
        by simpa [Expr.looseBVarsBounded] using hfM.2.1,
        fun l hl => hfM.2.2 l (by simpa [Expr.fvarLeaves] using hl)⟩,
      hCM.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)⟩
  have hfrF : ∀ x ∈ tmaj.getAppArgs ++
      [Expr.proj andName 0 major, Expr.proj andName 1 major],
      Frame d x ∧ CtxOkS m φ d Δa x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact hfrT x hx'
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · exact hprFr 0
      · rcases List.mem_singleton.mp hx'' with rfl
        exact hprFr 1
  have hdF : denoteMeta m.acval env φ d fab
      = some (AnnotTerm.mkAppN
        (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (tsa ++ [projAV (0 + env.projOff andName) ea,
          projAV (1 + env.projOff andName) ea])) := by
    rw [hfab]; exact denoteMeta_mkAppN hspF hheadCj
  obtain ⟨resta, hfit⟩ :=
    hcerts (fa := m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
      hfJ hCJ (hTVjaD d) hfrF hspF
  obtain ⟨hfTf, hsubTf, tfa, htfa, hInnerTf⟩ := htf hfF hCF hdF
  have hCTf : CtxOkS m φ d Δa tf := hCF.of_subset hsubTf
  refine ⟨hfF, hsub, _, hdF, fun ρ hρ hL hg => ?_⟩
  obtain ⟨hgT0, hmemM0⟩ := hInnerTm0 ρ hρ hL hg
  obtain ⟨hgTm, heqTm⟩ := hInnerTmaj ρ hρ (hL.of_subset hsubT0) hgT0.1 hgT0.ne_pt
  have hmemMW : interp V ρ ea ∈ˢ interp V ρ (AnnotTerm.mkAppN vT tsa) :=
      heqTm ▸ hmemM0
  obtain ⟨-, hoTs⟩ := hoist_spineV tsa hgTm
  have hLtmaj : LeavesGr m φ d tmaj ρ := (hL.of_subset hsubT0).of_subset hsubTm
  -- each projection is graded, by the two stored entries' law
  have hprojG : ∀ j, j < 2 →
      WellDenotedV V ρ (projAV (j + env.projOff andName) ea) := by
    intro j hj
    obtain ⟨entry, hfe, -, hnP, -, hfire⟩ := hslot j hj
    rw [← ConLeche.Env.findProj?_off hfe]
    obtain ⟨-, -, -, ⟨cvTj, capsTj, hfTj, hlpsTj, -⟩, hO5j, cvCj, hfCj, hlpsCj,
      hlawj, -⟩ := hin.tower_ok andName j entry hfe
    have hcvTj : cvTj = cvT := by
      rw [hind] at hfTj
      exact (ConLeche.ConstantInfo.indInfo.inj (Option.some.inj hfTj)).1.symm
    have hlpe : entry.levelParams = cvT.levelParams := by rw [← hlpsTj, hcvTj]
    have hgj : TowerGuardAt φ entry ust := towerGuardAt_of_fireOk hO5j hfire
    obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlawj ust (by rw [hlpe]; exact hlenus2)
    have hTad := (towerEntry_tele_at_depth hfe hTa).1
    have hlenVs : tsa.length = entry.numParams := by
      rw [← hspt.length, hlen, hnP]
    have hpc : PiChain (tsa ++ [ea]).length Ta := by
      rw [List.length_append, List.length_singleton, hlenVs]
      exact piChain_of_stripPis _
        (by rw [ConLeche.projTele_stripPis]; rfl) (hTad d)
    obtain ⟨restj, hpeel⟩ := peelPis_of_piChain _ hpc
    rw [hlpe, ← hvT'] at hA
    exact (hA hgj ρ tsa ea restj hlenVs hgTm hg hmemMW hpeel).1
  have hoksF : ∀ x ∈ (tsa ++ [projAV (0 + env.projOff andName) ea,
      projAV (1 + env.projOff andName) ea]), WellDenotedV V ρ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact hoTs x hx'
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · exact hprojG 0 (by decide)
      · rcases List.mem_singleton.mp hx'' with rfl
        exact hprojG 1 (by decide)
  have hLprojTerm : ∀ j, j < 2 → LeavesGr m φ d (Expr.proj andName j major) ρ :=
    fun _ _ => LeavesGr.of_subset hL (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  have hLF : ∀ x ∈ tmaj.getAppArgs ++
      [Expr.proj andName 0 major, Expr.proj andName 1 major],
      LeavesGr m φ d x ρ := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact leavesGr_spine hLtmaj x hx'
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · exact hLprojTerm 0 (by decide)
      · rcases List.mem_singleton.mp hx'' with rfl
        exact hLprojTerm 1 (by decide)
  obtain ⟨hfitVal, -⟩ :=
    hfit ρ hρ
      (LeavesGr.of_fvarLeaves_nil
        (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfJ))
      hLF (hokTVja ρ) hoksF (by simp)
  have hgF : WellDenotedV V ρ (AnnotTerm.mkAppN
      (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
      (tsa ++ [projAV (0 + env.projOff andName) ea,
        projAV (1 + env.projOff andName) ea])) :=
    (mkAppN_of_fitA _ (hokTVja ρ)
      ⟨m.acval_wellDenoted _ _ ρ, hin.leaf_valid _ _ ρ⟩
      hoksF (hmemCj ρ) hfitVal).1
  -- the fabrication's type is the major's ("not pt" source (1): two types)
  have hLfab : LeavesGr m φ d fab ρ := hL.of_subset hsub
  obtain ⟨hgTf, hmemF⟩ := hInnerTf ρ hρ hLfab hgF
  have hneTm : interp V ρ (AnnotTerm.mkAppN vT tsa) ≠ pt := heqTm ▸ hgT0.ne_pt
  have heqT := hdt hfTm hfTf hCTm hCTf htmajaSave htfa ρ hρ hLtmaj
    (hLfab.of_subset hsubTf) hgTm hgTf.1 hneTm hgTf.ne_pt
  have hmemM : interp V ρ ea ∈ˢ interp V ρ tfa := by
    rw [← heqT, ← heqTm]; exact hmemM0
  -- one type holds both: the conditional proof irrelevance is an equation
  exact ⟨hgF, (IsTy.eq_of_ne_pt hgTf.2 hmemF hmemM
    (hpi hfF hfM hCF hCM hdF hea ρ hρ hLfab hL hgF hg)).symm⟩

end ConLeche.Model.Rules
