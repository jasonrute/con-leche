module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Semantics.DefEqList

public section

/-!
# The soundness of the ι rule and the three stuck-major rescues (task #305)

One lemma per constructor: `Red.iota`, `Red.rescueK`, `Red.rescueEta`,
`Red.rescueAnd`; the master induction (`Sound.lean`) consumes them by
name.  The shared helpers live in `IotaSoundKit.lean`.

**These are the INTERIM UNCONDITIONAL proofs** (task #342, L9): every
lemma below is proved at the `…U` per-valuation motives
(`RedSemU`/`DefEqListSemU`, `Model/Rules/Motive.lean`), with no "not the
point" side condition.  L10 proves the ι rules at the CONDITIONAL
motives under the new licence and deletes these.

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

**`DefEqListSemU` concludes the walk's length.**  `Red.iota_sound`'s
`.nested` fire needs `pins.length = RecRule.ctorParams rl` before it
can build the comparand list's read spine at all, and the length is
needed to build the spines the motive's equation is about.
`DefEqListSemU` therefore leads with `as.length = bs.length`,
discharged in `CertsSound.lean`'s `DefEqList.nil_soundU`/`cons_soundU`.
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
/-- The ι row: the stored
recursor's fired contract (`RecRules`) at the two certified telescopes
and the parameter/index comparisons. -/
theorem Red.iota_soundU (hin : RulesInputs V m φ) {d : Nat} {e : Expr} {c : Name}
    {us : List Level} {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    {major : Expr} {cj : Name} {usj : List Level} {cvj : ConstantVal}
    {cnP cnF : Nat} {rl : RecRule} {residual : Expr}
    (hhead : e.getAppFn = .const c us)
    (hrec : env.find? c = some (.recInfo cv mI rP rules))
    (hlen : e.getAppArgs.length = mI + 1)
    (hus : us.length = cv.levelParams.length)
    (hmajor : RedSemU m φ d (e.getAppArgs.getD mI (.bvar 0)) major)
    (hmhead : major.getAppFn = .const cj usj)
    (hctor : env.find? cj = some (.ctorInfo cvj cnP cnF))
    (hrule : rules.find? (fun r' => r'.ctor == cj) = some rl)
    (hmlen : major.getAppArgs.length = rl.ctorParams + rl.nfields)
    (hfire : rl.fire ≠ .inert)
    (hlv : Level.isEquivList usj
      (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
        e.getAppArgs rP).1 = some true)
    (hparams : rl.compareParams = true →
      DefEqListSemU m φ d (major.getAppArgs.take rl.ctorParams)
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).2)
    (hcertR : CertsSem m φ d true (cv.type.instantiateLevelParams cv.levelParams us)
      (e.getAppArgs.take mI ++ [major]))
    (hcertC : CertsSem m φ d true
      (cvj.type.instantiateLevelParams cvj.levelParams usj) major.getAppArgs)
    (hres : mI ≠ rP →
      ConLeche.piResidual (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs = some residual)
    (hidx : mI ≠ rP →
      DefEqListSemU m φ d (residual.getAppArgs.drop rl.ctorParams)
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
  -- **the law**, and the fired right-hand side's reading at every depth
  obtain ⟨hrPle, hlaw0⟩ := hin.rec_rules c cv mI rP rules hrec rl hrmem hfire
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
  -- the prepared major: read and in slot position
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
  -- **the two licensed fits**, called structurally; their per-ρ fits are
  -- extracted once we are inside the per-valuation closure
  have hspR : DenoteMetaSpine m.acval env φ d (e.getAppArgs.take mI ++ [major])
      (xs.take mI ++ [AnnotTerm.mkAppN
        (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys]) :=
    (hspx.take mI).append (DenoteMetaSpine.cons hvmajSave DenoteMetaSpine.nil)
  have hframesR : ∀ x ∈ e.getAppArgs.take mI ++ [major],
      Frame d x ∧ CtxOkS m φ d Δa x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact hfrE x (List.mem_of_mem_take hx')
    · rcases List.mem_singleton.mp hx' with rfl
      exact ⟨hfmj, hCmj⟩
  obtain ⟨restR, hfitR⟩ :=
    hcertR (fa := m.acval c (Level.substFn φ cv.levelParams us))
      hfR hCR (hTVaD d) hframesR hspR
  obtain ⟨restC, hfitC⟩ :=
    hcertC (fa := m.acval rl.ctor (Level.substFn φ cvj.levelParams usj))
      hfJ hCJ (hTVjaD d) hfrC hspy
  -- the level congruence (currency-free: the comparand reads no arguments)
  have hψ : Level.substFn φ cvj.levelParams usj
      = Level.substFn φ cvj.levelParams
          (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
            [] rP).1 := by
    rw [recFireComparands_fst_nil] at hlv
    exact ConLeche.Level.substFn_congr (ConLeche.Level.isEquivList_sound hlv φ)
  -- the fired equation and the transported grading, at the one valuation
  have hmain : ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d e ρ →
      WellDenotedV V ρ (AnnotTerm.mkAppN
          (m.acval c (Level.substFn φ cv.levelParams us)) xs) →
      interp V ρ (AnnotTerm.mkAppN
          (m.acval c (Level.substFn φ cv.levelParams us)) xs)
          = interp V ρ (AnnotTerm.mkAppN Ra
              (xs.take rP ++ ys.drop (RecRule.ctorParams rl))) ∧
        WellDenotedV V ρ (AnnotTerm.mkAppN Ra
          (xs.take rP ++ ys.drop (RecRule.ctorParams rl))) := by
    intro ρ hρ hL hg
    obtain ⟨-, hoX⟩ := hoist_spineV xs hg
    have hLmajSlot : LeavesGr m φ d (e.getAppArgs.getD mI (.bvar 0)) ρ :=
      leavesGr_spine hL _ (ConLeche.getD_mem hmIlt)
    have hokMajArg : WellDenotedV V ρ (xs.getD mI default) :=
      hoX _ (ConLeche.getD_mem (by rw [← hspx.length]; exact hmIlt))
    obtain ⟨hokMj, heqAll⟩ := hInnerMaj ρ hρ hLmajSlot hokMajArg
    have hLmj : LeavesGr m φ d major ρ := hLmajSlot.of_subset hsubmj
    obtain ⟨-, hoY⟩ := hoist_spineV ys hokMj
    have hLargsR : ∀ x ∈ e.getAppArgs.take mI ++ [major],
        LeavesGr m φ d x ρ := by
      intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact leavesGr_spine hL x (List.mem_of_mem_take hx')
      · rcases List.mem_singleton.mp hx' with rfl; exact hLmj
    have hoksR : ∀ x ∈ (xs.take mI ++ [AnnotTerm.mkAppN
        (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys]),
        WellDenotedV V ρ x := by
      intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hoX x (List.mem_of_mem_take hx')
      · rcases List.mem_singleton.mp hx' with rfl; exact hokMj
    have hokSR : WellDenotedV V ρ (AnnotTerm.mkAppN
        (m.acval c (Level.substFn φ cv.levelParams us))
        (xs.take mI ++ [AnnotTerm.mkAppN
          (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys])) := by
      rw [take_getD_splitAK hxsLen] at hg
      exact wellDenotedV_mkAppN_snoc_congrK hg hokMj heqAll
    obtain ⟨hfitRVal, -⟩ :=
      hfitR ρ hρ
        (LeavesGr.of_fvarLeaves_nil
          (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfR))
        hLargsR (hokTVa ρ) hoksR (fun _ => ⟨hokSR, hmemR ρ⟩)
    have hLargsC : ∀ x ∈ major.getAppArgs, LeavesGr m φ d x ρ :=
      leavesGr_spine hLmj
    obtain ⟨hfitCVal, hokRestC⟩ :=
      hfitC ρ hρ
        (LeavesGr.of_fvarLeaves_nil
          (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfJ))
        hLargsC (hokTVja ρ) hoY (fun _ => ⟨hokMj, hmemJ ρ⟩)
    -- **the index pin**: trivial where the recursor has no indices,
    -- else the constructor telescope's residual against the indices
    have hpinI : IotaIndexPin (V := V) ρ restC (RecRule.ctorParams rl) mI rP
        (xs.take mI) := by
      by_cases hmr : mI = rP
      · exact ⟨restC, [], rfl, Or.inl hmr, fun i hi => absurd hi (by omega)⟩
      have hpres := hres hmr
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
          (hTVjaD d) hspy hfitCVal
      rw [show residual = Expr.mkAppN residual.getAppFn residual.getAppArgs from
        (ConLeche.Expr.mkAppN_getApp residual).symm] at hresC
      obtain ⟨Ha, cargsa, -, hspRes, hCeq⟩ := denoteMeta_mkAppN_inv hresC
      have hRcA : WellDenotedV V ρ (AnnotTerm.mkAppN Ha cargsa) := hCeq ▸ hokRestC
      obtain ⟨-, hoCargs⟩ := hoist_spineV cargsa hRcA
      have hspIdx : DenoteMetaSpine m.acval env φ d ((e.getAppArgs.take mI).drop rP)
          ((xs.take mI).drop rP) := (hspx.take mI).drop rP
      have hmapI : (cargsa.drop (RecRule.ctorParams rl)).map (interp V ρ)
          = ((xs.take mI).drop rP).map (interp V ρ) :=
        (hidx hmr).2
          (fun x hx => hfrRes x (List.mem_of_mem_drop hx))
          (fun x hx => hfrE x (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
          (hspRes.drop _) hspIdx ρ hρ
          (fun x hx => leavesGr_spine hLRes x (List.mem_of_mem_drop hx))
          (fun x hx => leavesGr_spine hL x
            (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
          (fun x hx => hoCargs x (List.mem_of_mem_drop hx))
          (fun x hx => hoX x (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
      have hlenDisj : mI = rP ∨
          cargsa.length = RecRule.ctorParams rl + (mI - rP) := by
        have hlen2 := congrArg List.length hmapI
        simp only [List.length_map, List.length_drop, List.length_take] at hlen2
        rw [hxsLen] at hlen2
        omega
      refine ⟨Ha, cargsa, hCeq, hlenDisj, fun i hi => ?_⟩
      have hlt : i < (cargsa.drop (RecRule.ctorParams rl)).length := by
        rw [List.length_drop]
        rcases hlenDisj with hh | hh <;> omega
      have hgi := map_interp_getD_eqK hmapI hlt
      rw [getD_dropAK, getD_dropAK] at hgi
      exact hgi
    -- the `.plain` comparands
    have hplain : RecRule.paramsBlind rl = false → RecRule.fire rl = .plain →
        ∀ i, i < RecRule.ctorParams rl → i < mI →
          interp V ρ (ys.getD i default)
            = interp V ρ ((xs.take mI).getD i default) := by
      intro hpb hp i hi him
      have hdefP' : DefEqListSemU m φ d
          (major.getAppArgs.take (RecRule.ctorParams rl))
          (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
            e.getAppArgs rP).2 :=
        hparams (RecRule.compareParams_plain hp hpb)
      rw [show (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).2 = e.getAppArgs.take (RecRule.ctorParams rl) from by
        unfold ConLeche.recFireComparands; rw [hp]] at hdefP'
      have hmapP := hdefP'.2
        (fun x hx => hfrC x (List.mem_of_mem_take hx))
        (fun x hx => hfrE x (List.mem_of_mem_take hx))
        (hspy.take _) (hspx.take _) ρ hρ
        (fun x hx => leavesGr_spine hLmj x (List.mem_of_mem_take hx))
        (fun x hx => leavesGr_spine hL x (List.mem_of_mem_take hx))
        (fun x hx => hoY x (List.mem_of_mem_take hx))
        (fun x hx => hoX x (List.mem_of_mem_take hx))
      have hlt : i < (ys.take (RecRule.ctorParams rl)).length := by
        rw [List.length_take, ← hspy.length, hmlen]; omega
      have hgi := map_interp_getD_eqK hmapP hlt
      rw [getD_takeAK hi, getD_takeAK hi] at hgi
      rw [getD_takeAK him]
      exact hgi
    -- the `.nested` pins
    have hnested : ∀ lvls pins, RecRule.fire rl = .nested lvls pins →
        ∀ i, i < RecRule.ctorParams rl →
        ∀ vpa : AnnotTerm,
          denoteMeta m.acval env φ rP (ConLeche.Verify.openRev 0 rP
            ((pins.getD i default).instantiateLevelParams cv.levelParams us))
            = some vpa →
          interp V ρ (ys.getD i default)
            = interp V ρ (AnnotTerm.instRevChain ((xs.take mI).take rP) vpa) := by
      intro lvls pins hn i hi vpa hvpa
      have hdefP' : DefEqListSemU m φ d
          (major.getAppArgs.take (RecRule.ctorParams rl))
          (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
            e.getAppArgs rP).2 :=
        hparams (RecRule.compareParams_nested hn)
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
      -- The stored pin list's length is the walk's own, which
      -- `DefEqListSemU` concludes (`Motive.lean`'s first conjunct).
      -- Both directions are needed here: `pins.length ≤ ctorParams`
      -- to build the comparand list's read spine at all (the law
      -- reads the pins only below `ctorParams`), and
      -- `ctorParams ≤ pins.length` to select the `i`-th comparand.
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
      -- the comparand's LEAVES, graded at this ρ off the recursor's
      -- own prefix (the pin itself is closed)
      have hLComp : ∀ (p : Expr), p ∈ pins →
          LeavesGr m φ d (Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
            (p.instantiateLevelParams cv.levelParams us)) ρ := by
        intro p hp l hl tya hden
        rcases ConLeche.fvarLeaves_instSpine _ hl with hl' | ⟨y, hy, hly⟩
        · exact absurd hl' (by
            rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar (hpinF' p hp)]; simp)
        · exact leavesGr_spine hL y (List.mem_of_mem_take hy) l hly tya hden
      -- each comparand reads, to the pin's open reading chained along
      -- the recursor's parameter prefix
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
        obtain ⟨mid, hmid⟩ := hfitRVal.take rP
        rw [List.take_append_of_le_length (by
              rw [List.length_take, hxsLen]; omega),
            List.take_take, Nat.min_eq_left hrPle] at hmid
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
      have hgB : ∀ x ∈ bsa, WellDenotedV V ρ x := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := mem_getD_index hx
        have hlenB : pins.length = bsa.length := by
          have := hspB.length
          simpa using this
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
      have hmapN := hdefP'.2
        (fun x hx => hfrC x (List.mem_of_mem_take hx))
        (fun x hx => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
          exact hfrPin p hp)
        (hspy.take _) hspB ρ hρ
        (fun x hx => leavesGr_spine hLmj x (List.mem_of_mem_take hx))
        hLb2
        (fun x hx => hoY x (List.mem_of_mem_take hx)) hgB
      have hlt : i < (ys.take (RecRule.ctorParams rl)).length := by
        rw [List.length_take, ← hspy.length, hmlen]; omega
      have hgi := map_interp_getD_eqK hmapN hlt
      rw [getD_takeAK hi] at hgi
      -- the `i`-th comparand's reading is the chained pin
      have hiB := hspB.getD (default : Expr) i (by
        simp only [List.length_map]; omega)
      rw [hgetB i (by omega), hvpa] at hiB
      simp only [Option.map_some, Option.some.injEq] at hiB
      rw [List.take_take, Nat.min_eq_left hrPle]
      rw [hgi, ← hiB]
    -- fire the law
    obtain ⟨heqLaw, htrans⟩ := hlaw cvj cnP cnF hctor usj ρ (xs.take mI) ys
      TVa TVja restR restC
      (by rw [List.length_take, hxsLen]; omega)
      (by rw [← hspy.length, hmlen])
      hlenUj hψ hplain hnested hpinI (hTVaD 0) (hTVjaD 0)
      hfitRVal hfitCVal
    rw [List.take_take, Nat.min_eq_left hrPle] at heqLaw htrans
    have hsubj : interp V ρ (AnnotTerm.mkAppN
        (m.acval c (Level.substFn φ cv.levelParams us)) xs)
        = interp V ρ (AnnotTerm.mkAppN
          (m.acval c (Level.substFn φ cv.levelParams us))
          (xs.take mI ++ [AnnotTerm.mkAppN
            (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys])) := by
      refine interp_mkAppN_congrK xs _ rfl ?_
      have hsplit : xs.map (interp V ρ)
          = (xs.take mI ++ [xs.getD mI default]).map (interp V ρ) := by
        rw [← take_getD_splitAK hxsLen]
      rw [hsplit, List.map_append, List.map_append]
      simp only [List.map_cons, List.map_nil, heqAll]
      rfl
    exact ⟨hsubj.trans heqLaw,
      htrans (fun a ha => hoX a (List.mem_of_mem_take ha))
        (fun b hb2 => hoY b hb2)⟩
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
  · have h := hmain ρ hρ hL hg
    exact ⟨h.2, h.1⟩

set_option linter.unusedVariables false in
/-- The K rescue: the fabrication reads and is
graded by the certified constructor telescope (`CertsSem`), and
proof irrelevance equates it to the major.

Several of the rule's premises are consumed by the BRIDGE and not by
the semantics: the recursor's storage, the K flag, the constructor's
result family (`hres`/`hind`), the parameter count and the two
type-check certificates `htf`/`hdt` are what makes the checker take
this branch and build `proofIrrel`'s argument; at the motive the whole
of that argument is the `DefEq fab major` premise.  Hence the linter
option. -/
theorem Red.rescueK_soundU (hin : RulesInputs V m φ) {d : Nat}
    {major tm tmaj fab tf : Expr} {recName : Name} {cv : ConstantVal}
    {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat} {T : Name}
    {tus ust : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (hrec : env.find? recName = some (.recInfo cv mI rP [rl]))
    (hk : rl.k = true)
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hres : (cvj.type.piResult).getAppFn = .const T tus)
    (hind : env.find? T = some (.indInfo cvT caps))
    (htm : InferSemIO m φ d major tm) (htmaj : RedSemU m φ d tm tmaj)
    (hthead : tmaj.getAppFn = .const T ust)
    (hlv : cvj.levelParams.length = ust.length)
    (hnP : cnP ≤ tmaj.getAppArgs.length)
    (hfab : fab = Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP))
    (hws : fab.wscopedB d = true) (hb : fab.looseBVarsBounded 0 = true)
    (hlv' : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (hcerts : CertsSem m φ d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (tmaj.getAppArgs.take cnP))
    (htf : InferSemIO m φ d fab tf) (hdt : DefEqSemU m φ d tmaj tf)
    (hpi : DefEqSemU m φ d fab major) :
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
  refine ⟨hfF, hsub, _, hdF, fun ρ hρ hL hg => ?_⟩
  have hLfab : LeavesGr m φ d fab ρ := hL.of_subset hsub
  -- per-ρ: the io type grading, transported along the reduction
  obtain ⟨hgT0, -⟩ := hInnerTm0 ρ hρ hL hg
  obtain ⟨hgTm, -⟩ := hInnerTmaj ρ hρ (hL.of_subset hsubT0) hgT0.1
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
  -- proof irrelevance identifies the fabrication with the major
  exact ⟨hgF, (hpi hfF hfM hCF hCM hdF hea ρ hρ hLfab hL hgF hg).symm⟩

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
two stored entries' typing law (`TowerOk`); the `DefEq fab major`
premise carries the proof-irrelevance identification. -/
theorem Red.rescueAnd_soundU (hin : RulesInputs V m φ) {d : Nat}
    {major tm tmaj fab tf : Expr} {recName : Name} {cv : ConstantVal}
    {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat}
    {tus ust : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (hrec : env.find? recName = some (.recInfo cv mI rP [rl]))
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hres : (cvj.type.piResult).getAppFn = .const andName tus)
    (hind : env.find? andName = some (.indInfo cvT caps))
    (htm : InferSemIO m φ d major tm) (htmaj : RedSemU m φ d tm tmaj)
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
    (htf : InferSemIO m φ d fab tf) (hdt : DefEqSemU m φ d tmaj tf)
    (hpi : DefEqSemU m φ d fab major) :
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
  refine ⟨hfF, hsub, _, hdF, fun ρ hρ hL hg => ?_⟩
  obtain ⟨hgT0, hmemM0⟩ := hInnerTm0 ρ hρ hL hg
  obtain ⟨hgTm, heqTm⟩ := hInnerTmaj ρ hρ (hL.of_subset hsubT0) hgT0.1
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
  exact ⟨hgF, (hpi hfF hfM hCF hCM hdF hea ρ hρ (hL.of_subset hsub) hL hgF hg).symm⟩

end ConLeche.Model.Rules
