module

public import ConLeche.Model.Inductives.GenClsData
public import ConLeche.Model.Inductives.BlockRecLaw
import ConLeche.Model.Inductives.GenRecRules
import ConLeche.Model.Inductives.GenClsSem
import ConLeche.Model.Inductives.GenRecPreRun
import ConLeche.Model.Inductives.GenRecClasses
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.BlockData
import ConLeche.Model.Inductives.BlockCaps
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Annot.BlockLfp
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Verify.InstSpine
import ConLeche.Verify.PropWhen

public section

/-!
# The ι licence's facts at the generated recursors (task #342 L10)

`RecRuleLaw` carries, besides the fired law, the facts the ι step's
licence consumes (`RecRuleExtra`): the K law at any major, the
constructor's arity, (S) a family never `Prop` at the constructor's
levels holds no point, (P) where the major's domain holds the point
every fitting constructor application is the point, (U) at a fired
spine the conditional comparisons are equations.  `blockRecRuleLaw_gen`
derives the K law from the fired law at a witness spine
(`RecRuleKWit`); this file discharges the witness and the rest
(`RecRuleExtraNK`) at every rule of the generated stage.

The facts are all about the CLASS the major lies in — the recursor's
fit puts the major in the class's carrier at the recursor's parameters
and index tuple (`GenClsSplit`):

* at `w ≠ 0` the carrier holds only injections, none the point
  (`LfpClause.injNePt`); at `w = 0` the constructor's type is a truth
  value (every binder's bit is the family's zero-ness,
  `CtorDataI.bits`), so the constructor and every application of it is
  the point;
* the member's capability record (`blockCapsAt`) carries the family's
  sort zero-ness, which decides `w` at the constructor's levels, and
  the K bit, which makes the member's only constructor fieldless — so
  the carrier's decomposition (`blockCarrier_case`) is that constructor
  at the recursor's parameters, whose stored fit's index clause is the
  recursor's index tuple;
* the coherence of the conditional comparisons is L7's: the parameters
  are fits of one telescope of types, the indices fits of the
  component's index telescope at them (`blockRule_coherent`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun ClassGenScoped RecShape NestState BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 0. Generic facts -/

section Generic

/-- **A recorded block's sort is read off its member's type**, so two
level assignments agreeing on the member's level parameters give the
same sort. -/
theorem lfpW_congr {envC : Env} (mpC : EnvModelM V μ envC) {D : LfpDatum V}
    (hD : D ∈ mpC.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal}
    {caps : ConLeche.IndCaps} (hf : envC.find? (D.member mm) = some (.indInfo cv caps))
    {ψ₁ ψ₂ : Name → Nat} (hag : ∀ q ∈ cv.levelParams, ψ₁ q = ψ₂ q) : D.w ψ₁ = D.w ψ₂ := by
  obtain ⟨-, -, hrd, -⟩ := mpC.lfp_ok D hD
  obtain ⟨cv', caps', hf', hab⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, -⟩ : cv = cv' ∧ caps = caps' := by
    injection hf' with h'; injection h' with h1 h2; exact ⟨h1, h2⟩
  obtain ⟨ab₁, h₁, -, -⟩ := hab ψ₁
  obtain ⟨ab₂, h₂, -, -⟩ := hab ψ₂
  have hwf := mpC.base2.wf _ (ConLeche.Semantics.Env.find?_mem hf)
  rw [denoteMeta_params_ext mpC.base2 hag 0 cv.type hwf.2.1, h₂] at h₁
  have h := (mkPisAV_sort_inj (Option.some.inj h₁)).2
  exact h.symm

/-- **The ι licence, unfolded.** -/
theorem iotaCtorLicensed_inv {f : Name → Option ConstantInfo} {cvj : ConstantVal}
    {usj : List Level} (h : ConLeche.iotaCtorLicensed f cvj usj = true) :
    ∃ (T : Name) (us₀ : List Level) (cvT : ConstantVal) (caps : ConLeche.IndCaps),
      (cvj.type.piResult).getAppFn = .const T us₀ ∧ f T = some (.indInfo cvT caps) ∧
      cvT.levelParams.length = usj.length ∧
      ConLeche.capsNeverZero cvT.levelParams usj caps = true := by
  revert h
  unfold ConLeche.iotaCtorLicensed
  match hpr : (cvj.type.piResult).getAppFn with
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _ _
  | .forallE _ _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ => intro h; exact nomatch h
  | .const T us₀ =>
    dsimp only
    match hfT : f T with
    | none => intro h; exact nomatch h
    | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _)
    | some (.ctorInfo _ _ _) | some (.recInfo _ _ _ _)
    | some (.projInfo _) => intro h; exact nomatch h
    | some (.indInfo cvT caps) =>
      intro h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨T, us₀, cvT, caps, rfl, hfT, h.1, h.2⟩

/-- An application spine over a head that is not a `∀` is its own
`piResult`. -/
theorem piResult_mkAppN_of_ne : ∀ (args : List Expr) (f : Expr),
    (∀ b c d, f ≠ .forallE b c d) → (Expr.mkAppN f args).piResult = Expr.mkAppN f args
  | [], f, hf => by
    cases f with
    | forallE b c d => exact absurd rfl (hf b c d)
    | _ => rfl
  | a :: as, f, _ => piResult_mkAppN_of_ne as (.app f a) (fun _ _ _ h => nomatch h)

/-- **A syntactic telescope ending in a constant application** has that
constant at the head of its `piResult`. -/
theorem piResult_getAppFn_of_stripPis {I : Name} {us : List Level} :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {args : List Expr},
      e.stripPis n = some (bs, Expr.mkAppN (.const I us) args) →
      (e.piResult).getAppFn = .const I us
  | 0, e, bs, args, h => by
    simp only [ConLeche.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2, piResult_mkAppN_of_ne args (.const I us) (fun _ _ _ h => nomatch h), getAppFn_mkAppN_const]
  | n + 1, e, bs, args, h => by
    match e with
    | .forallE ty b m =>
      simp only [ConLeche.Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', r⟩, hr, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      show b.piResult.getAppFn = _
      exact piResult_getAppFn_of_stripPis n hr
    | .bvar _ | .sort _ | .const _ _ | .lit _ | .fvar _ _ | .app _ _ | .lam _ _ _
    | .letE _ _ _ | .proj _ _ _ => exact absurd h (by simp [ConLeche.Expr.stripPis])

/-- **A never-zero sort datum, instantiated, is never zero.** -/
theorem eval_ne_zero_of_isNever {lps : List Name} {us : List Level} {v : Level}
    (h : (Level.substPW lps us (Level.zeronessOf v)).isNever = true) (φ : Name → Nat) :
    Level.eval (Level.substFn φ lps us) v ≠ 0 := by
  have hn := ConLeche.PropWhen.isNever_iff.mp h
  have hh := ConLeche.Level.holds_substPW φ lps us (Level.zeronessOf v)
  rw [hn, ConLeche.PropWhen.holds_never, ConLeche.PropWhen.zeronessOf_sound] at hh
  intro h0
  rw [h0] at hh
  exact nomatch hh

/-- Every member's record carries the block's sort zero-ness. -/
theorem blockCapsAt_sortZ (p : BlockShape) (mi : Nat) (isRec : Bool) :
    (ConLeche.blockCapsAt p mi isRec).sortZ = Level.zeronessOf p.resSort := by
  rcases blockCapsAt_cases p mi isRec with ⟨c, -, h⟩ | h <;> rw [h]

end Generic

/-! ## 1. A member class's facts -/

section Member

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {d : BlockData V}

/-- **What a member class knows of its constructor `i`**, at every level
assignment. -/
structure GenMemAt (mpC : EnvModelM V μ envC) (d : BlockData V) (pp : BlockParts)
    (out : List (ConstantVal × TargetMajor × List Expr)) (isRec : Bool) (cvT : ConstantVal)
    (j i t : Nat) (cA : ConstantVal × Nat) : Prop where
  hcj : (d.ctorsM t)[i]? = some cA
  htd : t < d.k
  hmN : t < d.N
  hjl : i < (d.ctorsM t).length
  hM : BlockModelAt mpC.base2 d.memberNames d
  hcf : BlockCtorFacts mpC.base2 d pp.lps t i cA
  hdnP : d.nP = pp.nP
  hnPc : (ConLeche.tgtMajorsOf out j).nPc = pp.nP
  hwd : ∀ ψ, d.w ψ = Level.eval ψ pp.toBlockShape.resSort
  hparamsC : ∀ (ψ : Name → Nat) (σ : Nat → V), Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF t i ψ).take d.nP).map (·.2.2)).reverse σ
  hlenP : ∀ ψ : Name → Nat, (d.params ψ).length = d.nP
  hctorRead : ∀ ψ' : Name → Nat, denoteMeta mpC.base2.acval envC ψ' 0 cA.1.type
      = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ')
  hcaps : envC.find? (d.memberName t)
      = some (.indInfo cvT (ConLeche.blockCapsAt pp.toBlockShape t isRec))
  hlfp : d.toLfp ∈ mpC.lfpBlocks
  hlenIds : ∀ ψ : Name → Nat, (d.IdsM t ψ).length = d.nIdxAt t
  hlpsT : cvT.levelParams = cA.1.levelParams

set_option maxHeartbeats 4000000 in
/-- **A member class's facts, from the run** (`genRows3_mem`'s preamble). -/
theorem genMemAt_of
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI' : Env}
    (hdR : d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hSt : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI'
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {t : Nat} (hm : (tgtMajor out j).member = some t)
    {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA) :
    ∃ cvT, GenMemAt mpC d pp out isRec cvT j i t cA := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨-, cls, -, -, -, -, -, -, -, hMj, hgc⟩ := genRun_at R hj
  have hi' : cls < R.Ms.length := by rw [← hgc]; exact genRun_cls_lt R hj
  obtain ⟨key, M₀, nfs, hMs, -, ⟨CR⟩⟩ := genRun_class R hi'
  have hget : R.Ms.getD cls default = { M₀ with nfs := nfs } := by
    rw [List.getD_eq_getElem?_getD, hMs, Option.getD_some]
  obtain ⟨ms, hms, -, htk⟩ := genRun_member R
    (show (R.Ms.getD cls default).member = some t by rw [← hMj]; exact hm)
  rw [hget] at hMj
  have hm0 : M₀.member = some t := by rw [hMj] at hm; exact hm
  obtain ⟨hctors, hnPc⟩ := CR.major.member_facts hm0
  have hnPc' : (ConLeche.tgtMajorsOf out j).nPc = pp.nP := by
    show (tgtMajor out j).nPc = _; rw [hMj]; exact hnPc
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by rw [← tgtRs_ctors hr]; exact hcA
  have hctM : d.ctorsM t = M₀.ctors := by
    subst hdR; show ctorsAs.getD t [] = M₀.ctors
    rw [List.getD_eq_getElem?_getD, hctors]; rfl
  have hcj : (d.ctorsM t)[i]? = some cA := by
    rw [hctM]; rw [hMj] at hcAM; exact hcAM
  have htd : t < d.k := by subst hdR; exact htk
  have hdnP : d.nP = pp.nP := by subst hdR; rfl
  have hwd : ∀ ψ, d.w ψ = Level.eval ψ pp.toBlockShape.resSort := by subst hdR; intro ψ; rfl
  have hk0 : 0 < d.k := by omega
  have hmN : t < d.N := Nat.lt_of_lt_of_le htd (Nat.le_add_right _ _)
  have hjl : i < (d.ctorsM t).length := (List.getElem?_eq_some_iff.mp hcj).1
  have hM : BlockModelAt mpC.base2 d.memberNames d := by
    subst hdR; exact blockModelAt_seam h hN hSt hcore
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ htd i cA hcj
  obtain ⟨-, -, hcd, -⟩ := hcore.2.2.1 _ i cA hcj
  have hcf : BlockCtorFacts mpC.base2 d pp.lps t i cA := ⟨hfindC, hlpsC, hcd⟩
  have hctorRead : ∀ ψ' : Name → Nat, denoteMeta mpC.base2.acval envC ψ' 0 cA.1.type
      = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ') := by
    intro ψ'
    have hrd : (tgtRs out).getD j default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
    have hsel : (((tgtRs out).getD j default).2.2.2.getD i default) = cA := by
      rw [hrd, List.getD_eq_getElem?_getD, hcA]; rfl
    rw [blockRecCtorTy, hsel, hcd.read ψ']
    rfl
  have hparamsC : ∀ (ψ : Name → Nat) (σ : Nat → V), Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF t i ψ).take d.nP).map (·.2.2)).reverse σ := fun ψ σ =>
    ⟨fun hσ => ((hSt.frames _ htd i cA hcj).1 _ σ).mp (hSt.paramsOf 0 hk0 _ σ hσ _ htd),
      fun hσ => hSt.paramsOf _ htd _ σ (((hSt.frames _ htd i cA hcj).1 _ σ).mpr hσ) 0 hk0⟩
  have hlenP : ∀ ψ : Name → Nat, (d.params ψ).length = d.nP := by
    intro ψ
    have hl := hSt.lenPps 0 ψ hk0
    show (((d.ppsM 0 ψ).take d.nP).map (·.2.2)).length = d.nP
    rw [List.length_map, List.length_take]
    exact Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq hl.symm))
  obtain ⟨cvT, hcvT⟩ : ∃ cvT, cvTas[t]? = some cvT :=
    ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact htd)⟩
  obtain ⟨hfT, -, -, -⟩ := hcore.1 t cvT hcvT
  have hcaps : envC.find? (d.memberName t)
      = some (.indInfo cvT (ConLeche.blockCapsAt pp.toBlockShape t isRec)) := by
    rw [hN.1 t cvT hcvT]; exact hfT
  refine ⟨cvT, hcj, htd, hmN, hjl, hM, hcf, hdnP, hnPc', hwd, hparamsC, hlenP, hctorRead,
    hcaps, hlfp, hSt.lenIds t htd, ?_⟩
  -- the member's former carries the constructor's level parameters (`LfpCtorReads`)
  obtain ⟨-, -, -, hrdC⟩ := mpC.lfp_ok _ hlfp
  obtain ⟨cv, nPc, nF, hfc, -, hall, -⟩ := hrdC.2 t htd i hjl
  have hname : d.toLfp.ctorName t i = cA.1.name := by
    show ((d.ctorsM t).getD i default).1.name = _
    rw [List.getD_eq_getElem?_getD, hcj]; rfl
  rw [hname, hfindC] at hfc
  obtain rfl : cA.1 = cv := by injection hfc with h'; injection h' with h1
  obtain ⟨cvm, capsm, hfm, hlm⟩ := hall t htd
  have hfm' : envC.find? (d.memberName t) = some (.indInfo cvm capsm) := hfm
  rw [hcaps] at hfm'
  obtain rfl : cvT = cvm := by injection hfm' with h'; injection h' with h1
  exact hlm

set_option maxHeartbeats 4000000 in
/-- **The major lies in the member's carrier** at the recursor's
parameters and index tuple (`genRows3_mem`'s class step). -/
theorem genMem_major (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {isRec : Bool} {cvT : ConstantVal} {j i t : Nat} {cA : ConstantVal × Nat}
    (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hm : (tgtMajor out j).member = some t)
    (ψ : Name → Nat) {ρ : Nat → V} {xs : List AnnotTerm} {a restR : AnnotTerm}
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [a]) restR) :
    SpineFit ρ (d.params ψ) (((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take d.nP) ∧
    SpineFit (consList (((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take d.nP) ρ)
      (d.IdsM t ψ) ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ∧
    interp V ρ a ∈ˢ app (lfpTuple (d.w ψ) d.N
        (d.idx ψ (consList (((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take d.nP) ρ))
        (d.Φ ψ (consList (((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take d.nP) ρ)) t)
      (d.tup ψ t ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ))) := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hmS : (tgtMajor out j).member.isSome = true := by rw [hm]; rfl
  have hrt : pp.toBlockShape.recTgtAt j = t := genRun_recTgt R hj hm
  obtain ⟨hpref, hws, hxvl, hisl⟩ := genRow3_frame hμ h hr ψ hxl hfitR
  obtain ⟨hTin, hmajIn, hisT⟩ := hS ψ ρ j hj _ _ _ hxvl hisl hws
  rw [tgtClsIs_mem hmS] at hTin
  obtain ⟨hpar, -⟩ := blockRecIs_fits hTin
  rw [blockRecIs_pos hpar hpref, tgtClsTup_mem hmS] at hTin
  rw [tgtClsU_mem hmS, tgtClsNIdx_mem hmS, tgtClsTup_mem hmS, hrt] at hisT
  have hTin' := hTin
  rw [hrt] at hTin'
  obtain ⟨is', hsp', hTe⟩ := mem_idxSet_elim hTin'
  have hIok := G.hM.idxOk ψ _ (d.satOfSpine hpar) t G.hmN
  rw [hTe, ← G.hlenIds ψ, isOfW_tupW hIok hsp'] at hisT
  rw [hisT] at hsp' hTe
  refine ⟨hpar, hsp', ?_⟩
  rw [tgtClsCr_mem hmS, tgtClsTup_mem hmS] at hmajIn
  unfold blockRecCr at hmajIn
  rw [hrt] at hmajIn
  exact hmajIn

/-- **(S) at a member class**: where the member's sort is never zero at
the constructor's levels (the licence reads the member's record,
`blockCapsAt`, which carries the block's sort zero-ness), the member's
carrier at the recursor's parameters is strict, so the major is not the
point. -/
theorem genMem_S (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {isRec : Bool} {cvT : ConstantVal} {j i t : Nat} {cA : ConstantVal × Nat}
    (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hm : (tgtMajor out j).member = some t)
    {ψ : Name → Nat} {usj : List Level} {φ : Name → Nat}
    (hlv : ∀ q ∈ cA.1.levelParams, Level.substFn φ cA.1.levelParams usj q = ψ q)
    (hlic : ConLeche.iotaCtorLicensed envC.find? cA.1 usj = true)
    (ρ : Nat → V) (xs : List AnnotTerm) (a restR : AnnotTerm)
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [a]) restR) :
    interp V ρ a ≠ pt := by
  obtain ⟨T, us₀, cvT', caps, hhead, hfT, -, hnz⟩ := iotaCtorLicensed_inv hlic
  -- the constructor's family is the member
  obtain ⟨cbs, es, hres, -⟩ := G.hcf.2.2.resid
  rw [piResult_getAppFn_of_stripPis _ hres] at hhead
  obtain ⟨rfl, -⟩ := ConLeche.Expr.const.inj hhead
  rw [G.hcaps] at hfT
  obtain ⟨rfl, rfl⟩ : cvT = cvT' ∧ ConLeche.blockCapsAt pp.toBlockShape t isRec = caps := by
    injection hfT with h'; injection h' with h1 h2; exact ⟨h1, h2⟩
  unfold ConLeche.capsNeverZero at hnz
  rw [blockCapsAt_sortZ] at hnz
  have hne := eval_ne_zero_of_isNever hnz φ
  rw [G.hlpsT, ← G.hwd] at hne
  -- the member's sort at the recursor's levels
  have hc : d.w (Level.substFn φ cA.1.levelParams usj) = d.w ψ :=
    lfpW_congr mpC (D := d.toLfp) G.hlfp G.htd G.hcaps (fun q hq => by
      rw [G.hlpsT] at hq; exact hlv q hq)
  have hw : d.w ψ ≠ 0 := hc ▸ hne
  obtain ⟨hpar, hsp', hmaj⟩ := genMem_major hμ h R hS G hr hm ψ hxl hfitR
  have ht : d.tup ψ t ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ))
      ∈ˢ d.idx ψ (consList (((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take
        d.nP) ρ) t := tupW_mem hsp'
  obtain ⟨j', fs', -, heq⟩ := blockCarrier_case G.hM (d.satOfSpine hpar) G.hmN ht hmaj
  rw [heq]
  exact (mpC.lfp_ok _ G.hlfp).1.injNePt ψ hw t j' fs'

end Member

end ConLeche.Model
