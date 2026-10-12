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
import ConLeche.Model.Rules.DefEqSoundKit
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

/-- **Above `Prop` the member's carrier holds no point**: the major is an
injection (`blockCarrier_case`), and no injection is the point there. -/
theorem genMem_ne_pt (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {isRec : Bool} {cvT : ConstantVal} {j i t : Nat} {cA : ConstantVal × Nat}
    (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hm : (tgtMajor out j).member = some t)
    {ψ : Name → Nat} (hw : d.w ψ ≠ 0)
    (ρ : Nat → V) (xs : List AnnotTerm) (a restR : AnnotTerm)
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [a]) restR) :
    interp V ρ a ≠ pt := by
  obtain ⟨hpar, hsp', hmaj⟩ := genMem_major hμ h R hS G hr hm ψ hxl hfitR
  have ht : d.tup ψ t ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ))
      ∈ˢ d.idx ψ (consList (((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take
        d.nP) ρ) t := tupW_mem hsp'
  obtain ⟨j', fs', -, heq⟩ := blockCarrier_case G.hM (d.satOfSpine hpar) G.hmN ht hmaj
  rw [heq]
  exact (mpC.lfp_ok _ G.hlfp).1.injNePt ψ hw t j' fs'

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
  exact genMem_ne_pt hμ h R hS G hr hm (hc ▸ hne) ρ xs a restR hxl hfitR

/-- **At a `Prop` valuation of a member, its constructor is the point**,
and so is every application of it: every binder of the constructor's
type carries the family's zero-ness (`CtorDataI.bits`), so the type is
a truth value; a constructor with no binder at all lies in the
member's fibre, whose elements are injections, all the point. -/
theorem genMemCtor_pt {isRec : Bool} {cvT : ConstantVal} {j i t : Nat}
    {cA : ConstantVal × Nat} (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {ψj : Name → Nat} (hw : d.w ψj = 0) (ρ : Nat → V) (ys : List AnnotTerm) :
    interp V ρ (AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys) = pt := by
  refine Rules.interp_mkAppN_pt ?_ ys
  have hcd := G.hcf.2.2
  have hmem := mpC.mem_type _ (ConLeche.Semantics.Env.find?_mem G.hcf.1) ψj _ (hcd.read ψj) ρ
  change interp V ρ (mpC.base2.acval cA.1.name ψj) ∈ˢ _ at hmem
  cases hds : d.dsF t i ψj with
  | cons dd ds =>
    rw [hds] at hmem
    have hb : dd.2.1 = 0 := (hcd.bits ψj dd (by rw [hds]; exact List.mem_cons_self)).mp hw
    change interp V ρ (mpC.base2.acval cA.1.name ψj)
      ∈ˢ interp V ρ (.pi dd.1 dd.2.1 dd.2.2 (mkPisAV ds _)) at hmem
    rw [interp_pi, hb, piR_zero] at hmem
    exact eq_pt_of_mem_truthVal hmem
  | nil =>
    rw [hds] at hmem
    have hlen := hcd.len ψj
    rw [hds, List.length_nil] at hlen
    have hnP0 : d.nP = 0 := by omega
    have hnF0 : cA.2 = 0 := by omega
    -- the body is the member at the result index readings
    have hpar : d.params ψj = [] := List.eq_nil_of_length_eq_zero (by rw [G.hlenP, hnP0])
    have hsat : Sat V (d.params ψj).reverse ρ := by rw [hpar]; exact Sat_nil V ρ
    have hFssD : (d.Fss t ψj).getD i [] = ((d.dsF t i ψj).drop d.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD G.hcj
    have hFss : (d.Fss t ψj).getD i [] = [] := by rw [hFssD, hds]; simp
    have hfit0 : SpineFit ρ ((d.Fss t ψj).getD i []) [] := by rw [hFss]; trivial
    have hres := G.hM.resIdxFit ψj ρ hsat t G.hmN i G.hjl [] hfit0
    have hEssD : (d.Ess t ψj).getD i [] = d.esF t i ψj := essOfR_fixCtorDataList_getD G.hcj
    rw [hEssD] at hres
    have hleaf := G.hM.leaf t G.htd ψj ρ [] _ (by rw [hpar]; trivial) hres
    simp only [consList_nil, List.nil_append] at hleaf
    have hbody : interp V ρ (ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψj (d.esF t i ψj))
        = ((d.esF t i ψj).map (interp V ρ)).foldl SetTheory.app
            (interp V ρ (mpC.base2.acval (d.memberName t) ψj)) := by
      rw [ctorBodyAVI, hnP0, interp_mkAppN_foldl]
      simp [paramBvars]
    change interp V ρ (mpC.base2.acval cA.1.name ψj)
      ∈ˢ interp V ρ (ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψj (d.esF t i ψj)) at hmem
    rw [hbody, hleaf] at hmem
    have ht : d.tup ψj t ((d.esF t i ψj).map (interp V ρ)) ∈ˢ d.idx ψj ρ t := by
      have := tupW_mem (u := d.uM t ψj) hres
      simp only [consList_nil] at this
      exact this
    obtain ⟨j', fs', -, heq⟩ := blockCarrier_case G.hM (ρp := ρ) hsat G.hmN ht (by
      simpa [consList_nil] using hmem)
    rw [heq]
    exact G.hM.mkZero ψj hw t j' fs'

/-- **(P) at a member class**: where the major's domain holds the point
the member is `Prop` at the recursor's levels (above it the carrier holds
no point), hence at the constructor's, and every application of the
constructor is the point. -/
theorem genMem_P (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {isRec : Bool} {cvT : ConstantVal} {j i t : Nat} {cA : ConstantVal × Nat}
    (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hm : (tgtMajor out j).member = some t)
    {ψ ψj : Name → Nat} (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    (ρ : Nat → V) (xs : List AnnotTerm) (a restR : AnnotTerm)
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [a]) restR)
    (hapt : interp V ρ a = pt) (ys : List AnnotTerm) :
    interp V ρ (AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys) = pt := by
  have hw : d.w ψ = 0 := by
    refine Classical.byContradiction fun hw => ?_
    exact genMem_ne_pt hμ h R hS G hr hm hw ρ xs a restR hxl hfitR hapt
  have hc : d.w ψj = d.w ψ :=
    lfpW_congr mpC (D := d.toLfp) G.hlfp G.htd G.hcaps (fun q hq => by
      rw [G.hlpsT] at hq; exact hlv q hq)
  exact genMemCtor_pt G (hc.trans hw) ρ ys

/-- **The constructor residual's index arguments** (`blockRuleIdxPin_run`'s
decomposition, forwards): a spelling of the residual of a fit of the
constructor's type as an application whose arguments are the parameters
and indices names, at each index position, the constructor's own result
index reading at the fired spine. -/
theorem genMem_residual {isRec : Bool} {cvT : ConstantVal} {j i t : Nat}
    {cA : ConstantVal × Nat} (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {ψ ψj : Name → Nat} (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    {ρ : Nat → V} {ys : List AnnotTerm} {restC : AnnotTerm}
    (hys : ys.length = d.nP + cA.2)
    (hfitC : TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj) ys restC)
    {Ha : AnnotTerm} {cargsa : List AnnotTerm} (hrestEq : restC = AnnotTerm.mkAppN Ha cargsa)
    (hcarLen : cargsa.length = d.nP + (d.esF t i ψ).length) :
    ∀ q, q < (d.esF t i ψ).length →
      interp V ρ (cargsa.getD (d.nP + q) default)
        = interp V (consList (ys.map (interp V ρ)) ρ) ((d.esF t i ψ).getD q default) := by
  have hD := G.hcf.2.2
  have hct : blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj
      = mkPisAV (d.dsF t i ψj)
          (ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψj (d.esF t i ψj)) :=
    Option.some.inj ((G.hctorRead ψj).symm.trans (hD.read ψj))
  rw [hct] at hfitC
  have hes : d.esF t i ψj = d.esF t i ψ := (hD.params ψj ψ hlv).2
  have hteleC := piTeleAV_mkPisAV (d.dsF t i ψj)
    (ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψj (d.esF t i ψj))
  rw [hD.len ψj] at hteleC
  have hrest := teleFitPA_rest_eq (d.nP + cA.2) hteleC (by rw [hys]) hfitC
  have hrest2 : AnnotTerm.mkAppN Ha cargsa
      = AnnotTerm.mkAppN
          (ConLeche.Model.AnnotTerm.instSeq ys (d.nP + cA.2 - 1)
            (mpC.base2.acval (d.memberName t) ψj))
          ((paramBvars d.nP cA.2 ++ d.esF t i ψj).map
            (ConLeche.Model.AnnotTerm.instSeq ys (d.nP + cA.2 - 1))) := by
    rw [← hrestEq, hrest]
    unfold ctorBodyAVI
    rw [instSeqAV_mkAppN]
  obtain ⟨-, hcargs⟩ := AnnotTerm.mkAppN_inj hrest2
    (by rw [hcarLen, List.length_map, List.length_append, paramBvars, List.length_map,
      List.length_range, hes])
  intro q hq
  have hqj : q < (d.esF t i ψj).length := by rw [hes]; exact hq
  have hcel : cargsa.getD (d.nP + q) default
      = ConLeche.Model.AnnotTerm.instSeq ys (d.nP + cA.2 - 1) ((d.esF t i ψj).getD q default) := by
    have hq' := congrArg (fun l => l[d.nP + q]?) hcargs
    simp only [List.getElem?_map,
      List.getElem?_append_right
        (show (paramBvars d.nP cA.2).length ≤ d.nP + q by
          rw [paramBvars, List.length_map, List.length_range]; omega),
      show (paramBvars d.nP cA.2).length = d.nP from by
        rw [paramBvars, List.length_map, List.length_range],
      Nat.add_sub_cancel_left] at hq'
    rw [List.getD_eq_getElem?_getD, hq', List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hqj, Option.map_some, Option.getD_some, Option.getD_some]
  rw [hcel, show d.nP + cA.2 - 1 = ys.length - 1 from by rw [hys], interp_instSeq, hes]
  unfold chain
  rw [consN_eq_consList]

omit [SetTheory V] in
theorem getD_take' {α : Type _} {l : List α} {n q : Nat} {x : α} (hq : q < n) :
    (l.take n).getD q x = l.getD q x := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hq]

omit [SetTheory V] in
theorem getD_drop' {α : Type _} {l : List α} {n q : Nat} {x : α} :
    (l.drop n).getD q x = l.getD (n + q) x := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- A mapped spine's `getD` at a position in range. -/
theorem getD_map_pt {f : AnnotTerm → V} :
    ∀ {l : List AnnotTerm} {q : Nat}, q < l.length →
      (l.map f).getD q pt = f (l.getD q default) := by
  intro l q hq
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hq,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  rfl

set_option maxHeartbeats 4000000 in
/-- **(U)'s index pin at a member class** (L7's coherence): where the
fired constructor application is the point, the step compared the
parameters and the indices, each conditionally; the parameters are fits
of the constructor's parameter telescope (a telescope of types), so
they are equal, and the indices are then fits of the member's index
telescope at the same parameters, so they are equal too. -/
theorem genMem_U (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {isRec : Bool} {cvT : ConstantVal} {j i t : Nat} {cA : ConstantVal × Nat}
    (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hm : (tgtMajor out j).member = some t)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt j)
    {ψ ψj : Name → Nat} (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    {ρ : Nat → V} {xs ys : List AnnotTerm} {restR restC : AnnotTerm}
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j) (hyl : ys.length = pp.nP + cA.2)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys]) restR)
    (hfitC : TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj) ys restC)
    (hP : ∀ q, q < pp.nP → interp V ρ (ys.getD q default) ≠ pt →
      interp V ρ (xs.getD q default) ≠ pt →
      interp V ρ (ys.getD q default) = interp V ρ (xs.getD q default))
    (hpinC : IotaIndexPinC (V := V) ρ restC pp.nP (pp.toBlockShape.majorIdxAt j)
      (pp.toBlockShape.rulePrefixAt j) xs) :
    IotaIndexPin (V := V) ρ restC pp.nP (pp.toBlockShape.majorIdxAt j)
      (pp.toBlockShape.rulePrefixAt j) xs := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hrPle := blockRecHrPle (p := pp) h hj
  have hys : ys.length = d.nP + cA.2 := by rw [hyl, G.hdnP]
  have hnP' : d.nP ≤ pp.toBlockShape.rulePrefixAt j := by rw [G.hdnP]; exact hnP
  obtain ⟨hqs, hfq⟩ := blockRuleCtorFit_run G.hcj G.hcf hlv (G.hlenP ψ) (G.hparamsC ψ) hys
    (G.hctorRead ψj) hfitC
  obtain ⟨hpar, hsp', -⟩ := genMem_major hμ h R hS G hr hm ψ hxl hfitR
  have hpsV : ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take d.nP
      = (xs.take d.nP).map (interp V ρ) := by
    rw [← List.map_take, List.take_take, Nat.min_eq_left hnP']
  rw [hpsV] at hpar hsp'
  -- the parameters, in the constructor's own parameter telescope (a telescope of types)
  have hD := G.hcf.2.2
  have hlenD : (((d.dsF t i ψ).take d.nP).map (·.2.2)).length = d.nP := by
    rw [List.length_map, List.length_take, hD.len ψ]; omega
  have hTy : SpineTy ρ (((d.dsF t i ψ).take d.nP).map (·.2.2)) := by
    have := (spineTy_of_wellDenoted_mkPisAV (hD.okTy ψ ρ).1.1).take d.nP
    rwa [← List.map_take] at this
  have hlenPs := G.hlenP ψ
  have hq' := (spineFit_iff_of_sat_iff (by rw [hlenPs, hlenD]) (G.hparamsC ψ) ρ _
    (by rw [hqs.length_eq])).mp hqs
  have hp' := (spineFit_iff_of_sat_iff (by rw [hlenPs, hlenD]) (G.hparamsC ψ) ρ _
    (by rw [hpar.length_eq])).mp hpar
  have hxlP : d.nP ≤ xs.length := by rw [hxl]; omega
  have heqP : (ys.take d.nP).map (interp V ρ) = (xs.take d.nP).map (interp V ρ) := by
    refine spineFit_eq_of_cond_getD hTy hq' hp' fun q hq h1 h2 => ?_
    rw [hlenD] at hq
    have hqy : q < (ys.take d.nP).length := by rw [List.length_take]; omega
    have hqx : q < (xs.take d.nP).length := by rw [List.length_take]; omega
    rw [getD_map_pt hqy] at h1 ⊢
    rw [getD_map_pt hqx] at h2 ⊢
    simp only [getD_take' hq] at h1 h2 ⊢
    exact hP q (by rw [← G.hdnP]; exact hq) h1 h2
  -- the indices, in the member's index telescope at those parameters
  have hE := G.hM.resIdxFit ψ _ (d.satOfSpine hqs) t G.hmN i G.hjl _ hfq
  rw [heqP] at hE
  have hTI : SpineTy (consList ((xs.take d.nP).map (interp V ρ)) ρ) (d.IdsM t ψ) :=
    (G.hM.idxOk ψ _ (d.satOfSpine hpar) t G.hmN).1.spineTy
  have hEssD : (d.Ess t ψ).getD i [] = d.esF t i ψ := essOfR_fixCtorDataList_getD G.hcj
  rw [hEssD] at hE
  have hframe : consList ((ys.drop d.nP).map (interp V ρ))
      (consList ((xs.take d.nP).map (interp V ρ)) ρ)
      = consList (ys.map (interp V ρ)) ρ := by
    rw [← heqP, ← consList_append, ← List.map_append, List.take_append_drop]
  rw [hframe] at hE
  have hlenE : (d.esF t i ψ).length
      = pp.toBlockShape.majorIdxAt j - pp.toBlockShape.rulePrefixAt j := by
    have h1 := hE.length_eq
    have h2 := hsp'.length_eq
    rw [List.length_map] at h1
    rw [List.length_map, List.length_drop, hxl] at h2
    omega
  obtain ⟨Ha, cargsa, hrestEq, hcarLen, hcar⟩ := hpinC
  refine ⟨Ha, cargsa, hrestEq, hcarLen, fun q hq => ?_⟩
  have hcarLen' : cargsa.length = d.nP + (d.esF t i ψ).length := by
    rcases hcarLen with hc | hc
    · omega
    · rw [hc, hlenE, G.hdnP]
  have hres := genMem_residual G hlv hys hfitC hrestEq hcarLen'
  have heqI : (d.esF t i ψ).map (interp V (consList (ys.map (interp V ρ)) ρ))
      = (xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ) := by
    refine spineFit_eq_of_cond_getD hTI hE hsp' fun l hl h1 h2 => ?_
    have hlE : l < (d.esF t i ψ).length := by
      rw [← List.length_map (f := interp V (consList (ys.map (interp V ρ)) ρ)), hE.length_eq]
      exact hl
    have hlX : l < (xs.drop (pp.toBlockShape.rulePrefixAt j)).length := by
      rw [List.length_drop, hxl]; omega
    rw [getD_map_pt hlE] at h1 ⊢
    rw [getD_map_pt hlX] at h2 ⊢
    rw [getD_drop'] at h2 ⊢
    rw [← hres l hlE] at h1 ⊢
    rw [G.hdnP] at h1 ⊢
    exact hcar l (by omega) h1 h2
  have hq' : q < (d.esF t i ψ).length := by rw [hlenE]; exact hq
  have hl := congrArg (fun l => l.getD q pt) heqI
  rw [getD_map_pt hq', getD_map_pt (by rw [List.length_drop, hxl]; omega), getD_drop',
    ← hres q hq'] at hl
  rw [← G.hdnP]
  exact hl

end Member

end ConLeche.Model
