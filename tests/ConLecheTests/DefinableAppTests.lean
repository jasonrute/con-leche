module

public import ConLeche.SetTheory.Derive.Rec
public import ConLeche.SetTheory.Derive.Quot
public import ConLeche.SetTheory.Derive.Tg
public import ConLeche.SetModel.Iter
public import ConLeche.SetModel.UnionRec
import ConLeche.SetModel.Ops
import ConLeche.Semantics.Interp

public section

/-!
# Definable application: `appImageF` / `piSetApp` at a concrete graph

The Stage 15 toolkit exercised at `testS = {<pt, {pt}>, pt}`: a
single-valued graph with `app (testS V) pt = unitSet`.  The definable
image `appImageF (testS V) unitSet` and the definable function space
`piSetApp (testS V) unitSet` are shown equal to their meta twins
`image (app (testS V)) unitSet` / `piSet unitSet (fun j => app (testS V) j)`,
and closed under `tg w` via the clause-6 lemmas `appImageF_mem` /
`piSetApp_mem` (and `app_mem` for the point application) — no meta
`sep`/`image`/clause 5 anywhere.
-/

namespace ConLeche.SetTheory.DefinableAppEx

universe u

variable {V : Type u} [SetTheory V]

/-- A concrete single-valued graph: the only pair at `pt` is
`<pt, unitSet>`, so `app (testS V) pt = unitSet`. -/
noncomputable def testS (V : Type u) [SetTheory V] : V := upair (kpair pt unitSet) pt

theorem kpair_pt_unitSet_mem_testS : kpair pt (unitSet : V) ∈ˢ testS V :=
  mem_upair_left _ _

theorem testS_ne_pt : testS V ≠ (pt : V) := by
  intro h
  have hm := h ▸ kpair_pt_unitSet_mem_testS
  exact ptTag_ne_kpair pt unitSet (mem_pt.mp hm).symm

theorem testS_single : ∀ y, kpair pt y ∈ˢ testS V → y = unitSet := by
  intro y hy
  have hyu : (kpair pt y : V) ∈ˢ upair (kpair pt (unitSet : V)) (pt : V) := hy
  rcases mem_upair.mp hyu with h | h
  · exact (kpair_inj h).2
  · exact absurd h.symm (pt_ne_kpair pt y)

theorem app_testS_pt : app (testS V) pt = (unitSet : V) :=
  app_eq_of_unique testS_ne_pt kpair_pt_unitSet_mem_testS testS_single

/-- Single-valuedness of `testS` on the domain `unitSet`, in the shape
the `hfun` arguments of `piSetApp` take. -/
theorem testS_hfun : ∀ x, x ∈ˢ (unitSet : V) → ∃ y, y ∈ˢ app (testS V) x ∧
    ∀ y', y' ∈ˢ app (testS V) x → y' = y := by
  intro x hx
  rw [mem_unitSet_iff] at hx
  subst hx
  refine ⟨pt, ?_, fun y' hy' => ?_⟩
  · show pt ∈ˢ app (testS V) pt
    rw [app_testS_pt]
    exact pt_mem_unitSet
  · rw [app_testS_pt, mem_unitSet_iff] at hy'
    exact hy'

/-! ## Membership and equality with the meta twins -/

example (z : V) : z ∈ˢ appImageF (testS V) unitSet ↔ z = unitSet := by
  rw [mem_appImageF]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_unitSet_iff] at hx
    rw [hx, app_testS_pt]
  · intro rfl
    exact ⟨pt, pt_mem_unitSet, app_testS_pt.symm⟩

example : image (app (testS V)) (unitSet : V) = appImageF (testS V) (unitSet : V) :=
  image_app_eq

example : piSetApp (testS V) unitSet testS_hfun = piSet (unitSet : V) (fun j => app (testS V) j) :=
  piSetApp_eq_piSet testS_hfun

example : (sing (kpair pt pt) : V) ∈ˢ piSetApp (testS V) unitSet testS_hfun := by
  rw [mem_piSetApp testS_hfun]
  constructor
  · intro p hp
    rw [mem_sing] at hp
    subst hp
    rw [mem_sigmaPairsAppF]
    exact ⟨pt, pt_mem_unitSet, pt,
      by show pt ∈ˢ app (testS V) pt; rw [app_testS_pt]; exact pt_mem_unitSet, rfl⟩
  · intro x hx
    rw [mem_unitSet_iff] at hx
    subst hx
    exact ⟨pt, mem_sing.mpr rfl, fun y' hy' => (kpair_inj (mem_sing.mp hy')).2⟩

/-! ## Closure in `tg w` (clause 6, no meta clause 5) -/

variable {w : Nat}

theorem testS_mem_tg (hw : w ≠ 0) : testS V ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).upair_mem (empty_mem_tg w)
    ((tg_isUniverse hw).kpair_mem (empty_mem_tg w)
      ((tg_isUniverse hw).pt_mem (empty_mem_tg w)) (unitSet_mem_tg w))
    ((tg_isUniverse hw).pt_mem (empty_mem_tg w))

example (hw : w ≠ 0) : app (testS V) pt ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).app_mem (empty_mem_tg w) (testS_mem_tg hw)

example (hw : w ≠ 0) : appImageF (testS V) unitSet ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).appImageF_mem (empty_mem_tg w) (testS_mem_tg hw) (unitSet_mem_tg w)

example (hw : w ≠ 0) : piSetApp (testS V) unitSet testS_hfun ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).piSetApp_mem (empty_mem_tg w) (testS_mem_tg hw) (unitSet_mem_tg w)
    testS_hfun

/-! ## The definable graph of `app g` (`graphAppF`) -/

example : (kpair pt unitSet : V) ∈ˢ graphAppF (testS V) unitSet :=
  mem_graphAppF.mpr ⟨pt, pt_mem_unitSet, by rw [app_testS_pt]⟩

example : graphAppF (testS V) unitSet = graph (fun x => app (testS V) x) unitSet :=
  graphAppF_eq

example : app (graphAppF (testS V) unitSet) pt = unitSet := by
  rw [app_graphAppF pt_mem_unitSet, app_testS_pt]

example : graphAppF (testS V) unitSet ∈ˢ piSet unitSet (fun _ => upair (empty : V) unitSet) :=
  graphAppF_mem_piSet fun x hx => by
    rw [mem_unitSet_iff] at hx
    subst hx
    rw [app_testS_pt]
    exact mem_upair_right _ _

example (hw : w ≠ 0) : graphAppF (testS V) unitSet ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).graphAppF_mem (empty_mem_tg w) (testS_mem_tg hw) (unitSet_mem_tg w)

/-! ## The functionality-free twins (`sigmaPairsAppF`, `piSetAppNF`)

Stage 17: the raw app-pair product and the app function space WITHOUT a
single-valuedness hypothesis on the family graph `S` — exercised at the
NON-functional `twoS = {<pt, {pt}>, <pt, {empty}>}`, whose fibre
`app (twoS V) pt` has two members.  `sigmaPairsAppF (twoS V) unitSet`
still equals the meta `sigmaPairs unitSet (fun j => app (twoS V) j)` and
both close under `tg w` via the clause-6 lemmas only. -/

/-- Membership in an application: a member of a paired value. -/
theorem mem_app_of_mem_kpair {f a y z : V} (hf : f ≠ pt) (h : kpair a y ∈ˢ f) (hz : z ∈ˢ y) :
    z ∈ˢ app f a := by
  have happ : app f a = sUnion (sepF (sUnion (sUnion f)) kpairMemF (Form.snoc (fun _ => a) f)) := by
    unfold app; exact ite_eq_right hf
  rw [happ]
  have hy : y ∈ˢ sUnion (sUnion f) :=
    mem_sUnion.mpr ⟨upair a y, mem_sUnion.mpr ⟨kpair a y, h, mem_upair_right _ _⟩,
      mem_upair_right _ _⟩
  exact mem_sUnion.mpr ⟨y, mem_appSep.mpr ⟨hy, h⟩, hz⟩

/-- A concrete NON-single-valued graph: two pairs at `pt`, with values
`{pt}` and `{empty}`. -/
noncomputable def twoS (V : Type u) [SetTheory V] : V :=
  upair (kpair pt (sing pt)) (kpair pt (sing (empty : V)))

theorem kpair_pt_singPt_mem_twoS : kpair pt (sing pt) ∈ˢ twoS V := mem_upair_left _ _

theorem kpair_pt_singEmpty_mem_twoS : kpair pt (sing (empty : V)) ∈ˢ twoS V := mem_upair_right _ _

theorem twoS_ne_pt : twoS V ≠ (pt : V) := by
  intro h
  have hm := h ▸ kpair_pt_singPt_mem_twoS
  exact ptTag_ne_kpair pt (sing pt) (mem_pt.mp hm).symm

theorem pt_mem_app_twoS_pt : (pt : V) ∈ˢ app (twoS V) pt :=
  mem_app_of_mem_kpair twoS_ne_pt kpair_pt_singPt_mem_twoS (mem_sing.mpr rfl)

theorem empty_mem_app_twoS_pt : (empty : V) ∈ˢ app (twoS V) pt :=
  mem_app_of_mem_kpair twoS_ne_pt kpair_pt_singEmpty_mem_twoS (mem_sing.mpr rfl)

example : sigmaPairsAppF (testS V) unitSet = sigmaPairs (unitSet : V) (fun j => app (testS V) j) :=
  sigmaPairsAppF_eq

example : piSetAppNF (testS V) unitSet = piSet (unitSet : V) (fun j => app (testS V) j) :=
  piSetAppNF_eq_piSet

example : (kpair pt pt : V) ∈ˢ sigmaPairsAppF (testS V) unitSet :=
  mem_sigmaPairsAppF.mpr ⟨pt, pt_mem_unitSet, pt, by rw [app_testS_pt]; exact pt_mem_unitSet, rfl⟩

-- the NF product at the NON-functional twoS: both fibre members pair up
example : (kpair pt pt : V) ∈ˢ sigmaPairsAppF (twoS V) unitSet :=
  mem_sigmaPairsAppF.mpr ⟨pt, pt_mem_unitSet, pt, pt_mem_app_twoS_pt, rfl⟩

example : (kpair pt (empty : V) : V) ∈ˢ sigmaPairsAppF (twoS V) unitSet :=
  mem_sigmaPairsAppF.mpr ⟨pt, pt_mem_unitSet, empty, empty_mem_app_twoS_pt, rfl⟩

example : (sing (kpair pt pt) : V) ∈ˢ piSetAppNF (twoS V) unitSet := by
  rw [mem_piSetAppNF]
  constructor
  · intro p hp
    rw [mem_sing] at hp; subst hp
    exact mem_sigmaPairsAppF.mpr ⟨pt, pt_mem_unitSet, pt, pt_mem_app_twoS_pt, rfl⟩
  · intro x hx
    rw [mem_unitSet_iff] at hx; subst hx
    exact ⟨pt, mem_sing.mpr rfl, fun y' hy' => (kpair_inj (mem_sing.mp hy')).2⟩

theorem twoS_mem_tg (hw : w ≠ 0) : twoS V ∈ˢ (tg w : V) := by
  unfold twoS
  exact (tg_isUniverse hw).upair_mem (empty_mem_tg w)
    ((tg_isUniverse hw).kpair_mem (empty_mem_tg w) ((tg_isUniverse hw).pt_mem (empty_mem_tg w))
      ((tg_isUniverse hw).sing_mem (empty_mem_tg w) ((tg_isUniverse hw).pt_mem (empty_mem_tg w))))
    ((tg_isUniverse hw).kpair_mem (empty_mem_tg w) ((tg_isUniverse hw).pt_mem (empty_mem_tg w))
      ((tg_isUniverse hw).sing_mem (empty_mem_tg w) (empty_mem_tg w)))

example (hw : w ≠ 0) : sigmaPairsAppF (twoS V) unitSet ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).sigmaPairsAppF_mem (empty_mem_tg w) (twoS_mem_tg hw) (unitSet_mem_tg w)

example (hw : w ≠ 0) : piSetAppNF (twoS V) unitSet ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).piSetAppNF_mem (empty_mem_tg w) (twoS_mem_tg hw) (unitSet_mem_tg w)

/-! ## The disjoint union's per-class fibre is the definable app-pair product -/

/-- Inside `unionSet` the per-class fibre is `sigmaPairsAppF (X c) (Is c)`:
the meta `sigmaPairs` image is gone from the family. -/
example {Is X : Nat → V} (c : Nat) :
    Tower.natFibre (fun c => sigmaPairsAppF (X c) (Is c)) (vnat c)
      = sigmaPairsAppF (X c) (Is c) :=
  Tower.natFibre_vnat _ _

example {Is X : Nat → V} {i x : V} (hi : i ∈ˢ Is 0) (hx : x ∈ˢ app (X 0) i) :
    tagged 0 i x ∈ˢ unionSet 1 Is X :=
  tagged_mem_unionSet Nat.zero_lt_one hi hx

/-! ## The quotient saturation toolkit, repl-free (`Derive/Quot.lean`)

`qclassF` is read through `qsatF` alone: self-membership, closure under a
generating step, and invariance of a base-relation-invariant function
along the class — all via definable `sepF`, no meta `sep`/`image`. -/

example {A R a : V} (ha : a ∈ˢ A) : a ∈ˢ qclassF A R a :=
  self_mem_qclassF ha

example {A R a x y : V} (hx : x ∈ˢ qclassF A R a) (h : qstep A R x y ∨ qstep A R y x) :
    y ∈ˢ qclassF A R a :=
  qclassF_step_closed hx h

example {A R f a b : V}
    (hinv : ∀ a' b', a' ∈ˢ A → b' ∈ˢ A → (∃ w, w ∈ˢ app (app R a') b') → app f a' = app f b')
    (ha : a ∈ˢ A) (hb : b ∈ˢ qclassF A R a) : app f b = app f a :=
  app_eq_of_mem_qclassF hinv ha hb

/-- Concretely: over the one-point domain `unitSet` every function is
invariant, so it is constant on the definable class of `pt`. -/
example {b : V} (hb : b ∈ˢ qclassF (unitSet : V) (testS V) pt) :
    app (testS V) b = app (testS V) pt :=
  app_eq_of_mem_qclassF (f := testS V) (A := (unitSet : V)) (R := testS V) (a := pt)
    (fun a' b' ha' hb' _ => by
      rw [mem_unitSet_iff] at ha' hb'
      rw [ha', hb'])
    pt_mem_unitSet hb

/-- The definable app-graph eta: a `piSet` member is its own
`graphAppF`. -/
example {A f : V} {B : V → V} (hf : f ∈ˢ piSet A B) : graphAppF f A = f :=
  eq_graphAppF_of_mem_piSet hf

example : graphAppF (testS V) (unitSet : V) ∈ˢ piSet (unitSet : V) (fun _ => upair (empty : V) unitSet) :=
  graphAppF_mem_piSet fun x hx => by
    rw [mem_unitSet_iff] at hx
    subst hx
    rw [app_testS_pt]
    exact mem_upair_right _ _

/-! ## The quotient rewire: `qclass` is the definable `qclassF`

`qclass A R a = qclassF A R a` by definition, so the class API reads
through `qsatF` alone: symmetry and transitivity of the definable class
(repl-free, via the complement of a saturated set), equal classes from a
member or a `QuotRel` step, and the class membership as the `qsatF`
realization. -/

example {A R a b : V} (ha : a ∈ˢ A) (hb : b ∈ˢ qclass A R a) : a ∈ˢ qclass A R b :=
  qclassF_symm ha hb

example {A R a b c : V} (hb : b ∈ˢ qclass A R a) (hc : c ∈ˢ qclass A R b) :
    c ∈ˢ qclass A R a :=
  qclassF_trans hb hc

example {A R a b : V} (ha : a ∈ˢ A) (hb : b ∈ˢ qclass A R a) :
    qclass A R a = qclass A R b :=
  qclassF_eq_of_mem ha hb

example {A R a b : V} (h : QuotRel A R a b) : qclass A R a = qclass A R b :=
  qclass_eq_of_rel h

example {A R a b : V} :
    b ∈ˢ qclass A R a ↔ b ∈ˢ A ∧ Form.Realize Mem (Form.snoc (qclassParam A R a) b) qsatF :=
  mem_qclass

/-- Concretely: the one-point class is symmetric and the invariance
lemma fires through `qclass` itself. -/
example {b : V} (ha : (pt : V) ∈ˢ (unitSet : V)) (hb : b ∈ˢ qclass (unitSet : V) (testS V) pt) :
    app (testS V) b = app (testS V) pt :=
  app_eq_of_mem_qclassF (f := testS V) (A := (unitSet : V)) (R := testS V) (a := pt)
    (fun a' b' ha' hb' _ => by
      rw [mem_unitSet_iff] at ha' hb'
      rw [ha', hb'])
    ha hb

/-! ## The definable selector graph `recGraphF`

At `G = graphAppF (testS V) unitSet` (the definable graph of
`app (testS V)` over `unitSet`, with `app G pt = unitSet = {pt}`),
`recGraphF G unitSet` is the singleton `{kpair pt pt}`: a member of
`piSetAppNF G unitSet` whose application at `pt` is `pt` — the
first-order twin of `graph (fun j => recSel G j) unitSet`. -/

/-- Single-valuedness of `graphAppF (testS V) unitSet` on `unitSet`. -/
theorem testGraphF_single : ∀ j, j ∈ˢ (unitSet : V) →
    ∃ y, y ∈ˢ app (graphAppF (testS V) unitSet) j ∧
      ∀ z, z ∈ˢ app (graphAppF (testS V) unitSet) j → z = y := by
  intro j hj
  rw [mem_unitSet_iff] at hj
  subst hj
  refine ⟨pt, ?_, fun z hz => ?_⟩
  · rw [app_graphAppF pt_mem_unitSet, app_testS_pt]
    exact pt_mem_unitSet
  · rw [app_graphAppF pt_mem_unitSet, app_testS_pt, mem_unitSet_iff] at hz
    exact hz

theorem app_testGraphF_pt : app (graphAppF (testS V) unitSet) pt = (unitSet : V) := by
  rw [app_graphAppF pt_mem_unitSet, app_testS_pt]

example : kpair pt pt ∈ˢ recGraphF (graphAppF (testS V) unitSet) (unitSet : V) :=
  mem_recGraphF_of_single pt_mem_unitSet
    (by rw [app_testGraphF_pt]; exact pt_mem_unitSet)
    (fun z hz => by rw [app_testGraphF_pt, mem_unitSet_iff] at hz; exact hz)

example : recGraphF (graphAppF (testS V) unitSet) (unitSet : V) ∈ˢ
    piSetAppNF (graphAppF (testS V) unitSet) (unitSet : V) :=
  recGraphF_mem_piSetAppNF testGraphF_single

example : app (recGraphF (graphAppF (testS V) unitSet) (unitSet : V)) pt = (pt : V) :=
  app_recGraphF_eq testGraphF_single pt_mem_unitSet
    (by rw [app_testGraphF_pt]; exact pt_mem_unitSet)

example (p : V) : p ∈ˢ recGraphF (graphAppF (testS V) unitSet) (unitSet : V) ↔
    p = kpair pt pt := by
  rw [mem_recGraphF]
  constructor
  · rintro ⟨-, j, y, hp, hj, hy, -⟩
    rw [mem_unitSet_iff] at hj
    subst hj
    rw [app_testGraphF_pt, mem_unitSet_iff] at hy
    subst hy
    exact hp
  · intro rfl
    exact ⟨mem_sigmaPairsAppF.mpr ⟨pt, pt_mem_unitSet, pt,
      by rw [app_testGraphF_pt]; exact pt_mem_unitSet, rfl⟩,
      pt, pt, rfl, pt_mem_unitSet,
      by rw [app_testGraphF_pt]; exact pt_mem_unitSet,
      fun z hz => by rw [app_testGraphF_pt, mem_unitSet_iff] at hz; exact hz⟩

example (hw : w ≠ 0) : recGraphF (graphAppF (testS V) unitSet) (unitSet : V) ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).recGraphF_mem (empty_mem_tg w)
    ((tg_isUniverse hw).graphAppF_mem (empty_mem_tg w) (testS_mem_tg hw) (unitSet_mem_tg w))
    (unitSet_mem_tg w)

/-! ## The definable constant graphs (`constGraphF`, `sigmaConstGraphF`)

`constGraphF c A = {⟨x, c⟩ : x ∈ˢ A}` and `sigmaConstGraphF A D =
{⟨x, sigmaConstF A x⟩ : x ∈ˢ D}` — the first-order twins of the meta
constant graphs, with beta, equality, and clause-6 closure, exercised
over the one-point domain `unitSet`. -/

example : (kpair pt unitSet : V) ∈ˢ constGraphF (unitSet : V) (unitSet : V) :=
  mem_constGraphF.mpr ⟨pt, pt_mem_unitSet, rfl⟩

example : app (constGraphF (unitSet : V) (unitSet : V)) pt = (unitSet : V) :=
  app_constGraphF pt_mem_unitSet

example : constGraphF (unitSet : V) (unitSet : V) = graph (fun _ => (unitSet : V)) (unitSet : V) :=
  constGraphF_eq_graph _ _

example (hw : w ≠ 0) : constGraphF (unitSet : V) (unitSet : V) ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).constGraphF_mem (empty_mem_tg w) (unitSet_mem_tg w) (unitSet_mem_tg w)

example : (kpair pt (sigmaConstF (unitSet : V) pt) : V) ∈ˢ
    sigmaConstGraphF (unitSet : V) (unitSet : V) :=
  mem_sigmaConstGraphF.mpr ⟨pt, pt_mem_unitSet, rfl⟩

example : app (sigmaConstGraphF (unitSet : V) (unitSet : V)) pt = sigmaConstF (unitSet : V) pt :=
  app_sigmaConstGraphF pt_mem_unitSet

example : sigmaConstGraphF (unitSet : V) (unitSet : V) =
    graph (fun x => sigmaConstF (unitSet : V) x) (unitSet : V) :=
  sigmaConstGraphF_eq_graph _ _

example (hw : w ≠ 0) : sigmaConstGraphF (unitSet : V) (unitSet : V) ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).sigmaConstGraphF_mem (empty_mem_tg w) (unitSet_mem_tg w) (unitSet_mem_tg w)

/-! ## The definable countable union (`natUnionF`) and the natFibre bridges

Over `ω`, `natUnionF (constGraphF c omega)` collects `app (constGraphF c
omega) d = c` for every `d ∈ˢ omega`, i.e. it is exactly `c` (the meta
`natUnion` was retired in stage 26). -/

example (c x : V) : x ∈ˢ Tower.natUnionF (constGraphF c omega) ↔ x ∈ˢ c := by
  rw [Tower.mem_natUnionF]
  constructor
  · rintro ⟨d, hd, hx⟩
    rw [app_constGraphF hd] at hx
    exact hx
  · intro hx
    exact ⟨vnat 0, vnat_mem_omega 0, by rw [app_constGraphF (vnat_mem_omega 0)]; exact hx⟩

example (hw : w ≠ 0) : Tower.natUnionF (constGraphF (unitSet : V) omega) ∈ˢ (tg w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  exact Tower.natUnionF_mem_tg_pos (Nat.succ_ne_zero w')
    ((tg_isUniverse (Nat.succ_ne_zero w')).constGraphF_mem (empty_mem_tg _)
      (unitSet_mem_tg _) (omega_mem_tg_succ w'))

/-! ## The definable iteration graph (`iterStepGraphF` / `iterGraphF` / `accPathsF`) -/

/-- `sigmaConstF` at the empty base is empty. -/
theorem sigmaConstF_empty (c : V) : sigmaConstF (empty : V) c = empty := by
  refine SetTheory.ext fun z => ?_
  rw [mem_sigmaConstF]
  constructor
  · rintro ⟨x, hx, _, _, _⟩
    exact absurd hx (not_mem_empty x)
  · intro hz
    exact absurd hz (not_mem_empty z)

/-- The meta family `unitSet, empty, empty, …` (the `accPathsN empty` shape). -/
noncomputable def iterF : Nat → V
  | 0 => unitSet
  | _ + 1 => empty

theorem iterF_succ (n : Nat) : iterF (n + 1) = sigmaConstF (empty : V) (iterF n) := by
  show (empty : V) = sigmaConstF (empty : V) (iterF n)
  rw [sigmaConstF_empty]

theorem iterF_mem_tg1 (n : Nat) : iterF n ∈ˢ power (tg 1 : V) := by
  rw [mem_power]
  intro z hz
  cases n with
  | zero =>
      have h0 : iterF 0 = (unitSet : V) := rfl
      rw [h0, mem_unitSet_iff] at hz
      rw [hz]
      exact (tg_isUniverse (Nat.succ_ne_zero 0)).pt_mem (univChain_one_mem_tg_succ 0)
  | succ n =>
      have h1 : iterF (n + 1) = (empty : V) := rfl
      rw [h1] at hz
      exact absurd hz (not_mem_empty z)

/-- The constant step graph beta-reduces at standard numerals. -/
example : app (app (Tower.iterStepGraphF (unitSet : V) (tg 1 : V)) (vnat 0)) (unitSet : V) =
    sigmaConstF (unitSet : V) unitSet :=
  Tower.app_iterStepGraphF (vnat_mem_omega 0) (unitSet_mem_tg 1)

/-- The iteration graph reads off `iterF` at every standard numeral. -/
example (n : Nat) : app (Tower.iterGraphF (empty : V) (power (tg 1 : V))) (vnat n) = iterF n :=
  Tower.iterGraphF_vnat_eq (empty : V) (power (tg 1 : V)) iterF rfl
    (fun n => iterF_succ n) iterF_mem_tg1 n

example : app (Tower.iterGraphF (empty : V) (power (tg 1 : V))) (vnat 0) = (unitSet : V) :=
  Tower.iterGraphF_vnat_eq (empty : V) (power (tg 1 : V)) iterF rfl
    (fun n => iterF_succ n) iterF_mem_tg1 0

example : app (Tower.iterGraphF (empty : V) (power (tg 1 : V))) (vnat 2) = (empty : V) :=
  Tower.iterGraphF_vnat_eq (empty : V) (power (tg 1 : V)) iterF rfl
    (fun n => iterF_succ n) iterF_mem_tg1 2

/-- The empty path is in the definable path set. -/
example : (pt : V) ∈ˢ Tower.accPathsF (unitSet : V) (tg 1 : V) :=
  Tower.pt_mem_accPathsF _ _

/-- The iteration graph over `ω` stays in `tg 1` (definable induction). -/
theorem iterGraphF_unitSet_mem_tg1 (c : V) (hc : c ∈ˢ omega) :
    app (Tower.iterGraphF (unitSet : V) (tg 1 : V)) c ∈ˢ (tg 1 : V) :=
  Tower.iterGraphF_app_mem (tg_isUniverse (Nat.succ_ne_zero 0)) (empty_mem_tg 1)
    (unitSet_mem_tg 1) hc

/-- Pair closure of the definable path set over a universe bound. -/
example : kpair pt pt ∈ˢ Tower.accPathsF (unitSet : V) (tg 1 : V) :=
  Tower.kpair_mem_accPathsF pt_mem_unitSet (Tower.pt_mem_accPathsF _ _) iterGraphF_unitSet_mem_tg1

/-- `appBoundF` realizes `app G c ∈ˢ U` at a concrete graph. -/
example : Form.Realize Mem (Form.snoc (Tower.appBoundParam (testS V) (tg 1 : V)) pt)
    Tower.appBoundF :=
  Tower.realize_appBoundF.mpr (by rw [app_testS_pt]; exact unitSet_mem_tg 1)

/-- The recursion graph over a `tg 1`-closed step is a member of `tg 1`
(clause-6 closure of `recGraph` via `IsUniverse.recGraph_mem`). -/
theorem recGraph_iterStep_mem_tg1 :
    recGraph (unitSet : V) (Tower.iterStepGraphF (empty : V) (tg 1 : V)) ∈ˢ (tg 1 : V) :=
  IsUniverse.recGraph_mem (tg_isUniverse (Nat.succ_ne_zero 0)) (unitSet_mem_tg 1)
    (omega_mem_tg_succ 0) (fun m hm u hu => by
      rw [Tower.app_iterStepGraphF hm hu]
      exact (tg_isUniverse (Nat.succ_ne_zero 0)).sigmaConstF_mem (empty_mem_tg 1)
        (empty_mem_tg 1) hu)

/-- The definable path set at a universe bound is a member of the universe. -/
example : Tower.accPathsF (empty : V) (tg 1 : V) ∈ˢ (tg 1 : V) :=
  Tower.natUnionF_mem_tg_pos (Nat.succ_ne_zero 0) recGraph_iterStep_mem_tg1

/-- Same at base `unitSet`, with the step closure through
`sigmaConstF_mem`. -/
theorem accPathsF_unitSet_mem_tg1 : Tower.accPathsF (unitSet : V) (tg 1 : V) ∈ˢ (tg 1 : V) :=
  Tower.natUnionF_mem_tg_pos (Nat.succ_ne_zero 0)
    (IsUniverse.recGraph_mem (tg_isUniverse (Nat.succ_ne_zero 0)) (unitSet_mem_tg 1)
      (omega_mem_tg_succ 0) (fun m hm u hu => by
        rw [Tower.app_iterStepGraphF hm hu]
        exact (tg_isUniverse (Nat.succ_ne_zero 0)).sigmaConstF_mem (empty_mem_tg 1)
          (unitSet_mem_tg 1) hu))

/-! ## Value-level clause-6 twins (stages 28–31)

`sigmaPairsAppF_val_mem`, `piSetAppNF_val_mem`, `appImageF_val_mem`,
`graphAppF_val_mem`, `sUnion_appImageF_val_mem`: clause-6 closure at
`app S`-families when only the VALUES `app S x` are members of `U`,
not the graph `S` itself — exercised at the non-functional `twoS`
over `unitSet`. -/

theorem app_twoS_pt_mem_tg (hw : w ≠ 0) : app (twoS V) pt ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).app_mem (empty_mem_tg w) (twoS_mem_tg hw)

theorem twoS_val_tg (hw : w ≠ 0) :
    ∀ x, x ∈ˢ (unitSet : V) → app (twoS V) x ∈ˢ (tg w : V) := by
  intro x hx
  rw [mem_unitSet_iff] at hx
  subst hx
  exact app_twoS_pt_mem_tg hw

example (hw : w ≠ 0) : sigmaPairsAppF (twoS V) unitSet ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).sigmaPairsAppF_val_mem (empty_mem_tg w) (unitSet_mem_tg w) (twoS_val_tg hw)

example (hw : w ≠ 0) : piSetAppNF (twoS V) unitSet ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).piSetAppNF_val_mem (empty_mem_tg w) (unitSet_mem_tg w) (twoS_val_tg hw)

example (hw : w ≠ 0) : appImageF (twoS V) unitSet ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).appImageF_val_mem (unitSet_mem_tg w) (twoS_val_tg hw)

example (hw : w ≠ 0) : sUnion (appImageF (twoS V) (unitSet : V)) ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).sUnion_appImageF_val_mem (unitSet_mem_tg w) (twoS_val_tg hw)

example (hw : w ≠ 0) : graphAppF (twoS V) unitSet ∈ˢ (tg w : V) :=
  (tg_isUniverse hw).graphAppF_val_mem (empty_mem_tg w) (unitSet_mem_tg w) (twoS_val_tg hw)

/-! ## Universe-level clause-6 formation (stages 28–30)

`sigma_mem_univ_const` / `sigma_mem_univ_app` and
`piV_mem_univ_const` / `piV_mem_univ_app` at small concrete levels. -/

example : sigmaSet (Nat.max 1 1) (omega : V) (fun _ => (univ 0 : V)) ∈ˢ (univ (Nat.max 1 1) : V) :=
  sigma_mem_univ_const (omega_mem_univ_succ 0) (univ_mem_univ 0)

example : sigmaSet (Nat.max 1 1) (unitSet : V) (fun j => app (testS V) j) ∈ˢ (univ (Nat.max 1 1) : V) :=
  sigma_mem_univ_app (unitSet_mem_univ 1) fun j hj => by
    rw [mem_unitSet_iff] at hj; subst hj; rw [app_testS_pt]; exact unitSet_mem_univ 1

example : SetModel.piV (omega : V) (fun _ => (univ 0 : V)) ∈ˢ (univ (if 1 = 0 then 0 else Nat.max 1 1) : V) :=
  SetModel.piV_mem_univ_const (u := 1) (v := 1) (omega_mem_univ_succ 0) (univ_mem_univ 0)

example : SetModel.piV (unitSet : V) (fun j => app (testS V) j) ∈ˢ (univ (if 1 = 0 then 0 else Nat.max 1 1) : V) :=
  SetModel.piV_mem_univ_app (u := 1) (v := 1) (unitSet_mem_univ 1) fun j hj => by
    rw [mem_unitSet_iff] at hj; subst hj; rw [app_testS_pt]; exact unitSet_mem_univ 1

/-! ## Stage 34: V-codes for the erased syntax -/

example : ConLeche.Semantics.bconstCode (W := V) .nat = kpair (vnat 0) (empty : V) := rfl

example : ConLeche.Semantics.bconstCode (W := V) (.lfpTuple 2) = kpair (vnat 18) (vnat 2) := rfl

example (h : ConLeche.Semantics.bconstCode (W := V) .nat =
    ConLeche.Semantics.bconstCode (W := V) .natZero) : False :=
  ConLeche.Term.BConst.noConfusion (ConLeche.Semantics.bconstCode_inj h)

example (k k' : Nat) (h : ConLeche.Semantics.bconstCode (W := V) (.lfpTuple k) =
    ConLeche.Semantics.bconstCode (W := V) (.lfpTuple k')) : k = k' := by
  have := ConLeche.Semantics.bconstCode_inj h
  cases this
  rfl

example : ConLeche.Semantics.vnatListCode (W := V) [1, 2] =
    Tower.mkTower [vnat 1, vnat 2] := rfl

example (h : ConLeche.Semantics.vnatListCode (W := V) [1] =
    ConLeche.Semantics.vnatListCode (W := V) [1, 2]) : False := by
  have := ConLeche.Semantics.vnatListCode_inj h
  simp at this

/-! ## Stage 35: V-codes for terms -/

example : ConLeche.Semantics.tmCode (W := V) (.bvar 3) = kpair (vnat 0) (vnat 3) := rfl

example : ConLeche.Semantics.tmCode (W := V) (.const .nat [0, 2]) =
    kpair (vnat 2) (kpair (kpair (vnat 0) (empty : V)) (Tower.mkTower [vnat 0, vnat 2])) := rfl

example : ConLeche.Semantics.tmCode (W := V) (.app (.bvar 0) .prf) =
    kpair (vnat 3) (kpair (kpair (vnat 0) (vnat 0)) (kpair (vnat 10) (empty : V))) := rfl

example (h : ConLeche.Semantics.tmCode (W := V) (.bvar 1) =
    ConLeche.Semantics.tmCode (W := V) (.bvar 2)) : False := by
  have := ConLeche.Semantics.tmCode_inj _ _ h
  simp at this

example (h : ConLeche.Semantics.tmCode (W := V) (.bvar 1) =
    ConLeche.Semantics.tmCode (W := V) (.sort 1)) : False :=
  ConLeche.Term.Term.noConfusion (ConLeche.Semantics.tmCode_inj _ _ h)

example (t : ConLeche.Term.Term) :
    ConLeche.Semantics.tmCode (W := V) (.fst t) =
      kpair (vnat 8) (ConLeche.Semantics.tmCode (W := V) t) := rfl

/-! ## Stage 36: definable pair projections (readers of the V-codes) -/

example : Form.Realize Mem
    (Form.snoc (Form.snoc (fun _ => vnat 1) (kpair (vnat 1) (vnat 2))) (pt : V))
    ConLeche.Semantics.sfstEqF :=
  ConLeche.Semantics.realize_sfstEqF.mpr (sfst_kpair _ _).symm

example : Form.Realize Mem
    (Form.snoc (Form.snoc (fun _ => vnat 2) (kpair (vnat 1) (vnat 2))) (pt : V))
    ConLeche.Semantics.ssndEqF :=
  ConLeche.Semantics.realize_ssndEqF.mpr (ssnd_kpair _ _).symm

example : Form.Realize Mem
    (Form.snoc (Form.snoc (fun _ => (pt : V)) (empty : V)) (pt : V))
    ConLeche.Semantics.sfstEqF :=
  ConLeche.Semantics.realize_sfstEqF.mpr (by
    have h : ¬∃ a b, (empty : V) = kpair a b := fun hh =>
      ConLeche.Semantics.kpair_ne_empty hh.choose hh.choose_spec.choose hh.choose_spec.choose_spec.symm
    unfold sfst; rw [dite_eq_right h])

example : ¬ Form.Realize Mem
    (Form.snoc (Form.snoc (fun _ => vnat 1) (kpair (vnat 1) (vnat 2))) (pt : V))
    ConLeche.Semantics.ssndEqF := by
  rw [ConLeche.Semantics.realize_ssndEqF]
  rw [ssnd_kpair]
  intro h
  exact absurd (vnat_inj (V := V) h) (by omega)


/-! ## Stage 38: definable environment graphs (`consGraph`) -/

example : Form.Realize Mem
    (Form.snoc (fun _ => kpair (vnat (V := V) 0) (vnat (V := V) 2))
      (kpair (vnat (V := V) 1) (vnat (V := V) 2)))
    ConLeche.Semantics.consShiftF :=
  ConLeche.Semantics.realize_consShiftF.mpr (Or.inl ⟨vnat (V := V) 0, vnat (V := V) 2, rfl, rfl⟩)

example : kpair (vnat 1) (vnat 2) ∈ˢ
    ConLeche.Semantics.consGraph (W := V) (vnat 1) (sing (kpair (vnat 0) (vnat 2))) :=
  ConLeche.Semantics.mem_consGraph.mpr (Or.inr
    ⟨kpair (vnat 0) (vnat 2), mem_sing.mpr rfl, Or.inl ⟨vnat 0, vnat 2, rfl, rfl⟩⟩)

example : app (ConLeche.Semantics.consGraph (W := V) (vnat 1) (sing (kpair (vnat 0) (vnat 2))))
    (vnat 0) = vnat 1 :=
  ConLeche.Semantics.app_consGraph_zero

example : app (ConLeche.Semantics.consGraph (W := V) (vnat 1) (sing (kpair (vnat 0) (vnat 2))))
    (vnat 1) = vnat 2 := by
  have hρ : sing (kpair (vnat 0) (vnat 2)) ≠ (pt : V) := fun h =>
    ptTag_ne_kpair _ _ (mem_sing.mp (h.symm ▸ ptTag_mem_pt))
  rw [ConLeche.Semantics.app_consGraph_succ (W := V) hρ 0]
  exact app_eq_of_unique hρ (mem_sing.mpr rfl) (fun y hy => (kpair_inj (mem_sing.mp hy)).2)


/-! ## Stage 39: Form-level env reading (`appEqF` at `consGraph`) and the `bvar` step -/

example : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ => (pt : V)) (vnat (V := V) 1))
      (ConLeche.Semantics.consGraph (W := V) (vnat (V := V) 1)
        (sing (kpair (vnat (V := V) 0) (vnat (V := V) 2))))) (vnat (V := V) 0))
    appEqF :=
  ConLeche.Semantics.realize_appEqF_consGraph_zero.mpr rfl

example : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ => (pt : V)) (vnat (V := V) 2))
      (ConLeche.Semantics.consGraph (W := V) (vnat (V := V) 1)
        (sing (kpair (vnat (V := V) 0) (vnat (V := V) 2))))) (vnat (V := V) 1))
    appEqF := by
  have hρ : sing (kpair (vnat (V := V) 0) (vnat (V := V) 2)) ≠ (pt : V) := fun h =>
    ptTag_ne_kpair _ _ (mem_sing.mp (h.symm ▸ ptTag_mem_pt))
  rw [ConLeche.Semantics.realize_appEqF_consGraph_succ (W := V) hρ 0]
  exact (app_eq_of_unique hρ (mem_sing.mpr rfl) (fun y hy => (kpair_inj (mem_sing.mp hy)).2)).symm

example : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ => app (sing (kpair (vnat (V := V) 0) (vnat (V := V) 2)))
      (vnat (V := V) 0)) (sing (kpair (vnat (V := V) 0) (vnat (V := V) 2))))
      (ConLeche.Semantics.tmCode (ConLeche.Term.Term.bvar 0))) (pt : V))
    ConLeche.Semantics.bvarStepF :=
  ConLeche.Semantics.realize_bvarStepF_tmCode 0


/-! ## Stage 40: the `app` case of the definable interp step -/

example {X i : V} : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ => app (app X (kpair (sfst (ssnd (sfst i))) (ssnd i)))
      (app X (kpair (ssnd (ssnd (sfst i))) (ssnd i)))) X) i) (pt : V))
    ConLeche.Semantics.appStepF :=
  ConLeche.Semantics.realize_appStepF.mpr rfl

example (ρ : V) : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ =>
      app (app (empty : V) (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.bvar 0)) ρ))
        (app (empty : V) (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.bvar 1)) ρ)))
      (empty : V))
      (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.app (ConLeche.Term.Term.bvar 0)
        (ConLeche.Term.Term.bvar 1))) ρ)) (pt : V))
    ConLeche.Semantics.appStepF := by
  rw [ConLeche.Semantics.realize_appStepF]
  simp only [ConLeche.Semantics.tmCode, sfst_kpair, ssnd_kpair]


/-! ## Stage 41: the unary (`fst`/`snd`) and `prf` cases of the definable interp step -/

example {X i : V} : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ =>
      sfst (app X (kpair (ssnd (sfst i)) (ssnd i)))) X) i) (pt : V))
    ConLeche.Semantics.fstStepF :=
  ConLeche.Semantics.realize_fstStepF.mpr rfl

example {X i : V} : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ =>
      ssnd (app X (kpair (ssnd (sfst i)) (ssnd i)))) X) i) (pt : V))
    ConLeche.Semantics.sndStepF :=
  ConLeche.Semantics.realize_sndStepF.mpr rfl

example (ρ : V) : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ =>
      sfst (app (empty : V) (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.bvar 0)) ρ)))
      (empty : V))
      (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.fst (ConLeche.Term.Term.bvar 0))) ρ))
      (pt : V))
    ConLeche.Semantics.fstStepF := by
  rw [ConLeche.Semantics.realize_fstStepF]
  simp only [ConLeche.Semantics.tmCode, sfst_kpair, ssnd_kpair]

example (ρ : V) : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ =>
      ssnd (app (empty : V) (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.bvar 0)) ρ)))
      (empty : V))
      (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.snd (ConLeche.Term.Term.bvar 0))) ρ))
      (pt : V))
    ConLeche.Semantics.sndStepF := by
  rw [ConLeche.Semantics.realize_sndStepF]
  simp only [ConLeche.Semantics.tmCode, sfst_kpair, ssnd_kpair]

example (ρ : V) : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ => (pt : V)) (empty : V))
      (kpair (ConLeche.Semantics.tmCode ConLeche.Term.Term.prf) ρ)) (pt : V))
    ConLeche.Semantics.prfStepF :=
  ConLeche.Semantics.realize_prfStepF.mpr rfl


/-! ## Stage 42: definable truth values — `unitSetF`, `eqvF` -/

example {v pt : V} (h : v = sing pt) :
    Form.Realize Mem (Form.snoc (fun _ => v) pt) ConLeche.Semantics.unitSetF :=
  ConLeche.Semantics.realize_unitSetF.mpr h

example {x : V} (h : x = (empty : V)) :
    Form.Realize Mem (Form.snoc Form.nil x) emptyF :=
  ConLeche.Semantics.realize_emptyF_eq.mpr h

example {x : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => (unitSet : V)) x) x) (pt : V))
      ConLeche.Semantics.eqvF :=
  ConLeche.Semantics.realize_eqvF.mpr (ConLeche.Semantics.eqv_eq_unitSet rfl).symm

example {x y : V} (h : x ≠ y) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => (empty : V)) x) y) (pt : V))
      ConLeche.Semantics.eqvF :=
  ConLeche.Semantics.realize_eqvF.mpr (by rw [ConLeche.Semantics.eqv_eq_empty h])


/-! ## Stage 43: the `eqE` case of the definable interp step -/

example {X i : V} : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ =>
      eqv (app X (kpair (sfst (ssnd (sfst i))) (ssnd i)))
        (app X (kpair (ssnd (ssnd (sfst i))) (ssnd i)))) X) i) (pt : V))
    ConLeche.Semantics.eqEStepF :=
  ConLeche.Semantics.realize_eqEStepF.mpr rfl

example (ρ : V) : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ =>
      eqv (app (empty : V) (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.bvar 0)) ρ))
        (app (empty : V) (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.bvar 0)) ρ)))
      (empty : V))
      (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.eqE (ConLeche.Term.Term.bvar 0)
        (ConLeche.Term.Term.bvar 0))) ρ)) (pt : V))
    ConLeche.Semantics.eqEStepF := by
  rw [ConLeche.Semantics.realize_eqEStepF]
  simp only [ConLeche.Semantics.tmCode, sfst_kpair, ssnd_kpair]


/-! ## Stage 44: the Form-level reader `consGraphEqF` for `consGraph` -/

example {w x ρ : V} (h : w = ConLeche.Semantics.consGraph x ρ) :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ => w) x) ρ)
      ConLeche.Semantics.consGraphEqF :=
  ConLeche.Semantics.realize_consGraphEqF.mpr h

example : Form.Realize Mem
    (Form.snoc (Form.snoc (fun _ => ConLeche.Semantics.consGraph (empty : V) (empty : V)) (empty : V)) (empty : V))
      ConLeche.Semantics.consGraphEqF :=
  ConLeche.Semantics.realize_consGraphEqF.mpr rfl


/-! ## Stage 45: the `letE` case of the definable interp step -/

example {v X i : V} (h : v = app X (kpair (ssnd (ssnd (sfst i)))
    (ConLeche.Semantics.consGraph (app X (kpair (sfst (ssnd (sfst i))) (ssnd i))) (ssnd i)))) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) X) i) (pt : V))
      ConLeche.Semantics.letEStepF :=
  ConLeche.Semantics.realize_letEStepF.mpr h

example (ρ : V) : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ =>
      app (empty : V) (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.bvar 0))
        (ConLeche.Semantics.consGraph
          (app (empty : V) (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.prf)) ρ)) ρ))) (empty : V))
      (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.letE ConLeche.Term.Term.prf
        (ConLeche.Term.Term.bvar 0))) ρ)) (pt : V))
    ConLeche.Semantics.letEStepF :=
  ConLeche.Semantics.realize_letEStepF_tmCode (X := (empty : V)) (ρ := ρ)
    ConLeche.Term.Term.prf (ConLeche.Term.Term.bvar 0)


/-! ## Stage 46: the `lam` readers — definable function graph and point-condition -/

example {v a X b ρ : V} (h : v = graph (fun x => app X (kpair b
    (ConLeche.Semantics.consGraph x ρ))) a) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
      (fun _ => v) a) X) b) ρ) (pt : V))
      ConLeche.Semantics.lamGraphEqF :=
  ConLeche.Semantics.realize_lamGraphEqF.mpr h

example {a X b ρ : V} (h : ∀ x, x ∈ˢ a → app X (kpair b
    (ConLeche.Semantics.consGraph x ρ)) = pt) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc
      (fun _ => a) X) b) ρ) (pt : V))
      ConLeche.Semantics.ptAllF :=
  ConLeche.Semantics.realize_ptAllF.mpr h


/-! ## Stage 47: the `lam` case of the definable interp step -/

example {v X i : V} (h : v = ConLeche.SetModel.lamV (app X (kpair (sfst (ssnd (sfst i))) (ssnd i)))
    (fun x => app X (kpair (ssnd (ssnd (sfst i)))
      (ConLeche.Semantics.consGraph x (ssnd i))))) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) X) i) (pt : V))
      ConLeche.Semantics.lamStepF :=
  ConLeche.Semantics.realize_lamStepF.mpr h

example (ρ : V) : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ =>
      ConLeche.SetModel.lamV (app (empty : V) (kpair (ConLeche.Semantics.tmCode ConLeche.Term.Term.prf) ρ))
        (fun x => app (empty : V) (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.bvar 0))
          (ConLeche.Semantics.consGraph x ρ)))) (empty : V))
      (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.lam ConLeche.Term.Term.prf
        (ConLeche.Term.Term.bvar 0))) ρ)) (pt : V))
    ConLeche.Semantics.lamStepF :=
  ConLeche.Semantics.realize_lamStepF_tmCode (X := (empty : V)) (ρ := ρ)
    ConLeche.Term.Term.prf (ConLeche.Term.Term.bvar 0)


/-! ## Stage 48: the `pi` proposition-condition reader `propAllF` -/

example {a X b ρ : V} (h : ∀ x, x ∈ˢ a → app X (kpair b
    (ConLeche.Semantics.consGraph x ρ)) ∈ˢ (univZero : V)) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc
      (fun _ => a) X) b) ρ) (pt : V))
      ConLeche.Semantics.propAllF :=
  ConLeche.Semantics.realize_propAllF.mpr h



/-! ## Stage 49: the `piSet` reader `piSetEqF` -/

example {v a X b ρ : V} (h : v = piSet a (fun x => app X (kpair b
    (ConLeche.Semantics.consGraph x ρ)))) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
      (fun _ => v) a) X) b) ρ) (pt : V))
      ConLeche.Semantics.piSetEqF :=
  ConLeche.Semantics.realize_piSetEqF.mpr h



/-! ## Stage 50: the `pi` existential-fibre reader `exAllF` -/

example {a X b ρ : V} (h : ∀ x, x ∈ˢ a → ∃ y, y ∈ˢ app X (kpair b
    (ConLeche.Semantics.consGraph x ρ))) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc
      (fun _ => a) X) b) ρ) (pt : V))
      ConLeche.Semantics.exAllF :=
  ConLeche.Semantics.realize_exAllF.mpr h



/-! ## Stage 51: the `pi` case of the definable interp step -/

example {v X i : V} (h : v = ConLeche.SetModel.piV (app X (kpair (sfst (ssnd (sfst i))) (ssnd i)))
    (fun x => app X (kpair (ssnd (ssnd (sfst i)))
      (ConLeche.Semantics.consGraph x (ssnd i))))) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) X) i) (pt : V))
      ConLeche.Semantics.piStepF :=
  ConLeche.Semantics.realize_piStepF.mpr h

example (ρ : V) : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ =>
      ConLeche.SetModel.piV (app (empty : V) (kpair (ConLeche.Semantics.tmCode ConLeche.Term.Term.prf) ρ))
        (fun x => app (empty : V) (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.bvar 0))
          (ConLeche.Semantics.consGraph x ρ)))) (empty : V))
      (kpair (ConLeche.Semantics.tmCode (ConLeche.Term.Term.pi ConLeche.Term.Term.prf
        (ConLeche.Term.Term.bvar 0))) ρ)) (pt : V))
    ConLeche.Semantics.piStepF :=
  ConLeche.Semantics.realize_piStepF_tmCode (X := (empty : V)) (ρ := ρ)
    ConLeche.Term.Term.prf (ConLeche.Term.Term.bvar 0)


example {x : V} (h : x = vnat 3) : Form.Realize Mem
    (Form.snoc (fun _ : Fin 1 => x) (pt : V)) (ConLeche.Semantics.vnatEqF 3) :=
  (ConLeche.Semantics.realize_vnatEqF 3).mpr h


example {z y : V} (h : z = kpair (vnat 5) y) : Form.Realize Mem
    (Form.snoc (Form.snoc (fun _ : Fin 1 => z) y) (pt : V))
    (ConLeche.Semantics.vnatKpairEqF 5) :=
  (ConLeche.Semantics.realize_vnatKpairEqF 5).mpr h


example {v a : V} (h : v = power a) : Form.Realize Mem
    (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) (pt : V)) ConLeche.Semantics.powerEqF :=
  (ConLeche.Semantics.realize_powerEqF).mpr h


example {v : V} (h : v = univZero) : Form.Realize Mem
    (Form.snoc (fun _ : Fin 1 => v) (pt : V)) ConLeche.Semantics.univZeroEqF :=
  (ConLeche.Semantics.realize_univZeroEqF).mpr h


example {x : V} (h : x = ConLeche.Semantics.vnatListCode [1, 2]) : Form.Realize Mem
    (Form.snoc (fun _ : Fin 1 => x) (pt : V)) (ConLeche.Semantics.vnatListEqF [1, 2]) :=
  (ConLeche.Semantics.realize_vnatListEqF [1, 2]).mpr h


example {x : V} (h : x = ConLeche.Semantics.bconstCode ConLeche.Term.BConst.propext) :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => x) (pt : V))
      (ConLeche.Semantics.bconstCodeEqF ConLeche.Term.BConst.propext) :=
  (ConLeche.Semantics.realize_bconstCodeEqF ConLeche.Term.BConst.propext).mpr h


example {i : V} (h : i = ConLeche.Semantics.tmCode (ConLeche.Term.Term.const
    ConLeche.Term.BConst.propext [])) : Form.Realize Mem
    (Form.snoc (fun _ : Fin 1 => i) (pt : V))
    (ConLeche.Semantics.constCodeF ConLeche.Term.BConst.propext []) :=
  (ConLeche.Semantics.realize_constCodeF ConLeche.Term.BConst.propext []).mpr h


example {x : V} (h : x = kpair (vnat 7) (vnat 2)) : Form.Realize Mem
    (Form.snoc (fun _ : Fin 1 => x) (pt : V))
    (ConLeche.Semantics.vnatKpairPF 7 (ConLeche.Semantics.vnatEqF 2)) :=
  (ConLeche.Semantics.realize_vnatKpairPF 7 (pf := ConLeche.Semantics.vnatEqF 2) (P := fun p => p = (vnat 2 : V)) (fun p => ConLeche.Semantics.realize_vnatEqF 2 (x := p))).mpr
    ⟨vnat 2, h, rfl⟩


example {x : V} (h : x = ConLeche.Semantics.tmCode (ConLeche.Term.Term.app
    (ConLeche.Term.Term.bvar 0) (ConLeche.Term.Term.prf))) : Form.Realize Mem
    (Form.snoc (fun _ : Fin 1 => x) (pt : V))
    (ConLeche.Semantics.tmCodeEqF (ConLeche.Term.Term.app
      (ConLeche.Term.Term.bvar 0) (ConLeche.Term.Term.prf))) :=
  (ConLeche.Semantics.realize_tmCodeEqF _).mpr h


example {v X i : V} (h : i = ConLeche.Semantics.tmCode (ConLeche.Term.Term.bvar 2)) :
    Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V))
    ConLeche.Semantics.tagDispatchF :=
  (ConLeche.Semantics.realize_tagDispatchF).mpr
    ⟨0, by omega, _, by rw [h]; rfl⟩


example {v X i : V} (h : i = ConLeche.Semantics.tmCode (ConLeche.Term.Term.bvar 2))
    (hv : v = app X (ssnd i)) : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V))
    ConLeche.Semantics.interpStepF :=
  (ConLeche.Semantics.realize_interpStepF).mpr
    (Or.inl ⟨⟨_, by rw [h]; rfl⟩, hv⟩)


example {v a b : V} (h : v = upair a b) : Form.Realize Mem
    (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) b)
    ConLeche.Semantics.upairEqF :=
  (ConLeche.Semantics.realize_upairEqF).mpr h

example {v : V} (h : v = sing (empty : V)) : Form.Realize Mem
    (Form.snoc Form.nil v) ConLeche.Semantics.singEmptyF :=
  (ConLeche.Semantics.realize_singEmptyF).mpr h


example {v : V} (h : v = ptTag) : Form.Realize Mem
    (Form.snoc (fun _ : Fin 1 => v) (pt : V))
    ConLeche.Semantics.ptTagEqF :=
  (ConLeche.Semantics.realize_ptTagEqF).mpr h


example {v : V} (h : v = (pt : V)) : Form.Realize Mem
    (Form.snoc (fun _ : Fin 1 => v) (pt : V))
    ConLeche.Semantics.ptEqF :=
  (ConLeche.Semantics.realize_ptEqF).mpr h


example {v w : V} (k : Nat)
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : V))
      ConLeche.Semantics.unitSetAtVnatF)
    (hw : w = ConLeche.SetTheory.vnat k) :
    v = ConLeche.SetTheory.unitSetAt k :=
  ConLeche.Semantics.unitSetAtVnatF_apply k hR hw


example {v w : V} (k : Nat)
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : V))
      ConLeche.Semantics.unitAtVnatF)
    (hw : w = ConLeche.SetTheory.vnat k) :
    v = ConLeche.SetTheory.unitAt k :=
  ConLeche.Semantics.unitAtVnatF_apply k hR hw


example {x : V} (us : List Nat) (hx : x = ConLeche.Semantics.vnatListCode us) :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => x) (pt : V))
      (ConLeche.Semantics.vnatListNthF 0 (us.getD 0 0)) :=
  (ConLeche.Semantics.realize_vnatListNthF 0 (us.getD 0 0) us hx).mpr rfl


example {x v : V} (us : List Nat) (hx : x = ConLeche.Semantics.vnatListCode us)
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => x) v) (pt : V))
      (ConLeche.Semantics.vnatListNthQF 0 ConLeche.Semantics.unitSetAtVnatF)) :
    v = ConLeche.SetTheory.unitSetAt (us.getD 0 0) := by
  have hQ := (ConLeche.Semantics.realize_vnatListNthQF 0
    (qf := ConLeche.Semantics.unitSetAtVnatF)
    (Q := fun v w => (w = (empty : V) ∧ v = sing (pt : V)) ∨
      (¬ w = (empty : V) ∧ v = sing (empty : V)))
    (fun v w => ConLeche.Semantics.realize_unitSetAtVnatF) us hx).mp hR
  exact ConLeche.Semantics.unitSetAtVnatF_apply (us.getD 0 0)
    ((ConLeche.Semantics.realize_unitSetAtVnatF (v := v)
      (w := ConLeche.SetTheory.vnat (us.getD 0 0))).mpr hQ) rfl



example {cc uc : V}
    (hcc : cc = (ConLeche.Semantics.bconstCode Term.BConst.natZero : V)) :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (empty : V)) cc) uc) (pt : V))
      ConLeche.Semantics.constValueEasyF :=
  ConLeche.Semantics.realize_constValueEasyF.mpr (Or.inl ⟨hcc, rfl⟩)


example {v cc uc : V}
    (hR : Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : V))
      ConLeche.Semantics.constValueEasyF)
    (hcc : cc = (ConLeche.Semantics.bconstCode Term.BConst.punit : V))
    (huc : uc = ConLeche.Semantics.vnatListCode [0]) :
    v = ConLeche.SetModel.bval V Term.BConst.punit [0] :=
  ConLeche.Semantics.constValueEasyF_apply hR hcc huc



example {v X i : V} {c : Term.BConst} {us : List Nat}
    (hR : Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V))
      ConLeche.Semantics.constStepF)
    (hi : i = (ConLeche.Semantics.tmCode (Term.Term.const c us) : V)) :
    v = ConLeche.SetModel.bval V c us :=
  ConLeche.Semantics.constStepF_apply hR hi



example {X : V} :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (univ 0 : V)) X)
        (ConLeche.Semantics.tmCode (Term.Term.sort 0))) (pt : V))
      ConLeche.Semantics.sortZeroStepF :=
  ConLeche.Semantics.realize_sortZeroStepF_tmCode


example {v X i : V}
    (hR : Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V))
      ConLeche.Semantics.sortZeroStepF)
    (hi : i = (ConLeche.Semantics.tmCode (Term.Term.sort 0) : V)) :
    v = (univ 0 : V) :=
  ConLeche.Semantics.sortZeroStepF_apply hR hi



example {v X i : V}
    (hR' : Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V))
      ConLeche.Semantics.constStepF) :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V))
      ConLeche.Semantics.interpStepF2 :=
  ConLeche.Semantics.realize_interpStepF2.mpr (Or.inr (Or.inl hR'))



example {X : V} :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => ConLeche.SetModel.bval V Term.BConst.punit [3]) X)
        (ConLeche.Semantics.tmCode (Term.Term.const Term.BConst.punit [3]))) (pt : V))
      ConLeche.Semantics.interpStepF2 :=
  ConLeche.Semantics.realize_interpStepF2_const_tmCode (c := Term.BConst.punit) (us := [3])
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))


example {X : V} :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (univ 0 : V)) X)
        (ConLeche.Semantics.tmCode (Term.Term.sort 0))) (pt : V))
      ConLeche.Semantics.interpStepF2 :=
  ConLeche.Semantics.realize_interpStepF2_sortZero_tmCode



example {v X i : V}
    (hR : Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V))
      ConLeche.Semantics.interpStepF2)
    (hi : i = (ConLeche.Semantics.tmCode (Term.Term.const Term.BConst.quotInd []) : V)) :
    v = ConLeche.SetModel.bval V Term.BConst.quotInd [] :=
  ConLeche.Semantics.interpStepF2_apply_const hR hi


example {v X i : V}
    (hR : Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V))
      ConLeche.Semantics.interpStepF2)
    (hi : i = (ConLeche.Semantics.tmCode (Term.Term.sort 0) : V)) :
    v = (univ 0 : V) :=
  ConLeche.Semantics.interpStepF2_apply_sortZero hR hi



example {a : V} {p : V → Prop} {n : Nat} {φ : Form (n + 1)} {q : Fin n → V}
    (h : ∀ z, p z ↔ Form.Realize Mem (Form.snoc q z) φ) :
    sep a p = sepF a φ q :=
  sep_eq_sepF h


example {f : V → V} {a : V} {n : Nat} {ψ : Form (n + 2)} {p : Fin n → V}
    (hfun : ∀ x, x ∈ˢ a → ∃ y, Form.Realize Mem (Form.cons2 x y p) ψ ∧
      ∀ y', Form.Realize Mem (Form.cons2 x y' p) ψ → y' = y)
    (h : ∀ x y, x ∈ˢ a → (Form.Realize Mem (Form.cons2 x y p) ψ ↔ y = f x)) :
    image f a = imageF ψ p a hfun :=
  image_eq_imageF hfun h


example {f : V → V} {A : V} {n : Nat} {φ : Form (n + 2)} {p : Fin n → V}
    (hfun : ∀ x, x ∈ˢ A → ∃ z, Form.Realize Mem (Form.cons2 x z p) φ ∧
      ∀ z', Form.Realize Mem (Form.cons2 x z' p) φ → z' = z)
    (h : ∀ x w, x ∈ˢ A → (Form.Realize Mem (Form.cons2 x w p) φ ↔ w = f x)) :
    graph f A = graphF φ p A hfun :=
  graph_eq_graphF hfun h


example {A : V} {B : V → V} {n : Nat} {φ : Form (n + 2)} {p : Fin n → V}
    (hfun : ∀ x, x ∈ˢ A → ∃ z, Form.Realize Mem (Form.cons2 x z p) φ ∧
      ∀ z', Form.Realize Mem (Form.cons2 x z' p) φ → z' = z)
    (h : ∀ x y, x ∈ˢ A → (y ∈ˢ B x ↔ Form.Realize Mem (Form.cons2 x y p) φ)) :
    sigmaPairs A B = sigmaPairsF φ p A hfun :=
  sigmaPairs_eq_sigmaPairsF hfun h


example {v : V} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => v) (pt : V))
      ConLeche.Semantics.omegaEqF ↔
      v = (omega : V) :=
  ConLeche.Semantics.realize_omegaEqF


example {v : V} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => v) (pt : V))
      ConLeche.Semantics.natSuccEqF ↔
      v = ConLeche.SetModel.natSuccV V :=
  ConLeche.Semantics.realize_natSuccEqF


example {v cc uc : V} {c : Term.BConst} {us : List Nat}
    (hR : Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : V))
      ConLeche.Semantics.constValueNatF)
    (hcc : cc = (ConLeche.Semantics.bconstCode c : V))
    (huc : uc = (ConLeche.Semantics.vnatListCode us : V)) :
    v = ConLeche.SetModel.bval V c us :=
  ConLeche.Semantics.constValueNatF_apply hR hcc huc


example {v cc uc : V} :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : V))
      ConLeche.Semantics.constValueNatF ↔
      (cc = (ConLeche.Semantics.bconstCode .nat : V) ∧ v = (omega : V)) ∨
      (cc = (ConLeche.Semantics.bconstCode .natSucc : V) ∧
        v = ConLeche.SetModel.natSuccV V) :=
  ConLeche.Semantics.realize_constValueNatF


example {v cc uc : V} {c : Term.BConst} {us : List Nat}
    (hR : Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : V))
      ConLeche.Semantics.constValueF)
    (hcc : cc = (ConLeche.Semantics.bconstCode c : V))
    (huc : uc = (ConLeche.Semantics.vnatListCode us : V)) :
    v = ConLeche.SetModel.bval V c us :=
  ConLeche.Semantics.constValueF_apply hR hcc huc


example {v cc uc : V} :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : V))
      ConLeche.Semantics.constValueF ↔
      Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : V))
        ConLeche.Semantics.constValueEasyF ∨
      Form.Realize Mem
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : V))
        ConLeche.Semantics.constValueNatF :=
  ConLeche.Semantics.realize_constValueF


example {v g a b : V} :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) v) g) a) b)
      app2EqF ↔
      v = app (app g a) b :=
  realize_app2EqF


example {g a A z : V} :
    z ∈ˢ app2ImageF g a A ↔ ∃ x, x ∈ˢ A ∧ z = app (app g a) x :=
  mem_app2ImageF

example {g a A : V} :
    image (fun x => app (app g a) x) A = app2ImageF g a A :=
  image_app2_eq

example {x v g a : V} :
    Form.Realize Mem
      (Form.cons2 x v (Form.snoc (Form.snoc (fun _ : Fin 1 => g) a) (pt : V)))
      app2EqRepF ↔
      v = app (app g a) x :=
  realize_app2EqRepF


example {v F a m i : V} :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : V)) v)
        F) a) m) i)
      app3EqF ↔
      v = app (app (app F a) m) i :=
  realize_app3EqF


example {F a m A z : V} :
    z ∈ˢ app3ImageF F a m A ↔ ∃ x, x ∈ˢ A ∧ z = app (app (app F a) m) x :=
  mem_app3ImageF

example {F a m A : V} :
    image (fun x => app (app (app F a) m) x) A = app3ImageF F a m A :=
  image_app3_eq

example {x v F a m : V} :
    Form.Realize Mem
      (Form.cons2 x v
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => F) a) m) (pt : V)))
      app3EqRepF ↔
      v = app (app (app F a) m) x :=
  realize_app3EqRepF


example {U g A : V} (hU : ConLeche.IsUniverse (Mem (V := V)) U) (hA : A ∈ˢ U)
    (hval : ∀ x, x ∈ˢ A → app g x ∈ˢ U) :
    sUnion (appImageF g A) ∈ˢ U :=
  hU.sUnion_appImageF_val_mem hA hval



/-! ## Stage 88 example: the `sUnion` equality reader -/

example {v a : V} (h : Form.Realize Mem (Form.snoc (fun _ : Fin 1 => v) a)
    ConLeche.Semantics.sUnionEqF) : v = sUnion a :=
  ConLeche.Semantics.realize_sUnionEqF.mp h

example {a z : V} (h : z ∈ˢ sUnion a) : ∃ y, y ∈ˢ a ∧ z ∈ˢ y :=
  mem_sUnion.mp h



/-! ## Stage 89 example: the `binUnion` equality reader -/

example {v a b : V} (h : Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) b)
    ConLeche.Semantics.binUnionEqF) : v = binUnion a b :=
  ConLeche.Semantics.realize_binUnionEqF.mp h



/-! ## Stage 90 example: the `empty` equality reader -/

example {v : V} (h : Form.Realize Mem (Form.snoc Form.nil v)
    ConLeche.Semantics.emptyEqF) : v = (empty : V) :=
  ConLeche.Semantics.realize_emptyEqF.mp h



/-! ## Stage 91 example: the `kpairImage` equality reader -/

example {v a X : V} (h : Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X)
    ConLeche.Semantics.kpairImageEqF) : v = kpairImage a X :=
  ConLeche.Semantics.realize_kpairImageEqF.mp h



/-! ## Stage 92 example: the `unitSet` equality reader -/

example {v : V} (h : Form.Realize Mem (Form.snoc (fun _ : Fin 1 => v) (pt : V))
    ConLeche.Semantics.unitSetEqF) : v = (unitSet : V) :=
  ConLeche.Semantics.realize_unitSetEqF.mp h



/-! ## Stage 93 example: the swapped triple-application image `app3sImageF` -/

example {F m i A : V} :
    image (fun a => app (app (app F a) m) i) A = app3sImageF F m i A :=
  image_app3s_eq

example {F m i A z : V} (h : z ∈ˢ app3sImageF F m i A) :
    ∃ a, a ∈ˢ A ∧ z = app (app (app F a) m) i :=
  mem_app3sImageF.mp h



/-! ## Stage 94 example: `sUnionApp3sImageF` -/

example {F m i A : V} :
    sUnion (image (fun a => app (app (app F a) m) i) A) = sUnionApp3sImageF F m i A :=
  sUnion_image_app3s_eq

example {F m i A z : V} (h : z ∈ˢ sUnionApp3sImageF F m i A) :
    ∃ a, a ∈ˢ A ∧ ∃ s, s = app (app (app F a) m) i ∧ z ∈ˢ s :=
  mem_sUnionApp3sImageF'.mp h



/-! ## Stage 95 example: the swapped double-application image `app2sImageF` -/

example {g m A : V} :
    image (fun a => app (app g a) m) A = app2sImageF g m A :=
  image_app2s_eq

example {g m A z : V} (h : z ∈ˢ app2sImageF g m A) :
    ∃ a, a ∈ˢ A ∧ z = app (app g a) m :=
  mem_app2sImageF.mp h



/-! ## Stage 96 example: the `graphAppF` equality reader -/

example {v g A : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) g) A) (pt : V))
    graphAppEqF) : v = graphAppF g A :=
  realize_graphAppEqF.mp h



/-! ## Stage 97 example: the `sigmaPairsAppF` equality reader -/

example {v S A : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) S) A) (pt : V))
    sigmaPairsAppEqF) : v = sigmaPairsAppF S A :=
  realize_sigmaPairsAppEqF.mp h



/-! ## Stage 98 example: the `appImageF` equality reader -/

example {v g A : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) g) A) (pt : V))
    appImageEqF) : v = appImageF g A :=
  realize_appImageEqF.mp h



/-! ## Stage 99 example: the `app2ImageF` equality reader -/

example {v g a A : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) g) a) A) (pt : V))
    app2ImageEqF) : v = app2ImageF g a A :=
  realize_app2ImageEqF.mp h



/-! ## Stage 100 example: the `app3ImageF` equality reader -/

example {v F a m A : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) F) a) m) A) (pt : V))
    app3ImageEqF) : v = app3ImageF F a m A :=
  realize_app3ImageEqF.mp h


/-! ## Stage 101 example: the `sUnionApp3sImageF` equality reader -/

example {v F m i A : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) F) m) i) A) (pt : V))
    sUnionApp3sImageEqF) : v = sUnionApp3sImageF F m i A :=
  realize_sUnionApp3sImageEqF.mp h


/-! ## Stage 102 example: the `constGraphF` equality reader -/

example {v c A : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) c) A) (pt : V))
    constGraphEqF) : v = constGraphF c A :=
  realize_constGraphEqF.mp h


/-! ## Stage 103 example: the `app2sImageF` equality reader -/

example {v g m A : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) g) m) A) (pt : V))
    app2sImageEqF) : v = app2sImageF g m A :=
  realize_app2sImageEqF.mp h


/-! ## Stage 104 example: the `piSetAppNF` equality reader -/

example {v S A : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) S) A) (pt : V))
    piSetAppNFEqF) : v = piSetAppNF S A :=
  realize_piSetAppNFEqF.mp h


/-! ## Stage 105 example: the `sigmaConstGraphF` equality reader -/

example {v A D : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) A) D) (pt : V))
    sigmaConstGraphEqF) : v = sigmaConstGraphF A D :=
  realize_sigmaConstGraphEqF.mp h


/-! ## Stage 106 example: the `app3sImageF` equality reader -/

example {v F m i A : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) F) m) i) A) (pt : V))
    app3sImageEqF) : v = app3sImageF F m i A :=
  realize_app3sImageEqF.mp h


/-! ## Stage 107 example: the `interF` and `constImageF` equality readers -/

example {v a c : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) a) c)
    interFEqF) : v = interF a c :=
  realize_interFEqF.mp h

example {v c A : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) c) A)
    constImageEqF) : v = constImageF c A :=
  realize_constImageEqF.mp h


/-! ## Stage 108 example: the `sortStepF` reader with a universe-graph parameter -/

open ConLeche.Semantics in
example {v X i G : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V)) G)
    sortStepF) :
    (∃ y, i = kpair (vnat 1 : V) y) ∧ (∃ w, w = ssnd i ∧ v = app G w) :=
  realize_sortStepF.mp h


/-! ## Stage 109 example: the `univAppEqF` universe-at-a-numeral reader -/

open ConLeche.Semantics in
example {v w G : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) G) (pt : V)) univAppEqF) :
    v = app G w :=
  realize_univAppEqF.mp h


/-! ## Stage 110 example: the combined `interpStepF3` in the tower-graph context -/

open ConLeche.Semantics in
example {v X i G : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V)) G)
    interpStepF3) :
    (Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V)) interpStepF) ∨
    (Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V)) constStepF) ∨
    (Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V)) G)
      sortStepF) ∨
    (Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : V)) sortZeroStepF) :=
  realize_interpStepF3.mp h


/-! ## Stage 111 example: the `vnatListGetF` list-code element reader -/

open ConLeche.Semantics in
example (j : Nat) (us : List Nat) {x w : V} (hx : x = vnatListCode us)
    (h : Form.Realize Mem
      (Form.snoc (Form.snoc (fun _ : Fin 1 => x) w) (pt : V)) (vnatListGetF j)) :
    w = (vnat (us.getD j 0) : V) :=
  (realize_vnatListGetF j us hx).mp h


/-! ## Stage 112 example: the `tg`-at-a-numeral reader -/

open ConLeche.Semantics in
example {v w G : V} {k : Nat} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) G) (pt : V)) tgVnatF)
    (hw : w = (vnat k : V))
    (hG : ∀ n : Nat, app G (vnat n) = (univChain n : V)) :
    v = (tg k : V) :=
  tgVnatF_apply h hw hG


/-! ## Stage 113 example: the `sepF`-with-`tyF` equality reader -/

open ConLeche.Semantics in
example {v a U _p : V} (h : Form.Realize Mem
    (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) U) (pt : V)) sepTyFEqF) :
    v = sepF a tyF (Form.snoc (fun _ => U) (pt : V)) :=
  realize_sepTyFEqF.mp h

end ConLeche.SetTheory.DefinableAppEx
