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
    rw [mem_sigmaPairs]
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

example (hw : w ≠ 0) : sUnion (image (app (twoS V)) (unitSet : V)) ∈ˢ (tg w : V) :=
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

end ConLeche.SetTheory.DefinableAppEx
