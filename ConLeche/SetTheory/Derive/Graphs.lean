module

public import ConLeche.SetTheory.Derive.Pt
public import ConLeche.SetTheory.Derive.FormOps

@[expose] public section

/-!
# Function graphs, application, and the raw dependent-function set

* `graph F A = {⟨x, F x⟩ : x ∈ A}` — the set-theoretic function graph
  (replacement); never equal to `pt`, since `pt`'s element `ptTag` has
  an empty member and so is not a Kuratowski pair.
* `app f a = ⋃ {y : ⟨a, y⟩ ∈ f}` — untagged application on non-`pt`
  arguments; `app pt a = pt` is the tag that makes proofs degenerate
  (`app_pt` in the `SetTheory` interface).
* `sigmaPairs A B = {⟨x, y⟩ : x ∈ A, y ∈ B x}` — the raw dependent
  pair set (also the `w ≠ 0` sigma).
* `piSet A B ⊆ power (sigmaPairs A B)` — the total single-valued
  graphs: the `v ≠ 0` dependent function space.

The level-`0` truncations (`lam 0 = pt`, `pi 0` a truth value) live
in the numeral-indexed `piR`/`lamR` (`SetModel/Ops.lean`), which
dispatch on the regime numeral.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The function graph `{⟨x, F x⟩ : x ∈ A}`. -/
noncomputable def graph (F : V → V) (A : V) : V :=
  image (fun x => kpair x (F x)) A

theorem mem_graph {F : V → V} {A p : V} :
    p ∈ˢ graph F A ↔ ∃ x, x ∈ˢ A ∧ p = kpair x (F x) := mem_image

theorem graph_ne_pt {F : V → V} {A : V} : graph F A ≠ (pt : V) := by
  intro h
  obtain ⟨x, -, hx⟩ :=
    mem_graph.mp (h ▸ ptTag_mem_pt : (ptTag : V) ∈ˢ graph F A)
  exact ptTag_ne_kpair x (F x) hx

/-- No graph is a member of the point (a point law, task #342): the
point's one member `ptTag` has the empty set as a member, while every
member of a graph is a Kuratowski pair, hence nonempty. -/
theorem graph_not_mem_pt {F : V → V} {A : V} : ¬ graph F A ∈ˢ (pt : V) := by
  intro h
  have h' : (empty : V) ∈ˢ graph F A := mem_pt.mp h ▸ empty_mem_ptTag
  obtain ⟨x, -, hx⟩ := mem_graph.mp h'
  have hs : sing x ∈ˢ (empty : V) := hx ▸ mem_upair_left _ _
  exact not_mem_empty _ hs

theorem graph_congr {F F' : V → V} {A : V} (h : ∀ x, x ∈ˢ A → F x = F' x) :
    graph F A = graph F' A :=
  image_congr fun x hx => by rw [h x hx]

open Classical in
/-- Tagged set-theoretic application: the union of the values paired
with `a` in `f` — except at the proof point, which applies to `pt`
again. -/
noncomputable def app (f a : V) : V :=
  if f = pt then pt else
    sUnion (sepF (sUnion (sUnion f)) kpairMemF (Form.snoc (fun _ => a) f))

/-- Membership in the definable separation defining `app`: the predicate
`kpair a y ∈ˢ f` is the `Form` `kpairMemF` with parameters `a`, `f`. -/
theorem mem_appSep {f a y : V} :
    y ∈ˢ sepF (sUnion (sUnion f)) kpairMemF (Form.snoc (fun _ => a) f) ↔
      y ∈ˢ sUnion (sUnion f) ∧ kpair a y ∈ˢ f := by
  rw [mem_sepF, realize_kpairMemF]

/-- The definable image under `vsucc`: `{vsucc x | x ∈ˢ S}`. -/
noncomputable def vsuccImage (S : V) : V :=
  imageF vsuccF Form.nil S
    (fun x _ => ⟨vsucc x, realize_vsuccF.mpr rfl, fun _ hy => realize_vsuccF.mp hy⟩)

theorem mem_vsuccImage {S z : V} :
    z ∈ˢ vsuccImage S ↔ ∃ x, x ∈ˢ S ∧ z = vsucc x := by
  unfold vsuccImage
  rw [mem_imageF]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, realize_vsuccF.mp h⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, realize_vsuccF.mpr rfl⟩

/-- The definable image under `kpair a`: `{kpair a x | x ∈ˢ X}`. -/
noncomputable def kpairImage (a X : V) : V :=
  imageF kpairEqF' (fun _ => a) X
    (fun x _ => ⟨kpair a x, realize_kpairEqF'.mpr rfl, fun _ hy => realize_kpairEqF'.mp hy⟩)

theorem mem_kpairImage {a X z : V} :
    z ∈ˢ kpairImage a X ↔ ∃ x, x ∈ˢ X ∧ z = kpair a x := by
  unfold kpairImage
  rw [mem_imageF]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, realize_kpairEqF'.mp h⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, realize_kpairEqF'.mpr rfl⟩

/-- The meta-level `image (kpair a) X` is exactly the definable
`kpairImage a X`. -/
theorem image_kpair_eq {a X : V} : image (kpair a) X = kpairImage a X :=
  ext fun z => by rw [mem_image, mem_kpairImage]

/-- Definable tag-image closure (clause 6): the definable image of a
member under the tag function `kpair a` is a member — the first-order
twin of `image_mem` at `kpair a`. -/
theorem _root_.ConLeche.IsUniverse.kpairImage_mem {U a X : V} (hU : IsUniverse (Mem (V := V)) U)
    (he : (empty : V) ∈ˢ U) (ha : a ∈ˢ U) (hX : X ∈ˢ U) : kpairImage a X ∈ˢ U := by
  unfold kpairImage
  exact hU.imageF_mem hX fun x hx z hz => by
    rw [realize_kpairEqF'.mp hz]
    exact hU.kpair_mem he ha (hU.transitive hX hx)

/-- The definable constant image `{c | x ∈ˢ A}`: the `imageF` of the
relation `z = c` (variable `1 ↦ z`, parameter `0 ↦ c`) — the
first-order twin of `image (fun _ => c) A`. -/
noncomputable def constImageF (c A : V) : V :=
  imageF (n := 1) (Form.equal (⟨1, by omega⟩ : Fin 3) (⟨2, by omega⟩ : Fin 3))
    (fun _ => c) A
    (fun _ _ => ⟨c, by simp [Form.cons2], fun y hy => by simpa [Form.cons2] using hy⟩)

theorem mem_constImageF {c A z : V} :
    z ∈ˢ constImageF c A ↔ ∃ x, x ∈ˢ A ∧ z = c := by
  unfold constImageF
  rw [mem_imageF]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by simpa [Form.cons2] using h⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp [Form.cons2]⟩

theorem constImageF_eq_sing {c A x : V} (hx : x ∈ˢ A) :
    constImageF c A = sing c := by
  apply ext fun z => ?_
  rw [mem_constImageF, mem_sing]
  constructor
  · rintro ⟨_, -, rfl⟩; rfl
  · intro rfl; exact ⟨x, hx, rfl⟩

theorem app_pt (a : V) : app (pt : V) a = pt := by
  unfold app; exact ite_eq_left rfl

/-- Application computes on single-valued positions. -/
theorem app_eq_of_unique {f a b : V} (hf : f ≠ pt) (hab : kpair a b ∈ˢ f)
    (huniq : ∀ y, kpair a y ∈ˢ f → y = b) : app f a = b := by
  unfold app
  rw [ite_eq_right hf]
  have : sepF (sUnion (sUnion f)) kpairMemF (Form.snoc (fun _ => a) f) = sing b := by
    apply ext fun z => ?_
    rw [mem_appSep, mem_sing]
    constructor
    · exact fun ⟨_, hz⟩ => huniq z hz
    · rintro rfl
      refine ⟨?_, hab⟩
      exact mem_sUnion.mpr ⟨upair a z, mem_sUnion.mpr ⟨kpair a z, hab, mem_upair_right _ _⟩,
        mem_upair_right a z⟩
  rw [this, sUnion_sing]

/-- Beta on graphs. -/
theorem app_graph {F : V → V} {A a : V} (ha : a ∈ˢ A) :
    app (graph F A) a = F a := by
  refine app_eq_of_unique graph_ne_pt (mem_graph.mpr ⟨a, ha, rfl⟩) ?_
  intro y hy
  obtain ⟨x, -, hx⟩ := mem_graph.mp hy
  obtain ⟨rfl, rfl⟩ := kpair_inj hx
  rfl

/-! ## Definable function graphs (`graphF`, `sigmaPairsF`)

The first-order twins of `graph`/`sigmaPairs`: the graph of a
*definable* functional relation `φ` (replacement convention:
`Form.Realize Mem (Form.cons2 x z p) φ` means `z = F x`) is
`{⟨x, z⟩ : x ∈ˢ A, φ(x, z; p)}`, built by `imageF` from `replF` — no
meta-level `image` (the `repl` field) involved.  Since `graph F A` and
`sigmaPairs A B` coincide at `B x = sing (F x)`, one relation
`pairRelF` serves both. -/

/-- Variable map `Fin 3 → Fin (n+3)` reading `kpairEqF'` in the pair-relation
body: `(z, pair, x) ↦ (n+2, 1, 0)`, asserting `pair = ⟨x, z⟩`. -/
def pairRelMapK (n : Nat) : Fin 3 → Fin (n + 3) := fun i =>
  match i.val with
  | 0 => ⟨n + 2, by omega⟩
  | 1 => ⟨1, by omega⟩
  | _ => ⟨0, by omega⟩

/-- Variable map `Fin (n+2) → Fin (n+3)` reading the fibre formula `φ` in the
pair-relation body: `x ↦ 0`, `z ↦ n+2`, parameters unchanged. -/
def pairRelMapF (n : Nat) : Fin (n + 2) → Fin (n + 3) := fun i =>
  if i.val = 1 then ⟨n + 2, by omega⟩ else ⟨i.val, by omega⟩

/-- The pair-relation body: `y = ⟨x, z⟩ ∧ φ(x, z; p)` (variables `0 ↦ x`,
`1 ↦ y`, `2..n+1 ↦ p`, last ↦ bound `z`). -/
def pairRelBody (n : Nat) (φ : Form (n + 2)) : Form (n + 3) :=
  Form.and (Form.relabel (pairRelMapK n) kpairEqF') (Form.relabel (pairRelMapF n) φ)

/-- The pair relation `y = ⟨x, z⟩` for some `z` with `φ(x, z; p)`, in the
replacement convention (variables `0 ↦ x`, `1 ↦ y`, `i+2 ↦ p i`). -/
def pairRelF (n : Nat) (φ : Form (n + 2)) : Form (n + 2) :=
  Form.ex (pairRelBody n φ)

theorem realize_pairRelF {n : Nat} {φ : Form (n + 2)} {p : Fin n → V} {x y : V} :
    Form.Realize Mem (Form.cons2 x y p) (pairRelF n φ) ↔
      ∃ z, y = kpair x z ∧ Form.Realize Mem (Form.cons2 x z p) φ := by
  have hK : ∀ z : V, (Form.snoc (Form.cons2 x y p) z) ∘ pairRelMapK n =
      Form.cons2 z y (fun _ => x) := by
    intro z
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;>
      simp [pairRelMapK, Form.snoc, Form.cons2]
  have hF : ∀ z : V, (Form.snoc (Form.cons2 x y p) z) ∘ pairRelMapF n =
      Form.cons2 x z p := by
    intro z
    funext ⟨k, hk⟩
    by_cases hk0 : k = 0
    · subst hk0; simp [pairRelMapF, Form.snoc, Form.cons2]
    by_cases hk1 : k = 1
    · subst hk1; simp [pairRelMapF, Form.snoc, Form.cons2]
    · have hk2 : 2 ≤ k := by omega
      simp [pairRelMapF, Form.snoc, Form.cons2, hk0, hk1, hk]
  simp only [pairRelF, pairRelBody, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hK, hF, realize_kpairEqF']

theorem pairRelF_fun {n : Nat} {φ : Form (n + 2)} {p : Fin n → V} {A : V}
    (hfun : ∀ x, x ∈ˢ A → ∃ z, Form.Realize Mem (Form.cons2 x z p) φ ∧
      ∀ z', Form.Realize Mem (Form.cons2 x z' p) φ → z' = z) :
    ∀ x, x ∈ˢ A → ∃ y, Form.Realize Mem (Form.cons2 x y p) (pairRelF n φ) ∧
      ∀ y', Form.Realize Mem (Form.cons2 x y' p) (pairRelF n φ) → y' = y := by
  intro x hx
  obtain ⟨z, hφ, huniq⟩ := hfun x hx
  refine ⟨kpair x z, realize_pairRelF.mpr ⟨z, rfl, hφ⟩, fun y' hy' => ?_⟩
  obtain ⟨z', hz', hφ'⟩ := realize_pairRelF.mp hy'
  rw [hz', huniq z' hφ']

/-- The definable function graph `{⟨x, z⟩ : x ∈ˢ A, φ(x, z; p)}` — the
first-order twin of `graph`, from `replF` via `imageF`. -/
noncomputable def graphF {n : Nat} (φ : Form (n + 2)) (p : Fin n → V) (A : V)
    (hfun : ∀ x, x ∈ˢ A → ∃ z, Form.Realize Mem (Form.cons2 x z p) φ ∧
      ∀ z', Form.Realize Mem (Form.cons2 x z' p) φ → z' = z) : V :=
  imageF (pairRelF n φ) p A (pairRelF_fun hfun)

theorem mem_graphF {n : Nat} {φ : Form (n + 2)} {p : Fin n → V} {A z : V}
    (hfun : ∀ x, x ∈ˢ A → ∃ z, Form.Realize Mem (Form.cons2 x z p) φ ∧
      ∀ z', Form.Realize Mem (Form.cons2 x z' p) φ → z' = z) :
    z ∈ˢ graphF φ p A hfun ↔
      ∃ x, x ∈ˢ A ∧ ∃ w, z = kpair x w ∧ Form.Realize Mem (Form.cons2 x w p) φ := by
  unfold graphF
  rw [mem_imageF (pairRelF_fun hfun)]
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨w, h1, h2⟩ := realize_pairRelF.mp h
    exact ⟨x, hx, w, h1, h2⟩
  · rintro ⟨x, hx, w, h1, h2⟩
    exact ⟨x, hx, realize_pairRelF.mpr ⟨w, h1, h2⟩⟩

theorem graphF_ne_pt {n : Nat} {φ : Form (n + 2)} {p : Fin n → V} {A : V}
    (hfun : ∀ x, x ∈ˢ A → ∃ z, Form.Realize Mem (Form.cons2 x z p) φ ∧
      ∀ z', Form.Realize Mem (Form.cons2 x z' p) φ → z' = z) :
    graphF φ p A hfun ≠ (pt : V) := by
  intro h
  obtain ⟨x, -, w, hx, -⟩ := (mem_graphF hfun).mp (h ▸ ptTag_mem_pt)
  exact ptTag_ne_kpair x w hx

/-- Beta on definable graphs. -/
theorem app_graphF {n : Nat} {φ : Form (n + 2)} {p : Fin n → V} {A a w : V}
    (hfun : ∀ x, x ∈ˢ A → ∃ z, Form.Realize Mem (Form.cons2 x z p) φ ∧
      ∀ z', Form.Realize Mem (Form.cons2 x z' p) φ → z' = z)
    (ha : a ∈ˢ A) (hw : Form.Realize Mem (Form.cons2 a w p) φ) :
    app (graphF φ p A hfun) a = w := by
  refine app_eq_of_unique (graphF_ne_pt hfun) (mem_graphF hfun |>.mpr ⟨a, ha, w, rfl, hw⟩) ?_
  intro y hy
  obtain ⟨z₀, -, huniq⟩ := hfun a ha
  obtain ⟨x, -, z, hx, hφ⟩ := (mem_graphF hfun).mp hy
  obtain ⟨rfl, rfl⟩ := kpair_inj hx
  rw [huniq y hφ, huniq w hw]

/-- The raw dependent pair set `{⟨x, y⟩ : x ∈ˢ A, φ(x, y; p)}` — the
first-order twin of `sigmaPairs` (the same set as `graphF φ p A`). -/
noncomputable def sigmaPairsF {n : Nat} (φ : Form (n + 2)) (p : Fin n → V) (A : V)
    (hfun : ∀ x, x ∈ˢ A → ∃ z, Form.Realize Mem (Form.cons2 x z p) φ ∧
      ∀ z', Form.Realize Mem (Form.cons2 x z' p) φ → z' = z) : V :=
  graphF φ p A hfun

theorem mem_sigmaPairsF {n : Nat} {φ : Form (n + 2)} {p : Fin n → V} {A z : V}
    (hfun : ∀ x, x ∈ˢ A → ∃ z, Form.Realize Mem (Form.cons2 x z p) φ ∧
      ∀ z', Form.Realize Mem (Form.cons2 x z' p) φ → z' = z) :
    z ∈ˢ sigmaPairsF φ p A hfun ↔
      ∃ x, x ∈ˢ A ∧ ∃ y, z = kpair x y ∧ Form.Realize Mem (Form.cons2 x y p) φ :=
  mem_graphF hfun

/-- The raw dependent pair set `{⟨x, y⟩ : x ∈ A, y ∈ B x}`. -/

noncomputable def sigmaPairs (A : V) (B : V → V) : V :=
  sUnion (image (fun x => image (fun y => kpair x y) (B x)) A)

theorem mem_sigmaPairs {A p : V} {B : V → V} :
    p ∈ˢ sigmaPairs A B ↔ ∃ x, x ∈ˢ A ∧ ∃ y, y ∈ˢ B x ∧ p = kpair x y := by
  unfold sigmaPairs
  rw [mem_sUnion]
  constructor
  · rintro ⟨s, hs, hps⟩
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hps
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨image (fun y => kpair x y) (B x), mem_image.mpr ⟨x, hx, rfl⟩,
      mem_image.mpr ⟨y, hy, rfl⟩⟩

theorem sigmaPairs_congr {A : V} {B B' : V → V}
    (h : ∀ x, x ∈ˢ A → B x = B' x) : sigmaPairs A B = sigmaPairs A B' := by
  unfold sigmaPairs
  congr 1
  exact image_congr fun x hx => by rw [h x hx]

theorem _root_.ConLeche.IsUniverse.sigmaPairs_mem {U A : V} {B : V → V}
    (hU : IsUniverse (Mem (V := V)) U) (hA : A ∈ˢ U)
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ U) : sigmaPairs A B ∈ˢ U :=
  hU.famUnion_mem hA fun x hx =>
    hU.image_mem (hB x hx) fun _y hy =>
      hU.kpair_mem hA (hU.transitive hA hx) (hU.transitive (hB x hx) hy)

/-- Definable graph closure (clause 6): the definable graph of a member
under a functional definable relation with member-valued pairs is a
member.  First-order twin of `image_mem` for `graph`. -/
theorem _root_.ConLeche.IsUniverse.graphF_mem {U A : V} {n : Nat} {φ : Form (n + 2)}
    {p : Fin n → V}
    {hfun : ∀ x, x ∈ˢ A → ∃ z, Form.Realize Mem (Form.cons2 x z p) φ ∧
      ∀ z', Form.Realize Mem (Form.cons2 x z' p) φ → z' = z}
    (hU : IsUniverse (Mem (V := V)) U) (hA : A ∈ˢ U)
    (hval : ∀ x, x ∈ˢ A → ∀ w, Form.Realize Mem (Form.cons2 x w p) φ → kpair x w ∈ˢ U) :
    graphF φ p A hfun ∈ˢ U := by
  unfold graphF
  refine hU.imageF_mem hA (fun x hx y hy => ?_)
  obtain ⟨w, h1, h2⟩ := realize_pairRelF.mp hy
  rw [h1]
  exact hval x hx w h2

/-- Definable sigma-pair closure (clause 6): first-order twin of
`sigmaPairs_mem`. -/
theorem _root_.ConLeche.IsUniverse.sigmaPairsF_mem {U A : V} {n : Nat} {φ : Form (n + 2)}
    {p : Fin n → V}
    {hfun : ∀ x, x ∈ˢ A → ∃ z, Form.Realize Mem (Form.cons2 x z p) φ ∧
      ∀ z', Form.Realize Mem (Form.cons2 x z' p) φ → z' = z}
    (hU : IsUniverse (Mem (V := V)) U) (hA : A ∈ˢ U)
    (hval : ∀ x, x ∈ˢ A → ∀ y, Form.Realize Mem (Form.cons2 x y p) φ → kpair x y ∈ˢ U) :
    sigmaPairsF φ p A hfun ∈ˢ U :=
  hU.graphF_mem hA hval

/-- The set of total single-valued dependent graphs on `A` with fibres
`B`: the `v ≠ 0` dependent function space. -/
noncomputable def piSet (A : V) (B : V → V) : V :=
  sepF (power (sigmaPairs A B)) piSetF (fun _ => A)

theorem mem_piSet {A f : V} {B : V → V} :
    f ∈ˢ piSet A B ↔ f ⊆ˢ sigmaPairs A B ∧
      ∀ x, x ∈ˢ A → ∃ y, kpair x y ∈ˢ f ∧ ∀ y', kpair x y' ∈ˢ f → y' = y := by
  unfold piSet
  rw [mem_sepF, mem_power_iff_subset, realize_piSetF]

theorem piSet_congr {A : V} {B B' : V → V}
    (h : ∀ x, x ∈ˢ A → B x = B' x) : piSet A B = piSet A B' := by
  unfold piSet
  rw [sigmaPairs_congr h]

theorem _root_.ConLeche.IsUniverse.piSet_mem {U A : V} {B : V → V}
    (hU : IsUniverse (Mem (V := V)) U) (hA : A ∈ˢ U)
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ U) : piSet A B ∈ˢ U :=
  hU.mem_of_subset_mem (hU.power_mem (hU.sigmaPairs_mem hA hB)) sepF_subset

theorem graph_mem_piSet {A : V} {B F : V → V}
    (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x) : graph F A ∈ˢ piSet A B := by
  rw [mem_piSet]
  constructor
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := mem_graph.mp hp
    exact mem_sigmaPairs.mpr ⟨x, hx, F x, hF x hx, rfl⟩
  · intro x hx
    refine ⟨F x, mem_graph.mpr ⟨x, hx, rfl⟩, ?_⟩
    intro y' hy'
    obtain ⟨x', -, hx'⟩ := mem_graph.mp hy'
    obtain ⟨rfl, rfl⟩ := kpair_inj hx'
    rfl

theorem ne_pt_of_mem_piSet {A f : V} {B : V → V} (hf : f ∈ˢ piSet A B) :
    f ≠ pt := by
  rintro rfl
  have := (mem_piSet.mp hf).1 ptTag ptTag_mem_pt
  obtain ⟨x, -, y, -, hy⟩ := mem_sigmaPairs.mp this
  exact ptTag_ne_kpair x y hy

theorem app_mem_of_mem_piSet {A f a : V} {B : V → V}
    (hf : f ∈ˢ piSet A B) (ha : a ∈ˢ A) : app f a ∈ˢ B a := by
  obtain ⟨hsub, htot⟩ := mem_piSet.mp hf
  obtain ⟨y, hy, huniq⟩ := htot a ha
  rw [app_eq_of_unique (ne_pt_of_mem_piSet hf) hy huniq]
  obtain ⟨x', -, y', hy', hp⟩ := mem_sigmaPairs.mp (hsub _ hy)
  obtain ⟨rfl, rfl⟩ := kpair_inj hp
  exact hy'

/-- Eta: a member of `piSet A B` is the graph of its own application. -/
theorem eq_graph_app_of_mem_piSet {A f : V} {B : V → V}
    (hf : f ∈ˢ piSet A B) : graph (fun x => app f x) A = f := by
  obtain ⟨hsub, htot⟩ := mem_piSet.mp hf
  apply ext fun p => ?_
  rw [mem_graph]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, huniq⟩ := htot x hx
    rwa [app_eq_of_unique (ne_pt_of_mem_piSet hf) hy huniq]
  · intro hp
    obtain ⟨x, hx, y, -, rfl⟩ := mem_sigmaPairs.mp (hsub p hp)
    obtain ⟨y', hy', huniq⟩ := htot x hx
    refine ⟨x, hx, ?_⟩
    rw [app_eq_of_unique (ne_pt_of_mem_piSet hf) hy' huniq, huniq y hp]

/-- Members of `piSet A' B` that are graphs over `A` pin the domain:
every `x ∈ A'` lies in `A`. -/
theorem graph_dom_of_mem_piSet {A A' : V} {B F : V → V}
    (hf : graph F A ∈ˢ piSet A' B) : ∀ x, x ∈ˢ A' → x ∈ˢ A := by
  intro x hx
  obtain ⟨y, hy, -⟩ := (mem_piSet.mp hf).2 x hx
  obtain ⟨x', hx', hp⟩ := mem_graph.mp hy
  obtain ⟨rfl, rfl⟩ := kpair_inj hp
  exact hx'

/-! ### Off-domain and junk behavior of `app`

`app` is total: on a non-`pt` value with no pair at the argument —
in particular off a graph's domain, or on the canonical junk value
`empty` itself — it returns `empty`.  These lemmas record that a
graph's off-domain behavior is *canonical*: two graphs over the same
domain that agree on the domain agree everywhere, which is what makes
a **total** equality between interpreted function towers equivalent to
pointwise agreement on fitting inputs (`eq_of_mem_piSet_app_eq`). -/

theorem app_eq_empty_of_not_mem {f a : V} (hf : f ≠ pt)
    (h : ∀ y, ¬ kpair a y ∈ˢ f) : app f a = empty := by
  unfold app
  rw [ite_eq_right hf]
  refine eq_empty fun z hz => ?_
  obtain ⟨y, hy, -⟩ := mem_sUnion.mp hz
  exact h y (mem_appSep.mp hy).2

/-- `app` off a graph's domain is the canonical junk value. -/
theorem app_graph_of_not_mem {F : V → V} {A a : V} (ha : ¬ a ∈ˢ A) :
    app (graph F A) a = empty := by
  refine app_eq_empty_of_not_mem graph_ne_pt fun y hy => ?_
  obtain ⟨x, hx, hp⟩ := mem_graph.mp hy
  obtain ⟨rfl, rfl⟩ := kpair_inj hp
  exact ha hx

/-- `app` on the canonical junk value returns junk: junk propagates
through applications. -/
theorem app_empty (a : V) : app (empty : V) a = empty :=
  app_eq_empty_of_not_mem (Ne.symm pt_ne_empty)
    (fun _y hy => not_mem_empty _ hy)

/-- A member of `piSet` applied off the domain is junk. -/
theorem app_off_dom_of_mem_piSet {A f a : V} {B : V → V}
    (hf : f ∈ˢ piSet A B) (ha : ¬ a ∈ˢ A) : app f a = empty := by
  rw [← eq_graph_app_of_mem_piSet hf, app_graph_of_not_mem ha]

/-- Function extensionality for members of the raw dependent function space:
two total single-valued graphs over the same domain that agree under
application on every domain member are equal (off the domain both
apply to canonical junk, so nothing else distinguishes them). -/
theorem eq_of_mem_piSet_app_eq {A f g : V} {B B' : V → V}
    (hf : f ∈ˢ piSet A B) (hg : g ∈ˢ piSet A B')
    (h : ∀ x, x ∈ˢ A → app f x = app g x) : f = g := by
  rw [← eq_graph_app_of_mem_piSet hf, ← eq_graph_app_of_mem_piSet hg]
  exact graph_congr h

/- Opaque interface operator (see `Derive/Empty.lean`). -/
attribute [irreducible] app

end ConLeche.SetTheory
