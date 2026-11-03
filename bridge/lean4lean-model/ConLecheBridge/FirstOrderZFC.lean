import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import ConLeche.SetTheory.Core
import ConLeche.MainTheorem

/-!
# The main theorem in first-order ZFC (Mathlib model theory)

This module restates ConLeche's main theorem in the language of
first-order model theory, using Mathlib's `FirstOrder.Language`
machinery:

* `LSet` is the first-order language of pure set theory `L = {∈}` —
  one binary relation symbol, no function symbols;
* `ZFC` is the first-order theory of ZFC in `LSet`: the seven axioms
  (extensionality, empty set, pairing, union, power set, infinity,
  foundation) as `Sentence`s, plus the separation and replacement
  **schemas** as sets of sentences, one per formula with parameters;
* `inacc n` is the sentence "there exist `n` nested Grothendieck
  universes" (the first-order clauses of `ConLeche.IsUniverse`), and
  `ZFCInacc = ZFC ∪ { inacc n | n ∈ ω }` is ZFC with
  `{n inaccessibles | n ∈ ω}` — `n` inaccessibles being encoded as `n`
  nested universes `V_{κ₀} ∈ … ∈ V_{κₙ₋₁}`, the form the `SetTheory`
  interface consumes (`univChain`).

The main theorem, restated:

* `no_False_declaration_first_order` — if `M ⊨ ZFCInacc`, con-leche
  cannot accept a file declaring a theorem of type `False`.

It is proved by turning the first-order model into a
`ConLeche.SetTheory M` instance (`setTheory_of_ZFC_model`) and applying
`ConLeche.no_False_declaration`; the same instance restates
`ConLeche.model_exists` (every accepted environment has a model in `M`).

## The two bridge axioms

Everything except two steps is proved below.  The two steps a
first-order theory in `L = {∈}` cannot supply for an *arbitrary*
model `M` are stated as axioms (the same gap as in
`jasonrute/lean-intended-semantics`, `AXIOM_AUDIT.md`):

1. `replScheme_of_ZFC_model`: first-order replacement covers only
   *definable* relations, while `ConLeche.SetTheory.repl` is the
   meta-level scheme over all `p : M → M → Prop`.  For the intended
   models (e.g. Mathlib's `ZFSet`, where every relation is definable
   under `Classical.allZFSetDefinable`) the two coincide; for an
   arbitrary `M` they do not, so this is an axiom here.
2. `exists_univChain_of_inacc`: from `M ⊨ inacc n` for every standard
   `n` one gets finite tuples of nested universes, but extracting a
   coherent `ω`-chain needs an inverse-limit / dependent-choice
   argument over a non-finitely-branching tree, and each chain member
   must satisfy the *meta-level* fibre-replacement clause of
   `IsUniverse` (clause 5), again not first-order.  Axiomatized here.

The extensionality, pairing, union, power-set and regularity fields
are extracted from the corresponding `ZFC` sentences by actual proofs
(`ext_of_ZFC`, `pairing_of_ZFC`, `union_of_ZFC`, `power_of_ZFC`,
`regularity_of_ZFC`).

Nothing here is imported by the ConLeche libraries: like
`ConLecheBridge.Carneiro`, this lives in the separate bridge package so
that ConLeche never acquires a Mathlib dependency.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace ConLecheBridge

/-! ## The language `L = {∈}` and the membership predicate -/

/-- The first-order language of pure ZFC set theory: one binary
relation symbol `∈`, no function symbols. -/
def LSet : FirstOrder.Language.{0, 0} :=
  { Functions := fun _ => Empty
    Relations := fun n => match n with
      | 2 => Unit
      | _ => Empty }

/-- The membership relation symbol of `LSet`. -/
def memRel : LSet.Relations 2 := ()

/-- The membership atom `t₁ ∈ t₂` as a bounded formula. -/
def memF {n : ℕ} (t₁ t₂ : LSet.Term (Empty ⊕ Fin n)) : LSet.BoundedFormula Empty n :=
  memRel.boundedFormula₂ t₁ t₂

/-- Conjunction (no lattice instance on `BoundedFormula` in this
Mathlib version). -/
def conj {n : ℕ} (φ ψ : LSet.BoundedFormula Empty n) : LSet.BoundedFormula Empty n :=
  (φ.imp ψ.not).not

/-- Disjunction. -/
def disj {n : ℕ} (φ ψ : LSet.BoundedFormula Empty n) : LSet.BoundedFormula Empty n :=
  φ.not.imp ψ

/-- Membership as seen inside an `LSet`-structure. -/
def Mem (M : Type _) [LSet.Structure M] (x y : M) : Prop :=
  Structure.RelMap memRel ![x, y]

/-! ## The ZFC axiom sentences

Convention: a quantifier prefix `Q₀ … Qₖ₋₁` (outermost first) over
variables `&0 … &ₖ₋₁` is written as the suffix `body.qₖ₋₁…q₀`
(quantifiers bind the *last* variable, cf. `BoundedFormula.realize_all`
with `Fin.snoc`), so the written suffix reads innermost-first. -/

/-- Extensionality: `∀x ∀y, (∀z, z ∈ x ↔ z ∈ y) → x = y`. -/
def extensionality : LSet.Sentence :=
  let A : LSet.BoundedFormula Empty 3 := (memF (&2) (&0)).iff (memF (&2) (&1))
  let B : LSet.BoundedFormula Empty 2 := A.all.imp (Term.bdEqual (&0) (&1))
  B.all.all

/-- Empty set: `∃x ∀y, y ∉ x`. -/
def emptySet : LSet.Sentence :=
  let A : LSet.BoundedFormula Empty 2 := (memF (&1) (&0)).not
  A.all.ex

/-- Pairing: `∀x ∀y ∃z ∀w, w ∈ z ↔ (w = x ∨ w = y)`. -/
def pairing : LSet.Sentence :=
  let body : LSet.BoundedFormula Empty 4 :=
    (memF (&3) (&2)).iff (disj (Term.bdEqual (&3) (&0)) (Term.bdEqual (&3) (&1)))
  body.all.ex.all.all

/-- Union: `∀x ∃y ∀z, z ∈ y ↔ ∃w, z ∈ w ∧ w ∈ x`. -/
def unionAxiom : LSet.Sentence :=
  let inner : LSet.BoundedFormula Empty 4 := conj (memF (&3) (&0)) (memF (&2) (&3))
  let A : LSet.BoundedFormula Empty 3 := inner.ex
  let B : LSet.BoundedFormula Empty 3 := (memF (&2) (&1)).iff A
  B.all.ex.all

/-- Power set: `∀x ∃y ∀z, z ∈ y ↔ ∀w, w ∈ z → w ∈ x`. -/
def powerSet : LSet.Sentence :=
  let sub : LSet.BoundedFormula Empty 4 := (memF (&3) (&2)).imp (memF (&3) (&0))
  let A : LSet.BoundedFormula Empty 3 := sub.all
  let B : LSet.BoundedFormula Empty 3 := (memF (&2) (&1)).iff A
  B.all.ex.all

/-- Foundation (equivalent form): `∀x ∀y ∀z, (z ∈ y ∧ z ∈ x) → y ∉ x`. -/
def foundation : LSet.Sentence :=
  let body : LSet.BoundedFormula Empty 3 :=
    (conj (memF (&2) (&1)) (memF (&2) (&0))).imp (memF (&1) (&0)).not
  body.all.all.all

/-- Infinity: `∃x, (∅ ∈ x ∧ ∀y, y ∈ x → y ∪ {y} ∈ x)`, with `∅` and
`y ∪ {y}` expanded. -/
def infinity : LSet.Sentence :=
  let body : LSet.BoundedFormula Empty 6 :=
    let x := (&0 : LSet.Term (Empty ⊕ Fin 6))
    let u := (&1 : LSet.Term (Empty ⊕ Fin 6))
    let v := (&2 : LSet.Term (Empty ⊕ Fin 6))
    let y := (&3 : LSet.Term (Empty ⊕ Fin 6))
    let z := (&4 : LSet.Term (Empty ⊕ Fin 6))
    let w := (&5 : LSet.Term (Empty ⊕ Fin 6))
    conj (conj (memF u x) (memF v u).not)
      ((memF y x).imp (conj (memF z x)
        ((memF w z).iff (disj (memF w y) (Term.bdEqual w y)))))
  body.all.ex.all.all.ex.ex

/-! ## The separation and replacement schemas -/

/-- One instance of the separation schema: for `φ` a formula with `n`
parameters (in `Fin n`), `∀x ∀p ∃y ∀z, z ∈ y ↔ (z ∈ x ∧ φ(z, p))`. -/
def sepInst (n : ℕ) (φ : LSet.BoundedFormula (Fin n) 0) : LSet.Sentence :=
  let g : Fin n → Empty ⊕ Fin (n + 3) := fun i => Sum.inr ⟨1 + i.val, by omega⟩
  let φR : LSet.BoundedFormula Empty (n + 3) := φ.relabel g
  let z := (&⟨n + 2, by omega⟩ : LSet.Term (Empty ⊕ Fin (n + 3)))
  let y := (&⟨n + 1, by omega⟩ : LSet.Term (Empty ⊕ Fin (n + 3)))
  let x := (&0 : LSet.Term (Empty ⊕ Fin (n + 3)))
  let body : LSet.BoundedFormula Empty (n + 3) :=
    (memF z y).iff (conj (memF z x) φR)
  body.all.ex.alls

/-- One instance of the replacement schema: for `φ` a formula whose
first two free variables are the related pair `(z, y)` and whose
remaining `n` are parameters, `∀A ∀p ∃B ∀y, y ∈ B ↔ ∃z, z ∈ A ∧ φ(z, y, p)`. -/
def repInst (n : ℕ) (φ : LSet.BoundedFormula (Fin (n + 2)) 0) : LSet.Sentence :=
  let g : Fin (n + 2) → Empty ⊕ Fin (n + 4) := fun i =>
    if i.val = 0 then Sum.inr ⟨n + 3, by omega⟩
    else if i.val = 1 then Sum.inr ⟨n + 2, by omega⟩
    else Sum.inr ⟨i.val - 1, by omega⟩
  let φR : LSet.BoundedFormula Empty (n + 4) := φ.relabel g
  let z := (&⟨n + 3, by omega⟩ : LSet.Term (Empty ⊕ Fin (n + 4)))
  let A := (&0 : LSet.Term (Empty ⊕ Fin (n + 4)))
  let rhs : LSet.BoundedFormula Empty (n + 4) := conj (memF z A) φR
  let rhsEx : LSet.BoundedFormula Empty (n + 3) := rhs.ex
  let y := (&⟨n + 2, by omega⟩ : LSet.Term (Empty ⊕ Fin (n + 3)))
  let B := (&⟨n + 1, by omega⟩ : LSet.Term (Empty ⊕ Fin (n + 3)))
  let body : LSet.BoundedFormula Empty (n + 3) := (memF y B).iff rhsEx
  body.all.ex.alls

/-- The separation schema, as a set of sentences. -/
def sepSchema : Set LSet.Sentence :=
  { sepInst n φ | (n : ℕ) (φ : LSet.BoundedFormula (Fin n) 0) }

/-- The replacement schema, as a set of sentences. -/
def repSchema : Set LSet.Sentence :=
  { repInst n φ | (n : ℕ) (φ : LSet.BoundedFormula (Fin (n + 2)) 0) }

/-- **The first-order theory ZFC** in `L = {∈}`: the seven axioms plus
the separation and replacement schemas. -/
def ZFC : LSet.Theory :=
  { extensionality, emptySet, pairing, unionAxiom, powerSet, infinity, foundation }
    ∪ sepSchema ∪ repSchema

/-! ## ZFC + `{n inaccessibles | n ∈ ω}`, as nested Grothendieck universes -/

/-- Moves the single free variable of a `BoundedFormula Empty 1` to the
top (`&k`) of a `BoundedFormula Empty (k + 1)`. -/
def atTop {k : ℕ} (φ : LSet.BoundedFormula Empty 1) : LSet.BoundedFormula Empty (k + 1) :=
  φ.relabel (fun e => e.elim)

/-- The first-order clauses of "`u` is a Grothendieck universe"
(`ConLeche.IsUniverse`, clauses 1–4, plus nonemptiness): the
fibre-replacement clause 5 quantifies over meta-level relations and
is not first-order — see `exists_univChain_of_inacc`.

`u` is the free variable `&0`. -/
def isUnivFO : LSet.BoundedFormula Empty 1 :=
  -- nonempty: ∃x, x ∈ u
  let nonempty : LSet.BoundedFormula Empty 1 :=
    (memF (&1 : LSet.Term (Empty ⊕ Fin 2)) (&0 : LSet.Term (Empty ⊕ Fin 2))).ex
  -- transitivity: ∀y ∀z, y ∈ u → z ∈ y → z ∈ u
  let trans : LSet.BoundedFormula Empty 1 :=
    let body : LSet.BoundedFormula Empty 3 :=
      (memF (&1 : LSet.Term (Empty ⊕ Fin 3)) (&0 : LSet.Term (Empty ⊕ Fin 3))).imp
        ((memF (&2 : LSet.Term (Empty ⊕ Fin 3)) (&1 : LSet.Term (Empty ⊕ Fin 3))).imp
          (memF (&2 : LSet.Term (Empty ⊕ Fin 3)) (&0 : LSet.Term (Empty ⊕ Fin 3))))
    body.all.all
  -- subset closure: ∀y ∀z, y ∈ u → (∀w, w ∈ z → w ∈ y) → z ∈ u
  let subset : LSet.BoundedFormula Empty 1 :=
    let sub : LSet.BoundedFormula Empty 4 :=
      (memF (&3 : LSet.Term (Empty ⊕ Fin 4)) (&2 : LSet.Term (Empty ⊕ Fin 4))).imp
        (memF (&3 : LSet.Term (Empty ⊕ Fin 4)) (&1 : LSet.Term (Empty ⊕ Fin 4)))
    let subA : LSet.BoundedFormula Empty 3 := sub.all
    let body : LSet.BoundedFormula Empty 3 :=
      (memF (&1 : LSet.Term (Empty ⊕ Fin 3)) (&0 : LSet.Term (Empty ⊕ Fin 3))).imp
        (subA.imp (memF (&2 : LSet.Term (Empty ⊕ Fin 3)) (&0 : LSet.Term (Empty ⊕ Fin 3))))
    body.all.all
  -- power set closure: ∀y ∈ u, ∃p ∈ u, ∀z, (∀w, w ∈ z → w ∈ y) → z ∈ p
  let power : LSet.BoundedFormula Empty 1 :=
    let sub : LSet.BoundedFormula Empty 5 :=
      (memF (&4 : LSet.Term (Empty ⊕ Fin 5)) (&3 : LSet.Term (Empty ⊕ Fin 5))).imp
        (memF (&4 : LSet.Term (Empty ⊕ Fin 5)) (&1 : LSet.Term (Empty ⊕ Fin 5)))
    let subA : LSet.BoundedFormula Empty 4 := sub.all
    let body : LSet.BoundedFormula Empty 4 :=
      (memF (&1 : LSet.Term (Empty ⊕ Fin 4)) (&0 : LSet.Term (Empty ⊕ Fin 4))).imp
        (conj (memF (&2 : LSet.Term (Empty ⊕ Fin 4)) (&0 : LSet.Term (Empty ⊕ Fin 4))) subA)
    body.all.ex.all
  -- union closure: ∀s ∈ u, ∃q ∈ u, ∀z, z ∈ q ↔ ∃w, w ∈ s ∧ z ∈ w
  let unionC : LSet.BoundedFormula Empty 1 :=
    let inner : LSet.BoundedFormula Empty 5 :=
      conj (memF (&4 : LSet.Term (Empty ⊕ Fin 5)) (&1 : LSet.Term (Empty ⊕ Fin 5)))
        (memF (&3 : LSet.Term (Empty ⊕ Fin 5)) (&4 : LSet.Term (Empty ⊕ Fin 5)))
    let innerEx : LSet.BoundedFormula Empty 4 := inner.ex
    let body : LSet.BoundedFormula Empty 4 :=
      (memF (&1 : LSet.Term (Empty ⊕ Fin 4)) (&0 : LSet.Term (Empty ⊕ Fin 4))).imp
        ((memF (&3 : LSet.Term (Empty ⊕ Fin 4)) (&2 : LSet.Term (Empty ⊕ Fin 4))).iff innerEx)
    body.all.ex.all
  conj nonempty (conj trans (conj subset (conj power unionC)))

/-- The body of `inacc n`: `Uᵢ` is the variable `&i`, each `Uᵢ`
satisfies the universe clauses, and `Uᵢ ∈ Uᵢ₊₁` for `i + 1 < n`.
Built by recursion, adding the new universe at the top. -/
def univBody : (n : ℕ) → LSet.BoundedFormula Empty n
  | 0 => ⊤
  | 1 => atTop (k := 0) isUnivFO
  | n + 2 =>
    let newU : LSet.BoundedFormula Empty (n + 2) := atTop (k := n + 1) isUnivFO
    let chain : LSet.BoundedFormula Empty (n + 2) :=
      memF (&⟨n, by omega⟩ : LSet.Term (Empty ⊕ Fin (n + 2)))
        (&⟨n + 1, by omega⟩ : LSet.Term (Empty ⊕ Fin (n + 2)))
    let old : LSet.BoundedFormula Empty (n + 2) := (univBody (n + 1)).liftAt 1 (n + 1)
    conj newU (conj chain old)

/-- **`inacc n`**: "there exist `n` nested Grothendieck universes"
`U₀ ∈ U₁ ∈ … ∈ Uₙ₋₁` — the first-order encoding of "there are `n`
inaccessible cardinals" (`V_{κᵢ} ∈ V_{κᵢ₊₁}` for `κᵢ` inaccessible). -/
def inacc (n : ℕ) : LSet.Sentence := (univBody n).exs

/-- **ZFC + `{n inaccessibles | n ∈ ω}`**: the first-order theory whose
models are the models of ZFC with `ω`-many inaccessible cardinals. -/
def ZFCInacc : LSet.Theory := ZFC ∪ Set.range inacc

/-! ## Extraction of the ZF⁻ operations from `M ⊨ ZFC` -/

variable {M : Type _} [LSet.Structure M]

@[simp] theorem realize_conj {n : ℕ} (φ ψ : LSet.BoundedFormula Empty n) (v : Empty → M)
    (xs : Fin n → M) : (conj φ ψ).Realize v xs ↔ (φ.Realize v xs ∧ ψ.Realize v xs) := by
  simp [conj, BoundedFormula.realize_imp, BoundedFormula.realize_not, not_imp, not_not]

@[simp] theorem realize_disj {n : ℕ} (φ ψ : LSet.BoundedFormula Empty n) (v : Empty → M)
    (xs : Fin n → M) : (disj φ ψ).Realize v xs ↔ (φ.Realize v xs ∨ ψ.Realize v xs) := by
  simp [disj, BoundedFormula.realize_imp, BoundedFormula.realize_not, imp_iff_not_or, not_not]

/-- Extensionality, extracted from `M ⊨ ZFC`. -/
theorem ext_of_ZFC (hZFC : M ⊨ ZFC) : ∀ x y : M, (∀ z, Mem M z x ↔ Mem M z y) → x = y := by
  have h : M ⊨ extensionality := hZFC.realize_of_mem _ (by simp [ZFC])
  simp [extensionality, memF, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_iff, BoundedFormula.realize_imp, BoundedFormula.realize_bdEqual, Term.realize, Fin.snoc] at h
  exact h

/-- Pairing, extracted from `M ⊨ ZFC`. -/
theorem pairing_of_ZFC (hZFC : M ⊨ ZFC) :
    ∀ x y : M, ∃ z : M, ∀ w, Mem M w z ↔ (w = x ∨ w = y) := by
  have h : M ⊨ pairing := hZFC.realize_of_mem _ (by simp [ZFC])
  simp [pairing, memF, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_bdEqual, Term.realize, Fin.snoc] at h
  exact h

/-- Union, extracted from `M ⊨ ZFC`. -/
theorem union_of_ZFC (hZFC : M ⊨ ZFC) :
    ∀ x : M, ∃ y : M, ∀ z, Mem M z y ↔ ∃ w, Mem M w x ∧ Mem M z w := by
  have h : M ⊨ unionAxiom := hZFC.realize_of_mem _ (by simp [ZFC])
  simp [unionAxiom, memF, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, Term.realize, Fin.snoc] at h
  exact h

/-- Power set, extracted from `M ⊨ ZFC`. -/
theorem power_of_ZFC (hZFC : M ⊨ ZFC) :
    ∀ x : M, ∃ y : M, ∀ z, Mem M z y ↔ ∀ w, Mem M w z → Mem M w x := by
  have h : M ⊨ powerSet := hZFC.realize_of_mem _ (by simp [ZFC])
  simp [powerSet, memF, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_imp, Term.realize, Fin.snoc] at h
  exact h

/-- Regularity, extracted from `M ⊨ ZFC` (foundation). -/
theorem regularity_of_ZFC (hZFC : M ⊨ ZFC) :
    ∀ x : M, (∃ y, Mem M y x) → ∃ y, Mem M y x ∧ ¬ ∃ z, Mem M z y ∧ Mem M z x := by
  have h : M ⊨ foundation := hZFC.realize_of_mem _ (by simp [ZFC])
  simp [foundation, memF, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, Term.realize, Fin.snoc] at h
  intro x ⟨y, hy⟩
  refine ⟨y, hy, ?_⟩
  rintro ⟨z, hzy, hzx⟩
  exact h x y z hzy hzx hy

/-! ## The two bridge axioms (the gap between first-order and the
`SetTheory` scheme) -/

/-- **Bridge axiom 1.**  First-order replacement covers only definable
relations; `ConLeche.SetTheory.repl` is the meta-level scheme over all
`p : M → M → Prop`.  For the intended models (Mathlib's `ZFSet`, where
every relation is definable under `Classical.allZFSetDefinable` — the
route `ConLecheBridge.setTheoryOfChain` takes) the two coincide; for
an arbitrary first-order model they do not. -/
axiom replScheme_of_ZFC_model (M : Type _) [LSet.Structure M] (hZFC : M ⊨ ZFC) :
    ∀ a : M, ∀ p : M → M → Prop,
      (∀ x, Mem M x a → ∃ y, p x y ∧ ∀ y', p x y' → y' = y) →
      ∃ b : M, ∀ y, Mem M y b ↔ ∃ x, Mem M x a ∧ p x y

/-- **Bridge axiom 2.**  From `M ⊨ inacc n` for every standard `n` one
gets finite tuples of nested universes; extracting a coherent `ω`-chain
needs an inverse-limit argument over a non-finitely-branching tree, and
the meta-level fibre-replacement clause of `IsUniverse` is not
first-order.  Axiomatized here. -/
axiom exists_univChain_of_inacc (M : Type _) [LSet.Structure M] (hInacc : ∀ n, M ⊨ inacc n) :
    ∃ univChain : ℕ → M,
      (∀ n, Mem M (univChain n) (univChain (n + 1))) ∧
      ∀ n, ConLeche.IsUniverse (Mem M) (univChain n)

/-! ## The `SetTheory` instance and the restated main theorem -/

set_option warn.classDefReducibility false in
/-- A first-order model `M` of `ZFC + {n inaccessibles | n ∈ ω}`
carries ConLeche's `SetTheory` interface: the ZF⁻ fields are extracted
from the `ZFC` sentences (`ext_of_ZFC` … `regularity_of_ZFC`), the
replacement scheme and the `ω`-chain of universes come from the two
bridge axioms above. -/
noncomputable def setTheory_of_ZFC_model (M : Type _) [LSet.Structure M] (hZFC : M ⊨ ZFC)
    (hInacc : ∀ n, M ⊨ inacc n) : ConLeche.SetTheory M where
  Mem := Mem M
  ext := fun h => ext_of_ZFC hZFC _ _ h
  upair a b := Classical.choose (pairing_of_ZFC hZFC a b)
  mem_upair {z a b} := Classical.choose_spec (pairing_of_ZFC hZFC a b) z
  sUnion x := Classical.choose (union_of_ZFC hZFC x)
  mem_sUnion {z x} := Classical.choose_spec (union_of_ZFC hZFC x) z
  power x := Classical.choose (power_of_ZFC hZFC x)
  mem_power {z x} := Classical.choose_spec (power_of_ZFC hZFC x) z
  regularity := regularity_of_ZFC hZFC
  repl := replScheme_of_ZFC_model M hZFC
  univChain := Classical.choose (exists_univChain_of_inacc M hInacc)
  univChain_mem n := (Classical.choose_spec (exists_univChain_of_inacc M hInacc)).1 n
  univChain_univ n := (Classical.choose_spec (exists_univChain_of_inacc M hInacc)).2 n

open ConLeche ConLeche.Frontend ConLeche.Cached in
/-- **The main corollary, restated in first-order ZFC.**  If `M` is a
first-order model of `ZFC + {n inaccessibles | n ∈ ω}`, then con-leche
cannot accept a file that declares a theorem of type `False` (in the
`jsonWithTheoremFalse` shape). -/
theorem no_False_declaration_first_order (M : Type _) [LSet.Structure M]
    (hZFC : M ⊨ ZFC) (hInacc : ∀ n, M ⊨ inacc n)
    (pins : List NatOpPinSet) (chunks : List ByteArray)
    (h : jsonWithTheoremFalse chunks) :
    ∃ e, (do
      let pre ← builtinPreludeE
      let r ← parseChunks chunks
      let ds := preparePrelude pre r.decls
      checkDecls .verified pins ds) = .error e := by
  exact @ConLeche.no_False_declaration M (setTheory_of_ZFC_model M hZFC hInacc) pins chunks h

/--
info: 'ConLecheBridge.no_False_declaration_first_order' depends on axioms: [propext,
 Classical.choice,
 exists_univChain_of_inacc,
 replScheme_of_ZFC_model,
 Quot.sound]
-/
#guard_msgs in
#print axioms no_False_declaration_first_order

end ConLecheBridge
