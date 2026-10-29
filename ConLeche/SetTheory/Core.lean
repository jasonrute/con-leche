module

@[expose] public section

/-!
# The axiomatic core: first-order ZF⁻ plus an ω-chain of Grothendieck universes

The `SetTheory` class below is the *entire* axiomatic interface of the
consistency proof; every operator and law the model construction uses
(`ConLeche/SetTheory/Basic.lean`) is *derived* from it in
`ConLeche/SetTheory/Derive/*`, never assumed.

The set-theoretic axioms are **extensionality, pairing, union, power
set, regularity, the replacement scheme, and an ω-chain of
Grothendieck universes** `univChain 0 ∈ univChain 1 ∈ …`.  Every
axiom is a FIRST-ORDER statement over the membership relation: the
replacement scheme is encoded the standard way, as a scheme over
Prop-valued functional relations (`∀ a p, (∀ x ∈ a, ∃ y, p x y ∧ ∀ y', p x y' → y' = y) →
∃ b, ∀ y, y ∈ b ↔ ∃ x ∈ a ∧ p x y`, one instance per
meta-level relation `p : V → V → Prop` — exactly how Mathlib's
`ZFSet` carries it under `Classical.allZFSetDefinable`), and a
Grothendieck universe is given by its five first-order closure clauses
(`IsUniverse`): transitivity, subsets of members are members, power
sets stay inside, unions of members stay inside, and fibre-wise
replacement closure.  Infinity and separation are derivable and
therefore absent.

This calibrates the axiomatic strength to exactly what the checker
consumes — the ω-indexed tower `univ 0, univ 1, univ 2, …` — and to
the known consistency strength of Lean itself: ZFC plus a strictly
increasing ω-sequence of inaccessible cardinals — the
`OmegaInaccessibles` hypothesis
`∃ κ : ℕ → Cardinal, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible`
of Mario Carneiro, *The Type Theory of Lean*, master's thesis,
Carnegie Mellon University, 2019, §1.2.  Under that hypothesis the intended
model takes `univChain n := V_{κ n}`.  This is strictly weaker than
full Tarski–Grothendieck set theory (Tarski's Axiom A places a
universe above *every* set, a proper class of inaccessibles; cf. the
Mizar axiomatics, A. Trybulec, *Tarski Grothendieck Set Theory*,
Formalized Mathematics 1(1), 1990).

Deliberate deviations from a textbook first-order presentation:

* **Replacement is a scheme over meta-level relations.**  A
  first-order theory states one replacement axiom per *formula*;
  quantifying over `p : V → V → Prop` at the meta-level is the same
  scheme (Lean's `Prop` plays the role of the formula universe), and
  it is the form the bridge to Mathlib's `ZFSet` instantiates
  (`Classical.allZFSetDefinable`).  The previous formulation took an
  arbitrary function `V → V` as the image operator — a
  *second-order* strengthening (a class function, not a relation);
  the image of a set under a function is now *derived* from the
  scheme (`Derive/Sep.lean`).
* **Choice is not a field.**  A first-order axiomatization of ZFC
  must assert choice; here the ambient logic is Lean with
  `Classical.choice`, and every set-level form of choice over `V`
  (the global selector `schoice`, and the Jech-form choice-function
  statement, *Set Theory*, §5) is a *theorem* — replacement applied
  to a classically chosen selector.  See
  `ConLeche/SetTheory/Derive/Choice.lean`.  Asserting it here would
  add redundant axiomatic content; global choice is supplied by the
  meta-logic, not by this class.
* **No `nonempty` field.**  First-order logic's nonempty domain is
  implied: `univChain` already exhibits elements of `V`.

Everything else — the empty set, separation, ordered pairs, infinity,
function graphs, the universe tower, quotients — is constructed in
`ConLeche/SetTheory/Derive/*`.
-/

namespace ConLeche

universe u

/-- A Grothendieck universe, as five first-order closure clauses (SGA 4,
Exp. I, Appendix): a transitive set closed under subsets of members,
power sets of members, unions of members, and fibre-wise replacement.
The five clauses, in order:

1. *transitivity*: members of members are members;
2. *subsets of members are members*;
3. *power sets stay inside*: some member contains all subsets of a
   member (with clause 2 this makes `power y` itself a member);
4. *unions stay inside*: the union of a member's members has a member
   containing exactly them (with clause 2 this makes `sUnion s`
   itself a member);
5. *fibre-wise replacement*: the image of a member under a
   relation functional on it, with all values in `u`, is contained in
   a member.

The fibre-wise form of clause 5 (functional on each member, with the
witnessed values in `u`) is what the intended models satisfy: unrestricted relativized
replacement is *false* for `V_κ` in the meta-theory (the image of
`V_κ` under `x ↦ {V_κ}` is not a member of `V_κ`), while the
fibre-wise form holds because an image inside `V_κ` of a member has
cardinality below κ (the bridge, `isUniverse_vonNeumann`).  It is
also exactly what the derivation needs: the closure laws of
`Derive/Universe.lean` are all instances of it. -/
def IsUniverse {V : Type u} (mem : V → V → Prop) (u : V) : Prop :=
  (∀ y z, mem y u → mem z y → mem z u) ∧
  (∀ y z, mem y u → (∀ w, mem w z → mem w y) → mem z u) ∧
  (∀ y, mem y u → ∃ p, mem p u ∧ ∀ z, (∀ w, mem w z → mem w y) → mem z p) ∧
  (∀ s, mem s u → ∃ q, mem q u ∧ ∀ z, mem z q ↔ ∃ w, mem w s ∧ mem z w) ∧
  (∀ a, mem a u → ∀ p : V → V → Prop,
    (∀ x, mem x a → ∃ y, mem y u ∧ p x y ∧ ∀ y', p x y' → y' = y) →
    ∃ b, mem b u ∧ ∀ y, mem y b ↔ ∃ x, mem x a ∧ p x y)

/-- A model of set theory of exactly the strength the checker needs:
membership, the six ZF⁻ axioms (extensionality, pairing, union, power
set, regularity, the first-order replacement scheme), and an ω-chain of
Grothendieck universes.  Infinity is derivable; choice is inherited
from the meta-logic (`Classical.choice`); see the module docstring. -/
class SetTheory (V : Type u) where
  /-- Set membership. -/
  Mem : V → V → Prop
  /-- Extensionality: sets with the same members are equal. -/
  ext : ∀ {x y : V}, (∀ z, Mem z x ↔ Mem z y) → x = y
  /-- Pairing: the unordered pair. -/
  upair : V → V → V
  /-- Characterization of the unordered pair. -/
  mem_upair : ∀ {z a b : V}, Mem z (upair a b) ↔ z = a ∨ z = b
  /-- Union: the union of the members. -/
  sUnion : V → V
  /-- Characterization of the union. -/
  mem_sUnion : ∀ {z x : V}, Mem z (sUnion x) ↔ ∃ y, Mem y x ∧ Mem z y
  /-- Power set. -/
  power : V → V
  /-- Characterization of the power set: members are the subsets. -/
  mem_power : ∀ {z x : V}, Mem z (power x) ↔ ∀ w, Mem w z → Mem w x
  /-- Regularity: every nonempty set has an `∈`-minimal member. -/
  regularity : ∀ x : V, (∃ y, Mem y x) → ∃ y, Mem y x ∧ ¬ ∃ z, Mem z y ∧ Mem z x
  /-- **Replacement, the first-order scheme**: the image of a set
  under a functional relation `p`, as a relation, is a set.  One
  instance per meta-level relation — the standard encoding of the
  scheme (Mathlib's `ZFSet` carries it the same way, under
  `Classical.allZFSetDefinable`). -/
  repl : ∀ a : V, ∀ p : V → V → Prop,
    (∀ x, Mem x a → ∃ y, p x y ∧ ∀ y', p x y' → y' = y) →
    ∃ b : V, ∀ y, Mem y b ↔ ∃ x, Mem x a ∧ p x y
  /-- An ω-chain of Grothendieck universes: the sets interpreting the
  universe tower (Carneiro's ω-many inaccessibles, op. cit.;
  intended model `V_{κ n}`). -/
  univChain : Nat → V
  /-- The chain increases strictly: each universe is a member of the
  next. -/
  univChain_mem : ∀ n : Nat, Mem (univChain n) (univChain (n + 1))
  /-- Each chain member is a Grothendieck universe (`IsUniverse`). -/
  univChain_univ : ∀ n : Nat, IsUniverse Mem (univChain n)

namespace SetTheory

@[inherit_doc] scoped infix:50 " ∈ˢ " => Mem

variable {V : Type u} [SetTheory V]

/-- Subset, from membership. -/
protected def Subset (x y : V) : Prop := ∀ z, z ∈ˢ x → z ∈ˢ y

@[inherit_doc] scoped infix:50 " ⊆ˢ " => SetTheory.Subset

theorem Subset.refl (x : V) : x ⊆ˢ x := fun _ hz => hz

theorem Subset.trans {x y z : V} (h₁ : x ⊆ˢ y) (h₂ : y ⊆ˢ z) : x ⊆ˢ z :=
  fun w hw => h₂ w (h₁ w hw)

theorem Subset.antisymm {x y : V} (h₁ : x ⊆ˢ y) (h₂ : y ⊆ˢ x) : x = y :=
  ext fun z => ⟨h₁ z, h₂ z⟩

theorem mem_power_iff_subset {z x : V} : z ∈ˢ power x ↔ z ⊆ˢ x := mem_power

end SetTheory

end ConLeche
