module

public import ConLeche.SetModel.TaggedSum
public import ConLeche.SetTheory.Derive.Rec

@[expose] public section

/-!
# Countable unions (task #188)

The countable union `natUnion f = ⋃ₙ f n`, a member of `univ w` at
`w ≥ 1` when every `f n` is (`ω ∈ univ w`, `omega_mem_univ_succ`).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory.Tower

universe u

variable {V : Type u} [SetTheory V]

/-- The union of a countable family `f 0 ∪ f 1 ∪ …` (the ω-indexed union
through the tag fibre). -/
noncomputable def natUnion (f : Nat → V) : V :=
  sUnion (image (natFibre f) omega)

theorem mem_natUnion {f : Nat → V} {x : V} : x ∈ˢ natUnion f ↔ ∃ n, x ∈ˢ f n := by
  unfold natUnion
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨k, -, rfl⟩ := mem_image.mp hy
    obtain ⟨n, rfl, hfib⟩ := natFibre_eq_of_mem f hxy
    rw [hfib] at hxy
    exact ⟨n, hxy⟩
  · rintro ⟨n, hn⟩
    exact ⟨natFibre f (vnat n), mem_image.mpr ⟨vnat n, vnat_mem_omega n, rfl⟩,
      by rw [natFibre_vnat]; exact hn⟩

/-- A countable union of members of a positive axiomatic level is a
member (a size bound). -/
theorem natUnion_mem_tg_pos {w : Nat} (hw : w ≠ 0) {f : Nat → V}
    (h : ∀ n, f n ∈ˢ (tg w : V)) : natUnion f ∈ˢ (tg w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  unfold natUnion
  refine (tg_isUniverse (Nat.succ_ne_zero w')).famUnion_mem (omega_mem_tg_succ w') ?_
  intro k _
  rcases natFibre_cases f k with ⟨n, rfl, hfib⟩ | hempty
  · rw [hfib]
    exact h n
  · rw [hempty]
    exact empty_mem_tg _

/-! ## The definable countable union (`natUnionF`)

`natUnionF G = ⋃ {app G c | c ∈ˢ ω}` is the first-order twin of
`natUnion f` when the meta family `f` is internalized as a graph `G`
with `app G (vnat i) = f i`.  At nonstandard `c ∈ˢ ω` the junk fibre
`natFibre f c = empty` differs from `app G c`, so only the one-sided
bridge `natUnion_subset_natUnionF` holds over all of `ω`; on
standard-numeral domains the two-sided `sigmaPairs` bridge below holds. -/

/-- The definable union of a countable family read off a graph over `ω`:
`⋃ {app G c | c ∈ˢ ω}` — the first-order twin of `natUnion f` at
`app G (vnat i) = f i`. -/
noncomputable def natUnionF (G : V) : V :=
  sUnion (appImageF G omega)

theorem mem_natUnionF {G x : V} : x ∈ˢ natUnionF G ↔ ∃ c, c ∈ˢ omega ∧ x ∈ˢ app G c := by
  unfold natUnionF
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨c, hc, rfl⟩ := mem_appImageF.mp hy
    exact ⟨c, hc, hxy⟩
  · rintro ⟨c, hc, hxy⟩
    exact ⟨app G c, mem_appImageF.mpr ⟨c, hc, rfl⟩, hxy⟩

/-- A definable countable union of a member graph over `ω` is a member of
a positive axiomatic level — the first-order twin of
`natUnion_mem_tg_pos` (the value closure comes from `appImageF_mem`, so
only `G ∈ˢ tg w` is needed). -/
theorem natUnionF_mem_tg_pos {w : Nat} (hw : w ≠ 0) {G : V} (hG : G ∈ˢ (tg w : V)) :
    natUnionF G ∈ˢ (tg w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  exact (tg_isUniverse (Nat.succ_ne_zero w')).sUnion_mem
    ((tg_isUniverse (Nat.succ_ne_zero w')).appImageF_mem (empty_mem_tg _) hG
      (omega_mem_tg_succ w'))

/-- The meta countable union is contained in the definable one when the
graph `G` internalizes the family at the standard numerals. -/
theorem natUnion_subset_natUnionF {f : Nat → V} {G : V} (hG : ∀ i, app G (vnat i) = f i) :
    natUnion f ⊆ˢ natUnionF G := by
  intro x hx
  rw [mem_natUnion] at hx
  obtain ⟨n, hn⟩ := hx
  rw [mem_natUnionF]
  exact ⟨vnat n, vnat_mem_omega n, by rw [hG n]; exact hn⟩

/-- On a standard-numeral domain, the meta `sigmaPairs` at the `natFibre`
family equals the definable `sigmaPairsAppF` of the internalizing graph:
two-sided bridge (at nonstandard `c` the junk fibre `empty` differs from
`app G c`). -/
theorem sigmaPairs_natFibre_eq_sigmaPairsAppF {D : V} (hD : ∀ c, c ∈ˢ D → ∃ i, c = vnat i)
    {f : Nat → V} {G : V} (hG : ∀ i, app G (vnat i) = f i) :
    sigmaPairs D (natFibre f) = sigmaPairsAppF G D := by
  rw [sigmaPairsAppF_eq]
  exact sigmaPairs_congr fun c hc => by
    obtain ⟨i, rfl⟩ := hD c hc
    rw [natFibre_vnat, hG i]

end ConLeche.SetTheory.Tower
