module

public import ConLeche.SetTheory.Derive.Rec

@[expose] public section

/-!
# Recursion on `ω`

Set-theoretic recursion on `ω` is the definable recursion graph
`recGraph` (`Derive/Rec.lean`): `natrec z s n = app (recGraph z s) n`
(`natrecF`), with the base and step laws proved from
`recGraph_app_empty`/`recGraph_app_vsucc` alone.  No meta-level
`sep`/`image`/`repl` and no `vnat`-naming of `ω` members
(`mem_omega_iff`) is needed: `natrec_vnat` is meta-level induction on
the name `k`, and the typing theorem `natrec_mem_vsucc` runs through
`omega_induction` on the definable formula `recAppMemF`.  Off `ω`
the value is junk (`app` of a non-pair set), which no law constrains.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- Meta-level iteration of the set-level step function. -/
noncomputable def natIter (z s : V) : Nat → V
  | 0 => z
  | k + 1 => app (app s (vnat k)) (natIter z s k)

/-- Set-theoretic recursion on `ω`, via the definable recursion
graph `recGraph z s` (`natrecF` in `Derive/Rec.lean`). -/
noncomputable def natrec (z s n : V) : V := natrecF z s n

theorem natrec_empty (z s : V) : natrec z s (empty : V) = z :=
  natrecF_empty z s

theorem natrec_vsucc (z s : V) {n : V} (hn : n ∈ˢ (omega : V)) :
    natrec z s (vsucc n) = app (app s n) (natrec z s n) :=
  natrecF_vsucc z s hn

theorem natrec_vnat (z s : V) (k : Nat) :
    natrec z s (vnat k) = natIter z s k := by
  induction k with
  | zero => exact natrec_empty z s
  | succ k ih =>
    have h1 : (vnat (k + 1) : V) = vsucc (vnat k) := rfl
    have h2 : (natIter z s (k + 1) : V) = app (app s (vnat k)) (natIter z s k) := rfl
    rw [h1, h2, natrec_vsucc z s (vnat_mem_omega k), ih]

/-! ## The typing theorem as definable induction -/

/-- Variable map `Fin 4 → Fin 5` reading `appEqF`'s `(pt, v, g, u)` as
`(2, 4, 0, 3)` out of the `(G, M, pt, x, v)` context of the outer `.ex`. -/
def recAppM1 : Fin 4 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | 1 => ⟨4, by omega⟩
  | 2 => ⟨0, by omega⟩
  | _ => ⟨3, by omega⟩

/-- Variable map `Fin 4 → Fin 6` reading `appEqF`'s `(pt, v, g, u)` as
`(2, 5, 1, 3)` out of the `(G, M, pt, x, v, w)` context of the inner `.ex`. -/
def recAppM2 : Fin 4 → Fin 6 := fun i =>
  match i.val with
  | 0 => ⟨2, by omega⟩
  | 1 => ⟨5, by omega⟩
  | 2 => ⟨1, by omega⟩
  | _ => ⟨3, by omega⟩

/-- `app G x ∈ˢ app M x` (variables `0 → G`, `1 → M`,
`2 → pt`, bound `3 → x`). -/
def recAppMemF : Form 4 :=
  .ex (.and (Form.relabel recAppM1 appEqF)
    (.ex (.and (Form.relabel recAppM2 appEqF)
      (.mem ⟨4, by omega⟩ ⟨5, by omega⟩))))

theorem realize_recAppMemF {G M x : V} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => G) M) pt) x) recAppMemF ↔
      app G x ∈ˢ app M x := by
  have h1 : ∀ v x : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => G) M) pt) x) v) ∘ recAppM1 =
        Form.snoc (Form.snoc (Form.snoc (fun _ => pt) v) G) x := by
    intro v x
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have h2 : ∀ v w x : V,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => G) M) pt) x) v) w) ∘ recAppM2 =
        Form.snoc (Form.snoc (Form.snoc (fun _ => pt) w) M) x := by
    intro v w x
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [recAppMemF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    Form.realize_mem, h1, h2, realize_appEqF, Form.snoc_mk]
  constructor
  · rintro ⟨v, hv, w, hw, hvw⟩
    rw [hv, hw] at hvw
    exact hvw
  · intro h
    exact ⟨app G x, rfl, app M x, rfl, h⟩

/-- The recursion theorem with typing: the motive `M` is applied as a
set-theoretic function. -/
theorem natrec_mem_vsucc {M z s n : V}
    (hz : z ∈ˢ app M empty)
    (hs : ∀ k, k ∈ˢ (omega : V) → ∀ ih, ih ∈ˢ app M k →
      app (app s k) ih ∈ˢ app M (vsucc k))
    (hn : n ∈ˢ (omega : V)) : natrec z s n ∈ˢ app M n := by
  unfold natrec
  rw [natrecF_eq]
  have h := omega_induction
    (p := Form.snoc (Form.snoc (fun _ => recGraph z s) M) pt)
    (φ := recAppMemF)
    (by
      rw [realize_recAppMemF, recGraph_app_empty]
      exact hz)
    (fun x hx hIH => by
      rw [realize_recAppMemF] at hIH ⊢
      rw [recGraph_app_vsucc z s hx]
      exact hs x hx _ hIH)
    hn
  exact realize_recAppMemF.mp h

/- Opaque interface operator (see `Derive/Empty.lean`). -/
attribute [irreducible] natrec

end ConLeche.SetTheory
