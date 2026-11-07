module

public import ConLeche.SetModel.Value

@[expose] public section

/-!
# `interp` — the interpretation (task #151, tier B; task #342, L14a)

`interp V ρ e` maps a semantic term to an element of the set-theoretic
universe `V` under a variable environment `ρ : Nat → V`.

* **Total.**  A plain function on terms — never derivation-indexed, so
  coherence is not a theorem to prove but the absence of a question.
* **Environment-free.**  No global environment, no `Option`, no
  auxiliary truthfulness predicate: `interp` is a function of the term
  and the valuation alone.
* **The regime is read off the values.**  A Π-type is a truth value
  exactly when every fibre over its domain is one (`piV`), an
  abstraction is the point exactly when every body value over its
  domain is (`lamV`), `SetModel/Ops.lean`.  Over an empty domain both
  read "proposition": the function space is `{pt}`, the abstraction the
  point.

| term | value |
|---|---|
| `bvar i` | `ρ i` |
| `sort u` | `univ u` |
| `const c us` | `bval c us` |
| `app f a` | `app ⟦f⟧ ⟦a⟧` (`app pt _ = pt`) |
| `lam A b` | `lamV ⟦A⟧ (fun x => ⟦b⟧ₓ)` |
| `pi A B` | `piV ⟦A⟧ (fun x => ⟦B⟧ₓ)` |
| `letE v b` | `⟦b⟧` at `cons ⟦v⟧ ρ` |
| `eqE a b` | `eqv ⟦a⟧ ⟦b⟧` |
| `fst e` / `snd e` | `sfst ⟦e⟧` / `ssnd ⟦e⟧` |
| `prf` | `pt` |

β holds on the domain with no other premise (`app_lamV`).
-/

namespace ConLeche.Semantics
open ConLeche.Term (Term)
open ConLeche.SetModel

open SetTheory

universe w

/-! ## Variable environments

Pure `Nat → V` plumbing; no set theory is involved, so this section
carries no `SetTheory` instance.  These are `ConLeche.Term.Semantics`'
`cons`/`shiftE`/`instE` with `V` implicit; they are duplicated rather
than imported so that `Interp/*` depends on **no** module built over
the collapse operators. -/

section Env

variable {V : Type w}

/-- Extend an environment with a new innermost binding. -/
def cons (x : V) (ρ : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => ρ i

@[simp] theorem cons_zero (x : V) (ρ : Nat → V) : cons x ρ 0 = x := rfl
@[simp] theorem cons_succ (x : V) (ρ : Nat → V) (i : Nat) :
    cons x ρ (i + 1) = ρ i := rfl

/-- The environment transformation matching `Term.liftN n · k`. -/
def shiftE (n k : Nat) (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else ρ (i + n)

/-- The environment transformation matching `Term.inst · a k`. -/
def instE (k : Nat) (x : V) (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else if i = k then x else ρ (i - 1)

theorem shiftE_zero (n : Nat) (ρ : Nat → V) :
    shiftE n 0 ρ = fun i => ρ (i + n) := by
  funext i; simp [shiftE]

theorem shiftE_zero_zero (ρ : Nat → V) : shiftE 0 0 ρ = ρ := by
  funext i; simp [shiftE]

theorem instE_zero (x : V) (ρ : Nat → V) : instE 0 x ρ = cons x ρ := by
  funext i; cases i <;> simp [instE, cons]

theorem cons_shiftE (x : V) (n k : Nat) (ρ : Nat → V) :
    cons x (shiftE n k ρ) = shiftE n (k + 1) (cons x ρ) := by
  funext i
  cases i with
  | zero => simp [shiftE]
  | succ j =>
    show shiftE n k ρ j = shiftE n (k + 1) (cons x ρ) (j + 1)
    simp only [shiftE]
    by_cases h : j < k
    · rw [ite_eq_left h, ite_eq_left (show j + 1 < k + 1 by omega)]; rfl
    · rw [ite_eq_right h, ite_eq_right (show ¬ (j + 1 < k + 1) by omega)]
      show ρ (j + n) = cons x ρ (j + 1 + n)
      rw [show j + 1 + n = (j + n) + 1 by omega]; rfl

theorem cons_instE (x : V) (k : Nat) (y : V) (ρ : Nat → V) :
    cons x (instE k y ρ) = instE (k + 1) y (cons x ρ) := by
  funext i
  cases i with
  | zero => simp [instE]
  | succ j =>
    show instE k y ρ j = instE (k + 1) y (cons x ρ) (j + 1)
    simp only [instE]
    by_cases h : j < k
    · rw [ite_eq_left h, ite_eq_left (show j + 1 < k + 1 by omega)]; rfl
    · rw [ite_eq_right h, ite_eq_right (show ¬ (j + 1 < k + 1) by omega)]
      by_cases h2 : j = k
      · rw [ite_eq_left h2, ite_eq_left (show j + 1 = k + 1 by omega)]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ (j + 1 = k + 1) by omega)]
        show ρ (j - 1) = cons x ρ (j + 1 - 1)
        rw [show j + 1 - 1 = (j - 1) + 1 by omega]; rfl

theorem shiftE_succ_cons (x : V) (k : Nat) (ρ : Nat → V) :
    shiftE (k + 1) 0 (cons x ρ) = shiftE k 0 ρ := by
  rw [shiftE_zero, shiftE_zero]
  funext i
  show cons x ρ (i + (k + 1)) = ρ (i + k)
  rw [show i + (k + 1) = (i + k) + 1 by omega]; rfl

end Env

variable (V : Type w) [SetTheory V]

/-! ## The interpretation -/

/-- The interpretation: total, term-directed, environment-free; the
binders read their regime off the values. -/
noncomputable def interp : (Nat → V) → Term → V
  | ρ, .bvar i => ρ i
  | _, .sort u => univ u
  | _, .const c us => bval V c us
  | ρ, .app f a => SetTheory.app (interp ρ f) (interp ρ a)
  | ρ, .lam A b => lamV (interp ρ A) fun x => interp (cons x ρ) b
  | ρ, .pi A B => piV (interp ρ A) fun x => interp (cons x ρ) B
  | ρ, .letE v b => interp (cons (interp ρ v) ρ) b
  | ρ, .eqE a b => eqv (interp ρ a) (interp ρ b)
  | ρ, .fst e => sfst (interp ρ e)
  | ρ, .snd e => ssnd (interp ρ e)
  | _, .prf => pt

@[simp] theorem interp_bvar (ρ : Nat → V) (i : Nat) :
    interp V ρ (.bvar i) = ρ i := rfl
@[simp] theorem interp_sort (ρ : Nat → V) (u : Nat) :
    interp V ρ (.sort u) = univ u := rfl
@[simp] theorem interp_const (ρ : Nat → V) (c : ConLeche.Term.BConst)
    (us : List Nat) : interp V ρ (.const c us) = bval V c us := rfl
@[simp] theorem interp_app (ρ : Nat → V) (f a : Term) :
    interp V ρ (.app f a) = SetTheory.app (interp V ρ f) (interp V ρ a) := rfl
@[simp] theorem interp_lam (ρ : Nat → V) (A b : Term) :
    interp V ρ (.lam A b) =
      lamV (interp V ρ A) fun x => interp V (cons x ρ) b := rfl
@[simp] theorem interp_pi (ρ : Nat → V) (A B : Term) :
    interp V ρ (.pi A B) =
      piV (interp V ρ A) fun x => interp V (cons x ρ) B := rfl
@[simp] theorem interp_letE (ρ : Nat → V) (v b : Term) :
    interp V ρ (.letE v b) = interp V (cons (interp V ρ v) ρ) b := rfl
@[simp] theorem interp_eqE (ρ : Nat → V) (a b : Term) :
    interp V ρ (.eqE a b) = eqv (interp V ρ a) (interp V ρ b) := rfl
@[simp] theorem interp_fst (ρ : Nat → V) (e : Term) :
    interp V ρ (.fst e) = sfst (interp V ρ e) := rfl
@[simp] theorem interp_snd (ρ : Nat → V) (e : Term) :
    interp V ρ (.snd e) = ssnd (interp V ρ e) := rfl
@[simp] theorem interp_prf (ρ : Nat → V) : interp V ρ .prf = pt := rfl

variable {V} in
/-- `interp` of an application spine, as a `map`-then-`foldl`. -/
theorem interp_mkAppN_foldl (ρ : Nat → V) :
    ∀ (f : Term) (es : List Term),
      interp V ρ (Term.mkAppN f es) = (es.map (interp V ρ)).foldl SetTheory.app (interp V ρ f)
  | _, [] => rfl
  | f, e :: es => by
    rw [Term.mkAppN_cons, interp_mkAppN_foldl ρ (.app f e) es]
    rfl

/-! ## V-codes for the erased syntax (definable-semantics foundation,
bridge-axiom track)

`bconstCode`/`vnatListCode` encode the syntax alphabet and level lists as
values of `V`: a `kpair` of a numeral constructor tag and a coded payload
(`Tower.mkTower` of numeral codes for lists).  Every code is `kpair`-shaped,
so injectivity reduces to `kpair_inj` + `vnat_inj`. -/

/-- A Kuratowski pair is never the empty set. -/
theorem kpair_ne_empty {W : Type w} [SetTheory W] (a b : W) : kpair a b ≠ (empty : W) := by
  intro h
  have hm : sing a ∈ˢ kpair a b := mem_upair_left (sing a) (upair a b)
  exact not_mem_empty (sing a) (h ▸ hm)

/-- The list tupler is injective without a length hypothesis (a right-nested
`kpair` tower over the empty terminator). -/
theorem mkTower_inj_full {W : Type w} [SetTheory W] {as bs : List W} (h : Tower.mkTower as = Tower.mkTower bs) :
    as = bs := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [Tower.mkTower, spair] at h
      exact absurd h.symm (kpair_ne_empty b (Tower.mkTower bs))
  | cons a as ih =>
    cases bs with
    | nil =>
      simp only [Tower.mkTower, spair] at h
      exact absurd h (kpair_ne_empty a (Tower.mkTower as))
    | cons b bs =>
      simp only [Tower.mkTower, spair] at h
      obtain ⟨h1, h2⟩ := kpair_inj h
      rw [h1, ih h2]

/-- Codes of natural-number lists: the tupler over the numeral codes. -/
noncomputable def vnatListCode {W : Type w} [SetTheory W] (ns : List Nat) : W :=
  Tower.mkTower (ns.map (vnat (V := W)))

theorem map_vnat_inj {W : Type w} [SetTheory W] : ∀ (ns ms : List Nat),
    ns.map (vnat (V := W)) = ms.map (vnat (V := W)) → ns = ms := by
  intro ns
  induction ns with
  | nil =>
    intro ms h
    cases ms with
    | nil => rfl
    | cons m ms => simp at h
  | cons n ns ih =>
    intro ms h
    cases ms with
    | nil => simp at h
    | cons m ms =>
      simp only [List.map_cons] at h
      have h1 : vnat (V := W) n = vnat (V := W) m := by
        have h' := congrArg (fun l => l.head?) h
        simpa using h'
      have h2 : ns.map (vnat (V := W)) = ms.map (vnat (V := W)) := by
        have h' := congrArg List.tail h
        simpa using h'
      rw [vnat_inj (V := W) h1, ih ms h2]

theorem vnatListCode_inj {W : Type w} [SetTheory W] {ns ms : List Nat}
    (h : vnatListCode (W := W) ns = vnatListCode (W := W) ms) : ns = ms := by
  have h' : Tower.mkTower (ns.map (vnat (V := W))) = Tower.mkTower (ms.map (vnat (V := W))) := h
  exact map_vnat_inj _ _ (mkTower_inj_full h')

/-- Codes of the built-in constants: `kpair` of a numeral constructor tag
and the coded argument (`empty` off `lfpTuple`). -/
noncomputable def bconstCode {W : Type w} [SetTheory W] : Term.BConst → W
  | .nat => kpair (vnat 0) (empty : W)
  | .natZero => kpair (vnat 1) (empty : W)
  | .natSucc => kpair (vnat 2) (empty : W)
  | .natRec => kpair (vnat 3) (empty : W)
  | .punit => kpair (vnat 4) (empty : W)
  | .punitUnit => kpair (vnat 5) (empty : W)
  | .psigma => kpair (vnat 6) (empty : W)
  | .psigmaMk => kpair (vnat 7) (empty : W)
  | .empty => kpair (vnat 8) (empty : W)
  | .emptyRec => kpair (vnat 9) (empty : W)
  | .quot => kpair (vnat 10) (empty : W)
  | .quotMk => kpair (vnat 11) (empty : W)
  | .quotLift => kpair (vnat 12) (empty : W)
  | .quotInd => kpair (vnat 13) (empty : W)
  | .quotSound => kpair (vnat 14) (empty : W)
  | .propext => kpair (vnat 15) (empty : W)
  | .choice => kpair (vnat 16) (empty : W)
  | .lfpFam => kpair (vnat 17) (empty : W)
  | .lfpTuple k => kpair (vnat 18) (vnat k)

theorem bconstCode_inj {W : Type w} [SetTheory W] {c c' : Term.BConst} (h : bconstCode (W := W) c = bconstCode (W := W) c') : c = c' := by
  cases c <;> cases c' <;> simp only [bconstCode] at h
  all_goals first
    | rfl
    | (obtain ⟨h1, -⟩ := kpair_inj h; have htag := vnat_inj (V := W) h1; omega)
    | (obtain ⟨-, h2⟩ := kpair_inj h; rw [vnat_inj (V := W) h2])

/-- Codes of terms: `kpair` of a numeral constructor tag and the coded
payload (a `kpair` of the coded immediate arguments, `empty` off `prf`). -/
noncomputable def tmCode {W : Type w} [SetTheory W] : Term → W
  | .bvar i => kpair (vnat 0) (vnat i)
  | .sort u => kpair (vnat 1) (vnat u)
  | .const c us => kpair (vnat 2) (kpair (bconstCode c) (vnatListCode us))
  | .app f a => kpair (vnat 3) (kpair (tmCode (W := W) f) (tmCode (W := W) a))
  | .lam ty body => kpair (vnat 4) (kpair (tmCode (W := W) ty) (tmCode (W := W) body))
  | .pi ty body => kpair (vnat 5) (kpair (tmCode (W := W) ty) (tmCode (W := W) body))
  | .letE val body => kpair (vnat 6) (kpair (tmCode (W := W) val) (tmCode (W := W) body))
  | .eqE lhs rhs => kpair (vnat 7) (kpair (tmCode (W := W) lhs) (tmCode (W := W) rhs))
  | .fst e => kpair (vnat 8) (tmCode (W := W) e)
  | .snd e => kpair (vnat 9) (tmCode (W := W) e)
  | .prf => kpair (vnat 10) (empty : W)

theorem tmCode_inj {W : Type w} [SetTheory W] : ∀ (t t' : Term),
    tmCode (W := W) t = tmCode (W := W) t' → t = t' := by
  intro t
  induction t with
  | bvar i =>
    intro t' h
    cases t' <;> simp only [tmCode] at h
    all_goals first
      | (have htag := vnat_inj (V := W) (kpair_inj_left h); omega)
      | (obtain ⟨-, hp⟩ := kpair_inj h; rw [vnat_inj (V := W) hp])
  | sort u =>
    intro t' h
    cases t' <;> simp only [tmCode] at h
    all_goals first
      | (have htag := vnat_inj (V := W) (kpair_inj_left h); omega)
      | (obtain ⟨-, hp⟩ := kpair_inj h; rw [vnat_inj (V := W) hp])
  | const c us =>
    intro t' h
    cases t' <;> simp only [tmCode] at h
    all_goals first
      | (have htag := vnat_inj (V := W) (kpair_inj_left h); omega)
      | (obtain ⟨-, hp⟩ := kpair_inj h; obtain ⟨hc, hu⟩ := kpair_inj hp; rw [bconstCode_inj hc, vnatListCode_inj hu])
  | app f a ihf iha =>
    intro t' h
    cases t' <;> simp only [tmCode] at h
    all_goals first
      | (have htag := vnat_inj (V := W) (kpair_inj_left h); omega)
      | (obtain ⟨-, hp⟩ := kpair_inj h; obtain ⟨hf, ha⟩ := kpair_inj hp; rw [ihf _ hf, iha _ ha])
  | lam ty body ihty ihbody =>
    intro t' h
    cases t' <;> simp only [tmCode] at h
    all_goals first
      | (have htag := vnat_inj (V := W) (kpair_inj_left h); omega)
      | (obtain ⟨-, hp⟩ := kpair_inj h; obtain ⟨hty, hb⟩ := kpair_inj hp; rw [ihty _ hty, ihbody _ hb])
  | pi ty body ihty ihbody =>
    intro t' h
    cases t' <;> simp only [tmCode] at h
    all_goals first
      | (have htag := vnat_inj (V := W) (kpair_inj_left h); omega)
      | (obtain ⟨-, hp⟩ := kpair_inj h; obtain ⟨hty, hb⟩ := kpair_inj hp; rw [ihty _ hty, ihbody _ hb])
  | letE val body ihval ihbody =>
    intro t' h
    cases t' <;> simp only [tmCode] at h
    all_goals first
      | (have htag := vnat_inj (V := W) (kpair_inj_left h); omega)
      | (obtain ⟨-, hp⟩ := kpair_inj h; obtain ⟨hv, hb⟩ := kpair_inj hp; rw [ihval _ hv, ihbody _ hb])
  | eqE lhs rhs ihl ihr =>
    intro t' h
    cases t' <;> simp only [tmCode] at h
    all_goals first
      | (have htag := vnat_inj (V := W) (kpair_inj_left h); omega)
      | (obtain ⟨-, hp⟩ := kpair_inj h; obtain ⟨hl, hr⟩ := kpair_inj hp; rw [ihl _ hl, ihr _ hr])
  | fst e ihe =>
    intro t' h
    cases t' <;> simp only [tmCode] at h
    all_goals first
      | (have htag := vnat_inj (V := W) (kpair_inj_left h); omega)
      | (obtain ⟨-, hp⟩ := kpair_inj h; rw [ihe _ hp])
  | snd e ihe =>
    intro t' h
    cases t' <;> simp only [tmCode] at h
    all_goals first
      | (have htag := vnat_inj (V := W) (kpair_inj_left h); omega)
      | (obtain ⟨-, hp⟩ := kpair_inj h; rw [ihe _ hp])
  | prf =>
    intro t' h
    cases t' <;> simp only [tmCode] at h
    all_goals first
      | (have htag := vnat_inj (V := W) (kpair_inj_left h); omega)
      | rfl

/-! ## Definable pair projections — the readers of the V-codes

`sfstEqF`/`ssndEqF` internalize `y = sfst x` / `y = ssnd x` as first-order
`Form`s (variables `0 ↦ y`, `1 ↦ x`, `2 ↦ pt`), so that decoding a code —
reading its tag and its payload — is a first-order step of the definable
interpretation over the V-codes. -/

/-- Variable map `Fin 3 → Fin 5` for the two-existential unfolding of
`kpairEqF` inside a `Form 3` with variables `(0 ↦ y, 1 ↦ x, 2 ↦ pt)`:
`kpairEqF`'s `(z, a, b)` reads off `(x, ⟨4⟩, ⟨3⟩)`. -/
def kpairProjMap : Fin 3 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨1, by omega⟩
  | 1 => ⟨4, by omega⟩
  | _ => ⟨3, by omega⟩

/-- `y = sfst x` as a formula (variables `0 ↦ y`, `1 ↦ x`, `2 ↦ pt`): `x` is
a pair whose first component is `y`, or `x` is no pair and `y = pt`. -/
def sfstEqF : Form 3 :=
  .or (.ex (.ex (.and (Form.relabel kpairProjMap kpairEqF)
      (.equal ⟨0, by omega⟩ ⟨4, by omega⟩))))
    (.and (.not (.ex (.ex (Form.relabel kpairProjMap kpairEqF))))
      (.equal ⟨0, by omega⟩ ⟨2, by omega⟩))

/-- `y = ssnd x` as a formula (variables `0 ↦ y`, `1 ↦ x`, `2 ↦ pt`): `x` is
a pair whose second component is `y`, or `x` is no pair and `y = pt`. -/
def ssndEqF : Form 3 :=
  .or (.ex (.ex (.and (Form.relabel kpairProjMap kpairEqF)
      (.equal ⟨0, by omega⟩ ⟨3, by omega⟩))))
    (.and (.not (.ex (.ex (Form.relabel kpairProjMap kpairEqF))))
      (.equal ⟨0, by omega⟩ ⟨2, by omega⟩))

theorem realize_sfstEqF {W : Type w} [SetTheory W] {y x : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ => y) x) (pt : W)) sfstEqF ↔
      y = sfst x := by
  have hK : ∀ v3 v4 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => y) x) (pt : W)) v3) v4) ∘ kpairProjMap =
        Form.snoc (Form.snoc (fun _ => x) v4) v3 := by
    intro v3 v4
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [sfstEqF, Form.realize_or, Form.realize_and, Form.realize_not,
    Form.realize_ex, Form.realize_equal, Form.realize_relabel, hK,
    realize_kpairEqF, Form.snoc_mk]
  clear hK
  constructor
  · rintro (⟨v3, v4, hx, hy⟩ | ⟨hnot, hy⟩)
    · have hy' : y = v4 := hy
      rw [hy', hx]; exact (sfst_kpair _ _).symm
    · have hy' : y = (pt : W) := hy
      have h' : ¬∃ a b, x = kpair a b := by
        rintro ⟨a, b, hab⟩; exact hnot ⟨b, a, hab⟩
      have h2 : sfst x = (pt : W) := by
        unfold sfst; exact dite_eq_right h'
      rw [hy', h2]
  · intro h
    by_cases hk : ∃ a b, x = kpair a b
    · obtain ⟨a, b, hab⟩ := hk
      left
      refine ⟨b, a, hab, ?_⟩
      rw [hab, sfst_kpair] at h
      exact h
    · right
      refine ⟨?_, ?_⟩
      · rintro ⟨v3, v4, hx'⟩; exact hk ⟨v4, v3, hx'⟩
      · have h2 : sfst x = (pt : W) := by
          unfold sfst; exact dite_eq_right hk
        rw [h2] at h; exact h

theorem realize_ssndEqF {W : Type w} [SetTheory W] {y x : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ => y) x) (pt : W)) ssndEqF ↔
      y = ssnd x := by
  have hK : ∀ v3 v4 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ => y) x) (pt : W)) v3) v4) ∘ kpairProjMap =
        Form.snoc (Form.snoc (fun _ => x) v4) v3 := by
    intro v3 v4
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [ssndEqF, Form.realize_or, Form.realize_and, Form.realize_not,
    Form.realize_ex, Form.realize_equal, Form.realize_relabel, hK,
    realize_kpairEqF, Form.snoc_mk]
  clear hK
  constructor
  · rintro (⟨v3, v4, hx, hy⟩ | ⟨hnot, hy⟩)
    · have hy' : y = v3 := hy
      rw [hy', hx]; exact (ssnd_kpair _ _).symm
    · have hy' : y = (pt : W) := hy
      have h' : ¬∃ a b, x = kpair a b := by
        rintro ⟨a, b, hab⟩; exact hnot ⟨b, a, hab⟩
      have h2 : ssnd x = (pt : W) := by
        unfold ssnd; exact dite_eq_right h'
      rw [hy', h2]
  · intro h
    by_cases hk : ∃ a b, x = kpair a b
    · obtain ⟨a, b, hab⟩ := hk
      left
      refine ⟨b, a, hab, ?_⟩
      rw [hab, ssnd_kpair] at h
      exact h
    · right
      refine ⟨?_, ?_⟩
      · rintro ⟨v3, v4, hx'⟩; exact hk ⟨v4, v3, hx'⟩
      · have h2 : ssnd x = (pt : W) := by
          unfold ssnd; exact dite_eq_right hk
        rw [h2] at h; exact h


/-! ## Stage 38: definable environment graphs (`consGraph`) -/

variable {W : Type w} [SetTheory W]


/-- `vsucc` is injective (regularity at the pair); local copy of
`ConLeche.SetTheory.Tower.vsucc_inj` (`SetModel/Iter.lean`), not
imported here. -/
theorem vsucc_injW {a b : W} (h : vsucc a = vsucc b) : a = b :=
  Classical.byContradiction fun hne => by
  have ha : a ∈ˢ b := by
    have h1 : a ∈ˢ vsucc a := self_mem_vsucc a
    rw [h] at h1
    rcases mem_vsucc.mp h1 with h' | h'
    · exact h'
    · exact absurd h' hne
  have hb : b ∈ˢ a := by
    have h1 : b ∈ˢ vsucc b := self_mem_vsucc b
    rw [← h] at h1
    rcases mem_vsucc.mp h1 with h' | h'
    · exact h'
    · exact absurd h'.symm hne
  obtain ⟨y, hy, hmin⟩ := regularity (upair a b) ⟨a, mem_upair_left a b⟩
  have hba : b ∈ˢ upair a b := mem_upair_right a b
  have hab : a ∈ˢ upair a b := mem_upair_left a b
  rcases mem_upair.mp hy with rfl | rfl
  · exact hmin ⟨b, hb, hba⟩
  · exact hmin ⟨a, ha, hab⟩

/-- Variable map `Fin 2 → Fin 5`, `0 ↦ 4`, `1 ↦ 2` (reads `vsuccEqF`'s
`(e, m)` out of `(z, w, m, y, e)`). -/
def csVsMap : Fin 2 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨4, by omega⟩
  | _ => ⟨2, by omega⟩

/-- Variable map `Fin 3 → Fin 5`, `0 ↦ 0`, `1 ↦ 2`, `2 ↦ 3` (reads
`kpairEqF`'s `(z, x, y)` as `(z, m, y)` out of `(z, w, m, y, e)`). -/
def csKpMap1 : Fin 3 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨0, by omega⟩
  | 1 => ⟨2, by omega⟩
  | _ => ⟨3, by omega⟩

/-- Variable map `Fin 3 → Fin 5`, `0 ↦ 1`, `1 ↦ 4`, `2 ↦ 3` (reads
`kpairEqF`'s `(z, x, y)` as `(w, e, y)` out of `(z, w, m, y, e)`). -/
def csKpMap2 : Fin 3 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨1, by omega⟩
  | 1 => ⟨4, by omega⟩
  | _ => ⟨3, by omega⟩

/-- Variable map `Fin 3 → Fin 4`, `0 ↦ 0`, `1 ↦ 2`, `2 ↦ 3` (reads
`kpairEqF`'s `(z, x, y)` as `(z, m, y)` out of `(z, w, m, y)`). -/
def csKpMap0 : Fin 3 → Fin 4 := fun i =>
  match i.val with
  | 0 => ⟨0, by omega⟩
  | 1 => ⟨2, by omega⟩
  | _ => ⟨3, by omega⟩

/-- The definable shift relation for extending an environment graph
(variables `0 ↦ z`, `1 ↦ w`): `z = kpair m y` maps to
`w = kpair (vsucc m) y`; a non-pair `z` maps to itself. -/
def consShiftF : Form 2 :=
  .or (.ex (.ex (.ex (.and (Form.relabel csVsMap vsuccEqF)
      (.and (Form.relabel csKpMap1 kpairEqF) (Form.relabel csKpMap2 kpairEqF))))))
    (.and (.not (.ex (.ex (Form.relabel csKpMap0 kpairEqF))))
      (.equal ⟨0, by omega⟩ ⟨1, by omega⟩))

theorem realize_consShiftF {z w : W} :
    Form.Realize Mem (Form.snoc (fun _ => z) w) consShiftF ↔
      (∃ m y, z = kpair m y ∧ w = kpair (vsucc m) y) ∨
        ((¬ ∃ m y, z = kpair m y) ∧ w = z) := by
  have hVS : ∀ m y e : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => z) w) m) y) e) ∘ csVsMap =
        (Form.snoc (fun _ : Fin 1 => e) m : Fin 2 → W) := by
    intro m y e
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hK1 : ∀ m y e : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => z) w) m) y) e) ∘ csKpMap1 =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => z) m) y : Fin 3 → W) := by
    intro m y e
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK2 : ∀ m y e : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => z) w) m) y) e) ∘ csKpMap2 =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => w) e) y : Fin 3 → W) := by
    intro m y e
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK0 : ∀ m y : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => z) w) m) y) ∘ csKpMap0 =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => z) m) y : Fin 3 → W) := by
    intro m y
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [consShiftF, Form.realize_or, Form.realize_and, Form.realize_not,
    Form.realize_ex, Form.realize_equal, Form.realize_relabel, hVS, hK1, hK2, hK0,
    realize_vsuccEqF, realize_kpairEqF, Form.snoc_mk]
  clear hVS hK1 hK2 hK0
  constructor
  · rintro (⟨m, y, e, he, hz, hw⟩ | ⟨hnot, hw⟩)
    · have he' : kpair e y = kpair (vsucc m) y := by rw [he]
      exact Or.inl ⟨m, y, hz, hw.trans he'⟩
    · exact Or.inr ⟨hnot, hw.symm⟩
  · rintro (⟨m, y, hz, hw⟩ | ⟨hnot, hw⟩)
    · exact Or.inl ⟨m, y, vsucc m, rfl, hz, hw⟩
    · exact Or.inr ⟨hnot, hw.symm⟩

omit [SetTheory W] in
theorem cons2_nil_eq {z w : W} : Form.cons2 z w Form.nil = Form.snoc (fun _ => z) w := by
  funext ⟨k, hk⟩
  have hk2 : k = 0 ∨ k = 1 := by omega
  rcases hk2 with rfl | rfl <;> rfl

theorem consShiftF_fun (z : W) :
    ∃ w, Form.Realize Mem (Form.cons2 z w Form.nil) consShiftF ∧
      ∀ w', Form.Realize Mem (Form.cons2 z w' Form.nil) consShiftF → w' = w := by
  by_cases h : ∃ m y, z = kpair m y
  · obtain ⟨m, y, hm⟩ := h
    refine ⟨kpair (vsucc m) y, ?_, ?_⟩
    · rw [cons2_nil_eq]
      exact (realize_consShiftF (z := z) (w := kpair (vsucc m) y)).mpr (Or.inl ⟨m, y, hm, rfl⟩)
    · intro w' hw'
      rw [cons2_nil_eq] at hw'
      rcases (realize_consShiftF (z := z) (w := w')).mp hw' with ⟨m', y', hm', hw'⟩ | ⟨hnp, -⟩
      · have hmm : kpair m y = kpair m' y' := hm.symm.trans hm'
        obtain ⟨hm2, hy2⟩ := kpair_inj hmm
        subst hm2; subst hy2
        exact hw'
      · exact absurd ⟨m, y, hm⟩ hnp
  · refine ⟨z, ?_, ?_⟩
    · rw [cons2_nil_eq]
      exact (realize_consShiftF (z := z) (w := z)).mpr (Or.inr ⟨h, rfl⟩)
    · intro w' hw'
      rw [cons2_nil_eq] at hw'
      rcases (realize_consShiftF (z := z) (w := w')).mp hw' with ⟨m, y, hm, -⟩ | ⟨-, hw'⟩
      · exact absurd ⟨m, y, hm⟩ h
      · exact hw'

/-- Definable environment extension: the graph of `cons x ρ` read as
`app _ (vnat i)`, built as the shifted image of `ρ` plus the new
`0`-entry. -/
noncomputable def consGraph (x ρ : W) : W :=
  binUnion (sing (kpair (vnat 0) x)) (imageF consShiftF Form.nil ρ (fun z _ => consShiftF_fun z))

theorem mem_consGraph {x ρ z : W} :
    z ∈ˢ consGraph x ρ ↔
      z = kpair (vnat 0) x ∨
        ∃ z₀, z₀ ∈ˢ ρ ∧ ((∃ m y, z₀ = kpair m y ∧ z = kpair (vsucc m) y) ∨
          ((¬ ∃ m y, z₀ = kpair m y) ∧ z = z₀)) := by
  rw [show consGraph x ρ =
      binUnion (sing (kpair (vnat 0) x)) (imageF consShiftF Form.nil ρ (fun z _ => consShiftF_fun z)) from rfl,
    mem_binUnion, mem_sing, mem_imageF]
  constructor
  · rintro (rfl | ⟨z₀, hz₀, hψ⟩)
    · exact Or.inl rfl
    · rw [cons2_nil_eq] at hψ
      exact Or.inr ⟨z₀, hz₀, (realize_consShiftF (z := z₀) (w := z)).mp hψ⟩
  · rintro (rfl | ⟨z₀, hz₀, hψ⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨z₀, hz₀, ?_⟩
      rw [cons2_nil_eq]
      exact (realize_consShiftF (z := z₀) (w := z)).mpr hψ

theorem consGraph_ne_pt {x ρ : W} : consGraph x ρ ≠ pt := by
  intro h
  have h1 : kpair (vnat 0) x ∈ˢ (pt : W) :=
    h ▸ mem_binUnion.mpr (Or.inl (mem_sing.mpr rfl))
  exact ptTag_ne_kpair (vnat 0) x (mem_pt.mp h1).symm

theorem app_consGraph_zero {x ρ : W} : app (consGraph x ρ) (vnat 0) = x := by
  refine app_eq_of_unique (consGraph_ne_pt (x := x) (ρ := ρ)) ?_ ?_
  · exact mem_consGraph.mpr (Or.inl rfl)
  · intro y hy
    rcases mem_consGraph.mp hy with h0 | ⟨z₀, -, hψ⟩
    · exact (kpair_inj h0).2
    · rcases hψ with ⟨m, y', -, hw⟩ | ⟨hnp, hw⟩
      · have h1 : (vnat 0 : W) = vsucc m := kpair_inj_left hw
        have h3 : m ∈ˢ (vnat 0 : W) := h1.symm ▸ self_mem_vsucc m
        exact absurd h3 (not_mem_empty m)
      · exact absurd ⟨vnat 0, y, hw.symm⟩ hnp

theorem app_consGraph_succ {x ρ : W} (hρ : ρ ≠ pt) (i : Nat) :
    app (consGraph x ρ) (vnat (i + 1)) = app ρ (vnat i) := by
  have key : ∀ y : W, kpair (vnat (i + 1)) y ∈ˢ consGraph x ρ ↔ kpair (vnat i) y ∈ˢ ρ := by
    intro y
    constructor
    · intro hy
      rcases mem_consGraph.mp hy with h0 | ⟨z₀, hz₀, hψ⟩
      · exact absurd (kpair_inj_left h0) (fun h => Nat.succ_ne_zero i (vnat_inj (V := W) h))
      · rcases hψ with ⟨m, y', hm, hw⟩ | ⟨hnp, hw⟩
        · obtain ⟨h1, h2⟩ := kpair_inj hw
          have h4 : vnat i = m :=
            vsucc_injW ((show (vnat (i + 1) : W) = vsucc (vnat i) from rfl).symm.trans h1)
          subst h4; subst h2
          rw [← hm]; exact hz₀
        · exact absurd ⟨vnat (i + 1), y, hw.symm⟩ hnp
    · intro hy
      exact mem_consGraph.mpr (Or.inr ⟨kpair (vnat i) y, hy,
        Or.inl ⟨vnat i, y, rfl, rfl⟩⟩)
  have hsep : sepF (sUnion (sUnion (consGraph x ρ))) kpairMemF
        (Form.snoc (fun _ => vnat (i + 1)) (consGraph x ρ)) =
      sepF (sUnion (sUnion ρ)) kpairMemF (Form.snoc (fun _ => vnat i) ρ) := by
    apply ext fun y => ?_
    rw [mem_appSep, mem_appSep]
    constructor
    · rintro ⟨-, h⟩
      have h' := (key y).mp h
      exact ⟨mem_sUnion.mpr ⟨upair (vnat i) y,
        mem_sUnion.mpr ⟨kpair (vnat i) y, h', mem_upair_right _ _⟩, mem_upair_right _ _⟩, h'⟩
    · rintro ⟨-, h⟩
      have h' := (key y).mpr h
      exact ⟨mem_sUnion.mpr ⟨upair (vnat (i + 1)) y,
        mem_sUnion.mpr ⟨kpair (vnat (i + 1)) y, h', mem_upair_right _ _⟩, mem_upair_right _ _⟩, h'⟩
  unfold app
  rw [ite_eq_right consGraph_ne_pt, ite_eq_right hρ, hsep]

end ConLeche.Semantics