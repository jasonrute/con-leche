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


/-! ## Stage 39: Form-level environment reading and the `bvar` step -/

variable {W : Type w} [SetTheory W]

theorem realize_appEqF_consGraph_zero {x ρ v : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => pt) v) (consGraph x ρ))
      (vnat 0)) appEqF ↔ v = x := by
  rw [realize_appEqF, app_consGraph_zero]

theorem realize_appEqF_consGraph_succ {x ρ v : W} (hρ : ρ ≠ pt) (i : Nat) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => pt) v) (consGraph x ρ))
      (vnat (i + 1))) appEqF ↔ v = app ρ (vnat i) := by
  rw [realize_appEqF, app_consGraph_succ hρ i]

/-- Variable map `Fin 3 → Fin 5`, `0 ↦ 4`, `1 ↦ 2`, `2 ↦ 3` (reads
`ssndEqF`'s `(y, x, pt)` as `(u, c, pt)` out of `(v, ρ, c, pt, u)`). -/
def bvarSndMap : Fin 3 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨4, by omega⟩
  | 1 => ⟨2, by omega⟩
  | _ => ⟨3, by omega⟩

/-- Variable map `Fin 4 → Fin 5`, `0 ↦ 3`, `1 ↦ 0`, `2 ↦ 1`, `3 ↦ 4`
(reads `appEqF`'s `(pt, v, g, u)` out of `(v, ρ, c, pt, u)`). -/
def bvarAppMap : Fin 4 → Fin 5 := fun i =>
  match i.val with
  | 0 => ⟨3, by omega⟩
  | 1 => ⟨0, by omega⟩
  | 2 => ⟨1, by omega⟩
  | _ => ⟨4, by omega⟩

/-- The `bvar` step of the definable interpretation (variables
`0 ↦ v`, `1 ↦ ρ`, `2 ↦ c`, `3 ↦ pt`): `v = app ρ (ssnd c)` — the
value of a `bvar i` code `c = kpair (vnat 0) (vnat i)` under the
environment graph `ρ`. -/
def bvarStepF : Form 4 :=
  .ex (.and (Form.relabel bvarSndMap ssndEqF) (Form.relabel bvarAppMap appEqF))

theorem realize_bvarStepF {v ρ c : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) ρ) c) (pt : W))
      bvarStepF ↔ v = app ρ (ssnd c) := by
  have hS : ∀ u : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) ρ) c) (pt : W)) u) ∘ bvarSndMap =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => u) c) (pt : W) : Fin 3 → W) := by
    intro u
    funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hA : ∀ u : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) ρ) c) (pt : W)) u) ∘ bvarAppMap =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) v) ρ) u : Fin 4 → W) := by
    intro u
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [bvarStepF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hS, hA, realize_ssndEqF, realize_appEqF]
  clear hS hA
  constructor
  · rintro ⟨u, hu, hv⟩
    have hu' : u = ssnd c := hu
    rw [hu'] at hv
    exact hv
  · intro h
    exact ⟨ssnd c, rfl, h⟩

/-- The `bvar i` code reads off the environment graph: the value of
`tmCode (bvar i)` under `ρ` is `app ρ (vnat i)`. -/
theorem realize_bvarStepF_tmCode {ρ : W} (i : Nat) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => app ρ (vnat i)) ρ)
      (tmCode (ConLeche.Term.Term.bvar i))) (pt : W)) bvarStepF :=
  realize_bvarStepF.mpr (by rw [tmCode, ssnd_kpair])


/-! ## Stage 40: the `app` case of the definable interp step -/

variable {W : Type w} [SetTheory W]


/-- Variable maps into the `appStepF` bound context `(v, X, i, pt, c, ρ, p, f, a, kf, ka, vf, va)`. -/
def asMC : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨2, by omega⟩ | _ => ⟨3, by omega⟩
def asMR : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨5, by omega⟩ | 1 => ⟨2, by omega⟩ | _ => ⟨3, by omega⟩
def asMP : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨6, by omega⟩ | 1 => ⟨4, by omega⟩ | _ => ⟨3, by omega⟩
def asMF : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨6, by omega⟩ | _ => ⟨3, by omega⟩
def asMA : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨8, by omega⟩ | 1 => ⟨6, by omega⟩ | _ => ⟨3, by omega⟩
def asMK1 : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨9, by omega⟩ | 1 => ⟨7, by omega⟩ | _ => ⟨5, by omega⟩
def asMK2 : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨10, by omega⟩ | 1 => ⟨8, by omega⟩ | _ => ⟨5, by omega⟩
def asMV1 : Fin 4 → Fin 13 := fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨11, by omega⟩ | 2 => ⟨1, by omega⟩ | _ => ⟨9, by omega⟩
def asMV2 : Fin 4 → Fin 13 := fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨12, by omega⟩ | 2 => ⟨1, by omega⟩ | _ => ⟨10, by omega⟩
def asMV : Fin 4 → Fin 13 := fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨0, by omega⟩ | 2 => ⟨11, by omega⟩ | _ => ⟨12, by omega⟩

/-- The `app` step of the definable interpretation (variables `0 ↦ v`,
`1 ↦ X` (the current family graph), `2 ↦ i` (the index `kpair c ρ`),
`3 ↦ pt`): `v = app (app X (kpair (sfst (ssnd c)) ρ))
(app X (kpair (ssnd (ssnd c)) ρ))` where `c = sfst i`, `ρ = ssnd i`. -/
def appStepF : Form 4 :=
  .ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex
    (.and (Form.relabel asMC sfstEqF)
    (.and (Form.relabel asMR ssndEqF)
    (.and (Form.relabel asMP ssndEqF)
    (.and (Form.relabel asMF sfstEqF)
    (.and (Form.relabel asMA ssndEqF)
    (.and (Form.relabel asMK1 kpairEqF)
    (.and (Form.relabel asMK2 kpairEqF)
    (.and (Form.relabel asMV1 appEqF)
    (.and (Form.relabel asMV2 appEqF)
          (Form.relabel asMV appEqF))))))))))))))))))

theorem realize_appStepF {v X i : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) X) i) (pt : W)) appStepF ↔
      v = app (app X (kpair (sfst (ssnd (sfst i))) (ssnd i)))
        (app X (kpair (ssnd (ssnd (sfst i))) (ssnd i))) := by
  have hC : ∀ c ρ p f a kf ka vf va : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) f) a) kf) ka) vf) va) ∘ asMC =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => c) i) (pt : W) : Fin 3 → W) := by
    intro c ρ p f a kf ka vf va; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hR : ∀ c ρ p f a kf ka vf va : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) f) a) kf) ka) vf) va) ∘ asMR =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => ρ) i) (pt : W) : Fin 3 → W) := by
    intro c ρ p f a kf ka vf va; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hP : ∀ c ρ p f a kf ka vf va : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) f) a) kf) ka) vf) va) ∘ asMP =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => p) c) (pt : W) : Fin 3 → W) := by
    intro c ρ p f a kf ka vf va; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hF : ∀ c ρ p f a kf ka vf va : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) f) a) kf) ka) vf) va) ∘ asMF =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => f) p) (pt : W) : Fin 3 → W) := by
    intro c ρ p f a kf ka vf va; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hA : ∀ c ρ p f a kf ka vf va : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) f) a) kf) ka) vf) va) ∘ asMA =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => a) p) (pt : W) : Fin 3 → W) := by
    intro c ρ p f a kf ka vf va; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK1 : ∀ c ρ p f a kf ka vf va : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) f) a) kf) ka) vf) va) ∘ asMK1 =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => kf) f) ρ : Fin 3 → W) := by
    intro c ρ p f a kf ka vf va; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK2 : ∀ c ρ p f a kf ka vf va : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) f) a) kf) ka) vf) va) ∘ asMK2 =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => ka) a) ρ : Fin 3 → W) := by
    intro c ρ p f a kf ka vf va; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV1 : ∀ c ρ p f a kf ka vf va : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) f) a) kf) ka) vf) va) ∘ asMV1 =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) vf) X) kf : Fin 4 → W) := by
    intro c ρ p f a kf ka vf va; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hV2 : ∀ c ρ p f a kf ka vf va : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) f) a) kf) ka) vf) va) ∘ asMV2 =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) va) X) ka : Fin 4 → W) := by
    intro c ρ p f a kf ka vf va; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hV : ∀ c ρ p f a kf ka vf va : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) f) a) kf) ka) vf) va) ∘ asMV =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) v) vf) va : Fin 4 → W) := by
    intro c ρ p f a kf ka vf va; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [appStepF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hC, hR, hP, hF, hA, hK1, hK2, hV1, hV2, hV,
    realize_sfstEqF, realize_ssndEqF, realize_kpairEqF, realize_appEqF]
  clear hC hR hP hF hA hK1 hK2 hV1 hV2 hV
  constructor
  · rintro ⟨c, ρ, p, f, a, kf, ka, vf, va, hC, hR, hP, hF, hA, hK1, hK2, hV1, hV2, hV⟩
    have hC' : c = sfst i := hC
    have hR' : ρ = ssnd i := hR
    have hP' : p = ssnd c := hP
    have hF' : f = sfst p := hF
    have hA' : a = ssnd p := hA
    have hK1' : kf = kpair f ρ := hK1
    have hK2' : ka = kpair a ρ := hK2
    have hV1' : vf = app X kf := hV1
    have hV2' : va = app X ka := hV2
    have hV' : v = app vf va := hV
    rw [hV', hV1', hV2', hK1', hK2', hF', hA', hP', hC', hR']
  · intro h
    exact ⟨sfst i, ssnd i, ssnd (sfst i), sfst (ssnd (sfst i)), ssnd (ssnd (sfst i)),
      kpair (sfst (ssnd (sfst i))) (ssnd i), kpair (ssnd (ssnd (sfst i))) (ssnd i),
      app X (kpair (sfst (ssnd (sfst i))) (ssnd i)), app X (kpair (ssnd (ssnd (sfst i))) (ssnd i)),
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h⟩

/-! ## Stage 41: the unary (`fst`/`snd`) and `prf` cases of the definable interp step -/

variable {W : Type w} [SetTheory W]


/-- Variable maps into the bound context `(v, X, i, pt, c, ρ, p, k, w)`. -/
def unC : Fin 3 → Fin 9 := fun k => match k.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨2, by omega⟩ | _ => ⟨3, by omega⟩
def unR : Fin 3 → Fin 9 := fun k => match k.val with | 0 => ⟨5, by omega⟩ | 1 => ⟨2, by omega⟩ | _ => ⟨3, by omega⟩
def unP : Fin 3 → Fin 9 := fun k => match k.val with | 0 => ⟨6, by omega⟩ | 1 => ⟨4, by omega⟩ | _ => ⟨3, by omega⟩
def unK : Fin 3 → Fin 9 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨6, by omega⟩ | _ => ⟨5, by omega⟩
def unW : Fin 4 → Fin 9 := fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨8, by omega⟩ | 2 => ⟨1, by omega⟩ | _ => ⟨7, by omega⟩
def unV : Fin 3 → Fin 9 := fun k => match k.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨8, by omega⟩ | _ => ⟨3, by omega⟩

/-- The `fst` step of the definable interpretation (variables `0 ↦ v`,
`1 ↦ X`, `2 ↦ i = kpair c ρ`, `3 ↦ pt`): `v = sfst (app X (kpair (ssnd c) ρ))`. -/
def fstStepF : Form 4 :=
  .ex (.ex (.ex (.ex (.ex
    (.and (Form.relabel unC sfstEqF)
    (.and (Form.relabel unR ssndEqF)
    (.and (Form.relabel unP ssndEqF)
    (.and (Form.relabel unK kpairEqF)
    (.and (Form.relabel unW appEqF)
          (Form.relabel unV sfstEqF))))))))))

/-- The `snd` step: `v = ssnd (app X (kpair (ssnd c) ρ))`. -/
def sndStepF : Form 4 :=
  .ex (.ex (.ex (.ex (.ex
    (.and (Form.relabel unC sfstEqF)
    (.and (Form.relabel unR ssndEqF)
    (.and (Form.relabel unP ssndEqF)
    (.and (Form.relabel unK kpairEqF)
    (.and (Form.relabel unW appEqF)
          (Form.relabel unV ssndEqF))))))))))

/-- The `prf` step: `v = pt`. -/
def prfStepF : Form 4 := .equal ⟨0, by omega⟩ ⟨3, by omega⟩

theorem realize_prfStepF {v X i : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) X) i) (pt : W)) prfStepF ↔
      v = pt := by
  simp only [prfStepF, Form.realize_equal, Form.snoc_mk]
  constructor <;> intro h <;> exact h

theorem realize_unStepF {v X i : W} (op : W → W) (opF : Form 3) (hop : ∀ {y x : W},
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ => y) x) (pt : W)) opF ↔ y = op x)
    (stepF : Form 4)
    (hstep : stepF = .ex (.ex (.ex (.ex (.ex
      (.and (Form.relabel unC sfstEqF)
      (.and (Form.relabel unR ssndEqF)
      (.and (Form.relabel unP ssndEqF)
      (.and (Form.relabel unK kpairEqF)
      (.and (Form.relabel unW appEqF)
            (Form.relabel unV opF))))))))))) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) X) i) (pt : W)) stepF ↔
      v = op (app X (kpair (ssnd (sfst i)) (ssnd i))) := by
  have hC : ∀ c ρ p k w : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) k) w) ∘ unC =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => c) i) (pt : W) : Fin 3 → W) := by
    intro c ρ p k w; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hR : ∀ c ρ p k w : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) k) w) ∘ unR =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => ρ) i) (pt : W) : Fin 3 → W) := by
    intro c ρ p k w; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hP : ∀ c ρ p k w : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) k) w) ∘ unP =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => p) c) (pt : W) : Fin 3 → W) := by
    intro c ρ p k w; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK : ∀ c ρ p k w : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) k) w) ∘ unK =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => k) p) ρ : Fin 3 → W) := by
    intro c ρ p k w; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hW : ∀ c ρ p k w : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) k) w) ∘ unW =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) w) X) k : Fin 4 → W) := by
    intro c ρ p k w; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hV : ∀ c ρ p k w : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) k) w) ∘ unV =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W) : Fin 3 → W) := by
    intro c ρ p k w; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  rw [hstep]
  simp only [Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hC, hR, hP, hK, hW, hV,
    realize_sfstEqF, realize_ssndEqF, realize_kpairEqF, realize_appEqF, hop]
  clear hC hR hP hK hW hV
  constructor
  · rintro ⟨c, ρ, p, k, w, hC, hR, hP, hK, hW, hV⟩
    have hC' : c = sfst i := hC
    have hR' : ρ = ssnd i := hR
    have hP' : p = ssnd c := hP
    have hK' : k = kpair p ρ := hK
    have hW' : w = app X k := hW
    have hV' : v = op w := hV
    rw [hV', hW', hK', hP', hC', hR']
  · intro h
    exact ⟨sfst i, ssnd i, ssnd (sfst i), kpair (ssnd (sfst i)) (ssnd i),
      app X (kpair (ssnd (sfst i)) (ssnd i)),
      rfl, rfl, rfl, rfl, rfl, h⟩

theorem realize_fstStepF {v X i : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) X) i) (pt : W)) fstStepF ↔
      v = sfst (app X (kpair (ssnd (sfst i)) (ssnd i))) :=
  realize_unStepF (sfst (V := W)) sfstEqF realize_sfstEqF fstStepF rfl

theorem realize_sndStepF {v X i : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) X) i) (pt : W)) sndStepF ↔
      v = ssnd (app X (kpair (ssnd (sfst i)) (ssnd i))) :=
  realize_unStepF (ssnd (V := W)) ssndEqF realize_ssndEqF sndStepF rfl


/-! ## Stage 42: definable truth values — `unitSetF`, `eqvF` -/

variable {W : Type w} [SetTheory W]


/-- `v = sing pt` (variable `0 ↦ v`, variable `1 ↦ pt`):
`pt ∈ˢ v ∧ ∀ z, z ∈ˢ v → z = pt`. -/
def unitSetF : Form 2 :=
  .and (.mem ⟨1, by omega⟩ ⟨0, by omega⟩)
    (.all (.imp (.mem ⟨2, by omega⟩ ⟨0, by omega⟩) (.equal ⟨2, by omega⟩ ⟨1, by omega⟩)))

theorem realize_unitSetF {v pt : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => v) pt) unitSetF ↔ v = sing pt := by
  simp only [unitSetF, Form.realize_and, Form.realize_mem, Form.realize_all,
    Form.realize_imp, Form.realize_equal, Form.snoc_mk]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : pt ∈ˢ v := h1
    have h2' : ∀ z : W, z ∈ˢ v → z = pt := h2
    exact SetTheory.ext (V := W) fun z =>
      ⟨fun hz => mem_sing.mpr (h2' z hz), fun hz => (mem_sing.mp hz) ▸ h1'⟩
  · intro h
    rw [h]
    refine ⟨?_, ?_⟩
    · show pt ∈ˢ sing pt
      exact mem_sing.mpr rfl
    · intro z hz
      have hz' : z ∈ˢ sing pt := hz
      exact mem_sing.mp hz'

theorem realize_emptyF_eq {x : W} :
    Form.Realize Mem (Form.snoc Form.nil x) emptyF ↔ x = empty := by
  rw [realize_emptyF (V := W)]
  constructor
  · intro h
    exact SetTheory.ext (V := W) fun z =>
      ⟨fun hz => absurd hz (h z), fun hz => absurd hz (not_mem_empty z)⟩
  · intro h w
    rw [h]
    exact not_mem_empty w

theorem unitSet_eq_sing : (unitSet : W) = sing (pt : W) := by
  unfold unitSet; rfl

theorem eqv_eq_unitSet {x y : W} (h : x = y) : eqv x y = unitSet := by
  unfold eqv; exact truthVal_eq_unitSet h

theorem eqv_eq_empty {x y : W} (h : ¬ x = y) : eqv x y = empty := by
  unfold eqv; exact truthVal_eq_empty h

/-- Variable map `Fin 2 → Fin 4` reading `unitSetF`'s `(v, pt)` from `(v, x, y, pt)`. -/
def eqvUsMap : Fin 2 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | _ => ⟨3, by omega⟩

/-- Variable map `Fin 1 → Fin 4` reading `emptyF`'s `v` from `(v, x, y, pt)`. -/
def eqvEmap : Fin 1 → Fin 4 := fun _ => ⟨0, by omega⟩

/-- `v = eqv x y` (variables `0 ↦ v`, `1 ↦ x`, `2 ↦ y`, `3 ↦ pt`):
`(x = y ∧ v = sing pt) ∨ (x ≠ y ∧ v = empty)`. -/
def eqvF : Form 4 :=
  .or (.and (.equal ⟨1, by omega⟩ ⟨2, by omega⟩) (Form.relabel eqvUsMap unitSetF))
    (.and (.not (.equal ⟨1, by omega⟩ ⟨2, by omega⟩)) (Form.relabel eqvEmap emptyF))

theorem realize_eqvF {v x y : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) x) y) (pt : W)) eqvF ↔
      v = eqv x y := by
  have hUs : ∀ v x y : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) x) y) (pt : W)) ∘ eqvUsMap =
        (Form.snoc (fun _ : Fin 1 => v) (pt : W) : Fin 2 → W) := by
    intro v x y; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hE : ∀ v x y : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) x) y) (pt : W)) ∘ eqvEmap =
        (Form.snoc Form.nil v : Fin 1 → W) := by
    intro v x y; funext ⟨k, hk⟩
    have hk1 : k = 0 := by omega
    rcases hk1 with rfl; rfl
  simp only [eqvF, Form.realize_or, Form.realize_and, Form.realize_equal, Form.realize_not,
    Form.realize_relabel, hUs, hE, realize_unitSetF, realize_emptyF_eq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have h1' : x = y := h1
      have h2' : v = sing (pt : W) := h2
      rw [eqv_eq_unitSet h1', unitSet_eq_sing]
      exact h2'
    · have h1' : ¬ x = y := h1
      have h2' : v = empty := h2
      rw [eqv_eq_empty h1']
      exact h2'
  · intro h
    by_cases hxy : x = y
    · left
      refine ⟨hxy, ?_⟩
      rw [eqv_eq_unitSet hxy, unitSet_eq_sing] at h
      exact h
    · right
      refine ⟨hxy, ?_⟩
      rw [eqv_eq_empty hxy] at h
      exact h


/-! ## Stage 43: the `eqE` case of the definable interp step -/

variable {W : Type w} [SetTheory W]


/-- Variable maps into the bound context `(v, X, i, pt, c, ρ, p, p1, p2, k1, k2, x, y)`. -/
def eC : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨2, by omega⟩ | _ => ⟨3, by omega⟩
def eR : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨5, by omega⟩ | 1 => ⟨2, by omega⟩ | _ => ⟨3, by omega⟩
def eP : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨6, by omega⟩ | 1 => ⟨4, by omega⟩ | _ => ⟨3, by omega⟩
def eP1 : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨6, by omega⟩ | _ => ⟨3, by omega⟩
def eP2 : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨8, by omega⟩ | 1 => ⟨6, by omega⟩ | _ => ⟨3, by omega⟩
def eK1 : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨9, by omega⟩ | 1 => ⟨7, by omega⟩ | _ => ⟨5, by omega⟩
def eK2 : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨10, by omega⟩ | 1 => ⟨8, by omega⟩ | _ => ⟨5, by omega⟩
def eX : Fin 4 → Fin 13 := fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨11, by omega⟩ | 2 => ⟨1, by omega⟩ | _ => ⟨9, by omega⟩
def eY : Fin 4 → Fin 13 := fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨12, by omega⟩ | 2 => ⟨1, by omega⟩ | _ => ⟨10, by omega⟩
def eV : Fin 4 → Fin 13 := fun k => match k.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨11, by omega⟩ | 2 => ⟨12, by omega⟩ | _ => ⟨3, by omega⟩

/-- The `eqE` step of the definable interpretation (variables `0 ↦ v`, `1 ↦ X`,
`2 ↦ i = kpair c ρ`, `3 ↦ pt`): `v = eqv (app X (kpair p1 ρ)) (app X (kpair p2 ρ))`
where `c = sfst i`, `ρ = ssnd i`, `p = ssnd c`, `p1 = sfst p`, `p2 = ssnd p`. -/
def eqEStepF : Form 4 :=
  .ex ( .ex ( .ex ( .ex ( .ex ( .ex ( .ex ( .ex ( .ex
    (.and (Form.relabel eC sfstEqF)
    (.and (Form.relabel eR ssndEqF)
    (.and (Form.relabel eP ssndEqF)
    (.and (Form.relabel eP1 sfstEqF)
    (.and (Form.relabel eP2 ssndEqF)
    (.and (Form.relabel eK1 kpairEqF)
    (.and (Form.relabel eK2 kpairEqF)
    (.and (Form.relabel eX appEqF)
    (.and (Form.relabel eY appEqF)
          (Form.relabel eV eqvF))))))))))))))))))

theorem realize_eqEStepF {v X i : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) X) i) (pt : W)) eqEStepF ↔
      v = eqv (app X (kpair (sfst (ssnd (sfst i))) (ssnd i)))
        (app X (kpair (ssnd (ssnd (sfst i))) (ssnd i))) := by
  have hC : ∀ c ρ p p1 p2 k1 k2 x y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) p1) p2) k1) k2) x) y) ∘ eC =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => c) i) (pt : W) : Fin 3 → W) := by
    intro c ρ p p1 p2 k1 k2 x y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hR : ∀ c ρ p p1 p2 k1 k2 x y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) p1) p2) k1) k2) x) y) ∘ eR =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => ρ) i) (pt : W) : Fin 3 → W) := by
    intro c ρ p p1 p2 k1 k2 x y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hP : ∀ c ρ p p1 p2 k1 k2 x y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) p1) p2) k1) k2) x) y) ∘ eP =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => p) c) (pt : W) : Fin 3 → W) := by
    intro c ρ p p1 p2 k1 k2 x y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hP1 : ∀ c ρ p p1 p2 k1 k2 x y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) p1) p2) k1) k2) x) y) ∘ eP1 =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => p1) p) (pt : W) : Fin 3 → W) := by
    intro c ρ p p1 p2 k1 k2 x y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hP2 : ∀ c ρ p p1 p2 k1 k2 x y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) p1) p2) k1) k2) x) y) ∘ eP2 =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => p2) p) (pt : W) : Fin 3 → W) := by
    intro c ρ p p1 p2 k1 k2 x y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK1 : ∀ c ρ p p1 p2 k1 k2 x y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) p1) p2) k1) k2) x) y) ∘ eK1 =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => k1) p1) ρ : Fin 3 → W) := by
    intro c ρ p p1 p2 k1 k2 x y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK2 : ∀ c ρ p p1 p2 k1 k2 x y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) p1) p2) k1) k2) x) y) ∘ eK2 =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => k2) p2) ρ : Fin 3 → W) := by
    intro c ρ p p1 p2 k1 k2 x y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hX : ∀ c ρ p p1 p2 k1 k2 x y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) p1) p2) k1) k2) x) y) ∘ eX =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : W)) x) X) k1 : Fin 4 → W) := by
    intro c ρ p p1 p2 k1 k2 x y; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hY : ∀ c ρ p p1 p2 k1 k2 x y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) p1) p2) k1) k2) x) y) ∘ eY =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (pt : W)) y) X) k2 : Fin 4 → W) := by
    intro c ρ p p1 p2 k1 k2 x y; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hV : ∀ c ρ p p1 p2 k1 k2 x y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) p1) p2) k1) k2) x) y) ∘ eV =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) x) y) (pt : W) : Fin 4 → W) := by
    intro c ρ p p1 p2 k1 k2 x y; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [eqEStepF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hC, hR, hP, hP1, hP2, hK1, hK2, hX, hY, hV,
    realize_sfstEqF, realize_ssndEqF, realize_kpairEqF, realize_appEqF, realize_eqvF]
  clear hC hR hP hP1 hP2 hK1 hK2 hX hY hV
  constructor
  · rintro ⟨c, ρ, p, p1, p2, k1, k2, x, y, hC, hR, hP, hP1, hP2, hK1, hK2, hX, hY, hV⟩
    have hC' : c = sfst i := hC
    have hR' : ρ = ssnd i := hR
    have hP' : p = ssnd c := hP
    have hP1' : p1 = sfst p := hP1
    have hP2' : p2 = ssnd p := hP2
    have hK1' : k1 = kpair p1 ρ := hK1
    have hK2' : k2 = kpair p2 ρ := hK2
    have hX' : x = app X k1 := hX
    have hY' : y = app X k2 := hY
    have hV' : v = eqv x y := hV
    rw [hV', hX', hY', hK1', hK2', hP1', hP2', hP', hC', hR']
  · intro h
    exact ⟨sfst i, ssnd i, ssnd (sfst i), sfst (ssnd (sfst i)), ssnd (ssnd (sfst i)),
      kpair (sfst (ssnd (sfst i))) (ssnd i), kpair (ssnd (ssnd (sfst i))) (ssnd i),
      app X (kpair (sfst (ssnd (sfst i))) (ssnd i)), app X (kpair (ssnd (ssnd (sfst i))) (ssnd i)),
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h⟩




variable {W : Type w} [SetTheory W]

/-! ## Stage 44: the Form-level reader `consGraphEqF` for `consGraph` -/

/-- Variable maps for `consGraphEqF` (base vars `0 ↦ w`, `1 ↦ x`, `2 ↦ ρ`). -/
def cgZMap : Fin 2 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨3, by omega⟩ | _ => ⟨0, by omega⟩
def cgEmptyMap : Fin 1 → Fin 5 := fun _ => ⟨4, by omega⟩
def cgKpMap : Fin 3 → Fin 5 :=
  fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨4, by omega⟩ | _ => ⟨1, by omega⟩
def cgMMap : Fin 2 → Fin 5 :=
  fun k => match k.val with | 0 => ⟨4, by omega⟩ | _ => ⟨2, by omega⟩
def cgShiftMap : Fin 2 → Fin 5 :=
  fun k => match k.val with | 0 => ⟨4, by omega⟩ | _ => ⟨3, by omega⟩

/-- `w = consGraph x ρ` (variables `0 ↦ w`, `1 ↦ x`, `2 ↦ ρ`):
`∀ z, z ∈ˢ w ↔ (∃ e, e = ∅ ∧ z = kpair e x) ∨ (∃ z₀ ∈ˢ ρ, consShiftF z₀ z)`. -/
def consGraphEqF : Form 3 :=
  .all (.iff (Form.relabel cgZMap (.mem ⟨0, by omega⟩ ⟨1, by omega⟩))
    (.or
      (.ex (.and (Form.relabel cgEmptyMap emptyF) (Form.relabel cgKpMap kpairEqF)))
      (.ex (.and (Form.relabel cgMMap (.mem ⟨0, by omega⟩ ⟨1, by omega⟩))
        (Form.relabel cgShiftMap consShiftF)))))

theorem realize_consGraphEqF {w x ρ : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => w) x) ρ) consGraphEqF ↔
      w = consGraph x ρ := by
  have hZ : ∀ w x ρ z : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => w) x) ρ) z) ∘ cgZMap =
        (Form.snoc (fun _ : Fin 1 => z) w : Fin 2 → W) := by
    intro w x ρ z; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hE : ∀ w x ρ z e : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => w) x) ρ) z) e) ∘ cgEmptyMap =
        (Form.snoc Form.nil e : Fin 1 → W) := by
    intro w x ρ z e; funext ⟨k, hk⟩
    have hk1 : k = 0 := by omega
    rcases hk1 with rfl; rfl
  have hK : ∀ w x ρ z e : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => w) x) ρ) z) e) ∘ cgKpMap =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => z) e) x : Fin 3 → W) := by
    intro w x ρ z e; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hM : ∀ w x ρ z z₀ : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => w) x) ρ) z) z₀) ∘ cgMMap =
        (Form.snoc (fun _ : Fin 1 => z₀) ρ : Fin 2 → W) := by
    intro w x ρ z z₀; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hS : ∀ w x ρ z z₀ : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => w) x) ρ) z) z₀) ∘ cgShiftMap =
        (Form.snoc (fun _ : Fin 1 => z₀) z : Fin 2 → W) := by
    intro w x ρ z z₀; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [consGraphEqF, Form.realize_all, Form.realize_iff, Form.realize_or,
    Form.realize_ex, Form.realize_and, Form.realize_relabel, Form.realize_mem,
    hZ, hE, hK, hM, hS, realize_emptyF_eq, realize_kpairEqF, realize_consShiftF]
  clear hZ hE hK hM hS
  constructor
  · intro h
    refine SetTheory.ext (V := W) fun z => ?_
    have hz : z ∈ˢ w ↔ (∃ e : W, e = empty ∧ z = kpair e x) ∨
        (∃ z₀ : W, z₀ ∈ˢ ρ ∧ ((∃ m y : W, z₀ = kpair m y ∧ z = kpair (vsucc m) y) ∨
          (¬ ∃ m y : W, z₀ = kpair m y) ∧ z = z₀)) := h z
    rw [mem_consGraph]
    constructor
    · intro hw
      rcases hz.mp hw with ⟨e, he, hze⟩ | ⟨z₀, hz₀, hs⟩
      · left; rw [he] at hze; exact hze
      · right; exact ⟨z₀, hz₀, hs⟩
    · intro hw
      rcases hw with rfl | ⟨z₀, hz₀, hs⟩
      · exact hz.mpr (Or.inl ⟨empty, rfl, rfl⟩)
      · exact hz.mpr (Or.inr ⟨z₀, hz₀, hs⟩)
  · intro h z
    have hgoal : z ∈ˢ consGraph x ρ ↔ ((∃ e : W, e = empty ∧ z = kpair e x) ∨
        (∃ z₀ : W, z₀ ∈ˢ ρ ∧ ((∃ m y : W, z₀ = kpair m y ∧ z = kpair (vsucc m) y) ∨
          (¬ ∃ m y : W, z₀ = kpair m y) ∧ z = z₀))) := by
      rw [mem_consGraph]
      constructor
      · rintro (rfl | ⟨z₀, hz₀, hs⟩)
        · exact Or.inl ⟨empty, rfl, rfl⟩
        · exact Or.inr ⟨z₀, hz₀, hs⟩
      · rintro (⟨e, he, hze⟩ | ⟨z₀, hz₀, hs⟩)
        · left; rw [he] at hze; exact hze
        · right; exact ⟨z₀, hz₀, hs⟩
    rw [h]
    exact hgoal



variable {W : Type w} [SetTheory W]

/-! ## Stage 45: the `letE` case of the definable interp step -/

/-- Variable maps into the `letEStepF` bound context `(v, X, i, pt, c, ρ, p, a, b, k, v0, w, k2)`. -/
def leMC : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def leMR : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨5, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def leMP : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨6, by omega⟩ | 1 => ⟨4, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def leMA : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨6, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def leMB : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨8, by omega⟩ | 1 => ⟨6, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def leMK : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨9, by omega⟩ | 1 => ⟨7, by omega⟩ | 2 => ⟨5, by omega⟩ | _ => ⟨5, by omega⟩
def leMV0 : Fin 4 → Fin 13 := fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨1, by omega⟩ | 3 => ⟨9, by omega⟩ | _ => ⟨9, by omega⟩
def leMW : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨11, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨5, by omega⟩ | _ => ⟨5, by omega⟩
def leMK2 : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨12, by omega⟩ | 1 => ⟨8, by omega⟩ | 2 => ⟨11, by omega⟩ | _ => ⟨11, by omega⟩
def leMV : Fin 4 → Fin 13 := fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨0, by omega⟩ | 2 => ⟨1, by omega⟩ | 3 => ⟨12, by omega⟩ | _ => ⟨12, by omega⟩

/-- The `letE` step of the definable interpretation (variables `0 ↦ v`,
`1 ↦ X` (the current family graph), `2 ↦ i` (the index `kpair c ρ`),
`3 ↦ pt`): `v = app X (kpair (ssnd (ssnd (sfst i)))
(consGraph (app X (kpair (sfst (ssnd (sfst i))) (ssnd i))) (ssnd i)))`
where `c = sfst i`, `ρ = ssnd i` — the body's code read at the
environment extended by the value's value. -/
def letEStepF : Form 4 :=
  (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.and (Form.relabel leMC sfstEqF) (.and (Form.relabel leMR ssndEqF) (.and (Form.relabel leMP ssndEqF) (.and (Form.relabel leMA sfstEqF) (.and (Form.relabel leMB ssndEqF) (.and (Form.relabel leMK kpairEqF) (.and (Form.relabel leMV0 appEqF) (.and (Form.relabel leMW consGraphEqF) (.and (Form.relabel leMK2 kpairEqF) (Form.relabel leMV appEqF)))))))))))))))))))

theorem realize_letEStepF {v X i : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) X) i) (pt : W)) letEStepF ↔
      v = app X (kpair (ssnd (ssnd (sfst i)))
        (consGraph (app X (kpair (sfst (ssnd (sfst i))) (ssnd i))) (ssnd i))) := by
  have hMC: ∀ c ρ p a b k v0 w k2 : W,
      ((Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) a) b) k) v0) w) k2)) ∘ leMC =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => c) i) (pt : W) : Fin 3 → W) := by
    intro c ρ p a b k v0 w k2; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hMR: ∀ c ρ p a b k v0 w k2 : W,
      ((Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) a) b) k) v0) w) k2)) ∘ leMR =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => ρ) i) (pt : W) : Fin 3 → W) := by
    intro c ρ p a b k v0 w k2; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hMP: ∀ c ρ p a b k v0 w k2 : W,
      ((Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) a) b) k) v0) w) k2)) ∘ leMP =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => p) c) (pt : W) : Fin 3 → W) := by
    intro c ρ p a b k v0 w k2; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hMA: ∀ c ρ p a b k v0 w k2 : W,
      ((Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) a) b) k) v0) w) k2)) ∘ leMA =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => a) p) (pt : W) : Fin 3 → W) := by
    intro c ρ p a b k v0 w k2; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hMB: ∀ c ρ p a b k v0 w k2 : W,
      ((Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) a) b) k) v0) w) k2)) ∘ leMB =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => b) p) (pt : W) : Fin 3 → W) := by
    intro c ρ p a b k v0 w k2; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hMK: ∀ c ρ p a b k v0 w k2 : W,
      ((Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) a) b) k) v0) w) k2)) ∘ leMK =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => k) a) ρ : Fin 3 → W) := by
    intro c ρ p a b k v0 w k2; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hMV0: ∀ c ρ p a b k v0 w k2 : W,
      ((Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) a) b) k) v0) w) k2)) ∘ leMV0 =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) v0) X) k : Fin 4 → W) := by
    intro c ρ p a b k v0 w k2; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hMW: ∀ c ρ p a b k v0 w k2 : W,
      ((Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) a) b) k) v0) w) k2)) ∘ leMW =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => w) v0) ρ : Fin 3 → W) := by
    intro c ρ p a b k v0 w k2; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hMK2: ∀ c ρ p a b k v0 w k2 : W,
      ((Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) a) b) k) v0) w) k2)) ∘ leMK2 =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => k2) b) w : Fin 3 → W) := by
    intro c ρ p a b k v0 w k2; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hMV: ∀ c ρ p a b k v0 w k2 : W,
      ((Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) a) b) k) v0) w) k2)) ∘ leMV =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) v) X) k2 : Fin 4 → W) := by
    intro c ρ p a b k v0 w k2; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [letEStepF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hMC, hMR, hMP, hMA, hMB, hMK, hMV0, hMW, hMK2, hMV,
    realize_sfstEqF, realize_ssndEqF, realize_kpairEqF, realize_appEqF, realize_consGraphEqF]
  clear hMC hMR hMP hMA hMB hMK hMV0 hMW hMK2 hMV
  constructor
  · rintro ⟨c, ρ, p, a, b, k, v0, w, k2, hC, hR, hP, hA, hB, hK, hV0, hW, hK2, hV⟩
    rw [hV, hK2, hW, hV0, hK, hB, hA, hP, hC, hR]
  · intro h
    exact ⟨sfst i, ssnd i, ssnd (sfst i), sfst (ssnd (sfst i)), ssnd (ssnd (sfst i)),
      kpair (sfst (ssnd (sfst i))) (ssnd i),
      app X (kpair (sfst (ssnd (sfst i))) (ssnd i)),
      consGraph (app X (kpair (sfst (ssnd (sfst i))) (ssnd i))) (ssnd i),
      kpair (ssnd (ssnd (sfst i)))
        (consGraph (app X (kpair (sfst (ssnd (sfst i))) (ssnd i))) (ssnd i)),
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h⟩

/-- The `letE val body` code reads the body's value at the environment
extended by the value's value. -/
theorem realize_letEStepF_tmCode {X ρ : W} (val body : ConLeche.Term.Term) :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ =>
        app X (kpair (tmCode (W := W) body)
          (consGraph (app X (kpair (tmCode (W := W) val) ρ)) ρ))) X)
        (kpair (tmCode (W := W) (ConLeche.Term.Term.letE val body)) ρ)) (pt : W))
      letEStepF :=
  realize_letEStepF.mpr (by simp only [tmCode, sfst_kpair, ssnd_kpair])



variable {W : Type w} [SetTheory W]

/-! ## Stage 46: the `lam` readers — the definable function graph and the point-condition -/

/-- Variable maps into the `lamGraphEqF` contexts. -/
def lgZV : Fin 2 → Fin 7 := fun k => match k.val with | 0 => ⟨6, by omega⟩ | 1 => ⟨0, by omega⟩ | _ => ⟨0, by omega⟩
def lgXA : Fin 2 → Fin 8 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨1, by omega⟩ | _ => ⟨1, by omega⟩
def lgW : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨8, by omega⟩ | 1 => ⟨7, by omega⟩ | 2 => ⟨4, by omega⟩ | _ => ⟨4, by omega⟩
def lgK : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨9, by omega⟩ | 1 => ⟨3, by omega⟩ | 2 => ⟨8, by omega⟩ | _ => ⟨8, by omega⟩
def lgV : Fin 4 → Fin 11 := fun k => match k.val with | 0 => ⟨5, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨2, by omega⟩ | 3 => ⟨9, by omega⟩ | _ => ⟨9, by omega⟩
def lgZ : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨6, by omega⟩ | 1 => ⟨7, by omega⟩ | 2 => ⟨10, by omega⟩ | _ => ⟨10, by omega⟩

/-- The graph reader for the `lam` body (variables `0 ↦ v`, `1 ↦ a`,
`2 ↦ X`, `3 ↦ b`, `4 ↦ ρ`, `5 ↦ pt`): `v = graph (fun x => app X (kpair b (consGraph x ρ))) a`. -/
def lamGraphEqF : Form 6 :=
  .all (.iff (Form.relabel lgZV (.mem ⟨0, by omega⟩ ⟨1, by omega⟩)) (.ex (.and (Form.relabel lgXA (.mem ⟨0, by omega⟩ ⟨1, by omega⟩)) (.ex (.ex (.ex (.and (Form.relabel lgW consGraphEqF) (.and (Form.relabel lgK kpairEqF) (.and (Form.relabel lgV appEqF) (Form.relabel lgZ kpairEqF))))))))))

theorem realize_lamGraphEqF {v a X b ρ : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
      (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) lamGraphEqF ↔
      v = graph (fun x => app X (kpair b (consGraph x ρ))) a := by
  have hZV: ∀ z : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) ∘ lgZV =
        (Form.snoc (fun _ : Fin 1 => z) v : Fin 2 → W) := by
    intro z; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hXA: ∀ z x : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) x) ∘ lgXA =
        (Form.snoc (fun _ : Fin 1 => x) a : Fin 2 → W) := by
    intro z x; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hW: ∀ z x w k v0 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) x) w) k) v0) ∘ lgW =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => w) x) ρ : Fin 3 → W) := by
    intro z x w k v0; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK: ∀ z x w k v0 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) x) w) k) v0) ∘ lgK =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => k) b) w : Fin 3 → W) := by
    intro z x w k v0; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV: ∀ z x w k v0 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) x) w) k) v0) ∘ lgV =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) v0) X) k : Fin 4 → W) := by
    intro z x w k v0; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hZ: ∀ z x w k v0 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) x) w) k) v0) ∘ lgZ =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => z) x) v0 : Fin 3 → W) := by
    intro z x w k v0; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [lamGraphEqF, Form.realize_all, Form.realize_iff, Form.realize_ex,
    Form.realize_and, Form.realize_relabel, Form.realize_mem,
    hZV, hXA, hW, hK, hV, hZ,
    realize_consGraphEqF, realize_kpairEqF, realize_appEqF]
  clear hZV hXA hW hK hV hZ
  constructor
  · intro h
    have hc : ∀ z : W, z ∈ˢ v ↔ ∃ x, x ∈ˢ a ∧ ∃ w k v0,
        w = consGraph x ρ ∧ k = kpair b w ∧ v0 = app X k ∧ z = kpair x v0 := h
    apply SetTheory.ext (V := W)
    intro z
    rw [hc z, mem_graph]
    constructor
    · rintro ⟨x, hx, w, k, v0, hw, hk, hv0, hz⟩
      exact ⟨x, hx, by rw [hz, hv0, hk, hw]⟩
    · rintro ⟨x, hx, hz⟩
      exact ⟨x, hx, consGraph x ρ, kpair b (consGraph x ρ),
        app X (kpair b (consGraph x ρ)), rfl, rfl, rfl, hz⟩
  · intro h
    rw [h]
    intro z
    have hg : z ∈ˢ graph (fun x => app X (kpair b (consGraph x ρ))) a ↔
        ∃ x, x ∈ˢ a ∧ ∃ w k v0,
          w = consGraph x ρ ∧ k = kpair b w ∧ v0 = app X k ∧ z = kpair x v0 := by
      rw [mem_graph]
      constructor
      · rintro ⟨x, hx, hz⟩
        exact ⟨x, hx, consGraph x ρ, kpair b (consGraph x ρ),
          app X (kpair b (consGraph x ρ)), rfl, rfl, rfl, hz⟩
      · rintro ⟨x, hx, w, k, v0, hw, hk, hv0, hz⟩
        exact ⟨x, hx, by rw [hz, hv0, hk, hw]⟩
    exact hg

/-- Variable maps into the `ptAllF` contexts. -/
def paXA : Fin 2 → Fin 6 := fun k => match k.val with | 0 => ⟨5, by omega⟩ | 1 => ⟨0, by omega⟩ | _ => ⟨0, by omega⟩
def paW : Fin 3 → Fin 8 := fun k => match k.val with | 0 => ⟨6, by omega⟩ | 1 => ⟨5, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def paK : Fin 3 → Fin 8 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨6, by omega⟩ | _ => ⟨6, by omega⟩
def paV : Fin 4 → Fin 8 := fun k => match k.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨4, by omega⟩ | 2 => ⟨1, by omega⟩ | 3 => ⟨7, by omega⟩ | _ => ⟨7, by omega⟩

/-- The point-condition reader for `lam` (variables `0 ↦ a`, `1 ↦ X`,
`2 ↦ b`, `3 ↦ ρ`, `4 ↦ pt`): `∀ x ∈ˢ a, app X (kpair b (consGraph x ρ)) = pt`. -/
def ptAllF : Form 5 :=
  .all (.imp (Form.relabel paXA (.mem ⟨0, by omega⟩ ⟨1, by omega⟩)) (.ex (.ex (.and (Form.relabel paW consGraphEqF) (.and (Form.relabel paK kpairEqF) (Form.relabel paV appEqF))))))

theorem realize_ptAllF {a X b ρ : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc
      (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) ptAllF ↔
      ∀ x, x ∈ˢ a → app X (kpair b (consGraph x ρ)) = pt := by
  have hXA: ∀ x : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) ∘ paXA =
        (Form.snoc (fun _ : Fin 1 => x) a : Fin 2 → W) := by
    intro x; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hW: ∀ x w k : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) w) k) ∘ paW =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => w) x) ρ : Fin 3 → W) := by
    intro x w k; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK: ∀ x w k : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) w) k) ∘ paK =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => k) b) w : Fin 3 → W) := by
    intro x w k; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV: ∀ x w k : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) w) k) ∘ paV =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) pt) X) k : Fin 4 → W) := by
    intro x w k; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [ptAllF, Form.realize_all, Form.realize_imp, Form.realize_ex,
    Form.realize_and, Form.realize_relabel, Form.realize_mem,
    hXA, hW, hK, hV, realize_consGraphEqF, realize_kpairEqF, realize_appEqF]
  clear hXA hW hK hV
  constructor
  · rintro h x hx
    obtain ⟨w, k, hw, hk, hv⟩ := h x hx
    rw [hv, hk, hw]
  · intro h x hx
    exact ⟨consGraph x ρ, kpair b (consGraph x ρ), rfl, rfl, (h x hx).symm⟩



variable {W : Type w} [SetTheory W]

/-! ## Stage 47: the `lam` case of the definable interp step -/

/-- Variable maps into the `lamStepF` bound context `(v, X, i, pt, c, ρ, p, ac, bc, k, a)`. -/
def lmC : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def lmR : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨5, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def lmP : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨6, by omega⟩ | 1 => ⟨4, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def lmA : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨6, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def lmB : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨8, by omega⟩ | 1 => ⟨6, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def lmK : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨9, by omega⟩ | 1 => ⟨7, by omega⟩ | 2 => ⟨5, by omega⟩ | _ => ⟨5, by omega⟩
def lmV : Fin 4 → Fin 11 := fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨1, by omega⟩ | 3 => ⟨9, by omega⟩ | _ => ⟨9, by omega⟩
def lmPA : Fin 5 → Fin 11 := fun k => match k.val with | 0 => ⟨10, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨8, by omega⟩ | 3 => ⟨5, by omega⟩ | 4 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def lmGA : Fin 6 → Fin 11 := fun k => match k.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨1, by omega⟩ | 3 => ⟨8, by omega⟩ | 4 => ⟨5, by omega⟩ | 5 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩

/-- The `lam` step of the definable interpretation (variables `0 ↦ v`,
`1 ↦ X`, `2 ↦ i = kpair c ρ`, `3 ↦ pt`): `v = lamV a f` where
`a = app X (kpair (sfst (ssnd c)) ρ)` is the type's value and
`f x = app X (kpair (ssnd (ssnd c)) (consGraph x ρ))` is the body's
value at the extended environment. -/
def lamStepF : Form 4 :=
  (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.and (Form.relabel lmC sfstEqF) (.and (Form.relabel lmR ssndEqF) (.and (Form.relabel lmP ssndEqF) (.and (Form.relabel lmA sfstEqF) (.and (Form.relabel lmB ssndEqF) (.and (Form.relabel lmK kpairEqF) (.and (Form.relabel lmV appEqF) (.or (.and (Form.relabel lmPA ptAllF) (.equal ⟨0, by omega⟩ ⟨3, by omega⟩)) (.and (.not (Form.relabel lmPA ptAllF)) (Form.relabel lmGA lamGraphEqF)))))))))))))))))

theorem realize_lamStepF {v X i : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) X) i) (pt : W)) lamStepF ↔
      v = lamV (app X (kpair (sfst (ssnd (sfst i))) (ssnd i)))
        (fun x => app X (kpair (ssnd (ssnd (sfst i))) (consGraph x (ssnd i)))) := by
  have hC: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ lmC =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => c) i) (pt : W) : Fin 3 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hR: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ lmR =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => ρ) i) (pt : W) : Fin 3 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hP: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ lmP =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => p) c) (pt : W) : Fin 3 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hA: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ lmA =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => ac) p) (pt : W) : Fin 3 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hB: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ lmB =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => bc) p) (pt : W) : Fin 3 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ lmK =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => k) ac) ρ : Fin 3 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ lmV =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) a) X) k : Fin 4 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hPA: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ lmPA =
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) bc) ρ) (pt : W) : Fin 5 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hGA: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ lmGA =
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) bc) ρ) (pt : W) : Fin 6 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [lamStepF, Form.realize_ex, Form.realize_and, Form.realize_or,
    Form.realize_not, Form.realize_equal, Form.realize_relabel,
    hC, hR, hP, hA, hB, hK, hV, hPA, hGA,
    realize_sfstEqF, realize_ssndEqF, realize_kpairEqF, realize_appEqF,
    realize_ptAllF, realize_lamGraphEqF]
  clear hC hR hP hA hB hK hV hPA hGA
  constructor
  · rintro ⟨c, ρ, p, ac, bc, k, a, hC, hR, hP, hA, hB, hK, hV, hD⟩
    rw [hV, hK, hB, hA, hP, hC, hR] at hD
    rcases hD with ⟨hpt, hv⟩ | ⟨hnpt, hg⟩
    · have hv' : v = pt := hv
      rw [hv']
      unfold lamV
      rw [ptN_eq_zero.mpr hpt, lamR_zero]
    · rw [hg]
      unfold lamV
      rw [lamR_pos (fun h0 => hnpt (ptN_eq_zero.mp h0))]
  · intro h
    have key : ∀ (a : W) (f : W → W), v = lamV a f →
        ((∀ x, x ∈ˢ a → f x = pt) ∧ v = pt) ∨
          (¬ ∀ x, x ∈ˢ a → f x = pt) ∧ v = graph f a := by
      intro a f h
      unfold lamV at h
      by_cases hc : ∀ x, x ∈ˢ a → f x = pt
      · rw [ptN_eq_zero.mpr hc, lamR_zero] at h
        exact Or.inl ⟨hc, h⟩
      · have hn : ptN a f ≠ 0 := fun h0 => hc (ptN_eq_zero.mp h0)
        rw [lamR_pos hn] at h
        exact Or.inr ⟨hc, h⟩
    exact ⟨sfst i, ssnd i, ssnd (sfst i), sfst (ssnd (sfst i)), ssnd (ssnd (sfst i)),
      kpair (sfst (ssnd (sfst i))) (ssnd i),
      app X (kpair (sfst (ssnd (sfst i))) (ssnd i)),
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, key _ _ h⟩

/-- The `lam A b` code reads `lamV` of the type's value and the body's
extended-environment function. -/
theorem realize_lamStepF_tmCode {X ρ : W} (A b : ConLeche.Term.Term) :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ =>
        lamV (app X (kpair (tmCode (W := W) A) ρ))
          (fun x => app X (kpair (tmCode (W := W) b) (consGraph x ρ)))) X)
        (kpair (tmCode (W := W) (ConLeche.Term.Term.lam A b)) ρ)) (pt : W))
      lamStepF :=
  realize_lamStepF.mpr (by simp only [tmCode, sfst_kpair, ssnd_kpair])

/-! ## Stage 48: the `pi` proposition-condition reader `propAllF` -/

/-- Variable maps into the `propAllF` contexts. -/
def prXA : Fin 2 → Fin 6 := fun k => match k.val with | 0 => ⟨5, by omega⟩ | 1 => ⟨0, by omega⟩ | _ => ⟨0, by omega⟩
def prW : Fin 3 → Fin 9 := fun k => match k.val with | 0 => ⟨6, by omega⟩ | 1 => ⟨5, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def prK : Fin 3 → Fin 9 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨6, by omega⟩ | _ => ⟨6, by omega⟩
def prV : Fin 4 → Fin 9 := fun k => match k.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨8, by omega⟩ | 2 => ⟨1, by omega⟩ | 3 => ⟨7, by omega⟩ | _ => ⟨7, by omega⟩
def prY : Fin 2 → Fin 10 := fun k => match k.val with | 0 => ⟨9, by omega⟩ | 1 => ⟨8, by omega⟩ | _ => ⟨8, by omega⟩

/-- The proposition-condition reader for `pi` (variables `0 ↦ a`, `1 ↦ X`,
`2 ↦ b`, `3 ↦ ρ`, `4 ↦ pt`): `∀ x ∈ˢ a, app X (kpair b (consGraph x ρ)) ∈ˢ univZero`,
internalized via `mem_univZero`/`mem_unitSet_iff` as
`∀ x ∈ˢ a, ∀ y ∈ˢ app X (kpair b (consGraph x ρ)), y = pt`. -/
def propAllF : Form 5 :=
  .all (.imp (Form.relabel prXA (.mem ⟨0, by omega⟩ ⟨1, by omega⟩)) (.ex (.ex (.ex (.and (Form.relabel prW consGraphEqF) (.and (Form.relabel prK kpairEqF) (.and (Form.relabel prV appEqF) (.all (.imp (Form.relabel prY (.mem ⟨0, by omega⟩ ⟨1, by omega⟩)) (.equal ⟨9, by omega⟩ ⟨4, by omega⟩))))))))))

theorem realize_propAllF {a X b ρ : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc
      (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) propAllF ↔
      ∀ x, x ∈ˢ a → app X (kpair b (consGraph x ρ)) ∈ˢ (univZero : W) := by
  have hXA: ∀ x : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) ∘ prXA =
        (Form.snoc (fun _ : Fin 1 => x) a : Fin 2 → W) := by
    intro x; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hW: ∀ x w k v0 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) w) k) v0) ∘ prW =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => w) x) ρ : Fin 3 → W) := by
    intro x w k v0; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK: ∀ x w k v0 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) w) k) v0) ∘ prK =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => k) b) w : Fin 3 → W) := by
    intro x w k v0; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV: ∀ x w k v0 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) w) k) v0) ∘ prV =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) v0) X) k : Fin 4 → W) := by
    intro x w k v0; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hY: ∀ x w k v0 y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) w) k) v0) y) ∘ prY =
        (Form.snoc (fun _ : Fin 1 => y) v0 : Fin 2 → W) := by
    intro x w k v0 y; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [propAllF, Form.realize_all, Form.realize_imp, Form.realize_ex,
    Form.realize_and, Form.realize_relabel, Form.realize_mem, Form.realize_equal,
    Form.snoc_mk,
    hXA, hW, hK, hV, hY, realize_consGraphEqF, realize_kpairEqF, realize_appEqF]
  clear hXA hW hK hV hY
  constructor
  · rintro h x hx
    obtain ⟨w, k, v0, hw, hk, hv, hall⟩ := h x hx
    rw [mem_univZero]
    show ∀ y, y ∈ˢ app X (kpair b (consGraph x ρ)) → y ∈ˢ (unitSet : W)
    intro y hy
    rw [mem_unitSet_iff]
    apply hall y
    rw [hv, hk, hw]
    exact hy
  · intro h x hx
    refine ⟨consGraph x ρ, kpair b (consGraph x ρ), app X (kpair b (consGraph x ρ)), rfl, rfl, rfl, fun y hy => ?_⟩
    have hsub := (mem_univZero.mp (h x hx)) y hy
    rwa [mem_unitSet_iff] at hsub


/-! ## Stage 49: the `piSet` reader `piSetEqF` -/

/-- Variable maps into the `piSetEqF` contexts. -/
def pgZV : Fin 2 → Fin 7 := fun k => match k.val with | 0 => ⟨6, by omega⟩ | 1 => ⟨0, by omega⟩ | _ => ⟨0, by omega⟩
def pgWZ : Fin 2 → Fin 8 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨6, by omega⟩ | _ => ⟨6, by omega⟩
def pgXA : Fin 2 → Fin 13 := fun k => match k.val with | 0 => ⟨8, by omega⟩ | 1 => ⟨1, by omega⟩ | _ => ⟨1, by omega⟩
def pgW2 : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨10, by omega⟩ | 1 => ⟨8, by omega⟩ | 2 => ⟨4, by omega⟩ | _ => ⟨4, by omega⟩
def pgK : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨11, by omega⟩ | 1 => ⟨3, by omega⟩ | 2 => ⟨10, by omega⟩ | _ => ⟨10, by omega⟩
def pgV : Fin 4 → Fin 13 := fun k => match k.val with | 0 => ⟨5, by omega⟩ | 1 => ⟨12, by omega⟩ | 2 => ⟨2, by omega⟩ | 3 => ⟨11, by omega⟩ | _ => ⟨11, by omega⟩
def pgYV : Fin 2 → Fin 13 := fun k => match k.val with | 0 => ⟨9, by omega⟩ | 1 => ⟨12, by omega⟩ | _ => ⟨12, by omega⟩
def pgWK : Fin 3 → Fin 13 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨8, by omega⟩ | 2 => ⟨9, by omega⟩ | _ => ⟨9, by omega⟩
def pgXA2 : Fin 2 → Fin 8 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨1, by omega⟩ | _ => ⟨1, by omega⟩
def pgKZY : Fin 3 → Fin 9 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨6, by omega⟩ | 2 => ⟨8, by omega⟩ | _ => ⟨8, by omega⟩
def pgKZY2 : Fin 3 → Fin 10 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨6, by omega⟩ | 2 => ⟨9, by omega⟩ | _ => ⟨9, by omega⟩

/-- The `piSet` reader for `pi` (variables `0 ↦ v`, `1 ↦ a`, `2 ↦ X`, `3 ↦ b`, `4 ↦ ρ`, `5 ↦ pt`): `v = piSet a (fun x => app X (kpair b (consGraph x ρ)))` via extensionality, `mem_piSet` and `mem_sigmaPairs`. -/
def piSetEqF : Form 6 :=
  .all (.iff (Form.relabel pgZV (.mem ⟨0, by omega⟩ ⟨1, by omega⟩))
    (.and
      (.all (.imp (Form.relabel pgWZ (.mem ⟨0, by omega⟩ ⟨1, by omega⟩))
        (.ex (.ex (.ex (.ex (.ex
          (.and (Form.relabel pgXA (.mem ⟨0, by omega⟩ ⟨1, by omega⟩))
          (.and (Form.relabel pgW2 consGraphEqF)
          (.and (Form.relabel pgK kpairEqF)
          (.and (Form.relabel pgV appEqF)
          (.and (Form.relabel pgYV (.mem ⟨0, by omega⟩ ⟨1, by omega⟩))
                (Form.relabel pgWK kpairEqF)))))))))))))
      (.all (.imp (Form.relabel pgXA2 (.mem ⟨0, by omega⟩ ⟨1, by omega⟩))
        (.ex (.and (Form.relabel pgKZY kpairMemF)
          (.all (.imp (Form.relabel pgKZY2 kpairMemF)
            (.equal ⟨9, by omega⟩ ⟨8, by omega⟩)))))))))

theorem realize_piSetEqF {v a X b ρ : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc
      (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) piSetEqF ↔
      v = piSet a (fun x => app X (kpair b (consGraph x ρ))) := by
  have hZV: ∀ z : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) ∘ pgZV =
        (Form.snoc (fun _ : Fin 1 => z) v : Fin 2 → W) := by
    intro z; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hWZ: ∀ z w : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) w) ∘ pgWZ =
        (Form.snoc (fun _ : Fin 1 => w) z : Fin 2 → W) := by
    intro z w; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hXA: ∀ z w x y w2 k v0 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) w) x) y) w2) k) v0) ∘ pgXA =
        (Form.snoc (fun _ : Fin 1 => x) a : Fin 2 → W) := by
    intro z w x y w2 k v0; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hW2: ∀ z w x y w2 k v0 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) w) x) y) w2) k) v0) ∘ pgW2 =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => w2) x) ρ : Fin 3 → W) := by
    intro z w x y w2 k v0; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK: ∀ z w x y w2 k v0 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) w) x) y) w2) k) v0) ∘ pgK =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => k) b) w2 : Fin 3 → W) := by
    intro z w x y w2 k v0; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV: ∀ z w x y w2 k v0 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) w) x) y) w2) k) v0) ∘ pgV =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) v0) X) k : Fin 4 → W) := by
    intro z w x y w2 k v0; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hYV: ∀ z w x y w2 k v0 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) w) x) y) w2) k) v0) ∘ pgYV =
        (Form.snoc (fun _ : Fin 1 => y) v0 : Fin 2 → W) := by
    intro z w x y w2 k v0; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hWK: ∀ z w x y w2 k v0 : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) w) x) y) w2) k) v0) ∘ pgWK =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => w) x) y : Fin 3 → W) := by
    intro z w x y w2 k v0; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hXA2: ∀ z x : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) x) ∘ pgXA2 =
        (Form.snoc (fun _ : Fin 1 => x) a : Fin 2 → W) := by
    intro z x; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hKZY: ∀ z x y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) x) y) ∘ pgKZY =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => x) z) y : Fin 3 → W) := by
    intro z x y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hKZY2: ∀ z x y y' : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) b) ρ) (pt : W)) z) x) y) y') ∘ pgKZY2 =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => x) z) y' : Fin 3 → W) := by
    intro z x y y'; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [piSetEqF, Form.realize_all, Form.realize_iff, Form.realize_imp,
    Form.realize_ex, Form.realize_and, Form.realize_relabel, Form.realize_mem,
    Form.realize_equal, Form.snoc_mk,
    hZV, hWZ, hXA, hW2, hK, hV, hYV, hWK, hXA2, hKZY, hKZY2,
    realize_consGraphEqF, realize_kpairEqF, realize_appEqF, realize_kpairMemF]
  clear hZV hWZ hXA hW2 hK hV hYV hWK hXA2 hKZY hKZY2
  have key : ∀ z, (z ⊆ˢ sigmaPairs a (fun x => app X (kpair b (consGraph x ρ))) ∧
      ∀ x, x ∈ˢ a → ∃ y, kpair x y ∈ˢ z ∧ ∀ y', kpair x y' ∈ˢ z → y' = y) ↔
      ((∀ w, w ∈ˢ z → ∃ x, ∃ y, ∃ w2, ∃ k, ∃ v0,
          x ∈ˢ a ∧ w2 = consGraph x ρ ∧ k = kpair b w2 ∧ v0 = app X k ∧ y ∈ˢ v0 ∧ w = kpair x y) ∧
       (∀ x, x ∈ˢ a → ∃ y, kpair x y ∈ˢ z ∧ ∀ y', kpair x y' ∈ˢ z → y' = y)) := by
    intro z
    constructor
    · rintro ⟨hsub, hall⟩
      constructor
      · intro w hw
        have hw' := hsub w hw
        rw [mem_sigmaPairs] at hw'
        obtain ⟨x, hx, y, hy, hwk⟩ := hw'
        exact ⟨x, y, consGraph x ρ, kpair b (consGraph x ρ),
          app X (kpair b (consGraph x ρ)), hx, rfl, rfl, rfl, hy, hwk⟩
      · exact hall
    · rintro ⟨hsub, hall⟩
      constructor
      · show ∀ w, w ∈ˢ z → w ∈ˢ sigmaPairs a (fun x => app X (kpair b (consGraph x ρ)))
        intro w hw
        obtain ⟨x, y, w2, k, v0, hx, hw2, hk, hv, hy, hwk⟩ := hsub w hw
        rw [mem_sigmaPairs]
        rw [hv, hk, hw2] at hy
        exact ⟨x, hx, y, hy, hwk⟩
      · exact hall
  constructor
  · intro h
    apply SetTheory.ext
    intro z
    rw [mem_piSet]
    exact (h z).trans (key z).symm
  · intro h z
    rw [h]
    show z ∈ˢ piSet a (fun x => app X (kpair b (consGraph x ρ))) ↔ _
    rw [mem_piSet]
    exact key z


/-! ## Stage 50: the `pi` existential-fibre reader `exAllF` -/

/-- Variable maps into the `exAllF` contexts. -/
def peXA : Fin 2 → Fin 6 := fun k => match k.val with | 0 => ⟨5, by omega⟩ | 1 => ⟨0, by omega⟩ | _ => ⟨0, by omega⟩
def peW : Fin 3 → Fin 10 := fun k => match k.val with | 0 => ⟨6, by omega⟩ | 1 => ⟨5, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def peK : Fin 3 → Fin 10 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨6, by omega⟩ | _ => ⟨6, by omega⟩
def peV : Fin 4 → Fin 10 := fun k => match k.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨8, by omega⟩ | 2 => ⟨1, by omega⟩ | 3 => ⟨7, by omega⟩ | _ => ⟨7, by omega⟩
def peYV : Fin 2 → Fin 10 := fun k => match k.val with | 0 => ⟨9, by omega⟩ | 1 => ⟨8, by omega⟩ | _ => ⟨8, by omega⟩

/-- The existential-fibre reader for `pi` (variables `0 ↦ a`, `1 ↦ X`,
`2 ↦ b`, `3 ↦ ρ`, `4 ↦ pt`): `∀ x ∈ˢ a, ∃ y, y ∈ˢ app X (kpair b (consGraph x ρ))`. -/
def exAllF : Form 5 :=
  .all (.imp (Form.relabel peXA (.mem ⟨0, by omega⟩ ⟨1, by omega⟩)) (.ex (.ex (.ex (.ex (.and (Form.relabel peW consGraphEqF) (.and (Form.relabel peK kpairEqF) (.and (Form.relabel peV appEqF) (Form.relabel peYV (.mem ⟨0, by omega⟩ ⟨1, by omega⟩))))))))))

theorem realize_exAllF {a X b ρ : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc
      (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) exAllF ↔
      ∀ x, x ∈ˢ a → ∃ y, y ∈ˢ app X (kpair b (consGraph x ρ)) := by
  have hXA: ∀ x : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) ∘ peXA =
        (Form.snoc (fun _ : Fin 1 => x) a : Fin 2 → W) := by
    intro x; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hW: ∀ x w k v0 y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) w) k) v0) y) ∘ peW =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => w) x) ρ : Fin 3 → W) := by
    intro x w k v0 y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK: ∀ x w k v0 y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) w) k) v0) y) ∘ peK =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => k) b) w : Fin 3 → W) := by
    intro x w k v0 y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV: ∀ x w k v0 y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) w) k) v0) y) ∘ peV =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) v0) X) k : Fin 4 → W) := by
    intro x w k v0 y; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hYV: ∀ x w k v0 y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) b) ρ) (pt : W)) x) w) k) v0) y) ∘ peYV =
        (Form.snoc (fun _ : Fin 1 => y) v0 : Fin 2 → W) := by
    intro x w k v0 y; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [exAllF, Form.realize_all, Form.realize_imp, Form.realize_ex,
    Form.realize_and, Form.realize_relabel, Form.realize_mem, Form.snoc_mk,
    hXA, hW, hK, hV, hYV, realize_consGraphEqF, realize_kpairEqF, realize_appEqF]
  clear hXA hW hK hV hYV
  constructor
  · rintro h x hx
    obtain ⟨w, k, v0, y, hw, hk, hv, hy⟩ := h x hx
    rw [hv, hk, hw] at hy
    exact ⟨y, hy⟩
  · intro h x hx
    obtain ⟨y, hy⟩ := h x hx
    exact ⟨consGraph x ρ, kpair b (consGraph x ρ), app X (kpair b (consGraph x ρ)), y, rfl, rfl, rfl, hy⟩


/-! ## Stage 51: the `pi` case of the definable interp step -/

/-- Variable maps into the `piStepF` bound context `(v, X, i, pt, c, ρ, p, ac, bc, k, a)`. -/
def pmC : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def pmR : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨5, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def pmP : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨6, by omega⟩ | 1 => ⟨4, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def pmA : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨7, by omega⟩ | 1 => ⟨6, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def pmB : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨8, by omega⟩ | 1 => ⟨6, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def pmK : Fin 3 → Fin 11 := fun k => match k.val with | 0 => ⟨9, by omega⟩ | 1 => ⟨7, by omega⟩ | 2 => ⟨5, by omega⟩ | _ => ⟨5, by omega⟩
def pmV : Fin 4 → Fin 11 := fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨1, by omega⟩ | 3 => ⟨9, by omega⟩ | _ => ⟨9, by omega⟩
def pmPA : Fin 5 → Fin 11 := fun k => match k.val with | 0 => ⟨10, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨8, by omega⟩ | 3 => ⟨5, by omega⟩ | 4 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def pmGA : Fin 6 → Fin 11 := fun k => match k.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨1, by omega⟩ | 3 => ⟨8, by omega⟩ | 4 => ⟨5, by omega⟩ | 5 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩
def pmZV : Fin 2 → Fin 12 := fun k => match k.val with | 0 => ⟨11, by omega⟩ | 1 => ⟨0, by omega⟩ | _ => ⟨0, by omega⟩
def pmEX : Fin 5 → Fin 12 := fun k => match k.val with | 0 => ⟨10, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨8, by omega⟩ | 3 => ⟨5, by omega⟩ | 4 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩

/-- The `pi` step of the definable interpretation (variables `0 ↦ v`,
`1 ↦ X`, `2 ↦ i = kpair c ρ`, `3 ↦ pt`): `v = piV a B` where
`a = app X (kpair (sfst (ssnd c)) ρ)` and `B x = app X (kpair (ssnd (ssnd c)) (consGraph x ρ))`,
via the propAllF/truthVal and piSetEqF readers. -/
def piStepF : Form 4 :=
  (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.and (Form.relabel pmC sfstEqF) (.and (Form.relabel pmR ssndEqF) (.and (Form.relabel pmP ssndEqF) (.and (Form.relabel pmA sfstEqF) (.and (Form.relabel pmB ssndEqF) (.and (Form.relabel pmK kpairEqF) (.and (Form.relabel pmV appEqF) (.or (.and (Form.relabel pmPA propAllF) (.all (.iff (Form.relabel pmZV (.mem ⟨0, by omega⟩ ⟨1, by omega⟩)) (.and (Form.relabel pmEX exAllF) (.equal ⟨11, by omega⟩ ⟨3, by omega⟩))))) (.and (.not (Form.relabel pmPA propAllF)) (Form.relabel pmGA piSetEqF)))))))))))))))))

theorem realize_piStepF {v X i : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ => v) X) i) (pt : W)) piStepF ↔
      v = piV (app X (kpair (sfst (ssnd (sfst i))) (ssnd i)))
        (fun x => app X (kpair (ssnd (ssnd (sfst i))) (consGraph x (ssnd i)))) := by
  have hC: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ pmC =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => c) i) (pt : W) : Fin 3 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hR: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ pmR =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => ρ) i) (pt : W) : Fin 3 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hP: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ pmP =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => p) c) (pt : W) : Fin 3 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hA: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ pmA =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => ac) p) (pt : W) : Fin 3 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hB: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ pmB =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => bc) p) (pt : W) : Fin 3 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ pmK =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => k) ac) ρ : Fin 3 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ pmV =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) a) X) k : Fin 4 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hPA: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ pmPA =
        ((Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) bc) ρ) (pt : W)) : Fin 5 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hGA: ∀ c ρ p ac bc k a : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) ∘ pmGA =
        ((Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) bc) ρ) (pt : W)) : Fin 6 → W) := by
    intro c ρ p ac bc k a; funext ⟨k, hk⟩
    have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hk6 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hZV: ∀ c ρ p ac bc k a z : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) z) ∘ pmZV =
        (Form.snoc (fun _ : Fin 1 => z) v : Fin 2 → W) := by
    intro c ρ p ac bc k a z; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hEX: ∀ c ρ p ac bc k a z : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ρ) p) ac) bc) k) a) z) ∘ pmEX =
        ((Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => a) X) bc) ρ) (pt : W)) : Fin 5 → W) := by
    intro c ρ p ac bc k a z; funext ⟨k, hk⟩
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [piStepF, Form.realize_ex, Form.realize_and, Form.realize_or,
    Form.realize_not, Form.realize_all, Form.realize_iff, Form.realize_equal,
    Form.realize_relabel, Form.realize_mem, Form.snoc_mk,
    hC, hR, hP, hA, hB, hK, hV, hPA, hGA, hZV, hEX,
    realize_sfstEqF, realize_ssndEqF, realize_kpairEqF, realize_appEqF,
    realize_propAllF, realize_piSetEqF, realize_exAllF]
  clear hC hR hP hA hB hK hV hPA hGA hZV hEX
  constructor
  · rintro ⟨c, ρ, p, ac, bc, k, a, hC, hR, hP, hA, hB, hK, hV, hD⟩
    rw [hV, hK, hB, hA, hP, hC, hR] at hD
    rcases hD with ⟨hprop, htv⟩ | ⟨hnprop, hpi⟩
    · have hv : v = truthVal (∀ x, x ∈ˢ app X (kpair (sfst (ssnd (sfst i))) (ssnd i)) →
          ∃ y, y ∈ˢ app X (kpair (ssnd (ssnd (sfst i))) (consGraph x (ssnd i)))) := by
        apply SetTheory.ext
        intro z
        rw [mem_truthVal]
        exact htv z
      rw [hv]
      unfold piV
      rw [propN_eq_zero.mpr hprop, piR_zero]
    · rw [hpi]
      unfold piV
      rw [piR_pos (fun h0 => hnprop (propN_eq_zero.mp h0))]
  · intro h
    have key : ∀ (a : W) (B : W → W), v = piV a B →
        ((∀ x, x ∈ˢ a → B x ∈ˢ (univZero : W)) ∧
          ∀ z, z ∈ˢ v ↔ ((∀ x, x ∈ˢ a → ∃ y, y ∈ˢ B x) ∧ z = pt)) ∨
        ((¬ ∀ x, x ∈ˢ a → B x ∈ˢ (univZero : W)) ∧ v = piSet a B) := by
      intro a B h
      unfold piV at h
      by_cases hc : ∀ x, x ∈ˢ a → B x ∈ˢ (univZero : W)
      · rw [propN_eq_zero.mpr hc, piR_zero] at h
        refine Or.inl ⟨hc, fun z => ?_⟩
        rw [h, mem_truthVal]
      · have hn : propN a B ≠ 0 := fun h0 => hc (propN_eq_zero.mp h0)
        rw [piR_pos hn] at h
        exact Or.inr ⟨hc, h⟩
    exact ⟨sfst i, ssnd i, ssnd (sfst i), sfst (ssnd (sfst i)), ssnd (ssnd (sfst i)),
      kpair (sfst (ssnd (sfst i))) (ssnd i),
      app X (kpair (sfst (ssnd (sfst i))) (ssnd i)),
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, key _ _ h⟩

/-- The `pi A b` code reads `piV` of the type's value and the fibre's
extended-environment function. -/
theorem realize_piStepF_tmCode {X ρ : W} (A b : ConLeche.Term.Term) :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (fun _ =>
        piV (app X (kpair (tmCode (W := W) A) ρ))
          (fun x => app X (kpair (tmCode (W := W) b) (consGraph x ρ)))) X)
        (kpair (tmCode (W := W) (ConLeche.Term.Term.pi A b)) ρ)) (pt : W))
      piStepF :=
  realize_piStepF.mpr (by simp only [tmCode, sfst_kpair, ssnd_kpair])


/-! ## Stage 52: the numeral reader `vnatEqF` -/

/-- Variable maps into the `vnatEqF` bound context `(x, pt, y)`. -/
def vnatEqLift : Fin 2 → Fin 3 := fun k => match k.val with | 0 => ⟨2, by omega⟩ | 1 => ⟨1, by omega⟩ | _ => ⟨1, by omega⟩
def vsuccSwap : Fin 2 → Fin 3 := fun k => match k.val with | 0 => ⟨2, by omega⟩ | 1 => ⟨0, by omega⟩ | _ => ⟨0, by omega⟩

/-- The numeral reader (variables `0 ↦ x`, `1 ↦ pt`): `x = vnat t`,
by recursion on `t` — `vnat 0 = empty` via `emptyF`,
`vnat (t+1) = vsucc (vnat t)` via `vsuccF`. -/
def vnatEqF : Nat → Form 2
  | 0 => Form.relabel (fun _ : Fin 1 => ⟨0, by omega⟩) emptyF
  | t + 1 => .ex (.and (Form.relabel vnatEqLift (vnatEqF t)) (Form.relabel vsuccSwap vsuccF))

theorem realize_vnatEqF (t : Nat) {x : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => x) (pt : W)) (vnatEqF t) ↔ x = (vnat t : W) := by
  induction t generalizing x with
  | zero =>
    have hm : (Form.snoc (fun _ : Fin 1 => x) (pt : W)) ∘ (fun _ : Fin 1 => ⟨0, by omega⟩) =
        Form.snoc Form.nil x := by
      funext ⟨k, hk⟩
      have hk0 : k = 0 := by omega
      subst hk0; rfl
    simp only [vnatEqF, Form.realize_relabel, hm, realize_emptyF_eq]
    exact Iff.rfl
  | succ t ih =>
    have hL : ∀ y : W,
        (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) y) ∘ vnatEqLift =
          (Form.snoc (fun _ : Fin 1 => y) (pt : W) : Fin 2 → W) := by
      intro y; funext ⟨k, hk⟩
      have hk2 : k = 0 ∨ k = 1 := by omega
      rcases hk2 with rfl | rfl <;> rfl
    have hS : ∀ y : W,
        (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) y) ∘ vsuccSwap =
          Form.cons2 y x Form.nil := by
      intro y; funext ⟨k, hk⟩
      have hk2 : k = 0 ∨ k = 1 := by omega
      rcases hk2 with rfl | rfl <;> rfl
    simp only [vnatEqF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
      hL, hS, ih, realize_vsuccF]
    rw [show (vnat (t + 1) : W) = vsucc (vnat t) from rfl]
    constructor
    · rintro ⟨y, hy, hx⟩
      rw [hy] at hx
      exact hx
    · intro h
      exact ⟨vnat t, rfl, h⟩


/-! ## Stage 53: the tmCode tag reader `vnatKpairEqF` -/

/-- Variable map for the `vnatEqF t` conjunct (its vars `0 ↦ x`, `1 ↦ pt`)
into the `vnatKpairEqF` bound context `(z, y, pt, x)`. -/
def vnatKpairVnatMap : Fin 2 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨2, by omega⟩ | _ => ⟨2, by omega⟩

/-- Variable map for the `kpairEqF` conjunct (its vars `0 ↦ z`, `1 ↦ x`, `2 ↦ y`)
into the `vnatKpairEqF` bound context `(z, y, pt, x)`. -/
def vnatKpairKpairMap : Fin 3 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨3, by omega⟩ | 2 => ⟨1, by omega⟩ | _ => ⟨1, by omega⟩

/-- The tmCode tag reader (variables `0 ↦ z`, `1 ↦ y`, `2 ↦ pt`): `z = kpair (vnat t) y`,
by an existentially bound `x` with `x = vnat t` (`vnatEqF t`) and `z = kpair x y` (`kpairEqF`). -/
def vnatKpairEqF (t : Nat) : Form 3 :=
  .ex (.and (Form.relabel vnatKpairVnatMap (vnatEqF t))
    (Form.relabel vnatKpairKpairMap kpairEqF))

theorem realize_vnatKpairEqF (t : Nat) {z y : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => z) y) (pt : W)) (vnatKpairEqF t) ↔
      z = kpair (vnat t : W) y := by
  have hA : ∀ x : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => z) y) (pt : W)) x) ∘ vnatKpairVnatMap =
        (Form.snoc (fun _ : Fin 1 => x) (pt : W) : Fin 2 → W) := by
    intro x; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hB : ∀ x : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => z) y) (pt : W)) x) ∘ vnatKpairKpairMap =
        Form.snoc (Form.snoc (fun _ : Fin 1 => z) x) y := by
    intro x; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [vnatKpairEqF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hA, hB, realize_vnatEqF, realize_kpairEqF]
  constructor
  · rintro ⟨x, hx, hz⟩
    rw [hx] at hz
    exact hz
  · intro h
    exact ⟨vnat t, rfl, h⟩


/-! ## Stage 54: the power-set reader `powerEqF` -/

/-- The power-set reader (variables `0 ↦ v`, `1 ↦ a`, `2 ↦ pt`):
`v = power a`, via extensionality + `mem_power` —
`∀ z, z ∈ˢ v ↔ (∀ w, w ∈ˢ z → w ∈ˢ a)`. -/
def powerEqF : Form 3 :=
  .all (.iff (.mem ⟨3, by omega⟩ ⟨0, by omega⟩)
    (.all (.imp (.mem ⟨4, by omega⟩ ⟨3, by omega⟩) (.mem ⟨4, by omega⟩ ⟨1, by omega⟩))))

theorem realize_powerEqF {v a : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) (pt : W)) powerEqF ↔
      v = power a := by
  simp only [powerEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_imp, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans mem_power.symm
  · intro h z
    rw [h]
    exact mem_power


/-! ## Stage 55: the truth-value-universe reader `univZeroEqF` -/

/-- The `univZero` reader (variables `0 ↦ v`, `1 ↦ pt`): `v = univZero`,
via extensionality — `univZero = power unitSet`, so
`∀ z, z ∈ˢ v ↔ (∀ w, w ∈ˢ z → w = pt)`. -/
def univZeroEqF : Form 2 :=
  .all (.iff (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
    (.all (.imp (.mem ⟨3, by omega⟩ ⟨2, by omega⟩) (.equal ⟨3, by omega⟩ ⟨1, by omega⟩))))

theorem realize_univZeroEqF {v : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => v) (pt : W)) univZeroEqF ↔
      v = (univZero : W) := by
  have key : ∀ z : W, z ∈ˢ (univZero : W) ↔ ∀ w, w ∈ˢ z → w = (pt : W) := by
    intro z
    rw [mem_univZero]
    exact ⟨fun hz w hw => mem_unitSet_iff.mp (hz w hw),
      fun hz w hw => mem_unitSet_iff.mpr (hz w hw)⟩
  simp only [univZeroEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_imp, Form.realize_equal, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (key z).symm
  · intro h z
    rw [h]
    exact key z


/-! ## Stage 56: the numeral-list-code reader `vnatListEqF` -/

/-- Map of the `vnatEqF n` conjunct (vars `0 ↦ a`, `1 ↦ pt`) into the
`vnatListEqF (n :: ns)` bound context `(x, pt, a)`. -/
def vnatListA : Fin 2 → Fin 3 :=
  fun k => match k.val with | 0 => ⟨2, by omega⟩ | 1 => ⟨1, by omega⟩ | _ => ⟨1, by omega⟩

/-- Map of the `kpairEqF` conjunct (vars `0 ↦ z`, `1 ↦ x'`, `2 ↦ y'`) into the
inner bound context `(x, pt, a, y)`. -/
def vnatListK : Fin 3 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of the `vnatListEqF ns` conjunct (vars `0 ↦ y`, `1 ↦ pt`) into the
inner bound context `(x, pt, a, y)`. -/
def vnatListR : Fin 2 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨1, by omega⟩ | _ => ⟨1, by omega⟩

/-- The numeral-list-code reader (variables `0 ↦ x`, `1 ↦ pt`): `x = vnatListCode ns`,
by recursion on `ns` — `vnatListCode [] = mkTower [] = empty` via `emptyF`;
`vnatListCode (n :: ns) = kpair (vnat n) (vnatListCode ns)` via
`vnatEqF n` + `kpairEqF` + the induction hypothesis. -/
def vnatListEqF : List Nat → Form 2
  | [] => Form.relabel (fun _ : Fin 1 => ⟨0, by omega⟩) emptyF
  | n :: ns => .ex (.and (Form.relabel vnatListA (vnatEqF n))
      (.ex (.and (Form.relabel vnatListK kpairEqF) (Form.relabel vnatListR (vnatListEqF ns)))))

theorem realize_vnatListEqF (ns : List Nat) {x : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => x) (pt : W)) (vnatListEqF ns) ↔
      x = (vnatListCode ns : W) := by
  induction ns generalizing x with
  | nil =>
    have hm : (Form.snoc (fun _ : Fin 1 => x) (pt : W)) ∘ (fun _ : Fin 1 => ⟨0, by omega⟩) =
        Form.snoc Form.nil x := by
      funext ⟨k, hk⟩
      have hk0 : k = 0 := by omega
      subst hk0; rfl
    simp only [vnatListEqF, Form.realize_relabel, hm, realize_emptyF_eq]
    exact Iff.rfl
  | cons n ns ih =>
    have hA : ∀ a : W,
        (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) a) ∘ vnatListA =
          (Form.snoc (fun _ : Fin 1 => a) (pt : W) : Fin 2 → W) := by
      intro a; funext ⟨k, hk⟩
      have hk2 : k = 0 ∨ k = 1 := by omega
      rcases hk2 with rfl | rfl <;> rfl
    have hK : ∀ a y : W,
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) a) y) ∘ vnatListK =
          Form.snoc (Form.snoc (fun _ : Fin 1 => x) a) y := by
      intro a y; funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    have hR : ∀ a y : W,
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) a) y) ∘ vnatListR =
          (Form.snoc (fun _ : Fin 1 => y) (pt : W) : Fin 2 → W) := by
      intro a y; funext ⟨k, hk⟩
      have hk2 : k = 0 ∨ k = 1 := by omega
      rcases hk2 with rfl | rfl <;> rfl
    simp only [vnatListEqF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
      hA, hK, hR, realize_vnatEqF, realize_kpairEqF, ih]
    rw [show (vnatListCode (n :: ns) : W) = kpair (vnat n : W) (vnatListCode ns) from by
      simp only [vnatListCode, List.map_cons, Tower.mkTower, spair]]
    constructor
    · rintro ⟨a, ha, y, hx, hy⟩
      rw [ha] at hx; rw [hy] at hx
      exact hx
    · intro h
      exact ⟨vnat n, rfl, vnatListCode ns, h, rfl⟩


/-! ## Stage 57: the built-in-constant code reader `bconstCodeEqF` -/

/-- Map of the tag's `vnatEqF t` conjunct (vars `0 ↦ a`, `1 ↦ pt`) into the
outer bound context `(x, pt, a)`. -/
def bcPairA : Fin 2 → Fin 3 :=
  fun k => match k.val with | 0 => ⟨2, by omega⟩ | 1 => ⟨1, by omega⟩ | _ => ⟨1, by omega⟩

/-- Map of the `kpairEqF` conjunct (vars `0 ↦ x`, `1 ↦ a`, `2 ↦ y`) into the
inner bound context `(x, pt, a, y)`. -/
def bcPairK : Fin 3 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of the `emptyF` payload conjunct (var `0 ↦ y`) into the inner bound
context `(x, pt, a, y)`. -/
def bcPairE : Fin 1 → Fin 4 := fun _ => ⟨3, by omega⟩

/-- Map of the `vnatEqF k` payload conjunct (vars `0 ↦ y`, `1 ↦ pt`) into the
inner bound context `(x, pt, a, y)`. -/
def bcPairV : Fin 2 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨3, by omega⟩ | 1 => ⟨1, by omega⟩ | _ => ⟨1, by omega⟩

/-- Reader (variables `0 ↦ x`, `1 ↦ pt`): `x = kpair (vnat t) empty`. -/
def vnatKpairEmptyF (t : Nat) : Form 2 :=
  .ex (.and (Form.relabel bcPairA (vnatEqF t))
    (.ex (.and (Form.relabel bcPairK kpairEqF) (Form.relabel bcPairE emptyF))))

/-- Reader (variables `0 ↦ x`, `1 ↦ pt`): `x = kpair (vnat t) (vnat k)`. -/
def vnatKpairVnatF (t k : Nat) : Form 2 :=
  .ex (.and (Form.relabel bcPairA (vnatEqF t))
    (.ex (.and (Form.relabel bcPairK kpairEqF) (Form.relabel bcPairV (vnatEqF k)))))

theorem realize_vnatKpairEmptyF (t : Nat) {x : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => x) (pt : W)) (vnatKpairEmptyF t) ↔
      x = kpair (vnat t : W) (empty : W) := by
  have hA : ∀ a : W,
      (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) a) ∘ bcPairA =
        (Form.snoc (fun _ : Fin 1 => a) (pt : W) : Fin 2 → W) := by
    intro a; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hK : ∀ a y : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) a) y) ∘ bcPairK =
        Form.snoc (Form.snoc (fun _ : Fin 1 => x) a) y := by
    intro a y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hE : ∀ a y : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) a) y) ∘ bcPairE =
        Form.snoc Form.nil y := by
    intro a y; funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  simp only [vnatKpairEmptyF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hA, hK, hE, realize_vnatEqF, realize_kpairEqF, realize_emptyF_eq]
  constructor
  · rintro ⟨a, ha, y, hx, hy⟩
    rw [ha] at hx; rw [hy] at hx
    exact hx
  · intro h
    exact ⟨vnat t, rfl, empty, h, rfl⟩

theorem realize_vnatKpairVnatF (t k : Nat) {x : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => x) (pt : W)) (vnatKpairVnatF t k) ↔
      x = kpair (vnat t : W) (vnat k : W) := by
  have hA : ∀ a : W,
      (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) a) ∘ bcPairA =
        (Form.snoc (fun _ : Fin 1 => a) (pt : W) : Fin 2 → W) := by
    intro a; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hK : ∀ a y : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) a) y) ∘ bcPairK =
        Form.snoc (Form.snoc (fun _ : Fin 1 => x) a) y := by
    intro a y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV : ∀ a y : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) a) y) ∘ bcPairV =
        (Form.snoc (fun _ : Fin 1 => y) (pt : W) : Fin 2 → W) := by
    intro a y; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [vnatKpairVnatF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hA, hK, hV, realize_vnatEqF, realize_kpairEqF]
  constructor
  · rintro ⟨a, ha, y, hx, hy⟩
    rw [ha] at hx; rw [hy] at hx
    exact hx
  · intro h
    exact ⟨vnat t, rfl, vnat k, h, rfl⟩

/-- The built-in-constant code reader (variables `0 ↦ x`, `1 ↦ pt`):
`x = bconstCode c`, by cases on the constructor. -/
def bconstCodeEqF : Term.BConst → Form 2
  | .nat => vnatKpairEmptyF 0
  | .natZero => vnatKpairEmptyF 1
  | .natSucc => vnatKpairEmptyF 2
  | .natRec => vnatKpairEmptyF 3
  | .punit => vnatKpairEmptyF 4
  | .punitUnit => vnatKpairEmptyF 5
  | .psigma => vnatKpairEmptyF 6
  | .psigmaMk => vnatKpairEmptyF 7
  | .empty => vnatKpairEmptyF 8
  | .emptyRec => vnatKpairEmptyF 9
  | .quot => vnatKpairEmptyF 10
  | .quotMk => vnatKpairEmptyF 11
  | .quotLift => vnatKpairEmptyF 12
  | .quotInd => vnatKpairEmptyF 13
  | .quotSound => vnatKpairEmptyF 14
  | .propext => vnatKpairEmptyF 15
  | .choice => vnatKpairEmptyF 16
  | .lfpFam => vnatKpairEmptyF 17
  | .lfpTuple k => vnatKpairVnatF 18 k

theorem realize_bconstCodeEqF (c : Term.BConst) {x : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => x) (pt : W)) (bconstCodeEqF c) ↔
      x = (bconstCode c : W) := by
  cases c <;> simp only [bconstCodeEqF, bconstCode]
  <;> first
    | exact realize_vnatKpairEmptyF _
    | exact realize_vnatKpairVnatF _ _


/-! ## Stage 58: the `const` tmCode reader `constCodeF` -/

/-- The payload reader (variables `0 ↦ y`, `1 ↦ pt`):
`y = kpair (bconstCode c) (vnatListCode us)`, via `bconstCodeEqF c`,
`kpairEqF` and `vnatListEqF us`. -/
def constPayloadF (c : Term.BConst) (us : List Nat) : Form 2 :=
  .ex (.and (Form.relabel bcPairA (bconstCodeEqF c))
    (.ex (.and (Form.relabel bcPairK kpairEqF) (Form.relabel bcPairV (vnatListEqF us)))))

theorem realize_constPayloadF (c : Term.BConst) (us : List Nat) {y : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => y) (pt : W)) (constPayloadF c us) ↔
      y = kpair (bconstCode c : W) (vnatListCode us : W) := by
  have hA : ∀ a : W,
      (Form.snoc (Form.snoc (fun _ : Fin 1 => y) (pt : W)) a) ∘ bcPairA =
        (Form.snoc (fun _ : Fin 1 => a) (pt : W) : Fin 2 → W) := by
    intro a; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hK : ∀ a b : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => y) (pt : W)) a) b) ∘ bcPairK =
        Form.snoc (Form.snoc (fun _ : Fin 1 => y) a) b := by
    intro a b; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV : ∀ a b : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => y) (pt : W)) a) b) ∘ bcPairV =
        (Form.snoc (fun _ : Fin 1 => b) (pt : W) : Fin 2 → W) := by
    intro a b; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [constPayloadF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hA, hK, hV, realize_bconstCodeEqF, realize_kpairEqF, realize_vnatListEqF]
  constructor
  · rintro ⟨a, ha, b, hy', hb⟩
    rw [ha] at hy'; rw [hb] at hy'
    exact hy'
  · intro h
    exact ⟨bconstCode c, rfl, vnatListCode us, h, rfl⟩

/-- The `const` tmCode reader (variables `0 ↦ i`, `1 ↦ pt`):
`i = tmCode (.const c us)`, i.e.
`i = kpair (vnat 2) (kpair (bconstCode c) (vnatListCode us))`. -/
def constCodeF (c : Term.BConst) (us : List Nat) : Form 2 :=
  .ex (.and (Form.relabel bcPairA (vnatEqF 2))
    (.ex (.and (Form.relabel bcPairK kpairEqF) (Form.relabel bcPairV (constPayloadF c us)))))

theorem realize_constCodeF (c : Term.BConst) (us : List Nat) {i : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => i) (pt : W)) (constCodeF c us) ↔
      i = (tmCode (Term.Term.const c us) : W) := by
  have hA : ∀ a : W,
      (Form.snoc (Form.snoc (fun _ : Fin 1 => i) (pt : W)) a) ∘ bcPairA =
        (Form.snoc (fun _ : Fin 1 => a) (pt : W) : Fin 2 → W) := by
    intro a; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hK : ∀ a b : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => i) (pt : W)) a) b) ∘ bcPairK =
        Form.snoc (Form.snoc (fun _ : Fin 1 => i) a) b := by
    intro a b; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV : ∀ a b : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => i) (pt : W)) a) b) ∘ bcPairV =
        (Form.snoc (fun _ : Fin 1 => b) (pt : W) : Fin 2 → W) := by
    intro a b; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [constCodeF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hA, hK, hV, realize_vnatEqF, realize_kpairEqF, realize_constPayloadF]
  rw [show (tmCode (Term.Term.const c us) : W) =
      kpair (vnat 2 : W) (kpair (bconstCode c : W) (vnatListCode us : W)) from rfl]
  constructor
  · rintro ⟨a, ha, b, hi, hb⟩
    rw [ha] at hi; rw [hb] at hi
    exact hi
  · intro h
    exact ⟨vnat 2, rfl, kpair (bconstCode c : W) (vnatListCode us : W), h, rfl⟩


/-! ## Stage 59: generic coded-payload readers `vnatKpairPF` / `kpairCodeF` -/

/-- Generic single-payload code reader (variables `0 ↦ x`, `1 ↦ pt`):
`∃ r, x = kpair (vnat t) r ∧ P r`, where `pf` realizes `P` on `r`. -/
def vnatKpairPF (t : Nat) (pf : Form 2) : Form 2 :=
  .ex (.and (Form.relabel bcPairA (vnatEqF t))
    (.ex (.and (Form.relabel bcPairK kpairEqF) (Form.relabel bcPairV pf))))

theorem realize_vnatKpairPF (t : Nat) {pf : Form 2} {P : W → Prop}
    (hpf : ∀ p, Form.Realize Mem (Form.snoc (fun _ : Fin 1 => p) (pt : W)) pf ↔ P p) {x : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => x) (pt : W)) (vnatKpairPF t pf) ↔
      ∃ r, x = kpair (vnat t : W) r ∧ P r := by
  have hA : ∀ a : W,
      (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) a) ∘ bcPairA =
        (Form.snoc (fun _ : Fin 1 => a) (pt : W) : Fin 2 → W) := by
    intro a; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hK : ∀ a r : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) a) r) ∘ bcPairK =
        Form.snoc (Form.snoc (fun _ : Fin 1 => x) a) r := by
    intro a r; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV : ∀ a r : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) a) r) ∘ bcPairV =
        (Form.snoc (fun _ : Fin 1 => r) (pt : W) : Fin 2 → W) := by
    intro a r; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [vnatKpairPF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hA, hK, hV, realize_vnatEqF, realize_kpairEqF, hpf]
  constructor
  · rintro ⟨a, ha, r, hx, hr⟩
    rw [ha] at hx
    exact ⟨r, hx, hr⟩
  · rintro ⟨r, hx, hr⟩
    exact ⟨vnat t, rfl, r, hx, hr⟩

/-- Generic pair-payload code reader (variables `0 ↦ r`, `1 ↦ pt`):
`∃ p q, r = kpair p q ∧ P p ∧ Q q`, where `pf`/`qf` realize `P`/`Q`. -/
def kpairCodeF (pf qf : Form 2) : Form 2 :=
  .ex (.and (Form.relabel bcPairA pf)
    (.ex (.and (Form.relabel bcPairK kpairEqF) (Form.relabel bcPairV qf))))

theorem realize_kpairCodeF {pf qf : Form 2} {P Q : W → Prop}
    (hpf : ∀ p, Form.Realize Mem (Form.snoc (fun _ : Fin 1 => p) (pt : W)) pf ↔ P p)
    (hqf : ∀ q, Form.Realize Mem (Form.snoc (fun _ : Fin 1 => q) (pt : W)) qf ↔ Q q) {r : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => r) (pt : W)) (kpairCodeF pf qf) ↔
      ∃ p q, r = kpair p q ∧ P p ∧ Q q := by
  have hA : ∀ p : W,
      (Form.snoc (Form.snoc (fun _ : Fin 1 => r) (pt : W)) p) ∘ bcPairA =
        (Form.snoc (fun _ : Fin 1 => p) (pt : W) : Fin 2 → W) := by
    intro p; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hK : ∀ p q : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => r) (pt : W)) p) q) ∘ bcPairK =
        Form.snoc (Form.snoc (fun _ : Fin 1 => r) p) q := by
    intro p q; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV : ∀ p q : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => r) (pt : W)) p) q) ∘ bcPairV =
        (Form.snoc (fun _ : Fin 1 => q) (pt : W) : Fin 2 → W) := by
    intro p q; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [kpairCodeF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hA, hK, hV, realize_kpairEqF, hpf, hqf]
  constructor
  · rintro ⟨p, hp, q, hr, hq⟩
    exact ⟨p, q, hr, hp, hq⟩
  · rintro ⟨p, q, hr, hp, hq⟩
    exact ⟨p, hp, q, hr, hq⟩


/-! ## Stage 60: the recursive tmCode reader `tmCodeEqF` -/

/-- The tmCode reader (variables `0 ↦ x`, `1 ↦ pt`): `x = tmCode t`,
by recursion on the term — each constructor is a numeral tag
(`vnatEqF`) over a coded payload (`kpairEqF`, `vnatEqF`,
`bconstCodeEqF`/`vnatListEqF`, or the recursive `tmCodeEqF`). -/
def tmCodeEqF : Term.Term → Form 2
  | .bvar i => vnatKpairVnatF 0 i
  | .sort u => vnatKpairVnatF 1 u
  | .const c us => constCodeF c us
  | .app f a => vnatKpairPF 3 (kpairCodeF (tmCodeEqF f) (tmCodeEqF a))
  | .lam ty body => vnatKpairPF 4 (kpairCodeF (tmCodeEqF ty) (tmCodeEqF body))
  | .pi ty body => vnatKpairPF 5 (kpairCodeF (tmCodeEqF ty) (tmCodeEqF body))
  | .letE val body => vnatKpairPF 6 (kpairCodeF (tmCodeEqF val) (tmCodeEqF body))
  | .eqE lhs rhs => vnatKpairPF 7 (kpairCodeF (tmCodeEqF lhs) (tmCodeEqF rhs))
  | .fst e => vnatKpairPF 8 (tmCodeEqF e)
  | .snd e => vnatKpairPF 9 (tmCodeEqF e)
  | .prf => vnatKpairEmptyF 10

theorem realize_tmCodeEqF (t : Term.Term) {x : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => x) (pt : W)) (tmCodeEqF t) ↔
      x = (tmCode t : W) := by
  induction t generalizing x with
  | bvar i => exact realize_vnatKpairVnatF 0 i
  | sort u => exact realize_vnatKpairVnatF 1 u
  | const c us => exact realize_constCodeF c us
  | prf => exact realize_vnatKpairEmptyF 10
  | app f a ihf iha =>
    have h := realize_vnatKpairPF 3 (pf := kpairCodeF (tmCodeEqF f) (tmCodeEqF a))
      (P := fun r => ∃ p q, r = kpair p q ∧ p = (tmCode f : W) ∧ q = (tmCode a : W))
      (fun r => realize_kpairCodeF (fun p => ihf (x := p)) (fun q => iha (x := q)) (r := r)) (x := x)
    rw [show (tmCode (Term.Term.app f a) : W) =
        kpair (vnat 3 : W) (kpair (tmCode f : W) (tmCode a : W)) from rfl]
    exact h.trans ⟨fun ⟨r, hx, p, q, hr, hp, hq⟩ => by
        rw [hr] at hx; rw [hp, hq] at hx; exact hx,
      fun h => ⟨kpair (tmCode f : W) (tmCode a : W), h, tmCode f, tmCode a, rfl, rfl, rfl⟩⟩
  | lam ty body iht ihb =>
    have h := realize_vnatKpairPF 4 (pf := kpairCodeF (tmCodeEqF ty) (tmCodeEqF body))
      (P := fun r => ∃ p q, r = kpair p q ∧ p = (tmCode ty : W) ∧ q = (tmCode body : W))
      (fun r => realize_kpairCodeF (fun p => iht (x := p)) (fun q => ihb (x := q)) (r := r)) (x := x)
    rw [show (tmCode (Term.Term.lam ty body) : W) =
        kpair (vnat 4 : W) (kpair (tmCode ty : W) (tmCode body : W)) from rfl]
    exact h.trans ⟨fun ⟨r, hx, p, q, hr, hp, hq⟩ => by
        rw [hr] at hx; rw [hp, hq] at hx; exact hx,
      fun h => ⟨kpair (tmCode ty : W) (tmCode body : W), h, tmCode ty, tmCode body, rfl, rfl, rfl⟩⟩
  | pi ty body iht ihb =>
    have h := realize_vnatKpairPF 5 (pf := kpairCodeF (tmCodeEqF ty) (tmCodeEqF body))
      (P := fun r => ∃ p q, r = kpair p q ∧ p = (tmCode ty : W) ∧ q = (tmCode body : W))
      (fun r => realize_kpairCodeF (fun p => iht (x := p)) (fun q => ihb (x := q)) (r := r)) (x := x)
    rw [show (tmCode (Term.Term.pi ty body) : W) =
        kpair (vnat 5 : W) (kpair (tmCode ty : W) (tmCode body : W)) from rfl]
    exact h.trans ⟨fun ⟨r, hx, p, q, hr, hp, hq⟩ => by
        rw [hr] at hx; rw [hp, hq] at hx; exact hx,
      fun h => ⟨kpair (tmCode ty : W) (tmCode body : W), h, tmCode ty, tmCode body, rfl, rfl, rfl⟩⟩
  | letE val body ihv ihb =>
    have h := realize_vnatKpairPF 6 (pf := kpairCodeF (tmCodeEqF val) (tmCodeEqF body))
      (P := fun r => ∃ p q, r = kpair p q ∧ p = (tmCode val : W) ∧ q = (tmCode body : W))
      (fun r => realize_kpairCodeF (fun p => ihv (x := p)) (fun q => ihb (x := q)) (r := r)) (x := x)
    rw [show (tmCode (Term.Term.letE val body) : W) =
        kpair (vnat 6 : W) (kpair (tmCode val : W) (tmCode body : W)) from rfl]
    exact h.trans ⟨fun ⟨r, hx, p, q, hr, hp, hq⟩ => by
        rw [hr] at hx; rw [hp, hq] at hx; exact hx,
      fun h => ⟨kpair (tmCode val : W) (tmCode body : W), h, tmCode val, tmCode body, rfl, rfl, rfl⟩⟩
  | eqE lhs rhs ihl ihr =>
    have h := realize_vnatKpairPF 7 (pf := kpairCodeF (tmCodeEqF lhs) (tmCodeEqF rhs))
      (P := fun r => ∃ p q, r = kpair p q ∧ p = (tmCode lhs : W) ∧ q = (tmCode rhs : W))
      (fun r => realize_kpairCodeF (fun p => ihl (x := p)) (fun q => ihr (x := q)) (r := r)) (x := x)
    rw [show (tmCode (Term.Term.eqE lhs rhs) : W) =
        kpair (vnat 7 : W) (kpair (tmCode lhs : W) (tmCode rhs : W)) from rfl]
    exact h.trans ⟨fun ⟨r, hx, p, q, hr, hp, hq⟩ => by
        rw [hr] at hx; rw [hp, hq] at hx; exact hx,
      fun h => ⟨kpair (tmCode lhs : W) (tmCode rhs : W), h, tmCode lhs, tmCode rhs, rfl, rfl, rfl⟩⟩
  | fst e ihe =>
    have h := realize_vnatKpairPF 8 (pf := tmCodeEqF e) (P := fun r => r = (tmCode e : W))
      (fun r => ihe (x := r)) (x := x)
    rw [show (tmCode (Term.Term.fst e) : W) = kpair (vnat 8 : W) (tmCode e) from rfl]
    exact h.trans ⟨fun ⟨r, hx, hr⟩ => by rw [hr] at hx; exact hx,
      fun h => ⟨tmCode e, h, rfl⟩⟩
  | snd e ihe =>
    have h := realize_vnatKpairPF 9 (pf := tmCodeEqF e) (P := fun r => r = (tmCode e : W))
      (fun r => ihe (x := r)) (x := x)
    rw [show (tmCode (Term.Term.snd e) : W) = kpair (vnat 9 : W) (tmCode e) from rfl]
    exact h.trans ⟨fun ⟨r, hx, hr⟩ => by rw [hr] at hx; exact hx,
      fun h => ⟨tmCode e, h, rfl⟩⟩


/-! ## Stage 61: the tmCode tag dispatch `tagDispatchF` -/

/-- Map of a tag disjunct's `vnatKpairEqF t` (vars `0 ↦ z`, `1 ↦ y`, `2 ↦ pt`)
into the dispatch bound context `(v, X, i, pt, y)`: `z ↦ i`, `y ↦ y`, `pt ↦ pt`. -/
def tagDispatchMap : Fin 3 → Fin 5 :=
  fun k => match k.val with
    | 0 => ⟨2, by omega⟩ | 1 => ⟨4, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩

/-- The `t`-th tag disjunct (variables `0 ↦ v`, `1 ↦ X`, `2 ↦ i`, `3 ↦ pt`):
`∃ y, i = kpair (vnat t) y`. -/
def tagDisjF (t : Nat) : Form 4 := .ex (Form.relabel tagDispatchMap (vnatKpairEqF t))

/-- The tmCode tag dispatch (variables `0 ↦ v`, `1 ↦ X`, `2 ↦ i`, `3 ↦ pt`):
the disjunction over the 11 constructor tags `0..10` of `∃ y, i = kpair (vnat t) y`. -/
def tagDispatchF : Form 4 :=
  .or (tagDisjF 0) (.or (tagDisjF 1) (.or (tagDisjF 2) (.or (tagDisjF 3) (.or (tagDisjF 4)
    (.or (tagDisjF 5) (.or (tagDisjF 6) (.or (tagDisjF 7) (.or (tagDisjF 8)
      (.or (tagDisjF 9) (tagDisjF 10))))))))))

theorem realize_tagDispatchF {v X i : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W))
        tagDispatchF ↔
      ∃ t : Nat, t < 11 ∧ ∃ y, i = kpair (vnat t : W) y := by
  have hM : ∀ y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) y) ∘
          tagDispatchMap =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => i) y) (pt : W) : Fin 3 → W) := by
    intro y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [tagDispatchF, tagDisjF, Form.realize_or, Form.realize_ex, Form.realize_relabel,
    hM, realize_vnatKpairEqF]
  constructor
  · intro h
    rcases h with ⟨y, h⟩ | ⟨y, h⟩ | ⟨y, h⟩ | ⟨y, h⟩ | ⟨y, h⟩ | ⟨y, h⟩ | ⟨y, h⟩ | ⟨y, h⟩
      | ⟨y, h⟩ | ⟨y, h⟩ | ⟨y, h⟩
    · exact ⟨0, by omega, y, h⟩
    · exact ⟨1, by omega, y, h⟩
    · exact ⟨2, by omega, y, h⟩
    · exact ⟨3, by omega, y, h⟩
    · exact ⟨4, by omega, y, h⟩
    · exact ⟨5, by omega, y, h⟩
    · exact ⟨6, by omega, y, h⟩
    · exact ⟨7, by omega, y, h⟩
    · exact ⟨8, by omega, y, h⟩
    · exact ⟨9, by omega, y, h⟩
    · exact ⟨10, by omega, y, h⟩
  · rintro ⟨t, ht, y, h⟩
    have h_cases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 := by omega
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨y, h⟩
    · exact Or.inr (Or.inl ⟨y, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨y, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨y, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y, h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y, h⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y, h⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y, h⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y, h⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y, h⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨y, h⟩)))))))))


/-! ## Stage 62: the combined definable interp step `interpStepF` -/

/-- The combined definable interp step (variables `0 ↦ v`, `1 ↦ X`, `2 ↦ i`,
`3 ↦ pt`): the disjunction over the nine covered constructor tags
(`bvar 0`, `app 3`, `lam 4`, `pi 5`, `letE 6`, `eqE 7`, `fst 8`, `snd 9`,
`prf 10`), each guarded by its `tagDisjF t` and paired with the case's
step reader.  The `sort 1` and `const 2` cases are not yet covered
(`sort` needs a `univ` reader — the `univChain` primitive; `const` needs
a `bval` reader). -/
def interpStepF : Form 4 :=
  .or (.and (tagDisjF 0) bvarStepF)
  (.or (.and (tagDisjF 3) appStepF)
  (.or (.and (tagDisjF 4) lamStepF)
  (.or (.and (tagDisjF 5) piStepF)
  (.or (.and (tagDisjF 6) letEStepF)
  (.or (.and (tagDisjF 7) eqEStepF)
  (.or (.and (tagDisjF 8) fstStepF)
  (.or (.and (tagDisjF 9) sndStepF)
        (.and (tagDisjF 10) prfStepF))))))))

theorem realize_interpStepF {v X i : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W))
        interpStepF ↔
      ((∃ y, i = kpair (vnat 0 : W) y) ∧ v = app X (ssnd i)) ∨
      ((∃ y, i = kpair (vnat 3 : W) y) ∧
        v = app (app X (kpair (sfst (ssnd (sfst i))) (ssnd i)))
          (app X (kpair (ssnd (ssnd (sfst i))) (ssnd i)))) ∨
      ((∃ y, i = kpair (vnat 4 : W) y) ∧
        v = lamV (app X (kpair (sfst (ssnd (sfst i))) (ssnd i)))
          (fun x => app X (kpair (ssnd (ssnd (sfst i))) (consGraph x (ssnd i))))) ∨
      ((∃ y, i = kpair (vnat 5 : W) y) ∧
        v = piV (app X (kpair (sfst (ssnd (sfst i))) (ssnd i)))
          (fun x => app X (kpair (ssnd (ssnd (sfst i))) (consGraph x (ssnd i))))) ∨
      ((∃ y, i = kpair (vnat 6 : W) y) ∧
        v = app X (kpair (ssnd (ssnd (sfst i)))
          (consGraph (app X (kpair (sfst (ssnd (sfst i))) (ssnd i))) (ssnd i)))) ∨
      ((∃ y, i = kpair (vnat 7 : W) y) ∧
        v = eqv (app X (kpair (sfst (ssnd (sfst i))) (ssnd i)))
          (app X (kpair (ssnd (ssnd (sfst i))) (ssnd i)))) ∨
      ((∃ y, i = kpair (vnat 8 : W) y) ∧ v = sfst (app X (kpair (ssnd (sfst i)) (ssnd i)))) ∨
      ((∃ y, i = kpair (vnat 9 : W) y) ∧ v = ssnd (app X (kpair (ssnd (sfst i)) (ssnd i)))) ∨
      ((∃ y, i = kpair (vnat 10 : W) y) ∧ v = pt) := by
  have hM : ∀ y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) y) ∘
          tagDispatchMap =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => i) y) (pt : W) : Fin 3 → W) := by
    intro y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [interpStepF, tagDisjF, Form.realize_or, Form.realize_and, Form.realize_ex,
    Form.realize_relabel, hM, realize_vnatKpairEqF, realize_bvarStepF, realize_appStepF,
    realize_lamStepF, realize_piStepF, realize_letEStepF, realize_eqEStepF, realize_fstStepF,
    realize_sndStepF, realize_prfStepF]


/-! ## Stage 63: the unordered-pair reader `upairEqF` -/

/-- The unordered-pair reader (variables `0 ↦ v`, `1 ↦ a`, `2 ↦ b`):
`v = upair a b`, via extensionality + `mem_upair` —
`∀ z, z ∈ v ↔ (z = a ∨ z = b)`. -/
def upairEqF : Form 3 :=
  .all (.iff (.mem ⟨3, by omega⟩ ⟨0, by omega⟩)
    (.or (.equal ⟨3, by omega⟩ ⟨1, by omega⟩) (.equal ⟨3, by omega⟩ ⟨2, by omega⟩)))

theorem realize_upairEqF {v a b : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) b) upairEqF ↔
      v = upair a b := by
  simp only [upairEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_or, Form.realize_equal, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans mem_upair.symm
  · intro h z
    rw [h]
    exact mem_upair


/-! ## Stage 64: the singleton readers `singEqF` / `singEmptyF` -/

/-- The singleton reader (variables `0 ↦ v`, `1 ↦ a`): `v = sing a`,
via extensionality + `mem_sing` — `∀ z, z ∈ v ↔ z = a`. -/
def singEqF : Form 2 :=
  .all (.iff (.mem ⟨2, by omega⟩ ⟨0, by omega⟩) (.equal ⟨2, by omega⟩ ⟨1, by omega⟩))

theorem realize_singEqF {v a : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => v) a) singEqF ↔ v = sing a := by
  simp only [singEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_equal, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans mem_sing.symm
  · intro h z
    rw [h]
    exact mem_sing

/-- The `sing empty` reader (variable `0 ↦ v`): `v = sing empty`,
via extensionality — `∀ z, z ∈ v ↔ z = empty` (`emptyF` at `z`). -/
def singEmptyF : Form 1 :=
  .all (.iff (.mem ⟨1, by omega⟩ ⟨0, by omega⟩)
    (Form.relabel (fun _ : Fin 1 => ⟨1, by omega⟩) emptyF))

theorem realize_singEmptyF {v : W} :
    Form.Realize Mem (Form.snoc Form.nil v) singEmptyF ↔ v = sing (empty : W) := by
  have hm : ∀ z : W, (Form.snoc (Form.snoc Form.nil v) z) ∘ (fun _ : Fin 1 => ⟨1, by omega⟩) =
      Form.snoc Form.nil z := by
    intro z; funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  simp only [singEmptyF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_relabel, hm, realize_emptyF_eq, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans mem_sing.symm
  · intro h z
    rw [h]
    exact mem_sing



/-! ## Stage 65: the `sing (sing empty)` and `ptTag` readers -/

/-- Map of the `singEmptyF` conjunct (var `0 ↦ a`) into the bound context `(v, a)`. -/
def singSingA : Fin 1 → Fin 2 := fun _ => ⟨1, by omega⟩

/-- Map of the `singEqF` conjunct (vars `0 ↦ v`, `1 ↦ a`) into the bound context `(v, a)`. -/
def singSingS : Fin 2 → Fin 2 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | _ => ⟨1, by omega⟩

/-- The `sing (sing empty)` reader (variable `0 ↦ v`): `v = sing (sing empty)`,
via an existential `a = sing empty` with `v = sing a`. -/
def singSingEmptyF : Form 1 :=
  .ex (.and (Form.relabel singSingA singEmptyF) (Form.relabel singSingS singEqF))

theorem realize_singSingEmptyF {v : W} :
    Form.Realize Mem (Form.snoc Form.nil v) singSingEmptyF ↔ v = sing (sing (empty : W)) := by
  have hA : ∀ a : W, (Form.snoc (Form.snoc Form.nil v) a) ∘ singSingA = Form.snoc Form.nil a := by
    intro a; funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  have hS : ∀ a : W, (Form.snoc (Form.snoc Form.nil v) a) ∘ singSingS =
      (Form.snoc (fun _ : Fin 1 => v) a : Fin 2 → W) := by
    intro a; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [singSingEmptyF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hA, hS, realize_singEmptyF, realize_singEqF]
  constructor
  · rintro ⟨a, ha, hv⟩
    rw [ha] at hv
    exact hv
  · intro h
    exact ⟨sing (empty : W), rfl, h⟩

/-- Map of the `emptyF` conjunct (var `0 ↦ a`) into the bound context `(v, pt, a)`. -/
def ptTagA : Fin 1 → Fin 3 := fun _ => ⟨2, by omega⟩

/-- Map of the `singSingEmptyF` conjunct (var `0 ↦ b`) into the bound context `(v, pt, a, b)`. -/
def ptTagB : Fin 1 → Fin 4 := fun _ => ⟨3, by omega⟩

/-- Map of the `upairEqF` conjunct (vars `0 ↦ v`, `1 ↦ a`, `2 ↦ b`) into the
bound context `(v, pt, a, b)`. -/
def ptTagU : Fin 3 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨2, by omega⟩ | _ => ⟨3, by omega⟩

/-- The proof-tag reader (variables `0 ↦ v`, `1 ↦ pt`): `v = ptTag`,
i.e. `v = upair empty (sing (sing empty))`, via `emptyF` at the first
component, `singSingEmptyF` at the second, and `upairEqF`. -/
def ptTagEqF : Form 2 :=
  .ex (.and (Form.relabel ptTagA emptyF)
    (.ex (.and (Form.relabel ptTagB singSingEmptyF) (Form.relabel ptTagU upairEqF))))

theorem realize_ptTagEqF {v : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => v) (pt : W)) ptTagEqF ↔
      v = (ptTag : W) := by
  have hA : ∀ a : W,
      (Form.snoc (Form.snoc (fun _ : Fin 1 => v) (pt : W)) a) ∘ ptTagA =
        Form.snoc Form.nil a := by
    intro a; funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  have hB : ∀ a b : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) (pt : W)) a) b) ∘ ptTagB =
        Form.snoc Form.nil b := by
    intro a b; funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  have hU : ∀ a b : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) (pt : W)) a) b) ∘ ptTagU =
        Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) b := by
    intro a b; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [ptTagEqF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hA, hB, hU, realize_emptyF_eq, realize_singSingEmptyF, realize_upairEqF]
  rw [show (ptTag : W) = upair (empty : W) (sing (sing empty)) from by unfold ptTag; rfl]
  constructor
  · rintro ⟨a, ha, b, hb, hv⟩
    rw [ha, hb] at hv
    exact hv
  · intro h
    exact ⟨empty, rfl, sing (sing empty), rfl, h⟩


/-! ## Stage 66: the proof-point reader `ptEqF` -/

/-- Map of the `ptTagEqF` conjunct (vars `0 ↦ t`, `1 ↦ pt`) into the bound context `(v, pt, t)`. -/
def ptTagInto : Fin 2 → Fin 3 :=
  fun k => match k.val with | 0 => ⟨2, by omega⟩ | _ => ⟨1, by omega⟩

/-- Map of the `singEqF` conjunct (vars `0 ↦ v`, `1 ↦ t`) into the bound context `(v, pt, t)`. -/
def ptSingS : Fin 2 → Fin 3 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | _ => ⟨2, by omega⟩

/-- The proof-point reader (variables `0 ↦ v`, `1 ↦ pt`): `v = pt`,
i.e. `v = sing ptTag`, via an existential `t = ptTag` with `v = sing t`. -/
def ptEqF : Form 2 :=
  .ex (.and (Form.relabel ptTagInto ptTagEqF) (Form.relabel ptSingS singEqF))

theorem realize_ptEqF {v : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => v) (pt : W)) ptEqF ↔ v = (pt : W) := by
  have hT : ∀ t : W,
      (Form.snoc (Form.snoc (fun _ : Fin 1 => v) (pt : W)) t) ∘ ptTagInto =
        (Form.snoc (fun _ : Fin 1 => t) (pt : W) : Fin 2 → W) := by
    intro t; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hS : ∀ t : W,
      (Form.snoc (Form.snoc (fun _ : Fin 1 => v) (pt : W)) t) ∘ ptSingS =
        (Form.snoc (fun _ : Fin 1 => v) t : Fin 2 → W) := by
    intro t; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [ptEqF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
    hT, hS, realize_ptTagEqF, realize_singEqF]
  rw [show (pt : W) = sing (ptTag : W) from by unfold pt; rfl]
  constructor
  · rintro ⟨t, ht, hv⟩
    rw [ht] at hv
    exact hv
  · intro h
    exact ⟨ptTag, rfl, h⟩


/-! ## Stage 67: the `unitSetAt`-of-a-numeral reader `unitSetAtVnatF` -/

/-- Map of the `emptyF` conjunct (var `0 ↦ w`) into the context `(v, w, pt)`. -/
def usatE : Fin 1 → Fin 3 := fun _ => ⟨1, by omega⟩

/-- Map of the `unitSetF` conjunct (vars `0 ↦ v`, `1 ↦ pt`) into the context `(v, w, pt)`. -/
def usatU : Fin 2 → Fin 3 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | _ => ⟨2, by omega⟩

/-- Map of the `singEmptyF` conjunct (var `0 ↦ v`) into the context `(v, w, pt)`. -/
def usatS : Fin 1 → Fin 3 := fun _ => ⟨0, by omega⟩

/-- The `unitSetAt`-of-a-numeral reader (variables `0 ↦ v`, `1 ↦ w`, `2 ↦ pt`):
`(w = empty ∧ v = sing pt) ∨ (w ≠ empty ∧ v = sing empty)` — the two cases of
`unitSetAt k = if k = 0 then unitSet else sing empty` at the numeral `w = vnat k`
(`unitSet = sing pt`). -/
def unitSetAtVnatF : Form 3 :=
  .or (.and (Form.relabel usatE emptyF) (Form.relabel usatU unitSetF))
    (.and (.not (Form.relabel usatE emptyF)) (Form.relabel usatS singEmptyF))

theorem realize_unitSetAtVnatF {v w : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W)) unitSetAtVnatF ↔
      (w = (empty : W) ∧ v = sing (pt : W)) ∨ (¬ w = (empty : W) ∧ v = sing (empty : W)) := by
  have hE : (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W)) ∘ usatE =
      Form.snoc Form.nil w := by
    funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  have hU : (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W)) ∘ usatU =
      (Form.snoc (fun _ : Fin 1 => v) (pt : W) : Fin 2 → W) := by
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hS : (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W)) ∘ usatS =
      Form.snoc Form.nil v := by
    funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  simp only [unitSetAtVnatF, Form.realize_or, Form.realize_and, Form.realize_not,
    Form.realize_relabel, hE, hU, hS, realize_emptyF_eq, realize_unitSetF, realize_singEmptyF]

theorem unitSetAtVnatF_apply {v w : W} (k : Nat)
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W))
      unitSetAtVnatF)
    (hw : w = (vnat k : W)) : v = (unitSetAt k : W) := by
  rcases realize_unitSetAtVnatF.mp hR with ⟨h0, hv⟩ | ⟨hne, hv⟩
  · have hk0 : k = 0 :=
      vnat_inj (V := W) (hw.symm.trans (h0.trans (show (empty : W) = vnat 0 from rfl)))
    subst hk0
    rw [unitSetAt_zero, unitSet_eq_sing]
    exact hv
  · have hk : k ≠ 0 := by
      intro h
      subst h
      exact hne (hw.trans (show (vnat 0 : W) = empty from rfl))
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [unitSetAt_pos (Nat.succ_ne_zero n)]
    exact hv


/-! ## Stage 68: the `unitAt`-of-a-numeral reader `unitAtVnatF` -/

/-- Map of the `emptyF` conjunct on `w` (var `0 ↦ w`) into the context `(v, w, pt)`. -/
def uatE : Fin 1 → Fin 3 := fun _ => ⟨1, by omega⟩

/-- Map of the `ptEqF` conjunct (vars `0 ↦ v`, `1 ↦ pt`) into the context `(v, w, pt)`. -/
def uatU : Fin 2 → Fin 3 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | _ => ⟨2, by omega⟩

/-- Map of the `emptyF` conjunct on `v` (var `0 ↦ v`) into the context `(v, w, pt)`. -/
def uatV : Fin 1 → Fin 3 := fun _ => ⟨0, by omega⟩

/-- The `unitAt`-of-a-numeral reader (variables `0 ↦ v`, `1 ↦ w`, `2 ↦ pt`):
`(w = empty ∧ v = pt) ∨ (w ≠ empty ∧ v = empty)` — the two cases of
`unitAt k = if k = 0 then pt else empty` at the numeral `w = vnat k`. -/
def unitAtVnatF : Form 3 :=
  .or (.and (Form.relabel uatE emptyF) (Form.relabel uatU ptEqF))
    (.and (.not (Form.relabel uatE emptyF)) (Form.relabel uatV emptyF))

theorem realize_unitAtVnatF {v w : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W)) unitAtVnatF ↔
      (w = (empty : W) ∧ v = (pt : W)) ∨ (¬ w = (empty : W) ∧ v = (empty : W)) := by
  have hE : (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W)) ∘ uatE =
      Form.snoc Form.nil w := by
    funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  have hU : (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W)) ∘ uatU =
      (Form.snoc (fun _ : Fin 1 => v) (pt : W) : Fin 2 → W) := by
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hV : (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W)) ∘ uatV =
      Form.snoc Form.nil v := by
    funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  simp only [unitAtVnatF, Form.realize_or, Form.realize_and, Form.realize_not,
    Form.realize_relabel, hE, hU, hV, realize_emptyF_eq, realize_ptEqF]

theorem unitAtVnatF_apply {v w : W} (k : Nat)
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W))
      unitAtVnatF)
    (hw : w = (vnat k : W)) : v = (unitAt k : W) := by
  rcases realize_unitAtVnatF.mp hR with ⟨h0, hv⟩ | ⟨hne, hv⟩
  · have hk0 : k = 0 :=
      vnat_inj (V := W) (hw.symm.trans (h0.trans (show (empty : W) = vnat 0 from rfl)))
    subst hk0
    rw [unitAt_zero]
    exact hv
  · have hk : k ≠ 0 := by
      intro h
      subst h
      exact hne (hw.trans (show (vnat 0 : W) = empty from rfl))
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [unitAt_pos (Nat.succ_ne_zero n)]
    exact hv


/-! ## Stage 69: the list-code `j`-th-element reader `vnatListNthF` -/

/-- Map of the `emptyF` conjunct (var `0 ↦ x`) into the context `(x, pt)`. -/
def nthE : Fin 1 → Fin 2 := fun _ => ⟨0, by omega⟩

/-- Map of the `vnatKpairEqF k` conjunct (vars `0 ↦ z`, `1 ↦ y`, `2 ↦ pt`) into the
bound context `(x, pt, y)`. -/
def nth0K : Fin 3 → Fin 3 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨2, by omega⟩ | _ => ⟨1, by omega⟩

/-- Map of the `kpairEqF` conjunct (vars `0 ↦ z`, `1 ↦ w`, `2 ↦ r`) into the
bound context `(x, pt, w, r)`. -/
def nthK : Fin 3 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of the recursive `vnatListNthF j k` conjunct (vars `0 ↦ r`, `1 ↦ pt`) into the
bound context `(x, pt, w, r)`. -/
def nthR : Fin 2 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨3, by omega⟩ | _ => ⟨1, by omega⟩

theorem vnatListCode_nil : (vnatListCode ([] : List Nat) : W) = empty := rfl

theorem vnatListCode_cons (u : Nat) (us : List Nat) :
    (vnatListCode (u :: us) : W) = kpair (vnat u) (vnatListCode us) := by
  simp only [vnatListCode, List.map_cons, Tower.mkTower, spair]

/-- The list-code `j`-th-element reader (variables `0 ↦ x`, `1 ↦ pt`):
`x = vnatListCode us` with `us.getD j 0 = k`, by recursion on `j` and cases
on `k` — the empty list contributes the default `0` via `emptyF`. -/
def vnatListNthF : Nat → Nat → Form 2
  | 0, 0 => .or (Form.relabel nthE emptyF) (.ex (Form.relabel nth0K (vnatKpairEqF 0)))
  | 0, k + 1 => .ex (Form.relabel nth0K (vnatKpairEqF (k + 1)))
  | j + 1, 0 => .or (Form.relabel nthE emptyF)
      (.ex (.ex (.and (Form.relabel nthK kpairEqF) (Form.relabel nthR (vnatListNthF j 0)))))
  | j + 1, k + 1 => .ex (.ex (.and (Form.relabel nthK kpairEqF)
      (Form.relabel nthR (vnatListNthF j (k + 1)))))

theorem realize_vnatListNthF (j k : Nat) (us : List Nat) {x : W} (hx : x = vnatListCode us) :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => x) (pt : W)) (vnatListNthF j k) ↔
      us.getD j 0 = k := by
  subst hx
  have hE : ∀ x : W, (Form.snoc (fun _ : Fin 1 => x) (pt : W)) ∘ nthE =
      Form.snoc Form.nil x := by
    intro x; funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  have h0 : ∀ x y : W,
      (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) y) ∘ nth0K =
        Form.snoc (Form.snoc (fun _ : Fin 1 => x) y) (pt : W) := by
    intro x y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK : ∀ x w r : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) w) r) ∘ nthK =
        Form.snoc (Form.snoc (fun _ : Fin 1 => x) w) r := by
    intro x w r; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hR : ∀ x w r : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) (pt : W)) w) r) ∘ nthR =
        (Form.snoc (fun _ : Fin 1 => r) (pt : W) : Fin 2 → W) := by
    intro x w r; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  induction j generalizing us with
  | zero =>
    cases k with
    | zero =>
      simp only [vnatListNthF, Form.realize_or, Form.realize_ex, Form.realize_relabel,
        hE, h0, realize_emptyF_eq, realize_vnatKpairEqF]
      cases us with
      | nil =>
        rw [vnatListCode_nil]
        have h0d : ([] : List Nat).getD 0 0 = 0 := rfl
        rw [h0d]
        constructor
        · rintro (h | ⟨y, hy⟩)
          · rfl
          · exact absurd hy.symm (kpair_ne_empty _ _)
        · intro _
          exact Or.inl rfl
      | cons u us =>
        rw [vnatListCode_cons]
        have hget : (u :: us).getD 0 0 = u := rfl
        rw [hget]
        constructor
        · rintro (h | ⟨y, hy⟩)
          · exact absurd h (kpair_ne_empty _ _)
          · exact vnat_inj (V := W) (kpair_inj hy).1
        · intro h
          exact Or.inr ⟨vnatListCode us, by rw [h]⟩
    | succ k =>
      simp only [vnatListNthF, Form.realize_ex, Form.realize_relabel, h0, realize_vnatKpairEqF]
      cases us with
      | nil =>
        rw [vnatListCode_nil]
        have h0d : ([] : List Nat).getD 0 0 = 0 := rfl
        rw [h0d]
        constructor
        · rintro ⟨y, hy⟩
          exact absurd hy.symm (kpair_ne_empty _ _)
        · intro h
          omega
      | cons u us =>
        rw [vnatListCode_cons]
        have hget : (u :: us).getD 0 0 = u := rfl
        rw [hget]
        constructor
        · rintro ⟨y, hy⟩
          exact vnat_inj (V := W) (kpair_inj hy).1
        · intro h
          exact ⟨vnatListCode us, by rw [h]⟩
  | succ j ih =>
    cases k with
    | zero =>
      simp only [vnatListNthF, Form.realize_or, Form.realize_ex, Form.realize_and,
        Form.realize_relabel, hE, hK, hR, realize_emptyF_eq, realize_kpairEqF]
      cases us with
      | nil =>
        rw [vnatListCode_nil]
        have h0d : ([] : List Nat).getD (j + 1) 0 = 0 := rfl
        rw [h0d]
        constructor
        · rintro (h | ⟨w, r, hk, -⟩)
          · rfl
          · exact absurd hk.symm (kpair_ne_empty _ _)
        · intro _
          exact Or.inl rfl
      | cons u us =>
        rw [vnatListCode_cons]
        have hget : (u :: us).getD (j + 1) 0 = us.getD j 0 := rfl
        rw [hget]
        constructor
        · rintro (h | ⟨w, r, hk, hr⟩)
          · exact absurd h (kpair_ne_empty _ _)
          · obtain ⟨-, h2⟩ := kpair_inj hk
            rw [← h2] at hr
            exact (ih us).mp hr
        · intro h
          exact Or.inr ⟨vnat u, vnatListCode us, rfl, (ih us).mpr h⟩
    | succ k =>
      simp only [vnatListNthF, Form.realize_ex, Form.realize_and, Form.realize_relabel,
        hK, hR, realize_kpairEqF]
      cases us with
      | nil =>
        rw [vnatListCode_nil]
        have h0d : ([] : List Nat).getD (j + 1) 0 = 0 := rfl
        rw [h0d]
        constructor
        · rintro ⟨w, r, hk, -⟩
          exact absurd hk.symm (kpair_ne_empty _ _)
        · intro h
          omega
      | cons u us =>
        rw [vnatListCode_cons]
        have hget : (u :: us).getD (j + 1) 0 = us.getD j 0 := rfl
        rw [hget]
        constructor
        · rintro ⟨w, r, hk, hr⟩
          obtain ⟨-, h2⟩ := kpair_inj hk
          rw [← h2] at hr
          exact (ih us).mp hr
        · intro h
          exact ⟨vnat u, vnatListCode us, rfl, (ih us).mpr h⟩


/-! ## Stage 70: the generic list-code `j`-th-element application `vnatListNthQF` -/

/-- Map of the `emptyF`-on-`x` conjunct (var `0 ↦ x`) into the context `(x, v, pt)`. -/
def nthEX : Fin 1 → Fin 3 := fun _ => ⟨0, by omega⟩

/-- Map of the `emptyF`-on-`w` conjunct (var `0 ↦ w`) into the bound context `(x, v, pt, w)`. -/
def nthQE : Fin 1 → Fin 4 := fun _ => ⟨3, by omega⟩

/-- Map of the `qf` conjunct (vars `0 ↦ v`, `1 ↦ w`, `2 ↦ pt`) into the
bound context `(x, v, pt, w)`. -/
def nthQ0 : Fin 3 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨1, by omega⟩ | 1 => ⟨3, by omega⟩ | _ => ⟨2, by omega⟩

/-- Map of the `kpairEqF` conjunct (vars `0 ↦ x`, `1 ↦ w`, `2 ↦ r`) into the
bound context `(x, v, pt, w, r)`. -/
def nthQK : Fin 3 → Fin 5 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨3, by omega⟩ | 2 => ⟨4, by omega⟩ | _ => ⟨4, by omega⟩

/-- Map of the `qf` conjunct (vars `0 ↦ v`, `1 ↦ w`, `2 ↦ pt`) into the
bound context `(x, v, pt, w, r)`. -/
def nthQV : Fin 3 → Fin 5 :=
  fun k => match k.val with | 0 => ⟨1, by omega⟩ | 1 => ⟨3, by omega⟩ | _ => ⟨2, by omega⟩

/-- Map of the recursive `vnatListNthQF j qf` conjunct (vars `0 ↦ r`, `1 ↦ v`, `2 ↦ pt`)
into the bound context `(x, v, pt, w, r)`. -/
def nthQR : Fin 3 → Fin 5 :=
  fun k => match k.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨1, by omega⟩ | _ => ⟨2, by omega⟩

/-- The generic list-code `j`-th-element application (variables `0 ↦ x`, `1 ↦ v`,
`2 ↦ pt`): `x = vnatListCode us` and `Q v (vnat (us.getD j 0))`, where `qf`
realizes `Q` on `(v, w)` — recursion on `j`; the empty list applies `qf` at
`w = empty` (the `getD` default `0`), guarded by `x = empty`. -/
def vnatListNthQF : Nat → Form 3 → Form 3
  | 0, qf => .or (.and (Form.relabel nthEX emptyF)
      (.ex (.and (Form.relabel nthQE emptyF) (Form.relabel nthQ0 qf))))
    (.ex (.ex (.and (Form.relabel nthQK kpairEqF) (Form.relabel nthQV qf))))
  | j + 1, qf => .or (.and (Form.relabel nthEX emptyF)
      (.ex (.and (Form.relabel nthQE emptyF) (Form.relabel nthQ0 qf))))
    (.ex (.ex (.and (Form.relabel nthQK kpairEqF) (Form.relabel nthQR (vnatListNthQF j qf)))))

theorem realize_vnatListNthQF (j : Nat) {qf : Form 3} {Q : W → W → Prop}
    (hqf : ∀ v w : W,
      Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W)) qf ↔ Q v w)
    (us : List Nat) {x v : W} (hx : x = vnatListCode us) :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => x) v) (pt : W))
        (vnatListNthQF j qf) ↔
      Q v (vnat (us.getD j 0)) := by
  subst hx
  have hEX : ∀ x v : W,
      (Form.snoc (Form.snoc (fun _ : Fin 1 => x) v) (pt : W)) ∘ nthEX =
        Form.snoc Form.nil x := by
    intro x v; funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  have hQE : ∀ x v w : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) v) (pt : W)) w) ∘ nthQE =
        Form.snoc Form.nil w := by
    intro x v w; funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  have hQ0 : ∀ x v w : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) v) (pt : W)) w) ∘ nthQ0 =
        Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W) := by
    intro x v w; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hQK : ∀ x v w r : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) v) (pt : W)) w) r) ∘ nthQK =
        Form.snoc (Form.snoc (fun _ : Fin 1 => x) w) r := by
    intro x v w r; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hQV : ∀ x v w r : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) v) (pt : W)) w) r) ∘ nthQV =
        Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) (pt : W) := by
    intro x v w r; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hQR : ∀ x v w r : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => x) v) (pt : W)) w) r) ∘ nthQR =
        Form.snoc (Form.snoc (fun _ : Fin 1 => r) v) (pt : W) := by
    intro x v w r; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  induction j generalizing us with
  | zero =>
    simp only [vnatListNthQF, Form.realize_or, Form.realize_and, Form.realize_ex,
      Form.realize_relabel, hEX, hQE, hQ0, hQK, hQV, realize_emptyF_eq, realize_kpairEqF, hqf]
    cases us with
    | nil =>
      rw [vnatListCode_nil]
      have h0d : ([] : List Nat).getD 0 0 = 0 := rfl
      rw [h0d]
      constructor
      · rintro (⟨-, w, hw, hQ⟩ | ⟨w, r, hk, -⟩)
        · rw [hw] at hQ
          exact hQ
        · exact absurd hk.symm (kpair_ne_empty _ _)
      · intro h
        exact Or.inl ⟨rfl, empty, rfl, h⟩
    | cons u us =>
      rw [vnatListCode_cons]
      have hget : (u :: us).getD 0 0 = u := rfl
      rw [hget]
      constructor
      · rintro (⟨h, -, -, -⟩ | ⟨w, r, hk, hQ⟩)
        · exact absurd h (kpair_ne_empty _ _)
        · obtain ⟨h1, -⟩ := kpair_inj hk
          rw [← h1] at hQ
          exact hQ
      · intro h
        exact Or.inr ⟨vnat u, vnatListCode us, rfl, h⟩
  | succ j ih =>
    simp only [vnatListNthQF, Form.realize_or, Form.realize_and, Form.realize_ex,
      Form.realize_relabel, hEX, hQE, hQ0, hQK, hQR, realize_emptyF_eq, realize_kpairEqF, hqf]
    cases us with
    | nil =>
      rw [vnatListCode_nil]
      have h0d : ([] : List Nat).getD (j + 1) 0 = 0 := rfl
      rw [h0d]
      constructor
      · rintro (⟨-, w, hw, hQ⟩ | ⟨w, r, hk, -⟩)
        · rw [hw] at hQ
          exact hQ
        · exact absurd hk.symm (kpair_ne_empty _ _)
      · intro h
        exact Or.inl ⟨rfl, empty, rfl, h⟩
    | cons u us =>
      rw [vnatListCode_cons]
      have hget : (u :: us).getD (j + 1) 0 = us.getD j 0 := rfl
      rw [hget]
      constructor
      · rintro (⟨h, -, -, -⟩ | ⟨w, r, hk, hr⟩)
        · exact absurd h (kpair_ne_empty _ _)
        · obtain ⟨-, h2⟩ := kpair_inj hk
          rw [← h2] at hr
          exact (ih us).mp hr
      · intro h
        exact Or.inr ⟨vnat u, vnatListCode us, rfl, (ih us).mpr h⟩

/-! ## Stage 71: the easy `bval` value reader `constValueEasyF` -/

/-- Map of the `bconstCodeEqF c` conjunct (vars `0 ↦ cc`, `1 ↦ pt`) into the
context `(v, cc, uc, pt)`. -/
def cveC : Fin 2 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨1, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of the `emptyF` conjunct (var `0 ↦ v`) into the context `(v, cc, uc, pt)`. -/
def cveE : Fin 1 → Fin 4 := fun _ => ⟨0, by omega⟩

/-- Map of the `ptEqF` conjunct (vars `0 ↦ v`, `1 ↦ pt`) into the context `(v, cc, uc, pt)`. -/
def cveP : Fin 2 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of the `vnatListNthQF 0 qf` conjunct (vars `0 ↦ uc`, `1 ↦ v`, `2 ↦ pt`) into the
context `(v, cc, uc, pt)`. -/
def cveN : Fin 3 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨2, by omega⟩ | 1 => ⟨0, by omega⟩ | _ => ⟨3, by omega⟩

/-- The easy `bval` value reader (variables `0 ↦ v`, `1 ↦ cc`, `2 ↦ uc`, `3 ↦ pt`):
the disjunction over the seven `univChain`-free constant cases —
`natZero`/`empty` (`v = empty`), `quotInd`/`quotSound`/`propext` (`v = pt`),
`punit` (`v = unitSetAt (lv us 0)` via `vnatListNthQF 0 unitSetAtVnatF` on `uc`),
`punitUnit` (via `unitAtVnatF`) — each guarded by `cc = bconstCode c`. -/
def constValueEasyF : Form 4 :=
  .or (.and (Form.relabel cveC (bconstCodeEqF .natZero)) (Form.relabel cveE emptyF))
  (.or (.and (Form.relabel cveC (bconstCodeEqF .empty)) (Form.relabel cveE emptyF))
  (.or (.and (Form.relabel cveC (bconstCodeEqF .quotInd)) (Form.relabel cveP ptEqF))
  (.or (.and (Form.relabel cveC (bconstCodeEqF .quotSound)) (Form.relabel cveP ptEqF))
  (.or (.and (Form.relabel cveC (bconstCodeEqF .propext)) (Form.relabel cveP ptEqF))
  (.or (.and (Form.relabel cveC (bconstCodeEqF .punit))
        (Form.relabel cveN (vnatListNthQF 0 unitSetAtVnatF)))
        (.and (Form.relabel cveC (bconstCodeEqF .punitUnit))
          (Form.relabel cveN (vnatListNthQF 0 unitAtVnatF))))))))

theorem realize_constValueEasyF {v cc uc : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W))
        constValueEasyF ↔
      (cc = (bconstCode .natZero : W) ∧ v = (empty : W)) ∨
      (cc = (bconstCode .empty : W) ∧ v = (empty : W)) ∨
      (cc = (bconstCode .quotInd : W) ∧ v = (pt : W)) ∨
      (cc = (bconstCode .quotSound : W) ∧ v = (pt : W)) ∨
      (cc = (bconstCode .propext : W) ∧ v = (pt : W)) ∨
      (cc = (bconstCode .punit : W) ∧
        Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => uc) v) (pt : W))
          (vnatListNthQF 0 unitSetAtVnatF)) ∨
      (cc = (bconstCode .punitUnit : W) ∧
        Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => uc) v) (pt : W))
          (vnatListNthQF 0 unitAtVnatF)) := by
  have hC : ∀ v cc uc : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W)) ∘ cveC =
        (Form.snoc (fun _ : Fin 1 => cc) (pt : W) : Fin 2 → W) := by
    intro v cc uc; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hE : ∀ v cc uc : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W)) ∘ cveE =
        Form.snoc Form.nil v := by
    intro v cc uc; funext ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  have hP : ∀ v cc uc : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W)) ∘ cveP =
        (Form.snoc (fun _ : Fin 1 => v) (pt : W) : Fin 2 → W) := by
    intro v cc uc; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hN : ∀ v cc uc : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W)) ∘ cveN =
        Form.snoc (Form.snoc (fun _ : Fin 1 => uc) v) (pt : W) := by
    intro v cc uc; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [constValueEasyF, Form.realize_or, Form.realize_and, Form.realize_relabel,
    hC, hE, hP, hN, realize_bconstCodeEqF, realize_emptyF_eq, realize_ptEqF]

theorem constValueEasyF_apply {v cc uc : W} {c : Term.BConst} {us : List Nat}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W))
      constValueEasyF)
    (hcc : cc = (bconstCode c : W)) (huc : uc = (vnatListCode us : W)) :
    v = bval W c us := by
  rcases realize_constValueEasyF.mp hR with
    ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, hN⟩ | ⟨h, hN⟩
  · have hc : c = .natZero := bconstCode_inj (hcc.symm.trans h)
    subst hc
    have hb : bval W .natZero us = (empty : W) := by simp only [bval]; unfold natzero; rfl
    rw [hb]; exact hv
  · have hc : c = .empty := bconstCode_inj (hcc.symm.trans h)
    subst hc
    exact hv
  · have hc : c = .quotInd := bconstCode_inj (hcc.symm.trans h)
    subst hc
    exact hv
  · have hc : c = .quotSound := bconstCode_inj (hcc.symm.trans h)
    subst hc
    exact hv
  · have hc : c = .propext := bconstCode_inj (hcc.symm.trans h)
    subst hc
    exact hv
  · have hc : c = .punit := bconstCode_inj (hcc.symm.trans h)
    subst hc
    have hQ := (realize_vnatListNthQF 0 (qf := unitSetAtVnatF)
      (Q := fun v w => (w = (empty : W) ∧ v = sing (pt : W)) ∨
        (¬ w = (empty : W) ∧ v = sing (empty : W)))
      (fun v w => realize_unitSetAtVnatF) us huc).mp hN
    exact unitSetAtVnatF_apply _
      ((realize_unitSetAtVnatF (v := v) (w := vnat (us.getD 0 0))).mpr hQ) rfl
  · have hc : c = .punitUnit := bconstCode_inj (hcc.symm.trans h)
    subst hc
    have hQ := (realize_vnatListNthQF 0 (qf := unitAtVnatF)
      (Q := fun v w => (w = (empty : W) ∧ v = (pt : W)) ∨
        (¬ w = (empty : W) ∧ v = (empty : W)))
      (fun v w => realize_unitAtVnatF) us huc).mp hN
    exact unitAtVnatF_apply _
      ((realize_unitAtVnatF (v := v) (w := vnat (us.getD 0 0))).mpr hQ) rfl

/-! ## Stage 72: the `const` case of the definable interp step `constStepF` -/

/-- Map of `ssndEqF`'s `(y, x, pt)` into the bound context
`(v, X, i, pt, c)`: `y ↦ c`, `x ↦ i`, `pt ↦ pt`. -/
def csS : Fin 3 → Fin 5 :=
  fun k => match k.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨2, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of `sfstEqF`'s `(y, x, pt)` into `(v, X, i, pt, c, cc)`:
`y ↦ cc`, `x ↦ c`, `pt ↦ pt`. -/
def csF : Fin 3 → Fin 6 :=
  fun k => match k.val with | 0 => ⟨5, by omega⟩ | 1 => ⟨4, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of `ssndEqF`'s `(y, x, pt)` into `(v, X, i, pt, c, cc, uc)`:
`y ↦ uc`, `x ↦ c`, `pt ↦ pt`. -/
def csN : Fin 3 → Fin 7 :=
  fun k => match k.val with | 0 => ⟨6, by omega⟩ | 1 => ⟨4, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of `kpairEqF`'s `(z, x, y)` into `(v, X, i, pt, c, cc, uc)`:
`z ↦ c`, `x ↦ cc`, `y ↦ uc`. -/
def csK : Fin 3 → Fin 7 :=
  fun k => match k.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨5, by omega⟩ | _ => ⟨6, by omega⟩

/-- Map of `constValueEasyF`'s `(v, cc, uc, pt)` into
`(v, X, i, pt, c, cc, uc)`: `v ↦ v`, `cc ↦ cc`, `uc ↦ uc`, `pt ↦ pt`. -/
def csV : Fin 4 → Fin 7 :=
  fun k => match k.val with
    | 0 => ⟨0, by omega⟩ | 1 => ⟨5, by omega⟩ | 2 => ⟨6, by omega⟩ | _ => ⟨3, by omega⟩

/-- The `const` case body (variables `0 ↦ v`, `1 ↦ X`, `2 ↦ i`, `3 ↦ pt`):
decode `ssnd i = kpair (sfst (ssnd i)) (ssnd (ssnd i))` and read the
easy-`bval` value at `cc = sfst (ssnd i)`, `uc = ssnd (ssnd i)`. -/
def constBodyF : Form 4 :=
  .ex (.and (Form.relabel csS ssndEqF)
  (.ex (.and (Form.relabel csF sfstEqF)
  (.ex (.and (Form.relabel csN ssndEqF)
  (.and (Form.relabel csK kpairEqF)
    (Form.relabel csV constValueEasyF)))))))

/-- The `const` step of the definable interpretation (variables
`0 ↦ v`, `1 ↦ X`, `2 ↦ i`, `3 ↦ pt`): the `tagDisjF 2` guard paired with
`constBodyF` — for `i = kpair (vnat 2) y` the payload `y = ssnd i` is a
`kpair cc uc` and `constValueEasyF` reads `v` at `(cc, uc)`. -/
def constStepF : Form 4 := .and (tagDisjF 2) constBodyF

theorem realize_constStepF {v X i : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W))
        constStepF ↔
      (∃ y, i = kpair (vnat 2 : W) y) ∧
      (∃ c, c = ssnd i ∧ ∃ cc, cc = sfst c ∧ ∃ uc, uc = ssnd c ∧ (c = kpair cc uc ∧
        Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc)
          (pt : W)) constValueEasyF)) := by
  have hM : ∀ y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) y) ∘
          tagDispatchMap =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => i) y) (pt : W) : Fin 3 → W) := by
    intro y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hS : ∀ c : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c) ∘ csS =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => c) i) (pt : W) : Fin 3 → W) := by
    intro c; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hF : ∀ c cc : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) c)
          cc) ∘ csF =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => cc) c) (pt : W) : Fin 3 → W) := by
    intro c cc; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hN : ∀ c cc uc : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i)
            (pt : W)) c) cc) uc) ∘ csN =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => uc) c) (pt : W) : Fin 3 → W) := by
    intro c cc uc; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hK : ∀ c cc uc : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i)
            (pt : W)) c) cc) uc) ∘ csK =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => c) cc) uc : Fin 3 → W) := by
    intro c cc uc; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV : ∀ c cc uc : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i)
            (pt : W)) c) cc) uc) ∘ csV =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W) : Fin 4 → W) := by
    intro c cc uc; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [constStepF, constBodyF, tagDisjF, Form.realize_and, Form.realize_ex,
    Form.realize_relabel, hM, hS, hF, hN, hK, hV,
    realize_vnatKpairEqF, realize_ssndEqF, realize_sfstEqF, realize_kpairEqF]

/-- The `const` step at a concrete code: `i = tmCode (.const c us)` forces
`cc = bconstCode c`, `uc = vnatListCode us`, hence (via
`constValueEasyF_apply`) `v = bval W c us`. -/
theorem constStepF_apply {v X i : W} {c : Term.BConst} {us : List Nat}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W))
      constStepF)
    (hi : i = (tmCode (Term.Term.const c us) : W)) :
    v = bval W c us := by
  rcases (realize_constStepF.mp hR).2 with ⟨c0, hc0, cc, hcc, uc, huc, _, hR'⟩
  have hcc' : cc = (bconstCode c : W) := by
    rw [hcc, hc0, hi, tmCode, ssnd_kpair, sfst_kpair]
  have huc' : uc = (vnatListCode us : W) := by
    rw [huc, hc0, hi, tmCode, ssnd_kpair, ssnd_kpair]
  exact constValueEasyF_apply hR' hcc' huc'

/-! ## Stage 73: the `sort 0` case of the definable interp step `sortZeroStepF` -/

/-- Map of `ssndEqF`'s `(y, x, pt)` into the bound context `(v, X, i, pt, u)`:
`y ↦ u`, `x ↦ i`, `pt ↦ pt`. -/
def szN : Fin 3 → Fin 5 :=
  fun k => match k.val with | 0 => ⟨4, by omega⟩ | 1 => ⟨2, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of `vnatEqF t`'s `(x, pt)` into `(v, X, i, pt, u)`: `x ↦ u`, `pt ↦ pt`. -/
def szV : Fin 2 → Fin 5 :=
  fun k => match k.val with | 0 => ⟨4, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of `univZeroEqF`'s `(v, pt)` into `(v, X, i, pt, u)`: `v ↦ v`, `pt ↦ pt`. -/
def szU : Fin 2 → Fin 5 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | _ => ⟨3, by omega⟩

/-- The `sort 0` step of the definable interpretation (variables
`0 ↦ v`, `1 ↦ X`, `2 ↦ i`, `3 ↦ pt`): the `tagDisjF 1` guard paired with
`ssnd i = vnat 0 ∧ v = univZero` — the value of `tmCode (.sort 0)` is
`univ 0 = univZero`. -/
def sortZeroStepF : Form 4 :=
  .and (tagDisjF 1)
    (.ex (.and (Form.relabel szN ssndEqF)
      (.and (Form.relabel szV (vnatEqF 0)) (Form.relabel szU univZeroEqF))))

theorem realize_sortZeroStepF {v X i : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W))
        sortZeroStepF ↔
      (∃ y, i = kpair (vnat 1 : W) y) ∧
      (∃ u, u = ssnd i ∧ u = vnat 0 ∧ v = (univZero : W)) := by
  have hM : ∀ y : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) y) ∘
          tagDispatchMap =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => i) y) (pt : W) : Fin 3 → W) := by
    intro y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hN : ∀ u : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) u) ∘ szN =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => u) i) (pt : W) : Fin 3 → W) := by
    intro u; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hV : ∀ u : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) u) ∘ szV =
        (Form.snoc (fun _ : Fin 1 => u) (pt : W) : Fin 2 → W) := by
    intro u; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hU : ∀ u : W,
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W)) u) ∘ szU =
        (Form.snoc (fun _ : Fin 1 => v) (pt : W) : Fin 2 → W) := by
    intro u; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [sortZeroStepF, tagDisjF, Form.realize_and, Form.realize_ex, Form.realize_relabel,
    hM, hN, hV, hU, realize_vnatKpairEqF, realize_ssndEqF, realize_vnatEqF,
    realize_univZeroEqF]

/-- The `sort 0` step at a concrete code: `i = tmCode (.sort 0)` forces
`v = univ 0`. -/
theorem sortZeroStepF_apply {v X i : W}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W))
      sortZeroStepF)
    (_hi : i = (tmCode (Term.Term.sort 0) : W)) :
    v = (univ 0 : W) := by
  rcases (realize_sortZeroStepF.mp hR).2 with ⟨u, _, _, hv⟩
  exact hv.trans univ_zero.symm

/-- The `sort 0` code realizes the step at `v = univ 0`. -/
theorem realize_sortZeroStepF_tmCode {X : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (univ 0 : W)) X)
      (tmCode (Term.Term.sort 0))) (pt : W)) sortZeroStepF :=
  realize_sortZeroStepF.mpr
    ⟨⟨vnat 0, rfl⟩, ⟨vnat 0, by rw [tmCode, ssnd_kpair], rfl, univ_zero⟩⟩

/-! ## Stage 74: the combined definable interp step with `const`/`sort 0` `interpStepF2` -/

/-- The combined definable interp step, extended (variables `0 ↦ v`, `1 ↦ X`,
`2 ↦ i`, `3 ↦ pt`): `interpStepF` (the nine covered tags) plus the
`const 2` easy-`bval` case (`constStepF`) and the `sort 0` case
(`sortZeroStepF`).  The remaining gap is `sort u` for `u ≥ 1` and the
twelve `univChain`-dependent `const` cases. -/
def interpStepF2 : Form 4 :=
  .or interpStepF (.or constStepF sortZeroStepF)

theorem realize_interpStepF2 {v X i : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W))
        interpStepF2 ↔
      (Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W))
          interpStepF) ∨
      (Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W))
          constStepF) ∨
      (Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W))
          sortZeroStepF) := by
  simp only [interpStepF2, Form.realize_or, realize_interpStepF, realize_constStepF,
    realize_sortZeroStepF]

/-! ## Stage 75: `tmCode` corollaries — `realize_constStepF_tmCode` and the
`interpStepF2` entries for `const` (easy cases) and `sort 0` -/

/-- The `const` step realizes at a concrete easy-case code: for the seven
`univChain`-free `BConst` cases, `tmCode (.const c us)` steps to
`v = bval W c us`. -/
theorem realize_constStepF_tmCode {X : W} {c : Term.BConst} {us : List Nat}
    (hEasy : c = .natZero ∨ c = .empty ∨ c = .quotInd ∨ c = .quotSound ∨ c = .propext ∨
      c = .punit ∨ c = .punitUnit) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => bval W c us) X)
      (tmCode (Term.Term.const c us))) (pt : W)) constStepF := by
  refine realize_constStepF.mpr
    ⟨⟨kpair (bconstCode c : W) (vnatListCode us : W), rfl⟩, ?_⟩
  refine ⟨kpair (bconstCode c : W) (vnatListCode us : W), by rw [tmCode, ssnd_kpair],
    bconstCode c, by rw [sfst_kpair], vnatListCode us, by rw [ssnd_kpair], rfl, ?_⟩
  refine realize_constValueEasyF.mpr ?_
  rcases hEasy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl, by simp only [bval]; unfold natzero; rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, by simp only [bval]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, by simp only [bval]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by simp only [bval]⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by simp only [bval]⟩))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))))
    refine (realize_vnatListNthQF 0 (qf := unitSetAtVnatF)
      (Q := fun v w => (w = (empty : W) ∧ v = sing (pt : W)) ∨
        (¬ w = (empty : W) ∧ v = sing (empty : W)))
      (fun v w => realize_unitSetAtVnatF) us rfl).mpr ?_
    generalize hk : us.getD 0 0 = k
    rcases k with _ | k
    · left
      constructor
      · rfl
      · have hl : Term.lv us 0 = 0 := hk
        show (unitSetAt (Term.lv us 0) : W) = sing (pt : W)
        rw [hl, unitSetAt_zero, unitSet_eq_sing]
    · right
      constructor
      · exact vsucc_ne_empty _
      · have hl : Term.lv us 0 = k + 1 := hk
        show (unitSetAt (Term.lv us 0) : W) = sing (empty : W)
        rw [hl, unitSetAt_pos (Nat.succ_ne_zero k)]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩)))))
    refine (realize_vnatListNthQF 0 (qf := unitAtVnatF)
      (Q := fun v w => (w = (empty : W) ∧ v = (pt : W)) ∨
        (¬ w = (empty : W) ∧ v = (empty : W)))
      (fun v w => realize_unitAtVnatF) us rfl).mpr ?_
    generalize hk : us.getD 0 0 = k
    rcases k with _ | k
    · left
      constructor
      · rfl
      · have hl : Term.lv us 0 = 0 := hk
        show (unitAt (Term.lv us 0) : W) = (pt : W)
        rw [hl, unitAt_zero]
    · right
      constructor
      · exact vsucc_ne_empty _
      · have hl : Term.lv us 0 = k + 1 := hk
        show (unitAt (Term.lv us 0) : W) = (empty : W)
        rw [hl, unitAt_pos (Nat.succ_ne_zero k)]

/-- The `interpStepF2` entry for an easy `const` code: the step realizes at
`v = bval W c us`, `i = tmCode (.const c us)`. -/
theorem realize_interpStepF2_const_tmCode {X : W} {c : Term.BConst} {us : List Nat}
    (hEasy : c = .natZero ∨ c = .empty ∨ c = .quotInd ∨ c = .quotSound ∨ c = .propext ∨
      c = .punit ∨ c = .punitUnit) :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => bval W c us) X)
      (tmCode (Term.Term.const c us))) (pt : W)) interpStepF2 :=
  realize_interpStepF2.mpr (Or.inr (Or.inl (realize_constStepF_tmCode hEasy)))

/-- The `interpStepF2` entry for the `sort 0` code: the step realizes at
`v = univ 0`, `i = tmCode (.sort 0)`. -/
theorem realize_interpStepF2_sortZero_tmCode {X : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => (univ 0 : W)) X)
      (tmCode (Term.Term.sort 0))) (pt : W)) interpStepF2 :=
  realize_interpStepF2.mpr (Or.inr (Or.inr realize_sortZeroStepF_tmCode))

/-! ## Stage 76: the mp corollaries of `interpStepF2` at concrete codes -/

/-- A tag-`2` code cannot realize the nine covered tags or the `sort 0` tag. -/
theorem not_tag_of_tmCode_const {i : W} {c : Term.BConst} {us : List Nat} {t : Nat}
    (ht : t ≠ 2) (hi : i = (tmCode (Term.Term.const c us) : W)) (y : W)
    (hy : i = kpair (vnat t : W) y) : False := by
  rw [hi, tmCode] at hy
  exact absurd (vnat_inj (kpair_inj hy).1) (by omega)

/-- At a `const` code, `interpStepF2` forces `v = bval W c us`. -/
theorem interpStepF2_apply_const {v X i : W} {c : Term.BConst} {us : List Nat}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W))
      interpStepF2)
    (hi : i = (tmCode (Term.Term.const c us) : W)) :
    v = bval W c us := by
  rcases realize_interpStepF2.mp hR with h | h | h
  · rcases (realize_interpStepF.mp h) with
      (⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ |
        ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩)
    all_goals exact absurd (not_tag_of_tmCode_const (by omega) hi y hy) id
  · exact constStepF_apply h hi
  · obtain ⟨y, hy⟩ := (realize_sortZeroStepF.mp h).1
    exact absurd (not_tag_of_tmCode_const (by omega) hi y hy) id

/-- At a `sort 0` code, `interpStepF2` forces `v = univ 0`. -/
theorem interpStepF2_apply_sortZero {v X i : W}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) X) i) (pt : W))
      interpStepF2)
    (hi : i = (tmCode (Term.Term.sort 0) : W)) :
    v = (univ 0 : W) := by
  rcases realize_interpStepF2.mp hR with h | h | h
  · rcases (realize_interpStepF.mp h) with
      (⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ |
        ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩)
    all_goals
      rw [hi, tmCode] at hy
      exact absurd (vnat_inj (kpair_inj hy).1) (by omega)
  · rcases (realize_constStepF.mp h).1 with ⟨y, hy⟩
    rw [hi, tmCode] at hy
    exact absurd (vnat_inj (kpair_inj hy).1) (by omega)
  · exact sortZeroStepF_apply h hi

/-! ## Stage 78: the `omega` equality reader `omegaEqF` -/

/-- Map of the `inductiveF` conjunct (var `0 ↦ I`) into the bound context
`(v, pt, z, I)`: `0 ↦ 3`. -/
def omegaIMap : Fin 1 → Fin 4 := fun _ => ⟨3, by omega⟩

/-- The `omega` equality reader (variables `0 ↦ v`, `1 ↦ pt`): `v = omega`,
by extensionality and `mem_omega` (`z ∈ˢ omega ↔ ∀ I, Inductive I → z ∈ˢ I`,
itself the definable `omegaF`) — no `univChain` involved. -/
def omegaEqF : Form 2 :=
  .all (.iff (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
    (.all (.imp (Form.relabel omegaIMap inductiveF)
      (.mem ⟨2, by omega⟩ ⟨3, by omega⟩))))

theorem realize_omegaEqF {v : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => v) (pt : W)) omegaEqF ↔
      v = (omega : W) := by
  have hrel : ∀ z I : W,
      Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) (pt : W)) z) I)
          (Form.relabel omegaIMap inductiveF) ↔ Inductive I := by
    intro z I
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) (pt : W)) z) I) ∘ omegaIMap =
        Form.snoc Form.nil I := by
      funext ⟨k, hk⟩
      have hk0 : k = 0 := by omega
      subst hk0
      rfl
    rw [hcomp]
    exact inductive_iff_realize.symm
  simp only [omegaEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_imp, hrel, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (mem_omega (n := z)).symm
  · intro h z
    rw [h]
    exact mem_omega



/-! ## Stage 79: the `natSuccV` equality reader `natSuccEqF` -/

/-- Map of the `omegaF` conjunct (var `0 ↦ x`) into the bound context
`(v, pt, p, x, y)`: `0 ↦ 3`. -/
def nsOmMap : Fin 1 → Fin 5 := fun _ => ⟨3, by omega⟩

/-- Map of the `vsuccEqF` conjunct (vars `0 ↦ e`, `1 ↦ m`) into the bound
context `(v, pt, p, x, y)`: `0 ↦ 4`, `1 ↦ 3`. -/
def nsVsMap : Fin 2 → Fin 5 :=
  fun k => match k.val with | 0 => ⟨4, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of the `kpairEqF` conjunct (vars `0 ↦ z`, `1 ↦ x`, `2 ↦ y`) into the
bound context `(v, pt, p, x, y)`: `0 ↦ 2`, `1 ↦ 3`, `2 ↦ 4`. -/
def nsKpMap : Fin 3 → Fin 5 :=
  fun k => match k.val with
  | 0 => ⟨2, by omega⟩
  | 1 => ⟨3, by omega⟩
  | _ => ⟨4, by omega⟩

/-- The `natSuccV` equality reader (variables `0 ↦ v`, `1 ↦ pt`):
`v = natSuccV` — i.e. `v = graph vsucc omega` (via
`natSuccV_eq_lamR` + `lamR_pos`), by extensionality + `mem_graph`,
with `x ∈ˢ omega` read by `omegaF`, `y = vsucc x` by `vsuccEqF` and
`p = kpair x y` by `kpairEqF`. -/
def natSuccEqF : Form 2 :=
  .all (.iff (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
    (.ex (.ex (.and (Form.relabel nsOmMap omegaF)
      (.and (Form.relabel nsVsMap vsuccEqF) (Form.relabel nsKpMap kpairEqF))))))

theorem realize_natSuccEqF {v : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => v) (pt : W)) natSuccEqF ↔
      v = natSuccV W := by
  have hOm : ∀ p x y : W,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) (pt : W)) p) x) y)
          (Form.relabel nsOmMap omegaF) ↔ ∀ I : W, Inductive I → x ∈ˢ I := by
    intro p x y
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) (pt : W)) p) x) y)
        ∘ nsOmMap = Form.snoc Form.nil x := by
      funext ⟨k, hk⟩
      have hk0 : k = 0 := by omega
      subst hk0; rfl
    rw [hcomp]
    exact realize_omegaF
  have hVs : ∀ p x y : W,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) (pt : W)) p) x) y)
          (Form.relabel nsVsMap vsuccEqF) ↔ y = vsucc x := by
    intro p x y
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) (pt : W)) p) x) y)
        ∘ nsVsMap = Form.snoc (fun _ : Fin 1 => y) x := by
      funext ⟨k, hk⟩
      have hk2 : k = 0 ∨ k = 1 := by omega
      rcases hk2 with rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_vsuccEqF
  have hKp : ∀ p x y : W,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) (pt : W)) p) x) y)
          (Form.relabel nsKpMap kpairEqF) ↔ p = kpair x y := by
    intro p x y
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) (pt : W)) p) x) y)
        ∘ nsKpMap = Form.snoc (Form.snoc (fun _ : Fin 1 => p) x) y := by
      funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_kpairEqF
  have hg : natSuccV W = graph vsucc (omega : W) := by
    rw [natSuccV_eq_lamR, lamR_pos Nat.one_ne_zero]
    unfold natsucc
    rfl
  simp only [natSuccEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, hOm, hVs, hKp, Form.snoc_mk]
  have key : ∀ p : W, p ∈ˢ graph vsucc (omega : W) ↔
      ∃ x y : W, (∀ I : W, Inductive I → x ∈ˢ I) ∧ y = vsucc x ∧ p = kpair x y := by
    intro p
    rw [mem_graph]
    constructor
    · rintro ⟨x, hx, hp⟩
      exact ⟨x, vsucc x, (mem_omega (n := x)).mp hx, rfl, hp⟩
    · rintro ⟨x, y, hx, hy, hp⟩
      exact ⟨x, (mem_omega (n := x)).mpr hx, hp.trans (congrArg (kpair x) hy)⟩
  constructor
  · intro h
    have hvg : v = graph vsucc (omega : W) :=
      SetTheory.ext fun p => (h p).trans (key p).symm
    rw [hvg, hg]
  · intro h p
    rw [h, hg]
    exact key p



/-! ## Stage 80: the `nat`/`natSucc` `bval` value reader `constValueNatF` -/

/-- The `nat`/`natSucc` `bval` value reader (variables `0 ↦ v`, `1 ↦ cc`,
`2 ↦ uc`, `3 ↦ pt`): the disjunction over the two `omega`-based constant
cases — `nat` (`v = omega` via `omegaEqF`) and `natSucc`
(`v = natSuccV` via `natSuccEqF`) — each guarded by `cc = bconstCode c`. -/
def constValueNatF : Form 4 :=
  .or (.and (Form.relabel cveC (bconstCodeEqF .nat)) (Form.relabel cveP omegaEqF))
    (.and (Form.relabel cveC (bconstCodeEqF .natSucc)) (Form.relabel cveP natSuccEqF))

theorem realize_constValueNatF {v cc uc : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W))
        constValueNatF ↔
      (cc = (bconstCode .nat : W) ∧ v = (omega : W)) ∨
      (cc = (bconstCode .natSucc : W) ∧ v = natSuccV W) := by
  have hC : ∀ v cc uc : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W)) ∘ cveC =
        (Form.snoc (fun _ : Fin 1 => cc) (pt : W) : Fin 2 → W) := by
    intro v cc uc; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hP : ∀ v cc uc : W,
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W)) ∘ cveP =
        (Form.snoc (fun _ : Fin 1 => v) (pt : W) : Fin 2 → W) := by
    intro v cc uc; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  simp only [constValueNatF, Form.realize_or, Form.realize_and, Form.realize_relabel,
    hC, hP, realize_bconstCodeEqF, realize_omegaEqF, realize_natSuccEqF]

theorem constValueNatF_apply {v cc uc : W} {c : Term.BConst} {us : List Nat}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W))
      constValueNatF)
    (hcc : cc = (bconstCode c : W)) (_huc : uc = (vnatListCode us : W)) :
    v = bval W c us := by
  rcases realize_constValueNatF.mp hR with ⟨h, hv⟩ | ⟨h, hv⟩
  · have hc : c = .nat := bconstCode_inj (hcc.symm.trans h)
    subst hc
    have hb : bval W .nat us = (omega : W) := by simp only [bval]
    rw [hb]; exact hv
  · have hc : c = .natSucc := bconstCode_inj (hcc.symm.trans h)
    subst hc
    have hb : bval W .natSucc us = natSuccV W := by simp only [bval]
    rw [hb]; exact hv



/-! ## Stage 81: the combined `bval` value reader `constValueF` (9 of 19 cases) -/

/-- The combined `bval` value reader (variables `0 ↦ v`, `1 ↦ cc`, `2 ↦ uc`,
`3 ↦ pt`): the disjunction of the seven `univChain`-free easy cases
(`constValueEasyF`) and the two `omega`-based cases (`constValueNatF`). -/
def constValueF : Form 4 := .or constValueEasyF constValueNatF

theorem realize_constValueF {v cc uc : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W))
        constValueF ↔
      Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W))
          constValueEasyF ∨
      Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W))
          constValueNatF := by
  simp only [constValueF, Form.realize_or]

theorem constValueF_apply {v cc uc : W} {c : Term.BConst} {us : List Nat}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) cc) uc) (pt : W))
      constValueF)
    (hcc : cc = (bconstCode c : W)) (huc : uc = (vnatListCode us : W)) :
    v = bval W c us := by
  rcases realize_constValueF.mp hR with h | h
  · exact constValueEasyF_apply h hcc huc
  · exact constValueNatF_apply h hcc huc


/-! ## Stage 88: the `sUnion` equality reader `sUnionEqF` -/

/-- The `sUnion` equality reader (variables `0 ↦ v`, `1 ↦ a`):
`v = sUnion a`, by extensionality + `mem_sUnion`. -/
def sUnionEqF : Form 2 :=
  .all (.iff (.mem ⟨2, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (.mem ⟨3, by omega⟩ ⟨1, by omega⟩) (.mem ⟨2, by omega⟩ ⟨3, by omega⟩))))

theorem realize_sUnionEqF {v a : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => v) a) sUnionEqF ↔
      v = sUnion a := by
  simp only [sUnionEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (mem_sUnion (x := a)).symm
  · intro h z
    rw [h]
    exact mem_sUnion



/-! ## Stage 89: the `binUnion` equality reader `binUnionEqF` -/

/-- The `binUnion` equality reader (variables `0 ↦ v`, `1 ↦ a`, `2 ↦ b`):
`v = binUnion a b`, by extensionality + `mem_binUnion`. -/
def binUnionEqF : Form 3 :=
  .all (.iff (.mem ⟨3, by omega⟩ ⟨0, by omega⟩)
    (.or (.mem ⟨3, by omega⟩ ⟨1, by omega⟩) (.mem ⟨3, by omega⟩ ⟨2, by omega⟩)))

theorem realize_binUnionEqF {v a b : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) b) binUnionEqF ↔
      v = binUnion a b := by
  simp only [binUnionEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_or, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (mem_binUnion (a := a) (b := b)).symm
  · intro h z
    rw [h]
    exact mem_binUnion



/-! ## Stage 90: the `empty` equality reader `emptyEqF` -/

/-- The `empty` equality reader (variable `0 ↦ v`): `v = empty`,
i.e. `∀ z, z ∉ v` (`emptyF`), read back via extensionality +
`not_mem_empty`. -/
def emptyEqF : Form 1 := emptyF

theorem realize_emptyEqF {v : W} :
    Form.Realize Mem (Form.snoc Form.nil v) emptyEqF ↔ v = (empty : W) := by
  simp only [emptyEqF]
  rw [realize_emptyF]
  constructor
  · intro h
    exact SetTheory.ext fun z =>
      ⟨fun hz => (h z hz).elim, fun hz => (not_mem_empty z hz).elim⟩
  · intro h z
    rw [h]
    exact not_mem_empty z



/-! ## Stage 91: the `kpairImage` equality reader `kpairImageEqF` -/

/-- Map of the `kpairEqF` conjunct (vars `0 ↦ z`, `1 ↦ x`, `2 ↦ y`) into the
bound context `(v, a, X, z, x)`: `0 ↦ 3`, `1 ↦ 1`, `2 ↦ 4`. -/
def kpImKpMap : Fin 3 → Fin 5 :=
  fun k => match k.val with
  | 0 => ⟨3, by omega⟩
  | 1 => ⟨1, by omega⟩
  | _ => ⟨4, by omega⟩

/-- The `kpairImage` equality reader (variables `0 ↦ v`, `1 ↦ a`, `2 ↦ X`):
`v = kpairImage a X`, by extensionality + `mem_kpairImage`, with
`z = kpair a x` read by `kpairEqF`. -/
def kpairImageEqF : Form 3 :=
  .all (.iff (.mem ⟨3, by omega⟩ ⟨0, by omega⟩)
    (.ex (.and (.mem ⟨4, by omega⟩ ⟨2, by omega⟩)
      (Form.relabel kpImKpMap kpairEqF))))

theorem realize_kpairImageEqF {v a X : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) kpairImageEqF ↔
      v = kpairImage a X := by
  have hKp : ∀ z x : W,
      Form.Realize Mem
          (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) z) x)
          (Form.relabel kpImKpMap kpairEqF) ↔ z = kpair a x := by
    intro z x
    rw [Form.realize_relabel]
    have hcomp : (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) X) z) x)
        ∘ kpImKpMap = Form.snoc (Form.snoc (fun _ : Fin 1 => z) a) x := by
      funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    rw [hcomp]
    exact realize_kpairEqF
  simp only [kpairImageEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_ex, Form.realize_and, hKp, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (mem_kpairImage (a := a) (X := X)).symm
  · intro h z
    rw [h]
    exact mem_kpairImage



/-! ## Stage 92: the `unitSet` equality reader `unitSetEqF` -/

/-- The `unitSet` equality reader (variables `0 ↦ v`, `1 ↦ pt`):
`v = unitSet`, by extensionality + `mem_unitSet_iff`. -/
def unitSetEqF : Form 2 :=
  .all (.iff (.mem ⟨2, by omega⟩ ⟨0, by omega⟩) (.equal ⟨2, by omega⟩ ⟨1, by omega⟩))

theorem realize_unitSetEqF {v : W} :
    Form.Realize Mem (Form.snoc (fun _ : Fin 1 => v) (pt : W)) unitSetEqF ↔
      v = (unitSet : W) := by
  simp only [unitSetEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_equal, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans (mem_unitSet_iff (z := z)).symm
  · intro h z
    rw [h]
    exact mem_unitSet_iff


/-! ## Stage 108: the `sort u` case of the definable interp step `sortStepF`,
with the universe-tower graph as a parameter -/

/-- Map of `vnatKpairEqF t`'s `(z, y, pt)` into the bound context
`(v, X, i, pt, G, y)`: `z ↦ i`, `y ↦ y`, `pt ↦ pt`. -/
def tagDispatchMapS : Fin 3 → Fin 6 :=
  fun k => match k.val with
  | 0 => ⟨2, by omega⟩ | 1 => ⟨5, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of `ssndEqF`'s `(y, x, pt)` into the bound context
`(v, X, i, pt, G, w)`: `y ↦ w`, `x ↦ i`, `pt ↦ pt`. -/
def ssndMapS : Fin 3 → Fin 6 :=
  fun k => match k.val with
  | 0 => ⟨5, by omega⟩ | 1 => ⟨2, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of `appEqF`'s `(pt, v, g, u)` into the bound context
`(v, X, i, pt, G, w)`: `pt ↦ pt`, `v ↦ v`, `g ↦ G`, `u ↦ w`. -/
def appMapS : Fin 4 → Fin 6 :=
  fun k => match k.val with
  | 0 => ⟨3, by omega⟩ | 1 => ⟨0, by omega⟩ | 2 => ⟨4, by omega⟩ | _ => ⟨5, by omega⟩

/-- The `sort u` step of the definable interpretation (variables
`0 ↦ v`, `1 ↦ X`, `2 ↦ i`, `3 ↦ pt`, `4 ↦ G`, where `G` is the universe-tower
graph parameter): the `tagDisjF 1` guard paired with
`∃ w, w = ssnd i ∧ v = app G w` — since `tmCode (.sort u) = kpair (vnat 1) (vnat u)`,
`ssnd i = vnat u`, and with `app G (vnat u) = univ u` this reads `v = univ u`. -/
def sortStepF : Form 5 :=
  .and (.ex (Form.relabel tagDispatchMapS (vnatKpairEqF 1)))
    (.ex (.and (Form.relabel ssndMapS ssndEqF) (Form.relabel appMapS appEqF)))

theorem realize_sortStepF {v X i G : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) sortStepF ↔
      (∃ y, i = kpair (vnat 1 : W) y) ∧
      (∃ w, w = ssnd i ∧ v = app G w) := by
  have hM : ∀ y : W, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) y) ∘ tagDispatchMapS =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => i) y) (pt : W) : Fin 3 → W) := by
    intro y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hN : ∀ w : W, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) w) ∘ ssndMapS =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => w) i) (pt : W) : Fin 3 → W) := by
    intro w; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hA : ∀ w : W, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) w) ∘ appMapS =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) v) G) w : Fin 4 → W) := by
    intro w; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [sortStepF, Form.realize_and, Form.realize_ex, Form.realize_relabel,
    hM, hN, hA, realize_vnatKpairEqF, realize_ssndEqF, realize_appEqF]

/-- At a `sort u` code, `sortStepF` forces `v = app G (vnat u)`; with the
universe-tower law `app G (vnat u) = univ u`, `v = univ u`. -/
theorem sortStepF_apply {v X i G : W} {u : Nat}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) sortStepF)
    (hi : i = (tmCode (Term.Term.sort u) : W))
    (hG : app G (vnat u) = (univ u : W)) :
    v = (univ u : W) := by
  rcases (realize_sortStepF.mp hR).2 with ⟨w, hw, hv⟩
  rw [hi, tmCode, ssnd_kpair] at hw
  rw [hv, hw, hG]

/-- The `sort u` code realizes the step at `v = univ u`, given the
universe-tower law. -/
theorem realize_sortStepF_tmCode {X : W} {u : Nat} {G : W}
    (hG : app G (vnat u) = (univ u : W)) :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => univ u) X)
        (tmCode (Term.Term.sort u))) (pt : W)) G) sortStepF :=
  realize_sortStepF.mpr
    ⟨⟨vnat u, rfl⟩, vnat u, by rw [tmCode, ssnd_kpair], hG.symm⟩


/-! ## Stage 109: the universe-at-a-numeral reader `univAppEqF` -/

/-- Map of `appEqF`'s `(pt, v, g, u)` into `(v, w, G, pt)`:
`pt ↦ pt`, `v ↦ v`, `g ↦ G`, `u ↦ w`. -/
def univAppMap : Fin 4 → Fin 4 :=
  fun k => match k.val with
  | 0 => ⟨3, by omega⟩ | 1 => ⟨0, by omega⟩ | 2 => ⟨2, by omega⟩ | _ => ⟨1, by omega⟩

/-- The universe-at-a-numeral reader (variables `0 ↦ v`, `1 ↦ w`, `2 ↦ G`,
`3 ↦ pt`): `v = app G w` — with `w = vnat k` and the tower law
`app G (vnat k) = univ k`, this reads `v = univ k`. -/
def univAppEqF : Form 4 := Form.relabel univAppMap appEqF

theorem realize_univAppEqF {v w G : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) G) (pt : W))
        univAppEqF ↔
      v = app G w := by
  have hA : (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) G) (pt : W)) ∘ univAppMap =
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) v) G) w : Fin 4 → W) := by
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [univAppEqF, Form.realize_relabel, hA, realize_appEqF]

/-- At `w = vnat k`, the reader forces `v = app G (vnat k)`; with the
universe-tower law, `v = univ k`. -/
theorem univAppEqF_apply {v w G : W} {k : Nat}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) G)
      (pt : W)) univAppEqF)
    (hw : w = (vnat k : W)) (hG : app G (vnat k) = (univ k : W)) :
    v = (univ k : W) := by
  rw [realize_univAppEqF.mp hR, hw, hG]


/-! ## Stage 110: the combined definable interp step with the tower graph
`interpStepF3` -/

/-- The inclusion `Fin 4 → Fin 5` relabeling the `(v, X, i, pt)` readers into
the `(v, X, i, pt, G)` context. -/
def emb45 : Fin 4 → Fin 5 := fun k => ⟨k.val, by omega⟩

/-- The combined definable interp step in the tower-graph context (variables
`0 ↦ v`, `1 ↦ X`, `2 ↦ i`, `3 ↦ pt`, `4 ↦ G`): the nine covered tags of
`interpStepF`, the easy-`const` case `constStepF`, the `sort u` case
`sortStepF` (via the tower graph `G`), and the `sort 0` case
`sortZeroStepF`. -/
def interpStepF3 : Form 5 :=
  .or (Form.relabel emb45 interpStepF)
  (.or (Form.relabel emb45 constStepF)
  (.or sortStepF (Form.relabel emb45 sortZeroStepF)))

theorem realize_interpStepF3 {v X i G : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) interpStepF3 ↔
      (Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) interpStepF) ∨
      (Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) constStepF) ∨
      (Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) sortStepF) ∨
      (Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) sortZeroStepF) := by
  have hE : (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) ∘ emb45 = (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W) : Fin 4 → W) := by
    funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [interpStepF3, Form.realize_or, Form.realize_relabel, hE]

/-- At a `sort u` code, `interpStepF3` forces `v = univ u` (given the
tower law `app G (vnat u) = univ u`). -/
theorem interpStepF3_apply_sort {v X i G : W} {u : Nat}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) interpStepF3)
    (hi : i = (tmCode (Term.Term.sort u) : W))
    (hG : app G (vnat u) = (univ u : W)) :
    v = (univ u : W) := by
  rcases realize_interpStepF3.mp hR with h | h | h | h
  · rcases realize_interpStepF.mp h with
      (⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ |
        ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩ | ⟨⟨y, hy⟩, _⟩)
    all_goals
      rw [hi, tmCode] at hy
      exact absurd (vnat_inj (kpair_inj hy).1) (by omega)
  · rcases (realize_constStepF.mp h).1 with ⟨y, hy⟩
    rw [hi, tmCode] at hy
    exact absurd (vnat_inj (kpair_inj hy).1) (by omega)
  · exact sortStepF_apply h hi hG
  · rcases (realize_sortZeroStepF.mp h).2 with ⟨w, hw, hw0, -⟩
    rw [hi, tmCode, ssnd_kpair] at hw
    have hu : u = 0 := vnat_inj (hw ▸ hw0)
    subst hu
    exact sortZeroStepF_apply h hi

/-- The `sort u` code realizes `interpStepF3` at `v = univ u`, given the
tower law. -/
theorem realize_interpStepF3_tmCode_sort {X : W} {u : Nat} {G : W}
    (hG : app G (vnat u) = (univ u : W)) :
    Form.Realize Mem
      (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => univ u) X)
        (tmCode (Term.Term.sort u))) (pt : W)) G) interpStepF3 :=
  realize_interpStepF3.mpr (Or.inr (Or.inr (Or.inl (realize_sortStepF_tmCode hG))))


/-! ## Stage 111: the list-code element reader `vnatListGetF` -/

/-- Map of `emptyF`'s var into the `(x, w, pt)` context: `0 ↦ x`. -/
def getE0 : Fin 1 → Fin 3 := fun _ => ⟨0, by omega⟩

/-- Map of `vnatEqF 0`'s `(x, pt)` into `(x, w, pt)`: `x ↦ w`, `pt ↦ pt`. -/
def getV0 : Fin 2 → Fin 3 :=
  fun k => match k.val with | 0 => ⟨1, by omega⟩ | _ => ⟨2, by omega⟩

/-- Map of `kpairEqF`'s `(z, x, y)` into the bound context `(x, w, pt, r)`:
`z ↦ x`, `x ↦ w`, `y ↦ r` (reading `x = kpair w r`). -/
def getK0 : Fin 3 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | 1 => ⟨1, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of `kpairEqF`'s `(z, x, y)` into the doubly bound context
`(x, w, pt, a, r)`: `z ↦ x`, `x ↦ a`, `y ↦ r` (reading `x = kpair a r`). -/
def getK : Fin 3 → Fin 5 :=
  fun k => match k.val with
  | 0 => ⟨0, by omega⟩ | 1 => ⟨3, by omega⟩ | _ => ⟨4, by omega⟩

/-- Map of `vnatListGetF j`'s `(x, w, pt)` into the doubly bound context
`(x, w, pt, a, r)`: `x ↦ r`, `w ↦ w`, `pt ↦ pt`. -/
def getR : Fin 3 → Fin 5 :=
  fun k => match k.val with
  | 0 => ⟨4, by omega⟩ | 1 => ⟨1, by omega⟩ | _ => ⟨2, by omega⟩

/-- The list-code `j`-th-element reader (variables `0 ↦ x`, `1 ↦ w`,
`2 ↦ pt`): `x = vnatListCode us` with `w = vnat (us.getD j 0)`, by recursion
on `j` — the empty list contributes the default via `emptyF` +
`vnatEqF 0`; a cons contributes its head (`x = kpair w r`) at `j = 0` and
recurses into the tail `r` at `j + 1`. -/
def vnatListGetF : Nat → Form 3
  | 0 => .or (.and (Form.relabel getE0 emptyF) (Form.relabel getV0 (vnatEqF 0)))
      (.ex (Form.relabel getK0 kpairEqF))
  | j + 1 => .or (.and (Form.relabel getE0 emptyF) (Form.relabel getV0 (vnatEqF 0)))
      (.ex (.ex (.and (Form.relabel getK kpairEqF) (Form.relabel getR (vnatListGetF j)))))

theorem realize_vnatListGetF (j : Nat) (us : List Nat) {x w : W} (hx : x = vnatListCode us) :
    Form.Realize Mem (Form.snoc (Form.snoc (fun _ : Fin 1 => x) w) (pt : W)) (vnatListGetF j) ↔
      w = (vnat (us.getD j 0) : W) := by
  subst hx
  induction j generalizing us w with
  | zero =>
    have hE0 : (Form.snoc (Form.snoc (fun _ : Fin 1 => vnatListCode us) w) (pt : W)) ∘ getE0 =
        Form.snoc Form.nil (vnatListCode us) := by
      funext ⟨k, hk⟩
      have hk0 : k = 0 := by omega
      subst hk0; rfl
    have hV0 : (Form.snoc (Form.snoc (fun _ : Fin 1 => vnatListCode us) w) (pt : W)) ∘ getV0 =
        (Form.snoc (fun _ : Fin 1 => w) (pt : W) : Fin 2 → W) := by
      funext ⟨k, hk⟩
      have hk2 : k = 0 ∨ k = 1 := by omega
      rcases hk2 with rfl | rfl <;> rfl
    have hK0 : ∀ r : W,
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => vnatListCode us) w) (pt : W)) r) ∘ getK0 =
          (Form.snoc (Form.snoc (fun _ : Fin 1 => vnatListCode us) w) r : Fin 3 → W) := by
      intro r; funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    simp only [vnatListGetF, Form.realize_or, Form.realize_and, Form.realize_ex,
      Form.realize_relabel, hE0, hV0, hK0, realize_emptyF_eq, realize_vnatEqF,
      realize_kpairEqF]
    cases us with
    | nil =>
      simp only [List.getD_nil]
      constructor
      · rintro (⟨-, rfl⟩ | ⟨r, h⟩)
        · rfl
        · rw [vnatListCode_nil] at h; exact absurd h.symm (kpair_ne_empty _ _)
      · intro h; exact Or.inl ⟨vnatListCode_nil, h⟩
    | cons u us =>
      rw [vnatListCode_cons]
      simp only [List.getD_cons_zero]
      constructor
      · rintro (⟨h, -⟩ | ⟨r, h⟩)
        · exact absurd h (kpair_ne_empty _ _)
        · exact (kpair_inj h).1.symm
      · intro h; exact Or.inr ⟨vnatListCode us, by rw [h]⟩
  | succ j ih =>
    have hE0 : (Form.snoc (Form.snoc (fun _ : Fin 1 => vnatListCode us) w) (pt : W)) ∘ getE0 =
        Form.snoc Form.nil (vnatListCode us) := by
      funext ⟨k, hk⟩
      have hk0 : k = 0 := by omega
      subst hk0; rfl
    have hV0 : (Form.snoc (Form.snoc (fun _ : Fin 1 => vnatListCode us) w) (pt : W)) ∘ getV0 =
        (Form.snoc (fun _ : Fin 1 => w) (pt : W) : Fin 2 → W) := by
      funext ⟨k, hk⟩
      have hk2 : k = 0 ∨ k = 1 := by omega
      rcases hk2 with rfl | rfl <;> rfl
    have hK : ∀ a r : W,
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => vnatListCode us) w)
            (pt : W)) a) r) ∘ getK =
          (Form.snoc (Form.snoc (fun _ : Fin 1 => vnatListCode us) a) r : Fin 3 → W) := by
      intro a r; funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    have hR : ∀ a r : W,
        (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => vnatListCode us) w)
            (pt : W)) a) r) ∘ getR =
          (Form.snoc (Form.snoc (fun _ : Fin 1 => r) w) (pt : W) : Fin 3 → W) := by
      intro a r; funext ⟨k, hk⟩
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk3 with rfl | rfl | rfl <;> rfl
    simp only [vnatListGetF, Form.realize_or, Form.realize_and, Form.realize_ex,
      Form.realize_relabel, hE0, hV0, hK, hR, realize_emptyF_eq, realize_vnatEqF,
      realize_kpairEqF]
    cases us with
    | nil =>
      simp only [List.getD_nil]
      constructor
      · rintro (⟨-, rfl⟩ | ⟨a, r, h, -⟩)
        · rfl
        · rw [vnatListCode_nil] at h; exact absurd h.symm (kpair_ne_empty _ _)
      · intro h; exact Or.inl ⟨vnatListCode_nil, h⟩
    | cons u us =>
      rw [vnatListCode_cons]
      simp only [List.getD_cons_succ]
      constructor
      · rintro (⟨h, -⟩ | ⟨a, r, h, hr⟩)
        · exact absurd h (kpair_ne_empty _ _)
        · rw [← (kpair_inj h).2] at hr; exact (ih us).mp hr
      · intro h
        exact Or.inr ⟨vnat u, vnatListCode us, rfl, (ih us).mpr h⟩


/-! ## Stage 112: the `tg`-at-a-numeral reader `tgVnatF` -/

/-- Map of `vnatEqF 0`'s `(x, pt)` into `(v, w, G, pt)`: `x ↦ w`, `pt ↦ pt`. -/
def tv0 : Fin 2 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨1, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of `univZeroEqF`'s `(v, pt)` into `(v, w, G, pt)`: `v ↦ v`, `pt ↦ pt`. -/
def tvU : Fin 2 → Fin 4 :=
  fun k => match k.val with | 0 => ⟨0, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of `vsuccEqF`'s `(e, m)` into the bound context `(v, w, G, pt, u1)`:
`e ↦ u1`, `m ↦ w`. -/
def tvS : Fin 2 → Fin 5 :=
  fun k => match k.val with | 0 => ⟨4, by omega⟩ | _ => ⟨1, by omega⟩

/-- Map of `appEqF`'s `(pt, v, g, u)` into the bound context
`(v, w, G, pt, u1)`: `pt ↦ pt`, `v ↦ v`, `g ↦ G`, `u ↦ u1`. -/
def tvA1 : Fin 4 → Fin 5 :=
  fun k => match k.val with
  | 0 => ⟨3, by omega⟩ | 1 => ⟨0, by omega⟩ | 2 => ⟨2, by omega⟩ | _ => ⟨4, by omega⟩

/-- The `tg`-at-a-numeral reader (variables `0 ↦ v`, `1 ↦ w`, `2 ↦ G`,
`3 ↦ pt`, with `G` the graph of `univChain`): at `w = vnat 0`,
`v = univZero = tg 0`; at `w = vnat k` with `k ≠ 0`,
`v = app G (vsucc w) = app G (vnat (k+1)) = univChain (k+1) = tg k`. -/
def tgVnatF : Form 4 :=
  .or (.and (Form.relabel tv0 (vnatEqF 0)) (Form.relabel tvU univZeroEqF))
    (.and (.not (Form.relabel tv0 (vnatEqF 0)))
      (.ex (.and (Form.relabel tvS vsuccEqF) (Form.relabel tvA1 appEqF))))

theorem realize_tgVnatF {v w G : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) tgVnatF ↔
      (w = (vnat 0 : W) ∧ v = (univZero : W)) ∨
      (¬ w = (vnat 0 : W) ∧
        ∃ u1, u1 = vsucc w ∧ v = app G u1) := by
  have h0 : (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) ∘ tv0 = (Form.snoc (fun _ : Fin 1 => w) (pt : W) : Fin 2 → W) := by
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hU : (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) ∘ tvU = (Form.snoc (fun _ : Fin 1 => v) (pt : W) : Fin 2 → W) := by
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hS : ∀ u1 : W, (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) u1) ∘ tvS =
      (Form.snoc (fun _ : Fin 1 => u1) w : Fin 2 → W) := by
    intro u1; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hA : ∀ u1 : W, (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) u1) ∘ tvA1 =
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) v) G) u1 : Fin 4 → W) := by
    intro u1; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [tgVnatF, Form.realize_or, Form.realize_and, Form.realize_not,
    Form.realize_ex, Form.realize_relabel, h0, hU, hS, hA,
    realize_vnatEqF, realize_univZeroEqF, realize_vsuccEqF, realize_appEqF]

/-- At `w = vnat k`, the reader forces `v = tg k`, given the tower law
`app G (vnat n) = univChain n`. -/
theorem tgVnatF_apply {v w G : W} {k : Nat}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) tgVnatF)
    (hw : w = (vnat k : W))
    (hG : ∀ n : Nat, app G (vnat n) = (univChain n : W)) :
    v = (tg k : W) := by
  rcases realize_tgVnatF.mp hR with ⟨h0, hv⟩ | ⟨hne, u1, h1, hv⟩
  · have hk : k = 0 := vnat_inj (hw.symm.trans h0)
    subst hk; rw [tg_zero]; exact hv
  · have hk : k ≠ 0 := fun hk => hne (hw ▸ congrArg vnat hk)
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [show (vnat (n + 1) : W) = vsucc (vnat n) from rfl] at hw
    rw [hw] at h1
    have hu1 : u1 = (vnat (n + 2) : W) := h1
    rw [hv, hu1, hG (n + 2)]
    simp only [tg]


/-! ## Stage 113: the `sepF`-with-`tyF` equality reader `sepTyFEqF` -/

/-- Map of `tyF`'s `(U, p, X)` into the bound context `(v, a, U, p, z)`:
`U ↦ U`, `p ↦ p`, `X ↦ z`. -/
def sepTyMap : Fin 3 → Fin 5 :=
  fun k => match k.val with
  | 0 => ⟨2, by omega⟩ | 1 => ⟨3, by omega⟩ | _ => ⟨4, by omega⟩

/-- The `sepF`-with-`tyF` equality reader (variables `0 ↦ v`, `1 ↦ a`,
`2 ↦ U`, `3 ↦ p`): `v = sepF a tyF (snoc (fun _ => U) p)`, by extensionality
and `mem_sepF`. -/
def sepTyFEqF : Form 4 :=
  .all (.iff (.mem ⟨4, by omega⟩ ⟨0, by omega⟩)
    (.and (.mem ⟨4, by omega⟩ ⟨1, by omega⟩) (Form.relabel sepTyMap tyF)))

theorem realize_sepTyFEqF {v a U p : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) U) p) sepTyFEqF ↔
      v = sepF a tyF (Form.snoc (fun _ => U) p) := by
  have hM : ∀ z : W, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) a) U) p) z) ∘ sepTyMap =
      (Form.snoc (Form.snoc (fun _ : Fin 1 => U) p) z : Fin 3 → W) := by
    intro z; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  simp only [sepTyFEqF, Form.realize_all, Form.realize_iff, Form.realize_mem,
    Form.realize_and, Form.realize_relabel, hM, Form.snoc_mk]
  constructor
  · intro h
    exact SetTheory.ext fun z => (h z).trans mem_sepF.symm
  · intro h z
    rw [h]
    exact mem_sepF


/-! ## Stage 114: the `tyU`-at-a-numeral reader `tyUVnatF` -/

/-- Map of `appEqF`'s `(pt, v, g, u)` into the bound context
`(v, w, G, pt, u1, t)`: `pt ↦ pt`, `v ↦ t`, `g ↦ G`, `u ↦ u1`. -/
def tuT : Fin 4 → Fin 6 :=
  fun k => match k.val with
  | 0 => ⟨3, by omega⟩ | 1 => ⟨5, by omega⟩ | 2 => ⟨2, by omega⟩ | _ => ⟨4, by omega⟩

/-- Map of `univZeroEqF`'s `(v, pt)` into the bound context
`(v, w, G, pt, u1, t, U0)`: `v ↦ U0`, `pt ↦ pt`. -/
def tuU : Fin 2 → Fin 7 :=
  fun k => match k.val with | 0 => ⟨6, by omega⟩ | _ => ⟨3, by omega⟩

/-- Map of `sepTyFEqF`'s `(v, a, U, p)` into the bound context
`(v, w, G, pt, u1, t, U0)`: `v ↦ v`, `a ↦ t`, `U ↦ U0`, `p ↦ pt`. -/
def tuP : Fin 4 → Fin 7 :=
  fun k => match k.val with
  | 0 => ⟨0, by omega⟩ | 1 => ⟨5, by omega⟩ | 2 => ⟨6, by omega⟩ | _ => ⟨3, by omega⟩

/-- The `tyU`-at-a-numeral reader (variables `0 ↦ v`, `1 ↦ w`, `2 ↦ G`,
`3 ↦ pt`, with `G` the graph of `univChain`): at `w = vnat k`, `v = tyU k` —
at `k = 0`, `tyU 0 = univZero`; at `k ≠ 0`,
`tyU k = sepF (tg k) tyF (snoc (fun _ => univZero) pt)` with
`tg k = app G (vsucc w)`. -/
def tyUVnatF : Form 4 :=
  .or (.and (Form.relabel tv0 (vnatEqF 0)) (Form.relabel tvU univZeroEqF))
    (.and (.not (Form.relabel tv0 (vnatEqF 0)))
      (.ex (.and (Form.relabel tvS vsuccEqF)
        (.ex (.and (Form.relabel tuT appEqF)
          (.ex (.and (Form.relabel tuU univZeroEqF) (Form.relabel tuP sepTyFEqF))))))))

theorem realize_tyUVnatF {v w G : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) tyUVnatF ↔
      (w = (vnat 0 : W) ∧ v = (univZero : W)) ∨
      (¬ w = (vnat 0 : W) ∧
        ∃ u1, u1 = vsucc w ∧
          ∃ t, t = app G u1 ∧
            ∃ U0, U0 = (univZero : W) ∧ v = sepF t tyF (Form.snoc (fun _ => U0) (pt : W))) := by
  have h0 : (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) ∘ tv0 = (Form.snoc (fun _ : Fin 1 => w) (pt : W) : Fin 2 → W) := by
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hU : (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) ∘ tvU = (Form.snoc (fun _ : Fin 1 => v) (pt : W) : Fin 2 → W) := by
    funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hS : ∀ u1 : W, (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) u1) ∘ tvS =
      (Form.snoc (fun _ : Fin 1 => u1) w : Fin 2 → W) := by
    intro u1; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hT : ∀ u1 t : W, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) u1) t) ∘ tuT =
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => pt) t) G) u1 : Fin 4 → W) := by
    intro u1 t; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hU0 : ∀ u1 t U0 : W, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) u1) t) U0) ∘ tuU =
      (Form.snoc (fun _ : Fin 1 => U0) (pt : W) : Fin 2 → W) := by
    intro u1 t U0; funext ⟨k, hk⟩
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  have hP : ∀ u1 t U0 : W, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) u1) t) U0) ∘ tuP =
      (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) t) U0) (pt : W) : Fin 4 → W) := by
    intro u1 t U0; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [tyUVnatF, Form.realize_or, Form.realize_and, Form.realize_not,
    Form.realize_ex, Form.realize_relabel, h0, hU, hS, hT, hU0, hP,
    realize_vnatEqF, realize_univZeroEqF, realize_vsuccEqF, realize_appEqF, realize_sepTyFEqF]

/-- At `w = vnat k`, the reader forces `v = tyU k`, given the tower law
`app G (vnat n) = univChain n`. -/
theorem tyUVnatF_apply {v w G : W} {k : Nat}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) tyUVnatF)
    (hw : w = (vnat k : W))
    (hG : ∀ n : Nat, app G (vnat n) = (univChain n : W)) :
    v = (tyU k : W) := by
  rcases realize_tyUVnatF.mp hR with ⟨h0, hv⟩ | ⟨hne, u1, h1, t, ht, U0, hU0, hv⟩
  · have hk : k = 0 := vnat_inj (hw.symm.trans h0)
    subst hk; rw [tyU_zero]; exact hv
  · have hk : k ≠ 0 := fun hk => hne (hw ▸ congrArg vnat hk)
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [show (vnat (n + 1) : W) = vsucc (vnat n) from rfl] at hw
    rw [hw] at h1
    have hu1 : u1 = (vnat (n + 2) : W) := h1
    rw [ht, hu1, hG (n + 2), hU0] at hv
    have hty : (tyU (n + 1) : W) = sepF (tg (n + 1)) tyF (Form.snoc (fun _ => (univZero : W)) (pt : W)) := by
      unfold tyU
      rw [ite_eq_right (by omega)]
    rw [hv, hty]
    congr 1
    simp only [tg]


/-! ## Stage 115: the `univ`- and `univChain`-at-a-numeral corollaries -/

/-- At `w = vnat k`, the `tyUVnatF` reader forces `v = univ k` (since
`univ = tyU`), given the tower law `app G (vnat n) = univChain n`. -/
theorem univVnatF_apply {v w G : W} {k : Nat}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) w) G) (pt : W)) tyUVnatF)
    (hw : w = (vnat k : W))
    (hG : ∀ n : Nat, app G (vnat n) = (univChain n : W)) :
    v = (univ k : W) :=
  tyUVnatF_apply hR hw hG

/-- At `w = vnat k`, the `univAppEqF` reader forces `v = univChain k`,
given the tower law. -/
theorem univChainAppEqF_apply {v w G : W} {k : Nat}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) G) (pt : W)) univAppEqF)
    (hw : w = (vnat k : W))
    (hG : ∀ n : Nat, app G (vnat n) = (univChain n : W)) :
    v = (univChain k : W) := by
  rw [realize_univAppEqF.mp hR, hw]
  exact hG k


/-! ## Stage 116: the `sort u` case in the `univChain`-graph context
`sortStepG` -/

/-- Map of `tyUVnatF`'s `(v, w, G, pt)` into the bound context
`(v, X, i, pt, G, w)`: `v ↦ v`, `w ↦ w`, `G ↦ G`, `pt ↦ pt`. -/
def tyUMapS : Fin 4 → Fin 6 :=
  fun k => match k.val with
  | 0 => ⟨0, by omega⟩ | 1 => ⟨5, by omega⟩ | 2 => ⟨4, by omega⟩ | _ => ⟨3, by omega⟩

/-- The `sort u` step of the definable interpretation in the `univChain`-graph
context (variables `0 ↦ v`, `1 ↦ X`, `2 ↦ i`, `3 ↦ pt`, `4 ↦ G`, where `G` is the
graph of `univChain`): the `vnatKpairEqF 1` guard paired with
`∃ w, w = ssnd i ∧ tyUVnatF` — since `tmCode (.sort u) = kpair (vnat 1) (vnat u)`,
`ssnd i = vnat u`, and `tyUVnatF` reads `v = tyU u = univ u` from the tower
law `app G (vnat n) = univChain n`. -/
def sortStepG : Form 5 :=
  .and (.ex (Form.relabel tagDispatchMapS (vnatKpairEqF 1)))
    (.ex (.and (Form.relabel ssndMapS ssndEqF) (Form.relabel tyUMapS tyUVnatF)))

theorem realize_sortStepG {v X i G : W} :
    Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) sortStepG ↔
      (∃ y, i = kpair (vnat 1 : W) y) ∧
      (∃ w, w = ssnd i ∧
        ((w = (vnat 0 : W) ∧ v = (univZero : W)) ∨
         (¬ w = (vnat 0 : W) ∧
          ∃ u1, u1 = vsucc w ∧
            ∃ t, t = app G u1 ∧
              ∃ U0, U0 = (univZero : W) ∧ v = sepF t tyF (Form.snoc (fun _ => U0) (pt : W))))) := by
  have hM : ∀ y : W, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) y) ∘ tagDispatchMapS =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => i) y) (pt : W) : Fin 3 → W) := by
    intro y; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hN : ∀ w : W, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) w) ∘ ssndMapS =
        (Form.snoc (Form.snoc (fun _ : Fin 1 => w) i) (pt : W) : Fin 3 → W) := by
    intro w; funext ⟨k, hk⟩
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl <;> rfl
  have hY : ∀ w : W, (Form.snoc (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) w) ∘ tyUMapS =
        (Form.snoc (Form.snoc (Form.snoc (fun _ : Fin 1 => v) w) G) (pt : W) : Fin 4 → W) := by
    intro w; funext ⟨k, hk⟩
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  simp only [sortStepG, Form.realize_and, Form.realize_ex, Form.realize_relabel,
    hM, hN, hY, realize_vnatKpairEqF, realize_ssndEqF, realize_tyUVnatF]

/-- At a `sort u` code, `sortStepG` forces `v = univ u`, given the tower law
`app G (vnat n) = univChain n`. -/
theorem sortStepG_apply {v X i G : W} {u : Nat}
    (hR : Form.Realize Mem (Form.snoc (Form.snoc (Form.snoc (Form.snoc ((fun _ : Fin 1 => v)) X) i) (pt : W)) G) sortStepG)
    (hi : i = (tmCode (Term.Term.sort u) : W))
    (hG : ∀ n : Nat, app G (vnat n) = (univChain n : W)) :
    v = (univ u : W) := by
  rcases (realize_sortStepG.mp hR).2 with ⟨w, hw, hR'⟩
  rw [hi, tmCode, ssnd_kpair] at hw
  exact tyUVnatF_apply (realize_tyUVnatF.mpr hR') hw hG


end ConLeche.Semantics
