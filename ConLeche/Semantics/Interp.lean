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


end ConLeche.Semantics
