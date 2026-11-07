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


end ConLeche.Semantics
