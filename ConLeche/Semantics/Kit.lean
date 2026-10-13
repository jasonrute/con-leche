module

public import ConLeche.Semantics.Interp
public import ConLeche.Verify.Denote.VClosed

@[expose] public section

/-!
# The `interp` lemma kit (task #151, tier B)

Two halves.

**The substitution stack** — `interp_liftN` and `interp_inst`, the
layer's *entire* substitution metatheory: `interp` is structural, so
two lemmas suffice.  (lean4lean needs ~123 syntactic lemmas at
this spot because its metatheory is syntactic; soundness against a
model needs two semantic ones.)

**The regime lemmas** — what the two-regime design is *for*:

* `interp_mem_pi_pos` — the graph-regime inversion.  A member of
  `⟦(x : A) → B⟧` with the codomain sort nonzero **is** a graph, with
  domain exactly `⟦A⟧`, pointwise-fibred, non-`pt`, and canonical `∅`
  off the domain.  By definition, not by dispatch.
* `interp_beta_pos` / `interp_app_graph` — on-domain application
  computes, with no typing premise at all.
* `interp_pi_zero_subsingleton`, `interp_proof_irrel` — the squash
  regime is subsingleton-valued.
* `interp_pi_zero_small` — **impredicativity**: a function space landing in
  `Prop` is a truth value, for an arbitrary domain.
* `interp_not_pt_mem_pi_pos`, `interp_app_off_dom` — junk-freeness:
  the proof point never inhabits a graph-regime function space, and off-domain
  application is the canonical `∅`, never a point a consumer must
  dispatch on.

On `pt`: the only occurrences in this file are in *conclusions about
the squash regime* (`interp V ρ .prf = pt` and the `v = 0`
subsingleton facts) and in the *negative* junk-freeness statements.  No
lemma here has a `pt` hypothesis, no proof does a case split on whether
a value is `pt`, and the graph regime never mentions it except to deny
it.
-/

namespace ConLeche.Semantics
open ConLeche.Term (Term)
open ConLeche.SetModel

open SetTheory

universe w

variable (V : Type w) [SetTheory V]

/-! ## The substitution stack -/

theorem interp_liftN (n : Nat) :
    ∀ (e : Term) (k : Nat) (ρ : Nat → V),
      interp V ρ (e.liftN n k) = interp V (shiftE n k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    simp only [Term.liftN_bvar, interp_bvar, shiftE]
    split <;> rfl
  | sort u => intro k ρ; rfl
  | const c us => intro k ρ; rfl
  | app f a ihf iha =>
    intro k ρ; simp only [Term.liftN_app, interp_app, ihf, iha]
  | lam A b ihA ihb =>
    intro k ρ
    simp only [Term.liftN_lam, interp_lam, ihA]
    congr 1
    funext x
    rw [ihb, cons_shiftE]
  | pi A B ihA ihB =>
    intro k ρ
    simp only [Term.liftN_pi, interp_pi, ihA]
    congr 1
    funext x
    rw [ihB, cons_shiftE]
  | letE v b ihv ihb =>
    intro k ρ
    simp only [Term.liftN_letE, interp_letE, ihv]
    rw [ihb, cons_shiftE]
  | eqE a b iha ihb =>
    intro k ρ; simp only [Term.liftN_eqE, interp_eqE, iha, ihb]
  | fst e ihe =>
    intro k ρ; simp only [Term.liftN_fst, interp_fst, ihe]
  | snd e ihe =>
    intro k ρ; simp only [Term.liftN_snd, interp_snd, ihe]
  | prf => intro k ρ; rfl

theorem interp_lift (e : Term) (ρ : Nat → V) :
    interp V ρ e.lift = interp V (fun i => ρ (i + 1)) e := by
  rw [Term.lift, interp_liftN, shiftE_zero]

theorem interp_lift_cons (e : Term) (x : V) (ρ : Nat → V) :
    interp V (cons x ρ) e.lift = interp V ρ e := by
  rw [interp_lift]; rfl

theorem interp_inst :
    ∀ (e a : Term) (k : Nat) (ρ : Nat → V),
      interp V ρ (e.inst a k) =
        interp V (instE k (interp V (shiftE k 0 ρ) a) ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ
    show interp V ρ
        (if i < k then .bvar i
         else if i = k then Term.liftN k a else .bvar (i - 1)) =
      instE k (interp V (shiftE k 0 ρ) a) ρ i
    by_cases h : i < k
    · simp only [ite_eq_left h, instE]; rfl
    · by_cases h2 : i = k
      · simp only [ite_eq_right h, ite_eq_left h2, instE]
        exact interp_liftN V k a 0 ρ
      · simp only [ite_eq_right h, ite_eq_right h2, instE]; rfl
  | sort u => intro a k ρ; rfl
  | const c us => intro a k ρ; rfl
  | app f b ihf ihb =>
    intro a k ρ; simp only [Term.inst_app, interp_app, ihf, ihb]
  | lam A b ihA ihb =>
    intro a k ρ
    simp only [Term.inst_lam, interp_lam, ihA]
    congr 1
    funext x
    rw [ihb, shiftE_succ_cons, cons_instE]
  | pi A B ihA ihB =>
    intro a k ρ
    simp only [Term.inst_pi, interp_pi, ihA]
    congr 1
    funext x
    rw [ihB, shiftE_succ_cons, cons_instE]
  | letE v b ihv ihb =>
    intro a k ρ
    simp only [Term.inst_letE, interp_letE, ihv]
    rw [ihb, shiftE_succ_cons, cons_instE]
  | eqE b c ihb ihc =>
    intro a k ρ; simp only [Term.inst_eqE, interp_eqE, ihb, ihc]
  | fst e ihe =>
    intro a k ρ; simp only [Term.inst_fst, interp_fst, ihe]
  | snd e ihe =>
    intro a k ρ; simp only [Term.inst_snd, interp_snd, ihe]
  | prf => intro a k ρ; rfl

/-! ### Interpretation invariance below a bound

A closed term's interpretation does not read the environment.  Stated through the **erasure's** bound rather
than a fresh `Term.bvarsBelow`: `erase` maps `bvar i` to `bvar i` and
preserves every former's shape, so `Term.bvarsBelow k e` says
exactly "`e`'s indices are below `k`", and no new predicate is needed.

Needed by the literal clauses: the `Nat`/`String` blocks touch the
interpretation only through `interp_app`, `interp_bvar`, `interp_sort`,
`interp_pi` and `interp_closed`. -/

theorem interp_congr_below :
    ∀ (e : Term) (k : Nat) (ρ ρ' : Nat → V),
      ConLeche.Term.Term.bvarsBelow k e →
      (∀ i, i < k → ρ i = ρ' i) →
      interp V ρ e = interp V ρ' e := by
  intro e
  induction e with
  | bvar i => intro k ρ ρ' hb hag; exact hag i hb
  | sort u => intros; rfl
  | const c us => intros; rfl
  | prf => intros; rfl
  | app f a ihf iha =>
    intro k ρ ρ' hb hag
    simp only [interp_app, ihf k ρ ρ' hb.1 hag, iha k ρ ρ' hb.2 hag]
  | lam A b ihA ihb =>
    intro k ρ ρ' hb hag
    simp only [interp_lam, ihA k ρ ρ' hb.1 hag]
    refine lamV_congr fun x _ => ihb (k + 1) _ _ hb.2 ?_
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi)
  | pi A B ihA ihB =>
    intro k ρ ρ' hb hag
    simp only [interp_pi, ihA k ρ ρ' hb.1 hag]
    refine piV_congr fun x _ => ihB (k + 1) _ _ hb.2 ?_
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi)
  | letE v b ihv ihb =>
    intro k ρ ρ' hb hag
    simp only [interp_letE, ihv k ρ ρ' hb.1 hag]
    refine ihb (k + 1) _ _ hb.2 ?_
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi)
  | eqE a b iha ihb =>
    intro k ρ ρ' hb hag
    simp only [interp_eqE, iha k ρ ρ' hb.1 hag,
      ihb k ρ ρ' hb.2 hag]
  | fst e ihe =>
    intro k ρ ρ' hb hag
    simp only [interp_fst, ihe k ρ ρ' hb hag]
  | snd e ihe =>
    intro k ρ ρ' hb hag
    simp only [interp_snd, ihe k ρ ρ' hb hag]

/-- A closed term interprets the same under every environment. -/
theorem interp_closed {e : Term}
    (he : ConLeche.Term.Term.bvarsBelow 0 e) (ρ ρ' : Nat → V) :
    interp V ρ e = interp V ρ' e :=
  interp_congr_below V e 0 ρ ρ' he
    (fun i hi => absurd hi (Nat.not_lt_zero i))

/-- Substitution at the outermost binder — the form every rule uses. -/
theorem interp_inst0 (e a : Term) (ρ : Nat → V) :
    interp V ρ (e.inst a) = interp V (cons (interp V ρ a) ρ) e := by
  rw [interp_inst, shiftE_zero_zero, instE_zero]

theorem interp_mkAppN (ρ : Nat → V) :
    ∀ (as : List Term) (f : Term),
      interp V ρ (Term.mkAppN f as) =
        as.foldl (fun r a => SetTheory.app r (interp V ρ a)) (interp V ρ f)
  | [], _ => rfl
  | a :: as, f => by
    simp only [Term.mkAppN_cons, List.foldl_cons]
    rw [interp_mkAppN ρ as (.app f a)]
    rfl

/-! ## The value-read binders at the interpretation -/

/-- **The graph-regime inversion.**  A member of a Π-type's reading that
is not the point is a function graph: the graph of its own application
over `⟦A⟧`, its applications in the fibres, canonical junk `∅` off the
domain. -/
theorem interp_mem_pi_ne_pt {ρ : Nat → V} {A B : Term} {f : V}
    (hf : f ∈ˢ interp V ρ (.pi A B)) (hn : f ≠ pt) :
    graph (fun x => SetTheory.app f x) (interp V ρ A) = f ∧
    (∀ x, x ∈ˢ interp V ρ A →
      SetTheory.app f x ∈ˢ interp V (cons x ρ) B) ∧
    (∀ a, ¬ a ∈ˢ interp V ρ A → SetTheory.app f a = empty) := by
  rw [interp_pi] at hf
  have hs := mem_piSet_of_mem_piV hf hn
  exact ⟨eq_graph_app_of_mem_piSet hs, fun x hx => app_mem_of_mem_piSet hs hx,
    fun a ha => app_off_dom_of_mem_piSet hs ha⟩

/-- **β**, with no premise beyond the argument inhabiting the domain. -/
theorem interp_beta (ρ : Nat → V) (A b a : Term)
    (ha : interp V ρ a ∈ˢ interp V ρ A) :
    interp V ρ (.app (.lam A b) a) = interp V ρ (b.inst a) := by
  rw [interp_app, interp_lam, interp_inst0, app_lamV ha]

/-- Elimination at a Π-type's reading. -/
theorem interp_app_mem_pi {ρ : Nat → V} {A B : Term} {f a : V}
    (hf : f ∈ˢ interp V ρ (.pi A B)) (ha : a ∈ˢ interp V ρ A) :
    SetTheory.app f a ∈ˢ interp V (cons a ρ) B := by
  rw [interp_pi] at hf; exact app_mem_piV hf ha

/-- Proof irrelevance, in the form consumers use it: members of a
proposition — anything the interpretation places in `univ 0` — are all
equal, and all equal to the canonical proof `⟦prf⟧`. -/
theorem interp_proof_irrel {ρ : Nat → V} {T : Term} {x y : V}
    (hT : interp V ρ T ∈ˢ (univ 0 : V)) (hx : x ∈ˢ interp V ρ T)
    (hy : y ∈ˢ interp V ρ T) : x = y :=
  subsingleton_of_mem_univZero (univ_zero (V := V) ▸ hT) hx hy

end ConLeche.Semantics
