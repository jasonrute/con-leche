module

public import ConLeche.Term.Subst

@[expose] public section

/-!
# `AnnotTerm`: the semantic syntax (task #151, tier A; task #342, L14a)

`AnnotTerm` is the syntax `interp` reads: a checker term after its
universe levels are evaluated (`Term`'s ground numerals) and its
projections spelled.  Node for node it is `Term`; the binder formers
carry no annotation:

| `Term` | `AnnotTerm` |
|---|---|
| `pi A B` | `pi A B` |
| `lam A b` | `lam A b` |
| `letE v b` | `letE v b` (no type slot: nothing reads a `let`'s type) |
| everything else | the same node |

A binder's regime (truth value or graph) is read off the values by
`interp` (`piV`/`lamV`, `SetModel/Ops.lean`), not off the syntax.

History: until task #342 (L14a) the binder formers carried ground
numeral sorts (`pi u v A B`, `lam u A b`), the checker's cached
annotations, and `interp` dispatched on them.

## The structural kit

`erase` maps to `Term`; `liftN`/`inst` are the de Bruijn operations,
defined *clause for clause* against `ConLeche/Term/Subst.lean`'s.  Their
content is the pair of commutations `erase_liftN` / `erase_inst`.
-/

namespace ConLeche.Semantics

open ConLeche.Term

/-- The semantic syntax: `Term`'s nodes, read by `interp`.  See the
module docstring. -/
inductive AnnotTerm where
  /-- de Bruijn index -/
  | bvar (i : Nat)
  /-- `Sort u` at a concrete level -/
  | sort (u : Nat)
  /-- a built-in constant at a concrete level instantiation -/
  | const (c : BConst) (us : List Nat)
  /-- application -/
  | app (f a : AnnotTerm)
  /-- `fun (_ : ty) => body` -/
  | lam (ty body : AnnotTerm)
  /-- `(_ : ty) → body` -/
  | pi (ty body : AnnotTerm)
  /-- `let _ := val; body`: the body under one binder, read at the
  value; no type slot, as in `Term` -/
  | letE (val body : AnnotTerm)
  /-- `@Eq _ lhs rhs`; no annotation, and no type slot either, as in
  `Term` (task #237) -/
  | eqE (lhs rhs : AnnotTerm)
  /-- first field of a pair -/
  | fst (e : AnnotTerm)
  /-- second field of a pair -/
  | snd (e : AnnotTerm)
  /-- the canonical (irrelevant) proof of a derivable equation -/
  | prf
  deriving Repr, Inhabited

namespace AnnotTerm

/-- The `Term` a semantic term spells. -/
def erase : AnnotTerm → Term
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c us => .const c us
  | .app f a => .app (erase f) (erase a)
  | .lam A b => .lam (erase A) (erase b)
  | .pi A B => .pi (erase A) (erase B)
  | .letE v b => .letE (erase v) (erase b)
  | .eqE a b => .eqE (erase a) (erase b)
  | .fst e => .fst (erase e)
  | .snd e => .snd (erase e)
  | .prf => .prf

@[simp] theorem erase_bvar (i : Nat) : erase (.bvar i) = .bvar i := rfl
@[simp] theorem erase_sort (u : Nat) : erase (.sort u) = .sort u := rfl
@[simp] theorem erase_const (c : BConst) (us : List Nat) :
    erase (.const c us) = .const c us := rfl
@[simp] theorem erase_app (f a : AnnotTerm) :
    erase (.app f a) = .app (erase f) (erase a) := rfl
@[simp] theorem erase_lam (A b : AnnotTerm) :
    erase (.lam A b) = .lam (erase A) (erase b) := rfl
@[simp] theorem erase_pi (A B : AnnotTerm) :
    erase (.pi A B) = .pi (erase A) (erase B) := rfl
@[simp] theorem erase_letE (v b : AnnotTerm) :
    erase (.letE v b) = .letE (erase v) (erase b) := rfl
@[simp] theorem erase_eqE (a b : AnnotTerm) :
    erase (.eqE a b) = .eqE (erase a) (erase b) := rfl
@[simp] theorem erase_fst (e : AnnotTerm) :
    erase (.fst e) = .fst (erase e) := rfl
@[simp] theorem erase_snd (e : AnnotTerm) :
    erase (.snd e) = .snd (erase e) := rfl
@[simp] theorem erase_prf : erase .prf = .prf := rfl

/-- Weakening: insert `n` fresh binders at depth `k`.  Clause for
clause `Term.liftN`; the numerals ride along untouched. -/
def liftN (n : Nat) : AnnotTerm → (k : Nat := 0) → AnnotTerm
  | .bvar i, k => .bvar (if i < k then i else i + n)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app f a, k => .app (liftN n f k) (liftN n a k)
  | .lam A b, k => .lam (liftN n A k) (liftN n b (k + 1))
  | .pi A B, k => .pi (liftN n A k) (liftN n B (k + 1))
  | .letE v b, k => .letE (liftN n v k) (liftN n b (k + 1))
  | .eqE a b, k => .eqE (liftN n a k) (liftN n b k)
  | .fst e, k => .fst (liftN n e k)
  | .snd e, k => .snd (liftN n e k)
  | .prf, _ => .prf

/-- Weakening by one. -/
abbrev lift (e : AnnotTerm) : AnnotTerm := liftN 1 e

/-- Single substitution at depth `k`.  Clause for clause
`Term.inst`. -/
def inst : AnnotTerm → AnnotTerm → (k : Nat := 0) → AnnotTerm
  | .bvar i, a, k =>
    if i < k then .bvar i else if i = k then liftN k a else .bvar (i - 1)
  | .sort u, _, _ => .sort u
  | .const c us, _, _ => .const c us
  | .app f b, a, k => .app (inst f a k) (inst b a k)
  | .lam A b, a, k => .lam (inst A a k) (inst b a (k + 1))
  | .pi A B, a, k => .pi (inst A a k) (inst B a (k + 1))
  | .letE v b, a, k => .letE (inst v a k) (inst b a (k + 1))
  | .eqE b c, a, k => .eqE (inst b a k) (inst c a k)
  | .fst e, a, k => .fst (inst e a k)
  | .snd e, a, k => .snd (inst e a k)
  | .prf, _, _ => .prf

/-- Iterated application (`Term.mkAppN`'s transpose). -/
def mkAppN (f : AnnotTerm) : List AnnotTerm → AnnotTerm
  | [] => f
  | a :: as => mkAppN (.app f a) as

@[simp] theorem mkAppN_nil (f : AnnotTerm) : mkAppN f [] = f := rfl
@[simp] theorem mkAppN_cons (f a : AnnotTerm) (as : List AnnotTerm) :
    mkAppN f (a :: as) = mkAppN (.app f a) as := rfl

/-- `Term.projPair?`'s transpose: decode the checker's projection index
for the pinned pair (task #225).  The bound `i < 2` that the single
`proj i e` former carried as a side condition is this function's
`none` branch. -/
def projPair? : Nat → AnnotTerm → Option AnnotTerm
  | 0, e => some (.fst e)
  | 1, e => some (.snd e)
  | _ + 2, _ => none

/-- The decoder is defined exactly at the two field indices, so a
decoded projection still witnesses the old side condition. -/
theorem lt_of_projPair? {i : Nat} {e x : AnnotTerm} (h : projPair? i e = some x) :
    i < 2 := by
  rcases i with _ | _ | i
  · omega
  · omega
  · exact nomatch h

/-- …and conversely: below the bound the decoder always fires, on any
subject.  Definedness depends on the index alone. -/
theorem projPair?_exists_of_lt {i : Nat} (h : i < 2) (e : AnnotTerm) :
    ∃ x, projPair? i e = some x := by
  rcases i with _ | _ | i
  · exact ⟨.fst e, rfl⟩
  · exact ⟨.snd e, rfl⟩
  · omega

/-- A decoded projection is one of the two formers on the same
subject — the case split consumers of the decoder want. -/
theorem projPair?_cases {i : Nat} {e x : AnnotTerm} (h : projPair? i e = some x) :
    x = .fst e ∨ x = .snd e := by
  rcases i with _ | _ | i
  · exact Or.inl (Option.some.inj h).symm
  · exact Or.inr (Option.some.inj h).symm
  · exact nomatch h

/-- The same split for two decodings **at one index**: a congruence
site sees the same former on both sides. -/
theorem projPair?_cases₂ {i : Nat} {e x e' x' : AnnotTerm}
    (h : projPair? i e = some x) (h' : projPair? i e' = some x') :
    (x = .fst e ∧ x' = .fst e') ∨ (x = .snd e ∧ x' = .snd e') := by
  rcases i with _ | _ | i
  · exact Or.inl ⟨(Option.some.inj h).symm, (Option.some.inj h').symm⟩
  · exact Or.inr ⟨(Option.some.inj h).symm, (Option.some.inj h').symm⟩
  · exact nomatch h

/-! ### Clause equations for the substitution operations -/

@[simp] theorem liftN_bvar (n k i : Nat) :
    liftN n (.bvar i) k = .bvar (if i < k then i else i + n) := rfl
@[simp] theorem liftN_sort (n k u : Nat) : liftN n (.sort u) k = .sort u := rfl
@[simp] theorem liftN_const (n k : Nat) (c : BConst) (us : List Nat) :
    liftN n (.const c us) k = .const c us := rfl
@[simp] theorem liftN_app (n k : Nat) (f a : AnnotTerm) :
    liftN n (.app f a) k = .app (liftN n f k) (liftN n a k) := rfl
@[simp] theorem liftN_lam (n k : Nat) (A b : AnnotTerm) :
    liftN n (.lam A b) k = .lam (liftN n A k) (liftN n b (k + 1)) := rfl
@[simp] theorem liftN_pi (n k : Nat) (A B : AnnotTerm) :
    liftN n (.pi A B) k = .pi (liftN n A k) (liftN n B (k + 1)) := rfl
@[simp] theorem liftN_letE (n k : Nat) (v b : AnnotTerm) :
    liftN n (.letE v b) k = .letE (liftN n v k) (liftN n b (k + 1)) := rfl
@[simp] theorem liftN_eqE (n k : Nat) (a b : AnnotTerm) :
    liftN n (.eqE a b) k = .eqE (liftN n a k) (liftN n b k) := rfl
@[simp] theorem liftN_fst (n k : Nat) (e : AnnotTerm) :
    liftN n (.fst e) k = .fst (liftN n e k) := rfl
@[simp] theorem liftN_snd (n k : Nat) (e : AnnotTerm) :
    liftN n (.snd e) k = .snd (liftN n e k) := rfl
@[simp] theorem liftN_prf (n k : Nat) : liftN n .prf k = .prf := rfl

@[simp] theorem inst_bvar (a : AnnotTerm) (k i : Nat) :
    inst (.bvar i) a k =
      (if i < k then .bvar i else if i = k then liftN k a else .bvar (i - 1)) := by
  rfl
@[simp] theorem inst_sort (a : AnnotTerm) (k u : Nat) :
    inst (.sort u) a k = .sort u := rfl
@[simp] theorem inst_const (a : AnnotTerm) (k : Nat) (c : BConst) (us : List Nat) :
    inst (.const c us) a k = .const c us := rfl
@[simp] theorem inst_app (a : AnnotTerm) (k : Nat) (f b : AnnotTerm) :
    inst (.app f b) a k = .app (inst f a k) (inst b a k) := rfl
@[simp] theorem inst_lam (a : AnnotTerm) (k : Nat) (A b : AnnotTerm) :
    inst (.lam A b) a k = .lam (inst A a k) (inst b a (k + 1)) := rfl
@[simp] theorem inst_pi (a : AnnotTerm) (k : Nat) (A B : AnnotTerm) :
    inst (.pi A B) a k = .pi (inst A a k) (inst B a (k + 1)) := rfl
@[simp] theorem inst_letE (a : AnnotTerm) (k : Nat) (v b : AnnotTerm) :
    inst (.letE v b) a k = .letE (inst v a k) (inst b a (k + 1)) := rfl
@[simp] theorem inst_eqE (a : AnnotTerm) (k : Nat) (b c : AnnotTerm) :
    inst (.eqE b c) a k = .eqE (inst b a k) (inst c a k) := rfl
@[simp] theorem inst_fst (a : AnnotTerm) (k : Nat) (e : AnnotTerm) :
    inst (.fst e) a k = .fst (inst e a k) := rfl
@[simp] theorem inst_snd (a : AnnotTerm) (k : Nat) (e : AnnotTerm) :
    inst (.snd e) a k = .snd (inst e a k) := rfl
@[simp] theorem inst_prf (a : AnnotTerm) (k : Nat) : inst .prf a k = .prf := rfl

/-! ### The erase-commutations

**Annotations are inert data under substitution.**  Both operations
project onto `Term`'s on the nose: nothing in `liftN`/`inst` reads or
writes a numeral slot, so `erase` is a homomorphism for them.  These
two equations are the whole point of the structural kit — tier B and
tier C move annotated terms through β, ζ and telescope steps by
rewriting with them, never by re-deriving a sort fact. -/

/-- `erase` commutes with lifting. -/
@[simp] theorem erase_liftN : ∀ (e : AnnotTerm) (n k : Nat),
    erase (liftN n e k) = Term.liftN n (erase e) k := by
  intro e
  induction e with
  | bvar i => intros; rfl
  | sort u => intros; rfl
  | const c us => intros; rfl
  | app f a ihf iha => intro n k; simp only [liftN_app, erase_app, ihf, iha,
      Term.liftN_app]
  | lam A b ihA ihb => intro n k; simp only [liftN_lam, erase_lam, ihA, ihb,
      Term.liftN_lam]
  | pi A B ihA ihB => intro n k; simp only [liftN_pi, erase_pi, ihA, ihB,
      Term.liftN_pi]
  | letE v b ihv ihb => intro n k; simp only [liftN_letE, erase_letE, ihv, ihb,
      Term.liftN_letE]
  | eqE a b iha ihb => intro n k; simp only [liftN_eqE, erase_eqE,
      iha, ihb, Term.liftN_eqE]
  | fst e ih => intro n k; simp only [liftN_fst, erase_fst, ih,
      Term.liftN_fst]
  | snd e ih => intro n k; simp only [liftN_snd, erase_snd, ih,
      Term.liftN_snd]
  | prf => intros; rfl

/-- `erase` commutes with instantiation. -/
@[simp] theorem erase_inst : ∀ (e a : AnnotTerm) (k : Nat),
    erase (inst e a k) = Term.inst (erase e) (erase a) k := by
  intro e
  induction e with
  | bvar i =>
    intro a k
    simp only [inst_bvar, Term.inst_bvar, erase_bvar]
    split
    · rfl
    · split
      · exact erase_liftN a k 0
      · rfl
  | sort u => intros; rfl
  | const c us => intros; rfl
  | app f b ihf ihb => intro a k; simp only [inst_app, erase_app, ihf, ihb,
      Term.inst_app]
  | lam A b ihA ihb => intro a k; simp only [inst_lam, erase_lam, ihA, ihb,
      Term.inst_lam]
  | pi A B ihA ihB => intro a k; simp only [inst_pi, erase_pi, ihA, ihB,
      Term.inst_pi]
  | letE v b ihv ihb => intro a k; simp only [inst_letE, erase_letE, ihv, ihb,
      Term.inst_letE]
  | eqE b c ihb ihc => intro a k; simp only [inst_eqE, erase_eqE,
      ihb, ihc, Term.inst_eqE]
  | fst e ih => intro a k; simp only [inst_fst, erase_fst, ih,
      Term.inst_fst]
  | snd e ih => intro a k; simp only [inst_snd, erase_snd, ih,
      Term.inst_snd]
  | prf => intros; rfl

/-- `erase` commutes with application spines. -/
theorem erase_mkAppN : ∀ (as : List AnnotTerm) (f : AnnotTerm),
    erase (mkAppN f as) = Term.mkAppN (erase f) (as.map erase) := by
  intro as
  induction as with
  | nil => intro f; rfl
  | cons a as ih => intro f; simpa using ih (.app f a)

end AnnotTerm


/-! ## `erase` at the constant clause -/

open ConLeche.Term (BConst)

/-- **`erase` is injective at the constant clause.**  Every other
`AnnotTerm` constructor erases to a different `Term` constructor, so a
constant erasure has a constant source — with the *same* name and the
*same* level numerals, since the constant clause carries no
annotation to forget. -/
theorem erase_eq_const {ea : AnnotTerm} {c : BConst} {us : List Nat}
    (h : ea.erase = .const c us) : ea = .const c us := by
  cases ea with
  | bvar i => rw [AnnotTerm.erase_bvar] at h; exact nomatch h
  | sort u => rw [AnnotTerm.erase_sort] at h; exact nomatch h
  | const c' us' =>
    rw [AnnotTerm.erase_const] at h
    injection h with h1 h2
    rw [h1, h2]
  | app f a => rw [AnnotTerm.erase_app] at h; exact nomatch h
  | lam ty b => rw [AnnotTerm.erase_lam] at h; exact nomatch h
  | pi ty b => rw [AnnotTerm.erase_pi] at h; exact nomatch h
  | letE v b => rw [AnnotTerm.erase_letE] at h; exact nomatch h
  | eqE l r => rw [AnnotTerm.erase_eqE] at h; exact nomatch h
  | fst e => rw [AnnotTerm.erase_fst] at h; exact nomatch h
  | snd e => rw [AnnotTerm.erase_snd] at h; exact nomatch h
  | prf => rw [AnnotTerm.erase_prf] at h; exact nomatch h


end ConLeche.Semantics
