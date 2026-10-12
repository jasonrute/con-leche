module

public import ConLeche.Semantics.Syntax
public import ConLeche.Term.Const

@[expose] public section

/-!
# `BConst.typeAV` — the spelled basis-constant types (#151)

The first of the two suppliers the skeleton's `const` row waits on
(`Semantics/Skeleton.lean`): the `ITerm` mirror of
`ConLeche/Term/Const.lean`'s `BConst.type`, so that a built-in constant's
type can be *written* as an `ITerm` at all (`BConst.type` yields a
`Term`, not an `ITerm`).

The spelling carries no regime: `interp` reads each binder's regime off
the values (`piV`/`lamV`).  A codomain `Sort k` makes a function space
into a universe a *type*, never a proposition: `A → Prop` reads as
`piV ⟦A⟧ (fun _ => univ 0)`, whose fibre `univ 0` is not a truth value.

## The result sorts, read off the towers

| constant | `r` | tower |
|---|---|---|
| the five atomic types | — | no binder |
| `natSucc` | `1` | `lamR 1 omega natsucc` |
| `natRec` | `u` | `natRecV` |
| `psigma` | `max u v + 1` | `psigmaV` (a type former) |
| `psigmaMk` | `max u v` | `psigmaMkV` |
| `emptyRec` | `v` | `emptyRecV` |
| `quot` | `u + 1` | `quotV` (a type former) |
| `quotMk` | `u` | `quotMkV` |
| `quotLift` | `v` | `quotLiftV` |
| `quotInd`/`quotSound`/`propext` | `0` | `pt`: the types are `Prop` |
| `choice` | `u` | `choiceV` |
| `lfpFam` | `max (u + 1) (w + 1)` | `lfpFamV` (a type former) |
-/

namespace ConLeche.Semantics

open ConLeche.Semantics (ITerm)
open ConLeche.Term (BConst lv tupleIdxSort tupleFamSort)

/-! ## `ITerm` smart constructors

Mirrors of `ConLeche/Term/Const.lean`'s, one per former the basis types
mention.  Each carries the level numerals its own shape fixes. -/

/-- `Nat` -/
def natTyAV : ITerm := .const .nat []
/-- `Nat.zero` -/
def natZeroAV : ITerm := .const .natZero []
/-- `Nat.succ e` -/
def natSuccAV (e : ITerm) : ITerm := .app (.const .natSucc []) e
/-- `PUnit.{u}` -/
def punitAV (u : Nat) : ITerm := .const .punit [u]
/-- `Empty.{u}` -/
def emptyAV (u : Nat) : ITerm := .const .empty [u]
/-- `@BConst.psigma.{u,v} A B`, the dependent pair -/
def psigmaAV (u v : Nat) (A B : ITerm) : ITerm :=
  ITerm.mkAppN (.const .psigma [u, v]) [A, B]
/-- `@Quot.{u} A r` -/
def quotAV (u : Nat) (A r : ITerm) : ITerm :=
  ITerm.mkAppN (.const .quot [u]) [A, r]
/-- `@Quot.mk.{u} A r a` -/
def quotMkAV (u : Nat) (A r a : ITerm) : ITerm :=
  ITerm.mkAppN (.const .quotMk [u]) [A, r, a]

/-- `A → B`. -/
def arrowA (A B : ITerm) : ITerm := .pi A B.lift

/-- `A → A → Prop`, the relation type at `A : Sort u`.  Its own sort is
`max u 1` — a *type*, because `Prop` lives in `Sort 1`.  Matches
`relSpace`. -/
def relAV (A : ITerm) : ITerm :=
  .pi A (.pi A.lift (.sort 0))

/-- `¬ A`, i.e. `A → False`. -/
def negTyAV (A : ITerm) : ITerm := arrowA A (emptyAV 0)

/-! ## The block carrier's tuple spelling (#315)

`lfpTuple k` binds ONE tuple of index sets and ONE operator on the
tuple of families, so its type mentions two right-nested pair towers —
`⟨Sort u_0, …, Sort u_{k-1}⟩` and `⟨proj_0 Is → Sort w, …⟩`.  Both are
NON-dependent: component `m` may mention the ambient tuple variable but
never an earlier component, so the former takes its components
**already lifted to their own depth** (component `m` sits under `m` of
the tower's fibre binders).

`projAV` lives here rather than with the tower kit
(`Semantics/Tower/TowerKit.lean`, which imports this module) because a
basis constant's type needs it: it is ONE definition for every
structure and every index.  `ndTowerAV r` is `towerBodyAVPos r`'s
non-dependent twin — the same `.psigma [r, r]` tower, differing only in
the terminator's level, which no value reads (`bval .punit` is the
same `{∅}` at every positive level, task #342 B). -/

/-- The uniform projection spelling: `.fst ∘ .snd^i` — the `ITerm`
form of the tier's `projS i = sfst ∘ ssnd^i`.  Depends only on the
index. -/
def projAV : Nat → ITerm → ITerm
  | 0, e => .fst e
  | i + 1, e => projAV i (.snd e)

/-- The non-dependent pair tower at level `r`, `PUnit`-terminated:
`⟨G s, …, G (s + n - 1)⟩`.  The components are given at the BASE frame
and lifted to their own depth `d` by the former (component `s + i` sits
under `i` of the tower's fibre binders). -/
def ndTowerAV (r : Nat) (G : Nat → ITerm) : Nat → Nat → Nat → ITerm
  | _, _, 0 => .const .punit [r]
  | s, d, n + 1 =>
    .app (.app (.const .psigma [r, r]) ((G s).liftN d 0))
      (.lam ((G s).liftN d 0) (ndTowerAV r G (s + 1) (d + 1) n))

/-- `⟨Sort u_0, …, Sort u_{k-1}⟩`, the index-set tuple's type. -/
def tupleSortsAV (k : Nat) (us : List Nat) : ITerm :=
  ndTowerAV (tupleIdxSort us) (fun m => .sort (lv us m)) 0 0 k

/-- `⟨proj_0 Is → Sort w, …, proj_{k-1} Is → Sort w⟩`, the family
tuple's type, with `Is` at de Bruijn index `j` of the base frame. -/
def tupleFamsAV (k : Nat) (us : List Nat) (j : Nat) : ITerm :=
  ndTowerAV (tupleFamSort k us)
    (fun m => .pi (projAV m (.bvar j)) (.sort (lv us k))) 0 0 k

/-! ## The spelled type assignment -/

/-- The spelled type of each built-in constant — `BConst.type` as an
`ITerm` (see the module docstring). -/
def BConst.typeAV : BConst → List Nat → ITerm
  | .nat, _ => .sort 1
  | .natZero, _ => natTyAV
  | .natSucc, _ => arrowA natTyAV natTyAV
  | .natRec, us =>
    let u := lv us 0
    -- `∀ (M : Nat → Sort u), M 0 → (∀ n, M n → M (n+1)) → ∀ t, M t`
    .pi (arrowA natTyAV (.sort u)) <|
    .pi (.app (.bvar 0) natZeroAV) <|
    .pi (.pi natTyAV (.pi (.app (.bvar 2) (.bvar 0))
          (.app (.bvar 3) (natSuccAV (.bvar 1))))) <|
    .pi natTyAV <|
    .app (.bvar 3) (.bvar 0)
  | .punit, us => .sort (lv us 0)
  | .punitUnit, us => punitAV (lv us 0)
  | .psigma, us =>
    let u := lv us 0; let v := lv us 1
    .pi (.sort u) <|
    .pi (arrowA (.bvar 0) (.sort v)) <|
    .sort (Nat.max u v)
  | .psigmaMk, us =>
    let u := lv us 0; let v := lv us 1
    .pi (.sort u) <|
    .pi (arrowA (.bvar 0) (.sort v)) <|
    .pi (.bvar 1) <|
    .pi (.app (.bvar 1) (.bvar 0)) <|
    psigmaAV u v (.bvar 3) (.bvar 2)
  | .empty, us => .sort (lv us 0)
  | .emptyRec, us =>
    let u := lv us 0; let v := lv us 1
    .pi (arrowA (emptyAV u) (.sort v)) <|
    .pi (emptyAV u) <|
    .app (.bvar 1) (.bvar 0)
  | .quot, us =>
    let u := lv us 0
    .pi (.sort u) <|
    .pi (relAV (.bvar 0)) <|
    .sort u
  | .quotMk, us =>
    let u := lv us 0
    .pi (.sort u) <|
    .pi (relAV (.bvar 0)) <|
    .pi (.bvar 1) <|
    quotAV u (.bvar 2) (.bvar 1)
  | .quotLift, us =>
    let u := lv us 0; let v := lv us 1
    -- `∀ A r B (f : A → B), (∀ a b, r a b → f a = f b) → Quot A r → B`
    .pi (.sort u) <|
    .pi (relAV (.bvar 0)) <|
    .pi (.sort v) <|
    .pi (.pi (.bvar 2) (.bvar 1)) <|
    .pi (.pi (.bvar 3) (.pi (.bvar 4)
          (.pi (ITerm.mkAppN (.bvar 4) [.bvar 1, .bvar 0])
            (.eqE (.app (.bvar 3) (.bvar 2))
              (.app (.bvar 3) (.bvar 1)))))) <|
    .pi (quotAV u (.bvar 4) (.bvar 3)) <|
    .bvar 3
  | .quotInd, us =>
    let u := lv us 0
    .pi (.sort u) <|
    .pi (relAV (.bvar 0)) <|
    .pi (.pi (quotAV u (.bvar 1) (.bvar 0)) (.sort 0)) <|
    .pi (.pi (.bvar 2)
      (.app (.bvar 1) (quotMkAV u (.bvar 3) (.bvar 2) (.bvar 0)))) <|
    .pi (quotAV u (.bvar 3) (.bvar 2)) <|
    .app (.bvar 2) (.bvar 0)
  | .quotSound, us =>
    let u := lv us 0
    .pi (.sort u) <|
    .pi (relAV (.bvar 0)) <|
    .pi (.bvar 1) <|
    .pi (.bvar 2) <|
    .pi (ITerm.mkAppN (.bvar 2) [.bvar 1, .bvar 0]) <|
    .eqE (quotMkAV u (.bvar 4) (.bvar 3) (.bvar 2))
      (quotMkAV u (.bvar 4) (.bvar 3) (.bvar 1))
  | .propext, _ =>
    -- `∀ (A B : Prop), (A → B) → (B → A) → A = B`
    .pi (.sort 0) <| .pi (.sort 0) <|
    .pi (.pi (.bvar 1) (.bvar 1)) <|
    .pi (.pi (.bvar 1) (.bvar 3)) <|
    .eqE (.bvar 3) (.bvar 2)
  | .choice, us =>
    let u := lv us 0
    -- `∀ (A : Sort u), ¬¬A → A`
    .pi (.sort u) <|
    .pi (negTyAV (negTyAV (.bvar 0))) <|
    .bvar 1
  | .lfpFam, us =>
    let u := lv us 0; let w := lv us 1
    -- `Π (I : Sort u), ((I → Sort w) → (I → Sort w)) → I → Sort w` (task
    -- #188, indexed)
    .pi (.sort u) <|
    .pi (arrowA (arrowA (.bvar 0) (.sort w)) (arrowA (.bvar 0) (.sort w))) <|
    .pi (.bvar 1) (.sort w)
  | .lfpTuple k, us =>
    -- `Π (Is : ⟨Sort u_0, …, Sort u_{k-1}⟩) (F : Fams Is → Fams Is), Fams Is`
    .pi (tupleSortsAV k us) <|
    .pi (.pi (tupleFamsAV k us 0) (tupleFamsAV k us 1)) <|
    tupleFamsAV k us 1

end ConLeche.Semantics
