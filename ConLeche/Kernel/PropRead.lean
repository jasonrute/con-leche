module

public import ConLeche.Kernel.Env
public import ConLeche.Kernel.ExprOps

@[expose] public section

/-!
# Fast prop-ness off the head symbol (task #168)

Two pure readers that answer "is this type a proposition?" / "is this
term a proof?" from the **head symbol, the arity and the residual sorts of stored
types** — no inference, no reduction, no memo, no binder data (task
#342 S0).

Prop-ness is invariant under application: `zeronessOf (imax u v) =
zeronessOf v`, so the zero-ness of the sort of the type of `c a⃗` is
that of `c`'s *stored* type at every arity, over-application included.
The datum a head-symbol reader needs is therefore **one `PropWhen` per
constant** — the zero-ness of the sort of its type, read off the
stored (annotated, validated) type and instantiated at the use's
levels by `substPW`.

Both readers are three-valued (`some pw` = the datum, `none` = unknown,
fall back to inference).  The kernel's verdict on a datum is exactly the
slow path's `Level.isEquiv u .zero`: `pw == (.ifAllZero [])` ⟺ the
sort is zero at every valuation.

Trust: the readers consume annotations the checker validates
(`(forall-cod)`, `(lam-cod-leaf)`/`(lam-cod-chain)` in `inferBody`;
the stored types were validated at install), so they may only be
*consulted* at the verified modes (`mode.verifiedChecks`) — the trusted core
writes no data and the parser default stays.  The **"definitely not a
proof" arm** (`notProofFast`) needs no model theorem: refusing the
proof-irrelevance shortcut is always sound; its obligation is
kernel-level agreement with the slow path, which the landing census
records (DESIGN.md, task #168).  The **"definitely a proof" arm** is a
squash-regime licence (`prf_of_isProofFast`, `ConLeche/Model/Rules/DefEqSoundKit.lean`).
-/

namespace ConLeche

namespace Expr

/-- The residual after peeling `k` *syntactic* ∀ binders, whatever
their domains (no substitution — the residual may mention the peeled
binders; the readers only look at its head shape).  Task #342 S0: no
binder datum is read, so no `.never` requirement either (in #344's
model a type that is a member of a satisfying context is not the
point, so its head is a graph, which fixes the domains). -/
def peelPis : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .forallE _ b _ => peelPis k b
  | _ + 1, _ => none

/-- The domain of the `k`-th syntactic ∀ binder (`0` = outermost) of a
telescope, unsubstituted. -/
def binderDom : Nat → Expr → Option Expr
  | 0, .forallE A _ _ => some A
  | k + 1, .forallE _ b _ => binderDom k b
  | _, _ => none

/-- The number of arguments of an application spine. -/
def numArgs : Expr → Nat
  | .app f _ => numArgs f + 1
  | _ => 0

end Expr

/-- The zero-ness datum of the sort of a *residual type*: a `Sort u`
residual says the type inhabits `Sort u`.  (A ∀ residual would mean
the applied head is a function, not a type — unreachable on
well-typed input, and unknown here.) -/
def residualPW : Option Expr → Option PropWhen
  | some (.sort u) => some (Level.zeronessOf u)
  | _ => none

/-- The body of a λ-telescope that is a single bound variable: `some
(k, j)` for `fun x₁ … x_k => x_{k-j}` (the shape of `outParam`,
`semiOutParam`, `optParam`, `autoParam`). -/
def lamProj? : Nat → Expr → Option (Nat × Nat)
  | k, .lam _ b _ => lamProj? (k + 1) b
  | k, .bvar j => if j < k then some (k, j) else none
  | _, _ => none

/-- Task #342 S0: unfold an identity-like wrapper (a definition whose
value is `fun x₁ … x_k => x_i`, e.g. `outParam`) at the head of a
residual type, `fuel` times at most; definitional (δ then β). -/
def unwrapIdDefs (find? : Name → Option ConstantInfo) : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, e =>
    match e.getAppFn with
    | .const c _ =>
      match find? c with
      | some (.defnInfo _ v _) =>
        match lamProj? 0 v with
        | some (k, j) =>
          let args := e.getAppArgs
          if k ≤ args.length && args.length == k then
            unwrapIdDefs find? fuel (args.getD (k - 1 - j) e)
          else e
        | none => e
      | _ => e
    | _ => e

/-- `Expr.peelPis` through identity-like wrappers (`outParam (α → Sort u)`). -/
def peelPisW (find? : Name → Option ConstantInfo) : Nat → Expr → Option Expr
  | 0, e => some (unwrapIdDefs find? 4 e)
  | k + 1, .forallE _ b _ => peelPisW find? k b
  | k + 1, e =>
    match unwrapIdDefs find? 4 e with
    | .forallE _ b _ => peelPisW find? k b
    | _ => none

/-- The datum of a type-former application's *head* at `n` arguments:
a constant head reads its stored type (level-instantiated), an fvar
head its declared type, a `bvar` head (inside the ∀ telescope `root`,
`d` binders deep) its binder's domain; the residual after `n`
syntactic binders is read by `residualPW`. -/
def headTypePW (find? : Name → Option ConstantInfo) (root : Expr) (d : Nat) :
    Expr → Nat → Option PropWhen
  | .const I us, n =>
    match find? I with
    | some ci =>
      if ci.isTowerEntry then none else
      let cv := ci.toConstantVal
      if us.length = cv.levelParams.length then
        (residualPW (peelPisW find? n cv.type)).map
          (Level.substPW cv.levelParams us)
      else none
    | none => none
  | .fvar _ ty, n => residualPW (peelPisW find? n ty)
  | .bvar i, n =>
    if i < d then
      match root.binderDom (d - 1 - i) with
      | some D => residualPW (peelPisW find? n D)
      | none => none
    else none
  | _, _ => none

/-- The walk of `typeSortPW`: peel the ∀ telescope (a ∀'s prop-ness is
its codomain's: `zeronessOf (imax u v) = zeronessOf v`), counting the
binders, then read the residual's head. -/
def typeSortPWGo (find? : Name → Option ConstantInfo) (root : Expr) :
    Expr → Nat → Option PropWhen
  | .forallE _ b _, d => typeSortPWGo find? root b (d + 1)
  | .sort _, _ => some .never
  | R, d => headTypePW find? root d R.getAppFn R.numArgs

/-- The zero-ness datum of the sort of the *type* `T` ("is `T` a
proposition?"), read off `T`'s shape without binder data (task #342
S0): a ∀ telescope's is its codomain's; a sort's sort is never zero;
a constant-, fvar- or telescope-bvar-headed type-former application
reads the head's stored/declared type, peels the arity syntactically
and reads the residual, level-instantiated for a constant.  `none` =
unknown. -/
def typeSortPW (find? : Name → Option ConstantInfo) (T : Expr) :
    Option PropWhen :=
  typeSortPWGo find? T T 0

/-- The datum of a term's *head* (any arity): a constant head answers
from its stored type (prop-ness is invariant under application), an
fvar head from its declared type; sorts, ∀s and literals are never
proofs. -/
def headProofPW (find? : Name → Option ConstantInfo) : Expr →
    Option PropWhen
  | .const c us =>
    match find? c with
    | some ci =>
      if ci.isTowerEntry then none else
      let cv := ci.toConstantVal
      if us.length = cv.levelParams.length then
        (typeSortPW find? cv.type).map (Level.substPW cv.levelParams us)
      else none
    | none => none
  | .fvar _ ty => typeSortPW find? ty
  | .sort _ | .forallE .. | .lit _ => some .never
  | .proj S i _ =>
    -- Task #342 S0: the field's stored type, when its datum does not
    -- depend on the structure's levels
    match find? (projTableName S) with
    | some (.projInfo tbl) =>
      if i < tbl.numFields then
        match typeSortPW find? (tbl.entry i).body with
        | some pw => if pw.isNever || pw == .ifAllZero [] then some pw else none
        | none => none
      else none
    | _ => none
  | _ => none

/-- The zero-ness datum of the sort of the *type* of `a` ("is `a` a
proof?"), read off `a`'s head symbol at any arity: a constant or fvar
head answers from its stored/declared type; an unapplied λ answers from
its body (a λ's type is a ∀ whose prop-ness is its codomain's, the
body's type); sorts, ∀s and literals are never proofs.  `none` =
unknown. -/
partial def proofPW (find? : Name → Option ConstantInfo) : Expr → Option PropWhen
  | .lam _ b _ => proofPW find? b
  | .letE _ _ b => proofPW find? b
  | a =>
    match a.getAppFn with
    -- a β-redex's prop-ness is its λ's (invariant under application)
    | .lam _ b _ => proofPW find? b
    | .letE _ _ b => proofPW find? b
    | h => headProofPW find? h

/-- Is the datum "always zero" — the sort is `Prop` at every
valuation? -/
@[inline] def PropWhen.isProp (pw : PropWhen) : Bool :=
  pw == (.ifAllZero [])

/-- **Definitely not a proof** (the no arm): the datum is known and is
not always-zero. -/
def notProofFast (find? : Name → Option ConstantInfo) (a : Expr) : Bool :=
  match proofPW find? a with
  | some pw => !pw.isProp
  | none => false

/-- **Definitely a proof** (the yes arm): the datum is known and
always-zero. -/
def isProofFast (find? : Name → Option ConstantInfo) (a : Expr) : Bool :=
  match proofPW find? a with
  | some pw => pw.isProp
  | none => false

end ConLeche
