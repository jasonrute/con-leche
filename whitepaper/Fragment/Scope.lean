module

public import Fragment.Syntax

@[expose] public section

/-!
# Scope

Four syntactic predicates the declaration checks read: a term is
**closed** below a depth, it **mentions** some constants, it
**uses** some level parameters, and it **uses** a given bound
variable.  The checker checks them once per
declaration (con-leche's `looseBVarsBounded`, `constsResolve`,
`allLevelParamsDefined`); the model reads a term only through the
variables below its depth (and, finer, the variables it uses), the
constants it mentions and the parameters it uses (`Hygiene.lean`).
-/

namespace Fragment

namespace Level

/-- Every parameter of the level is one of `ps`. -/
def paramsIn (ps : List Name) : Level → Bool
  | zero => true
  | succ l => paramsIn ps l
  | max a b => paramsIn ps a && paramsIn ps b
  | imax a b => paramsIn ps a && paramsIn ps b
  | param n => ps.contains n

end Level

namespace Expr

/-- Every bound variable is below `k`: the term lives under `k`
binders. -/
def closedAt (k : Nat) : Expr → Bool
  | bvar i => decide (i < k)
  | sort _ => true
  | const _ _ => true
  | app f a => closedAt k f && closedAt k a
  | lam A b => closedAt k A && closedAt (k + 1) b
  | pi A B => closedAt k A && closedAt (k + 1) B

/-- The constants a term mentions. -/
def consts : Expr → List Name
  | bvar _ => []
  | sort _ => []
  | const c _ => [c]
  | app f a => consts f ++ consts a
  | lam A b => consts A ++ consts b
  | pi A B => consts A ++ consts B

/-- Every level parameter the term uses — in sorts, constant
instantiations — is one of `ps`. -/
def lparamsIn (ps : List Name) : Expr → Bool
  | bvar _ => true
  | sort u => u.paramsIn ps
  | const _ ls => ls.all (·.paramsIn ps)
  | app f a => lparamsIn ps f && lparamsIn ps a
  | lam A b => lparamsIn ps A && lparamsIn ps b
  | pi A B => lparamsIn ps A && lparamsIn ps B

/-- Does the term use the bound variable `i` (of the enclosing
context)?  Under a binder the variable is `i + 1`. -/
def usesVar (i : Nat) : Expr → Bool
  | bvar j => decide (j = i)
  | sort _ => false
  | const _ _ => false
  | app f a => usesVar i f || usesVar i a
  | lam A b => usesVar i A || usesVar (i + 1) b
  | pi A B => usesVar i A || usesVar (i + 1) B

end Expr

end Fragment
