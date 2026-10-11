module

public import Fragment.Uniform.Model
public import Fragment.Rules

@[expose] public section

/-!
# Uniform β: the rules (tasks #338, #339)

The fragment's three relations (`Rules.lean`), with **one β rule that
fires at every binder**: no certificate, no gate, no datum, no
comparison of the binder's annotation with anything.  δ and ι are the
fragment's.
`DefEqU` has no split rule: reducing a side and continuing (`redL`) is
sound outright under the model of `Uniform/Model.lean`, whose claims
say nothing about proofs.  Proof irrelevance stays as a rule — the
checker uses it to decide — but its soundness is vacuous: two proofs
are the point, and the claim is about non-proofs.
-/

namespace Fragment.Uniform

open Expr

variable [LevelOracle]

mutual

/-- **Reduction**: uniform β, δ, ι, chained. -/
inductive RedU (env : Env) : List Expr → Expr → Expr → Prop where
  | refl {Γ : List Expr} {e : Expr} : RedU env Γ e e
  | trans {Γ : List Expr} {e₁ e₂ e₃ : Expr} :
      RedU env Γ e₁ e₂ → RedU env Γ e₂ e₃ → RedU env Γ e₁ e₃
  | appFn {Γ : List Expr} {f f' a : Expr} :
      RedU env Γ f f' → RedU env Γ (app f a) (app f' a)
  /-- **β, uniform**: at every binder, with no premise. -/
  | beta {Γ : List Expr} {A b a : Expr} {pw : PropWhen} :
      RedU env Γ (app (lam A pw b) a) (b.inst a)
  | delta {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo} {v : Expr} :
      env.find? c = some ci → ci.value? = some v →
      ls.length = ci.lparams.length →
      RedU env Γ (const c ls) (v.instL ci.lparams ls)
  /-- **ι**, exactly as `Fragment.Red.iota`: the recursor's and the
  constructor's telescope certificates, then the constructor's levels,
  parameters and residual indices against the recursor's.  The major is
  reduced by `RedU`, so with uniform β; no β certificate is needed on
  the way, even where the major is a proof (`Acc`-style recursion):
  there the major and the constructor application are both the point,
  and the certificates alone supply what the law needs
  (`Uniform/Sound.lean`, `RedU.iota_sound`). -/
  | iota {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
      {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
      {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
      {cij : ConstInfo} {margs : List Expr} {rl : RecRule}
      {doms tys doms' tys' : List Expr}
      {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr} :
      env.find? c = some ci →
      ci.kind = .recursor numParams numMotives numMinors numIndices rules →
      us.length = ci.lparams.length →
      args.length = numParams + numMotives + numMinors + numIndices + 1 →
      ci.type.hasPis (numParams + numMotives + numMinors + numIndices + 1) = true →
      RedU env Γ (args.getD (numParams + numMotives + numMinors + numIndices) (bvar 0))
        major →
      major = mkAppN (const cj usj) margs →
      rl ∈ rules → rl.ctor = cj → rl.inst = none →
      env.find? cj = some cij →
      usj.length = cij.lparams.length →
      margs.length = numParams + rl.nfields →
      cij.type.hasPis (numParams + rl.nfields) = true →
      -- the recursor's telescope certificate, on the spine with the reduced major
      piDomains (ci.type.instL ci.lparams us)
        (args.take (numParams + numMotives + numMinors + numIndices) ++ [major]) = some doms →
      tys.length = doms.length →
      (∀ p ∈ (args.take (numParams + numMotives + numMinors + numIndices) ++ [major]).zip tys,
        InferU env Γ p.1 p.2) →
      (∀ p ∈ tys.zip doms, DefEqU env Γ p.1 p.2) →
      -- the constructor's telescope certificate
      piDomains (cij.type.instL cij.lparams usj) margs = some doms' →
      tys'.length = doms'.length →
      (∀ p ∈ margs.zip tys', InferU env Γ p.1 p.2) →
      (∀ p ∈ tys'.zip doms', DefEqU env Γ p.1 p.2) →
      -- the constructor's levels, parameters and residual indices against the recursor's
      Level.eqList usj (us.drop (us.length - usj.length)) = true →
      (∀ p ∈ (margs.take numParams).zip (args.take numParams), DefEqU env Γ p.1 p.2) →
      piResidual (cij.type.instL cij.lparams usj) margs = some residual →
      residual = mkAppN (const I lsI) (rps ++ ridx) →
      rps.length = numParams →
      (∀ p ∈ ridx.zip ((args.take (numParams + numMotives + numMinors + numIndices)).drop
        (numParams + numMotives + numMinors)), DefEqU env Γ p.1 p.2) →
      RedU env Γ (mkAppN (const c us) args)
        (mkAppN (rl.rhs.instL ci.lparams us)
          (args.take (numParams + numMotives + numMinors) ++ margs.drop numParams))
  /-- **ι, nested**, exactly as `Fragment.Red.iotaNested`. -/
  | iotaNested {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
      {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
      {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
      {cij : ConstInfo} {I' : Name} {nPc nfj : Nat} {margs : List Expr} {rl : RecRule}
      {lvs : List Level} {pinst : List Expr}
      {doms tys doms' tys' : List Expr}
      {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr} :
      env.find? c = some ci →
      ci.kind = .recursor numParams numMotives numMinors numIndices rules →
      us.length = ci.lparams.length →
      args.length = numParams + numMotives + numMinors + numIndices + 1 →
      ci.type.hasPis (numParams + numMotives + numMinors + numIndices + 1) = true →
      RedU env Γ (args.getD (numParams + numMotives + numMinors + numIndices) (bvar 0))
        major →
      major = mkAppN (const cj usj) margs →
      rl ∈ rules → rl.ctor = cj → rl.inst = some (lvs, pinst) →
      env.find? cj = some cij →
      cij.kind = .ctor I' nPc nfj →
      usj.length = cij.lparams.length →
      margs.length = nPc + rl.nfields →
      cij.type.hasPis (nPc + rl.nfields) = true →
      piDomains (ci.type.instL ci.lparams us)
        (args.take (numParams + numMotives + numMinors + numIndices) ++ [major]) = some doms →
      tys.length = doms.length →
      (∀ p ∈ (args.take (numParams + numMotives + numMinors + numIndices) ++ [major]).zip tys,
        InferU env Γ p.1 p.2) →
      (∀ p ∈ tys.zip doms, DefEqU env Γ p.1 p.2) →
      piDomains (cij.type.instL cij.lparams usj) margs = some doms' →
      tys'.length = doms'.length →
      (∀ p ∈ margs.zip tys', InferU env Γ p.1 p.2) →
      (∀ p ∈ tys'.zip doms', DefEqU env Γ p.1 p.2) →
      -- the constructor's levels and parameters against the stored instantiation
      Level.eqList usj (lvs.map (Level.subst ci.lparams us)) = true →
      pinst.length = nPc →
      (∀ p ∈ (margs.take nPc).zip
        (pinst.map fun e => instChain (e.instL ci.lparams us) (args.take numParams)),
        DefEqU env Γ p.1 p.2) →
      piResidual (cij.type.instL cij.lparams usj) margs = some residual →
      residual = mkAppN (const I lsI) (rps ++ ridx) →
      rps.length = nPc →
      (∀ p ∈ ridx.zip ((args.take (numParams + numMotives + numMinors + numIndices)).drop
        (numParams + numMotives + numMinors)), DefEqU env Γ p.1 p.2) →
      RedU env Γ (mkAppN (const c us) args)
        (mkAppN (rl.rhs.instL ci.lparams us)
          (args.take (numParams + numMotives + numMinors) ++ margs.drop nPc))


/-- **Definitional equality** (no `trans`, as in `Fragment.DefEq`). -/
inductive DefEqU (env : Env) : List Expr → Expr → Expr → Prop where
  | refl {Γ : List Expr} {a : Expr} : DefEqU env Γ a a
  | symm {Γ : List Expr} {a b : Expr} : DefEqU env Γ a b → DefEqU env Γ b a
  | redL {Γ : List Expr} {a a' b : Expr} :
      RedU env Γ a a' → DefEqU env Γ a' b → DefEqU env Γ a b
  | sort {Γ : List Expr} {u v : Level} :
      LevelOracle.eq u v = true → DefEqU env Γ (sort u) (sort v)
  | const {Γ : List Expr} {c : Name} {ls ls' : List Level} :
      Level.eqList ls ls' = true → DefEqU env Γ (const c ls) (const c ls')
  | pi {Γ : List Expr} {A₁ B₁ A₂ B₂ : Expr} {pw : PropWhen} :
      DefEqU env Γ A₁ A₂ → DefEqU env (A₂ :: Γ) B₁ B₂ →
      DefEqU env Γ (pi A₁ pw B₁) (pi A₂ pw B₂)
  | lam {Γ : List Expr} {A₁ b₁ A₂ b₂ : Expr} {pw : PropWhen} :
      DefEqU env Γ A₁ A₂ → DefEqU env (A₂ :: Γ) b₁ b₂ →
      DefEqU env Γ (lam A₁ pw b₁) (lam A₂ pw b₂)
  | app {Γ : List Expr} {f₁ a₁ f₂ a₂ : Expr} :
      DefEqU env Γ f₁ f₂ → DefEqU env Γ a₁ a₂ →
      DefEqU env Γ (app f₁ a₁) (app f₂ a₂)
  | eta {Γ : List Expr} {A₁ b₁ b tb A₂ B : Expr} {pw : PropWhen} :
      InferU env Γ b tb → RedU env Γ tb (pi A₂ pw B) →
      DefEqU env Γ A₂ A₁ →
      DefEqU env (A₁ :: Γ) b₁ (app (b.liftN 1) (bvar 0)) →
      DefEqU env Γ (lam A₁ pw b₁) b
  | proofIrrel {Γ : List Expr} {a ta tta b tb ttb : Expr} {u v : Level} :
      InferU env Γ a ta → InferU env Γ ta tta → RedU env Γ tta (sort u) →
      LevelOracle.eq u .zero = true →
      InferU env Γ b tb → InferU env Γ tb ttb → RedU env Γ ttb (sort v) →
      LevelOracle.eq v .zero = true →
      DefEqU env Γ a b

/-- **Type inference**, as `Fragment.Infer`. -/
inductive InferU (env : Env) : List Expr → Expr → Expr → Prop where
  | bvar {Γ : List Expr} {i : Nat} {A : Expr} :
      Γ[i]? = some A → InferU env Γ (bvar i) (A.liftN (i + 1))
  | sort {Γ : List Expr} {u : Level} :
      InferU env Γ (sort u) (sort (.succ u))
  | const {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo} :
      env.find? c = some ci → ls.length = ci.lparams.length →
      InferU env Γ (const c ls) (ci.type.instL ci.lparams ls)
  | pi {Γ : List Expr} {A B s t : Expr} {u v : Level} {pw : PropWhen} :
      InferU env Γ A s → RedU env Γ s (sort u) →
      InferU env (A :: Γ) B t → RedU env (A :: Γ) t (sort v) →
      Level.zeroness v = pw →
      InferU env Γ (pi A pw B) (sort (.imax u v))
  | lam {Γ : List Expr} {A b s bt btt : Expr} {u v : Level} {pw : PropWhen} :
      InferU env Γ A s → RedU env Γ s (sort u) →
      InferU env (A :: Γ) b bt →
      InferU env (A :: Γ) bt btt → RedU env (A :: Γ) btt (sort v) →
      Level.zeroness v = pw →
      InferU env Γ (lam A pw b) (pi A pw bt)
  | app {Γ : List Expr} {f a tf A B ta : Expr} {pw : PropWhen} :
      InferU env Γ f tf → RedU env Γ tf (pi A pw B) →
      InferU env Γ a ta → DefEqU env Γ ta A →
      InferU env Γ (app f a) (B.inst a)

end

end Fragment.Uniform
