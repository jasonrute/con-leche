module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSound
import ConLeche.Model.Rules.IotaSound
import ConLeche.Model.Rules.DefEqSound
import ConLeche.Model.Rules.InferSound
import ConLeche.Model.Rules.CertsSound
import ConLeche.Rules.Derived
import ConLeche.Model.CtxOkKit

public section

/-!
# The soundness of derivations (task #305)

**Derivation ⇒ P currency**, by one mutual structural recursion over
the six relations.  Every case is one per-rule lemma applied to the
recursive calls — nothing semantic happens here, which is the whole
point: the per-rule lemmas are the proof lanes' deliverables, this
file is fixed, and it is what the recomposition consumes.

The one non-mechanical move is the λ rule's `hshape`: the chain case
of the codomain validation reads the SHAPE of the body's inferred type
off the premise derivation (`Infer.lam_shape`), which the per-rule
lemma cannot see.

**Two inductions (task #342, L9, L11).**  The claims are conditional on
the point (`Motive.lean`): `red_sound`, `defeq_sound` … conclude the
conditional motives.  Their ι rules (`Red.iota`, the three rescues), the
two literal accelerations, and three `DefEq` rules (`lam`, `eta`,
`structEta`) are, for now, the **interim** unconditional side induction
(`red_soundU`, `defeq_soundU` …) weakened (`RedSemU.cond`,
`DefEqSemU.cond`); every other rule is proved at the conditional
motive, from the conditional claims of its premises.  The side
induction reads `Red.beta`'s certificate premises, which the conditional
one does not.  Task #342 L10 (ι) and L12 (the literal rows) move their
rules to the conditional induction.  λ-congruence and η need the
body-type check of the value reading (S4); structure η needs its two
spines in one telescope of types (the DESIGN record of L11).  The side
induction goes, and with it β's premises, once all of these are moved.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

/-! ## The interim unconditional side induction -/

mutual

theorem red_soundU (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {e e' : Expr}, Red env d e e' → RedSemU m φ d e e'
  | _, _, _, .refl => Red.refl_soundU
  | _, _, _, .trans h₁ h₂ =>
    Red.trans_soundU (red_soundU hin h₁) (red_soundU hin h₂)
  | _, _, _, .appFn h => Red.appFn_soundU (red_soundU hin h)
  | _, _, _, .projArg h => Red.projArg_soundU (red_soundU hin h)
  | _, _, _, .beta hta hd =>
    Red.beta_soundU (fun h => infer_soundU hin (hta h))
      (fun h => defeq_soundU hin (hd h))
  | _, _, _, .zeta => Red.zeta_soundU
  | _, _, _, .delta h => Red.delta_soundU hin h
  | _, _, _, .natLit h => Red.natLit_soundU h
  | _, _, _, .strLit h => Red.strLit_soundU h
  | _, _, _, .natSucc hsup hw hn =>
    Red.natSucc_soundU hin hsup (red_soundU hin hw) hn
  | _, _, _, .natOp hc hst hwa hn₁ hwb hn₂ hr =>
    Red.natOp_soundU hin hc hst (red_soundU hin hwa) hn₁ (red_soundU hin hwb) hn₂ hr
  | _, _, _, .proj hent hhead hi hlen hus hfire hctor hcerts =>
    Red.proj_soundU hin hent hhead hi hlen hus hfire hctor (certs_soundU hin hcerts)
  | _, _, _, .iota hhead hrec hlen hus hmajor hmhead hctor hrule hmlen hfire hlv
      hparams hcertR hcertC hres hidx =>
    Red.iota_sound hin hhead hrec hlen hus (red_soundU hin hmajor).cond hmhead hctor
      hrule hmlen hfire hlv (fun hc => (defEqList_soundU hin (hparams hc)).cond)
      (certs_soundU hin hcertR) (fun h3 => certsF_soundU hin (hcertC h3)) hres
      (fun h3 hne => (defEqList_soundU hin (hidx h3 hne)).cond)
  | _, _, _, .rescueK hrec hk hctor hres hind htm htmaj hthead hlv hnP hfab hws
      hb hlv' hcerts htf hdt hpi =>
    Red.rescueK_sound hin hrec hk hctor hres hind (infer_soundU hin htm)
      (red_soundU hin htmaj).cond hthead hlv hnP hfab hws hb hlv'
      (certs_soundU hin hcerts) (infer_soundU hin htf) (defeq_soundU hin hdt).cond
      (defeq_soundU hin hpi).cond
  | _, _, _, .rescueEta hrec heta hctor hres hind htm htmaj hthead hlen hlv hnz
      hfab hws hb hlv' hcerts hproj hpi =>
    Red.rescueEta_soundU hin hrec heta hctor hres hind (infer_soundU hin htm)
      (red_soundU hin htmaj) hthead hlen hlv hnz hfab hws hb hlv'
      (certs_soundU hin hcerts)
      (fun hno => etaProjCerts_soundU hin (hproj hno)) (defeq_soundU hin hpi)
  | _, _, _, .rescueAnd hrec hctor hres hind htm htmaj hthead hlen hlv hslots
      hfab hws hb hlv' hcerts htf hdt hpi =>
    Red.rescueAnd_sound hin hrec hctor hres hind (infer_soundU hin htm)
      (red_soundU hin htmaj).cond hthead hlen hlv hslots hfab hws hb hlv'
      (certs_soundU hin hcerts) (infer_soundU hin htf) (defeq_soundU hin hdt).cond
      (defeq_soundU hin hpi).cond

theorem defeq_soundU (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {a b : Expr}, DefEq env d a b → DefEqSemU m φ d a b
  | _, _, _, .refl => DefEq.refl_soundU
  | _, _, _, .symm h => DefEq.symm_soundU (defeq_soundU hin h)
  | _, _, _, .redL hr h => DefEq.redL_soundU (red_soundU hin hr) (defeq_soundU hin h)
  | _, _, _, .sort h => DefEq.sort_soundU h
  | _, _, _, .fvar => DefEq.fvar_soundU
  | _, _, _, .const h => DefEq.const_soundU h
  | _, _, _, .natZero => DefEq.natZero_soundU
  | _, _, _, .natSucc h => DefEq.natSucc_soundU (defeq_soundU hin h)
  | _, _, _, .forallE hty hbody hpw =>
    DefEq.forallE_soundU (defeq_soundU hin hty) (defeq_soundU hin hbody) hpw
  | _, _, _, .lam hty hbody hpw =>
    DefEq.lam_soundU (defeq_soundU hin hty) (defeq_soundU hin hbody) hpw
  | _, _, _, .app hf ha => DefEq.app_soundU (defeq_soundU hin hf) (defeq_soundU hin ha)
  | _, _, _, .proj h => DefEq.proj_soundU (defeq_soundU hin h)
  | _, _, _, .eta htb hwtb hty hbody hpw =>
    DefEq.eta_soundU (infer_soundU hin htb) (red_soundU hin hwtb)
      (defeq_soundU hin hty) (defeq_soundU hin hbody) hpw
  | _, _, _, .proofFast ha hb => DefEq.proofFast_soundU hin ha hb
  | _, _, _, .proofIrrel hta htta hu hu0 htb httb hv hv0 =>
    DefEq.proofIrrel_soundU (infer_soundU hin hta) (infer_soundU hin htta)
      (red_soundU hin hu) hu0 (infer_soundU hin htb) (infer_soundU hin httb)
      (red_soundU hin hv) hv0
  | _, _, _, .structEta htb hwtb hhead hctor hlen hthead hind heta hetaCtor hresT
      hresc htlen hlv hlps hslots hus hcerts hproj hparams hfields =>
    DefEq.structEta_soundU hin (infer_soundU hin htb) (red_soundU hin hwtb) hhead
      hctor hlen hthead hind heta hetaCtor hresT hresc htlen hlv hlps hslots hus
      (certs_soundU hin hcerts) (fun hno => etaProjCerts_soundU hin (hproj hno))
      (defEqList_soundU hin hparams) (defEqList_soundU hin hfields)
  | _, _, _, .structUnit hta hwta hthead hind hunit hresT htlen hlv htb hwtb hd
      hcerts =>
    DefEq.structUnit_soundU hin (infer_soundU hin hta) (red_soundU hin hwta) hthead
      hind hunit hresT htlen hlv (infer_soundU hin htb) (red_soundU hin hwtb)
      (defeq_soundU hin hd) (certs_soundU hin hcerts)

theorem infer_soundU (hin : RulesInputs V m φ) :
    ∀ {g : Grade} {d : Nat} {e t : Expr}, Infer env g d e t → InferSem m φ g d e t
  | _, _, _, _, .sort => Infer.sort_sound
  | _, _, _, _, .fvar h => Infer.fvar_sound h
  | _, _, _, _, .const hf htower hus => Infer.const_sound hin hf htower hus
  | _, _, _, _, .natLit h => Infer.natLit_sound hin h
  | _, _, _, _, .strLit h => Infer.strLit_sound hin h
  | _, _, _, _, .forallE hs hu hbs hv hz =>
    Infer.forallE_sound (infer_soundU hin hs) (red_soundU hin hu).cond
      (infer_soundU hin hbs) (red_soundU hin hv).cond hz
  | _, _, _, _, .lam hs hu hbt hchain hbtt hv hz =>
    Infer.lam_sound (fun hg => infer_soundU hin (hs hg))
      (fun hg => (red_soundU hin (hu hg)).cond) (infer_soundU hin hbt)
      (fun _ _ _ hbody => by subst hbody; exact Infer.lam_shape hbt)
      hchain (fun hn => infer_soundU hin (hbtt hn))
      (fun hn => (red_soundU hin (hv hn)).cond) hz
  | _, _, _, _, .letE _ _ htv _ hb =>
    Infer.letE_sound (fun hg => infer_soundU hin (htv hg)) (infer_soundU hin hb)
  | _, _, _, _, .app htf hw hta hd =>
    Infer.app_sound (infer_soundU hin htf) (red_soundU hin hw).cond
      (infer_soundU hin hta) (defeq_soundU hin hd).cond
  | _, _, _, _, .appSkip htf hw hnev =>
    Infer.appSkip_sound (infer_soundU hin htf) (red_soundU hin hw).cond hnev
  | _, _, _, _, .proj htpe hte hhead hent hlen hus hprop =>
    Infer.proj_sound hin (infer_soundU hin htpe) (red_soundU hin hte).cond hhead hent
      hlen hus hprop

theorem certs_soundU (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {lic : Bool} {ty : Expr} {args : List Expr},
      Certs env d lic ty args → CertsSem m φ d lic ty args
  | _, _, _, _, .nil => Certs.nil_sound
  | _, _, _, _, .skip hlic hnev hrest =>
    Certs.skip_sound hlic hnev (certs_soundU hin hrest)
  | _, _, _, _, .cert hta hd hrest =>
    Certs.cert_sound (infer_soundU hin hta) (defeq_soundU hin hd).cond
      (certs_soundU hin hrest)

theorem certsF_soundU (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {ty : Expr} {args : List Expr},
      CertsF env d ty args → CertsFSem m φ d ty args
  | _, _, _, .nil => CertsF.nil_sound
  | _, _, _, .cert hta hd hrest =>
    CertsF.cert_sound (infer_soundU hin hta) (defeq_soundU hin hd).cond
      (certsF_soundU hin hrest)

theorem defEqList_soundU (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {as bs : List Expr},
      DefEqList env d as bs → DefEqListSemU m φ d as bs
  | _, _, _, .nil => DefEqList.nil_soundU
  | _, _, _, .cons h hs =>
    DefEqList.cons_soundU (defeq_soundU hin h) (defEqList_soundU hin hs)

theorem etaProjCerts_soundU (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {T : Name} {us' : List Level} {targs : List Expr} {b : Expr}
      {lpsT : List Name} {idxs : List Nat},
      EtaProjCerts env d T us' targs b lpsT idxs →
      EtaProjCertsSem m φ d T us' targs b lpsT idxs
  | _, _, _, _, _, _, _, .nil => EtaProjCerts.nil_sound
  | _, _, _, _, _, _, _, .cons hf hlps hstrip hcerts hrest =>
    EtaProjCerts.cons_sound hf hlps hstrip (certs_soundU hin hcerts)
      (etaProjCerts_soundU hin hrest)

end

/-! ## The conditional induction -/

mutual

theorem red_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {e e' : Expr}, Red env d e e' → RedSem m φ d e e'
  | _, _, _, .refl => Red.refl_sound
  | _, _, _, .trans h₁ h₂ =>
    Red.trans_sound (red_sound hin h₁) (red_sound hin h₂)
  | _, _, _, .appFn h => Red.appFn_sound (red_sound hin h)
  | _, _, _, .projArg h => Red.projArg_sound (red_sound hin h)
  | _, _, _, .beta _ _ => Red.beta_sound
  | _, _, _, .zeta => Red.zeta_sound
  | _, _, _, .delta h => Red.delta_sound hin h
  | _, _, _, .natLit h => Red.natLit_sound h
  | _, _, _, .strLit h => Red.strLit_sound h
  | _, _, _, .proj hent hhead hi hlen hus hfire hctor hcerts =>
    Red.proj_sound hin hent hhead hi hlen hus hfire hctor (certs_sound hin hcerts)
  -- **interim** (task #342, L12): the literal rows through the side induction
  | _, _, _, h@(.natSucc ..) => (red_soundU hin h).cond
  | _, _, _, h@(.natOp ..) => (red_soundU hin h).cond
  -- ι and the K/`And` rescues (task #342 L10): one lemma each, from the
  -- conditional claims of their premises
  | _, _, _, .iota hhead hrec hlen hus hmajor hmhead hctor hrule hmlen hfire hlv
      hparams hcertR hcertC hres hidx =>
    (Red.iota_sound hin hhead hrec hlen hus (red_sound hin hmajor) hmhead hctor
      hrule hmlen hfire hlv (fun hc => defEqList_sound hin (hparams hc))
      (certs_sound hin hcertR) (fun h3 => certsF_sound hin (hcertC h3)) hres
      (fun h3 hne => defEqList_sound hin (hidx h3 hne))).cond
  | _, _, _, .rescueK hrec hk hctor hres hind htm htmaj hthead hlv hnP hfab hws
      hb hlv' hcerts htf hdt hpi =>
    (Red.rescueK_sound hin hrec hk hctor hres hind (infer_sound hin htm)
      (red_sound hin htmaj) hthead hlv hnP hfab hws hb hlv'
      (certs_sound hin hcerts) (infer_sound hin htf) (defeq_sound hin hdt)
      (defeq_sound hin hpi)).cond
  | _, _, _, .rescueAnd hrec hctor hres hind htm htmaj hthead hlen hlv hslots
      hfab hws hb hlv' hcerts htf hdt hpi =>
    (Red.rescueAnd_sound hin hrec hctor hres hind (infer_sound hin htm)
      (red_sound hin htmaj) hthead hlen hlv hslots hfab hws hb hlv'
      (certs_sound hin hcerts) (infer_sound hin htf) (defeq_sound hin hdt)
      (defeq_sound hin hpi)).cond
  -- **interim** (task #342 L10 → the coherence-law lane): the structure-η
  -- rescue's certificate is read by its unconditional proof, through the
  -- side induction
  | _, _, _, h@(.rescueEta ..) => (red_soundU hin h).cond

theorem defeq_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {a b : Expr}, DefEq env d a b → DefEqSem m φ d a b
  | _, _, _, .refl => DefEq.refl_sound
  | _, _, _, .symm h => DefEq.symm_sound (defeq_sound hin h)
  | _, _, _, .redL hr h => DefEq.redL_sound (red_sound hin hr) (defeq_sound hin h)
  | _, _, _, .sort h => DefEq.sort_sound h
  | _, _, _, .fvar => DefEq.fvar_sound
  | _, _, _, .const h => DefEq.const_sound h
  | _, _, _, .natZero => DefEq.natZero_sound
  | _, _, _, .natSucc h => DefEq.natSucc_sound hin (defeq_sound hin h)
  | _, _, _, .forallE hty hbody hpw =>
    DefEq.forallE_sound (defeq_sound hin hty) (defeq_sound hin hbody) hpw
  | _, _, _, .app hf ha => DefEq.app_sound (defeq_sound hin hf) (defeq_sound hin ha)
  | _, _, _, .proj h => DefEq.proj_sound (defeq_sound hin h)
  | _, _, _, .proofFast ha hb => DefEq.proofFast_sound hin ha hb
  | _, _, _, .proofIrrel hta htta hu hu0 htb httb hv hv0 =>
    DefEq.proofIrrel_sound (infer_sound hin hta) (infer_sound hin htta)
      (red_sound hin hu) hu0 (infer_sound hin htb) (infer_sound hin httb)
      (red_sound hin hv) hv0
  | _, _, _, .structUnit hta hwta hthead hind hunit hresT htlen hlv htb hwtb hd
      hcerts =>
    DefEq.structUnit_sound hin (infer_sound hin hta) (red_sound hin hwta) hthead
      hind hunit hresT htlen hlv (infer_sound hin htb) (red_sound hin hwtb)
      (defeq_sound hin hd) (certs_sound hin hcerts)
  -- **interim** (task #342, L11 → S4): λ-congruence and η compare two
  -- bodies that nothing types alike under the annotated reading;
  -- structure η compares spines that nothing places in one telescope
  -- (`DefEqSound.lean`'s conditional section, the DESIGN record of L11)
  | _, _, _, h@(.lam ..) => (defeq_soundU hin h).cond
  | _, _, _, h@(.eta ..) => (defeq_soundU hin h).cond
  | _, _, _, h@(.structEta ..) => (defeq_soundU hin h).cond

theorem infer_sound (hin : RulesInputs V m φ) :
    ∀ {g : Grade} {d : Nat} {e t : Expr}, Infer env g d e t → InferSem m φ g d e t
  | _, _, _, _, .sort => Infer.sort_sound
  | _, _, _, _, .fvar h => Infer.fvar_sound h
  | _, _, _, _, .const hf htower hus => Infer.const_sound hin hf htower hus
  | _, _, _, _, .natLit h => Infer.natLit_sound hin h
  | _, _, _, _, .strLit h => Infer.strLit_sound hin h
  | _, _, _, _, .forallE hs hu hbs hv hz =>
    Infer.forallE_sound (infer_sound hin hs) (red_sound hin hu)
      (infer_sound hin hbs) (red_sound hin hv) hz
  | _, _, _, _, .lam hs hu hbt hchain hbtt hv hz =>
    Infer.lam_sound (fun hg => infer_sound hin (hs hg))
      (fun hg => red_sound hin (hu hg)) (infer_sound hin hbt)
      (fun _ _ _ hbody => by subst hbody; exact Infer.lam_shape hbt)
      hchain (fun hn => infer_sound hin (hbtt hn))
      (fun hn => red_sound hin (hv hn)) hz
  | _, _, _, _, .letE _ _ htv _ hb =>
    Infer.letE_sound (fun hg => infer_sound hin (htv hg)) (infer_sound hin hb)
  | _, _, _, _, .app htf hw hta hd =>
    Infer.app_sound (infer_sound hin htf) (red_sound hin hw)
      (infer_sound hin hta) (defeq_sound hin hd)
  | _, _, _, _, .appSkip htf hw hnev =>
    Infer.appSkip_sound (infer_sound hin htf) (red_sound hin hw) hnev
  | _, _, _, _, .proj htpe hte hhead hent hlen hus hprop =>
    Infer.proj_sound hin (infer_sound hin htpe) (red_sound hin hte) hhead hent
      hlen hus hprop

theorem certs_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {lic : Bool} {ty : Expr} {args : List Expr},
      Certs env d lic ty args → CertsSem m φ d lic ty args
  | _, _, _, _, .nil => Certs.nil_sound
  | _, _, _, _, .skip hlic hnev hrest =>
    Certs.skip_sound hlic hnev (certs_sound hin hrest)
  | _, _, _, _, .cert hta hd hrest =>
    Certs.cert_sound (infer_sound hin hta) (defeq_sound hin hd)
      (certs_sound hin hrest)

theorem certsF_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {ty : Expr} {args : List Expr},
      CertsF env d ty args → CertsFSem m φ d ty args
  | _, _, _, .nil => CertsF.nil_sound
  | _, _, _, .cert hta hd hrest =>
    CertsF.cert_sound (infer_sound hin hta) (defeq_sound hin hd)
      (certsF_sound hin hrest)

theorem defEqList_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {as bs : List Expr},
      DefEqList env d as bs → DefEqListSem m φ d as bs
  | _, _, _, .nil => DefEqList.nil_sound
  | _, _, _, .cons h hs =>
    DefEqList.cons_sound (defeq_sound hin h) (defEqList_sound hin hs)

end

theorem etaProjCerts_sound (hin : RulesInputs V m φ) :
    ∀ {d : Nat} {T : Name} {us' : List Level} {targs : List Expr} {b : Expr}
      {lpsT : List Name} {idxs : List Nat},
      EtaProjCerts env d T us' targs b lpsT idxs →
      EtaProjCertsSem m φ d T us' targs b lpsT idxs
  | _, _, _, _, _, _, _, .nil => EtaProjCerts.nil_sound
  | _, _, _, _, _, _, _, .cons hf hlps hstrip hcerts hrest =>
    EtaProjCerts.cons_sound hf hlps hstrip (certs_sound hin hcerts)
      (etaProjCerts_sound hin hrest)

/-! ## The global forms the inductive installer's readers consume -/

/-- An establishing inference claim, at every satisfying valuation of a
full context discipline. -/
theorem InferSemFull.global {d : Nat} {e t : Expr} (h : InferSemFull m φ d e t)
    (hf : Frame d e) {Δa : List AnnotTerm} {ea : AnnotTerm}
    (hC : CtxOk m φ d Δa e) (hea : denoteMeta m.acval env φ d e = some ea) :
    Frame d t ∧ LeavesSub t e ∧
      ∃ ta, denoteMeta m.acval env φ d t = some ta ∧
        Graded V Δa ea ∧ GradedTy V Δa ta ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ∈ˢ interp V ρ ta := by
  obtain ⟨hft, hsub, ta, hta, hs⟩ := h hf hC.toS hea
  exact ⟨hft, hsub, ta, hta, fun ρ hρ => (hs ρ hρ (hC.leavesGr hρ)).1,
    fun ρ hρ => (hs ρ hρ (hC.leavesGr hρ)).2.1,
    fun ρ hρ => (hs ρ hρ (hC.leavesGr hρ)).2.2⟩

/-- **Interim** (task #342, L12): a reduction of a globally graded
subject, unconditionally, through the side induction.  The positivity
readers (`Model/Inductives/Pos*`, `NestPosRed`) walk types and read their
whnf steps through it; once they carry the walked types' `IsTy`, the
conditional `red_sound` serves them ("not pt" source (1)). -/
theorem red_sound_global (hin : RulesInputs V m φ) {d : Nat} {e e' : Expr}
    (h : Red env d e e') (hf : Frame d e) {Δa : List AnnotTerm} {ea : AnnotTerm}
    (hC : CtxOk m φ d Δa e) (hea : denoteMeta m.acval env φ d e = some ea)
    (hg : Graded V Δa ea) :
    Frame d e' ∧ LeavesSub e' e ∧
      ∃ ea', denoteMeta m.acval env φ d e' = some ea' ∧ Graded V Δa ea' ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ea' := by
  obtain ⟨hf', hsub, ea', hea', hs⟩ := red_soundU hin h hf hC.toS hea
  exact ⟨hf', hsub, ea', hea', fun ρ hρ => (hs ρ hρ (hC.leavesGr hρ) (hg ρ hρ)).1,
    fun ρ hρ => (hs ρ hρ (hC.leavesGr hρ) (hg ρ hρ)).2⟩

/-- **Interim** (task #342, L10/L12): a comparison of two globally
graded sides, unconditionally, through the side induction.  The
recursor-class match (`Model/Inductives/TargetDefeqTie.lean`) compares
PARAMETERS, which may be proofs; under the conditional claims it needs
the parameters' telescope (`spineFit_eq_of_cond`, as `blockRule_coherent`
does for the block rules). -/
theorem defeq_sound_global (hin : RulesInputs V m φ) {d : Nat} {a b : Expr}
    (h : DefEq env d a b) (hfa : Frame d a) (hfb : Frame d b)
    {Δa : List AnnotTerm} {aa ba : AnnotTerm}
    (hCa : CtxOk m φ d Δa a) (hCb : CtxOk m φ d Δa b)
    (haa : denoteMeta m.acval env φ d a = some aa)
    (hba : denoteMeta m.acval env φ d b = some ba)
    (hga : Graded V Δa aa) (hgb : Graded V Δa ba) :
    ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ aa = interp V ρ ba := fun ρ hρ =>
  defeq_soundU hin h hfa hfb hCa.toS hCb.toS haa hba ρ hρ (hCa.leavesGr hρ)
    (hCb.leavesGr hρ) (hga ρ hρ) (hgb ρ hρ)

end ConLeche.Model.Rules
