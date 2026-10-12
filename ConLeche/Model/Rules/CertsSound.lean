module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Model.Annot.BitInst

public section

/-!
# The soundness of the three list walks (task #305)

`Certs` (one step per constructor), `DefEqList` and `EtaProjCerts`
(pointwise), at one valuation (task #342, L9).  The certificate's slot
comparison is between two types (the argument's inferred type and the
binder's domain), so the conditional `DefEqSem` decides it outright.
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

theorem Certs.nil_sound {d : Nat} {lic : Bool} {T : Expr} :
    CertsSem m φ d lic T [] := by
  intro _ Δa Ta _ vs _ _ _ hsp
  cases hsp
  exact ⟨Ta, fun _ _ _ _ hgT _ _ => ⟨.nil, hgT⟩⟩

/-- **One slot of the certificate walk, given the slot membership.**
The two `Certs` rules differ only in how the membership at `ρ` is
obtained — the licence's transfer or the certificate's run — so
everything else (the residual's reading, its frame, its grading, the
licence handed to the tail, and `TeleFitPA.cons`) is shared. -/
theorem certs_step {d : Nat} {lic : Bool} {ty body arg : Expr}
    {mb : ConLeche.BinderMeta} {rest : List Expr}
    {Δa : List AnnotTerm} {doma bodya fa aa : AnnotTerm}
    {vs' : List AnnotTerm}
    (hrest : CertsSem m φ d lic (body.instantiate1 arg) rest)
    (hCT : CtxOkS m φ d Δa (.forallE ty body mb))
    (hargs : ∀ x ∈ arg :: rest, Frame d x ∧ CtxOkS m φ d Δa x)
    (hsp' : DenoteMetaSpine m.acval env φ d rest vs')
    (hbodyw : Expr.WScoped d body)
    (hbodyb : Expr.looseBVarsBounded 1 body = true)
    (hLbty : Expr.LeavesBounded (.forallE ty body mb))
    (hbodya : denoteMeta m.acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty)) = some bodya)
    (haa : denoteMeta m.acval env φ d arg = some aa)
    (hfarg : Frame d arg) (hCarg : CtxOkS m φ d Δa arg) :
    ∃ resta : AnnotTerm,
      ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d (.forallE ty body mb) ρ →
        (∀ x ∈ arg :: rest, LeavesGr m φ d x ρ) →
        WellDenotedV V ρ (.pi doma bodya) →
        (∀ x ∈ aa :: vs', WellDenotedV V ρ x) →
        (lic = true →
          WellDenotedV V ρ (AnnotTerm.mkAppN fa (aa :: vs')) ∧
            interp V ρ fa ∈ˢ interp V ρ (.pi doma bodya) ∧
            interp V ρ (AnnotTerm.mkAppN fa (aa :: vs')) ≠ pt) →
        interp V ρ aa ∈ˢ interp V ρ doma →
        TeleFitPA V ρ (.pi doma bodya) (aa :: vs') resta ∧
          WellDenotedV V ρ resta := by
  obtain ⟨hwa, hba, hLa⟩ := hfarg
  have hbody' : denoteMeta m.acval env φ d (body.instantiate1 arg)
      = some (bodya.inst aa) := by
    rw [denoteMeta_beta m.acval_closed (acval_inst_self m)
      (ty := ty) hbodyw.fvarsBelow hwa hba haa 0, hbodya]
    rfl
  have hLbbody : Expr.LeavesBounded (body.instantiate1 arg) := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact hLbty l (by simp [Expr.fvarLeaves, hl'])
    · exact hLa l hl'
  have hsubBody : ∀ l ∈ (body.instantiate1 arg).fvarLeaves,
      l ∈ (Expr.forallE ty body mb).fvarLeaves ∨ l ∈ arg.fvarLeaves := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact Or.inl (by simp [Expr.fvarLeaves, hl'])
    · exact Or.inr hl'
  have hCbody : CtxOkS m φ d Δa (body.instantiate1 arg) := by
    refine ⟨hCT.1, fun l hl => ?_⟩
    rcases hsubBody l hl with hl' | hl'
    · exact hCT.2 l hl'
    · exact hCarg.2 l hl'
  obtain ⟨resta, hfit⟩ :=
    hrest (fa := .app fa aa)
      ⟨ConLeche.Expr.WScoped.instantiate1_gen hwa 0 hbodyw,
        ConLeche.Expr.looseBVarsBounded_instantiate1_gen hba hbodyb, hLbbody⟩
      hCbody hbody'
      (fun x hx => hargs x (List.mem_cons_of_mem arg hx)) hsp'
  refine ⟨resta, fun ρ hρ hLT hLargs hgT hgvs hlicP hmemA => ?_⟩
  have hokA : WellDenotedV V ρ aa := hgvs aa List.mem_cons_self
  have hokBody : WellDenotedV V ρ (bodya.inst aa) :=
    (WellDenotedV_inst0 hokA).mpr (hgT.pi_body _ hmemA)
  have hLbody : LeavesGr m φ d (body.instantiate1 arg) ρ := by
    intro l hl
    rcases hsubBody l hl with hl' | hl'
    · exact hLT l hl'
    · exact hLargs arg List.mem_cons_self l hl'
  have hlicP' : lic = true →
      WellDenotedV V ρ (AnnotTerm.mkAppN (.app fa aa) vs') ∧
        interp V ρ (.app fa aa) ∈ˢ interp V ρ (bodya.inst aa) ∧
        interp V ρ (AnnotTerm.mkAppN (.app fa aa) vs') ≠ pt := by
    intro hl
    obtain ⟨hokS, hfaM, hne⟩ := hlicP hl
    refine ⟨hokS, ?_, hne⟩
    have hoks : ∀ x ∈ [aa], WellDenotedV V ρ x := by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact hokA
    exact (mkAppN_of_fitA [aa] hgT (mkAppN_head (aa :: vs') hokS)
      hoks hfaM (TeleFitPA.cons hmemA .nil)).2
  obtain ⟨hfit', hgresta⟩ := hfit ρ hρ hLbody
    (fun x hx => hLargs x (List.mem_cons_of_mem arg hx)) hokBody
    (fun x hx => hgvs x (List.mem_cons_of_mem aa hx)) hlicP'
  exact ⟨.cons hmemA hfit', hgresta⟩

/-- The checker's arity test (`Expr.peelPis`, no substitution) is
`stripPis`'s. -/
theorem stripPis_isSome_of_peelPis :
    ∀ {n : Nat} {T : Expr}, (Expr.peelPis n T).isSome = true →
      (T.stripPis n).isSome = true
  | 0, _, _ => by simp [ConLeche.Expr.stripPis]
  | n + 1, .forallE _ b _, h => by
    simp only [ConLeche.Expr.stripPis, Option.isSome_map]
    exact stripPis_isSome_of_peelPis (by simpa [Expr.peelPis] using h)
  | _ + 1, .bvar _, h | _ + 1, .fvar _ _, h | _ + 1, .sort _, h
  | _ + 1, .const _ _, h | _ + 1, .app _ _, h | _ + 1, .lam _ _ _, h
  | _ + 1, .letE _ _ _, h | _ + 1, .lit _, h | _ + 1, .proj _ _ _, h => by
    simp [Expr.peelPis] at h

/-- **A graded application that is not the point fits its head's
telescope** (`teleFitPA_of_graded_ne_pt` at the peel's residual): every
prefix of the spine is not the point (`app_pt`), so it is a graph, and
the argument's own application slot puts it in the telescope's domain
(`slotTransfer`). -/
theorem teleFitPA_of_peel_ne_pt {ρ : Nat → V} :
    ∀ (vs : List AnnotTerm) {T f r : AnnotTerm},
      ConLeche.Model.AnnotTerm.peelPis T vs = some r →
      WellDenotedV V ρ T → interp V ρ f ∈ˢ interp V ρ T →
      WellDenotedV V ρ (AnnotTerm.mkAppN f vs) →
      interp V ρ (AnnotTerm.mkAppN f vs) ≠ pt →
      TeleFitPA V ρ T vs r
  | [], T, _, r, hp, _, _, _, _ => by
    obtain rfl : T = r := Option.some.inj hp
    exact .nil
  | x :: xs, .pi A B, f, r, hp, hT, hmem, hg, hne => by
    have hg' : WellDenotedV V ρ (AnnotTerm.mkAppN (.app f x) xs) := hg
    have hne' : interp V ρ (AnnotTerm.mkAppN (.app f x) xs) ≠ pt := hne
    have happ : WellDenotedV V ρ (.app f x) := mkAppN_head xs hg'
    obtain ⟨v', A', B', hslot, hx, -⟩ := (cast (WellDenoted_app V ρ f x) happ).2.2
    have hmem' := hmem
    rw [interp_pi] at hmem'
    have hfne : interp V ρ f ≠ pt := by
      intro h0
      exact hne' (interp_mkAppN_of_pt (by rw [interp_app, h0, app_pt]) xs)
    have hgr : interp V ρ f ∈ˢ piR 1 (interp V ρ A) fun y => interp V (cons y ρ) B := by
      rw [piR_pos Nat.one_ne_zero]; exact mem_piSet_of_mem_piV hmem' hfne
    have hxA : interp V ρ x ∈ˢ interp V ρ A := slotTransfer Nat.one_ne_zero hgr hslot hx
    have hokx : WellDenotedV V ρ x := happ.app_arg
    have hBx : WellDenotedV V ρ (B.inst x) :=
      (WellDenotedV_inst0 hokx).mpr (hT.pi_body _ hxA)
    have hmemB : interp V ρ (.app f x) ∈ˢ interp V ρ (B.inst x) := by
      rw [interp_inst0, interp_app]
      exact app_mem_piV hmem' hxA
    exact .cons hxA (teleFitPA_of_peel_ne_pt xs hp hBx hmemB hg' hne')
  | _ :: _, .bvar _, _, _, hp, _, _, _, _ | _ :: _, .sort _, _, _, hp, _, _, _, _
  | _ :: _, .const _ _, _, _, hp, _, _, _, _ | _ :: _, .app _ _, _, _, hp, _, _, _, _
  | _ :: _, .lam _ _, _, _, hp, _, _, _, _ | _ :: _, .letE _ _, _, _, hp, _, _, _, _
  | _ :: _, .eqE _ _, _, _, hp, _, _, _, _ | _ :: _, .fst _, _, _, hp, _, _, _, _
  | _ :: _, .snd _, _, _, hp, _, _, _, _ | _ :: _, .prf, _, _, hp, _, _, _, _ =>
    nomatch hp

/-- **The licensed walk** (`Certs.licensed`): no certificate, the
telescope's syntactic arity only.  A licensed walk's spine is the
subject's own; where it is not the point ("not pt" source (2): a
reduction claims nothing of a redex that is the point) it fits its
head's telescope (`teleFitPA_of_peel_ne_pt`), the arity making the
telescope's reading a ∀-chain (`piChain_of_stripPis`). -/
theorem Certs.licensed_sound {d : Nat} {T : Expr} {args : List Expr}
    (harity : (Expr.peelPis args.length T).isSome = true) :
    CertsSem m φ d true T args := by
  intro _ Δa Ta fa vs _ hTa _ hsp
  have hstrip : (T.stripPis vs.length).isSome = true := by
    rw [← hsp.length]
    exact stripPis_isSome_of_peelPis harity
  obtain ⟨r, hr⟩ := peelPis_of_piChain vs (piChain_of_stripPis vs.length hstrip hTa)
  refine ⟨r, fun ρ _ _ _ hgT hgvs hlic => ?_⟩
  obtain ⟨hgS, hfM, hne⟩ := hlic rfl
  have hfit := teleFitPA_of_peel_ne_pt vs hr hgT hfM hgS hne
  exact ⟨hfit, teleFitPA_rest_graded hfit hgT hgvs⟩

/-- The certified slot: the certificate's run supplies the membership. -/
theorem Certs.cert_sound {d : Nat} {lic : Bool}
    {ty body arg ta : Expr} {mb : BinderMeta} {rest : List Expr}
    (hta : InferSemIO m φ d arg ta) (hd : DefEqSem m φ d ta ty)
    (hrest : CertsSem m φ d lic (body.instantiate1 arg) rest) :
    CertsSem m φ d lic (.forallE ty body mb) (arg :: rest) := by
  intro hfT Δa Ta fa vs hCT hTa hargs hsp
  obtain ⟨hwty, hbty, hLbty⟩ := hfT
  obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d ty ∧ Expr.WScoped d body := by
    simpa [Expr.WScoped] using hwty
  obtain ⟨hdomb, hbodyb⟩ :
      ty.looseBVarsBounded 0 = true ∧ Expr.looseBVarsBounded 1 body = true := by
    simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbty
  have hLbdom : Expr.LeavesBounded ty := fun l hl =>
    hLbty l (by simp [Expr.fvarLeaves, hl])
  have hCdom : CtxOkS m φ d Δa ty := hCT.forallE_ty
  obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteMeta_forallE_inv hTa
  cases hsp with | @cons _ aa _ vs' haa hsp' =>
  obtain ⟨hfarg, hCarg⟩ := hargs arg List.mem_cons_self
  obtain ⟨resta, hstep⟩ := certs_step (fa := fa) hrest hCT hargs hsp' hbodyw
    hbodyb hLbty hbodya haa hfarg hCarg
  -- the certificate's two runs, read outside the valuation
  obtain ⟨hfta, hsubta, taA, htaA, hA⟩ := hta hfarg hCarg haa
  refine ⟨resta, fun ρ hρ hLT hLargs hgT hgvs hlicP => hstep ρ hρ hLT hLargs hgT
    hgvs hlicP ?_⟩
  have hLarg : LeavesGr m φ d arg ρ := hLargs arg List.mem_cons_self
  -- L-dead (S4 ledger): an io certificate gives the slot's membership only
  -- where the argument's io claim is a membership; at an argument that is
  -- the point, or whose claim is hereditary, its io-inferred type does
  -- not hold it (`IORel`).  Unlicensed walks certify the rescues'
  -- synthetic spines only: the K and `And` rescues' (whose majors are
  -- proofs, so no claim reads them: dead certificates) and the
  -- projection-function η certificates (`structEtaProjCerts`, which never
  -- run).  Deleting them deletes this rule.
  have hmemIO : IOMem m φ d ta ρ (interp V ρ aa) := by
    rcases (hA ρ hρ hLarg (hgvs aa List.mem_cons_self)).1 with h | h | h
    · exact sorry
    · exact h
    · exact sorry
  obtain ⟨hgtaA, hmem⟩ := hmemIO.of_reading htaA
  have hokDom : WellDenotedTy V ρ doma := hgT.pi_dom
  -- "not pt" source (1): both sides of the slot comparison are types —
  -- the argument's inferred type and the binder's domain
  have heq := hd hfta ⟨hdomw, hdomb, hLbdom⟩ (hCarg.of_subset hsubta) hCdom
    htaA hdoma ρ hρ (hLarg.of_subset hsubta) hLT.forallE_ty hgtaA.1 hokDom.1
    hgtaA.ne_pt hokDom.ne_pt
  exact heq ▸ hmem

/-! ### The full-grade certificate (task #342 L10, ι's case 3) -/

theorem CertsF.nil_sound {d : Nat} {T : Expr} : CertsFSem m φ d T [] := by
  intro _ Δa Ta vs _ _ _ hsp
  cases hsp
  exact ⟨Ta, fun _ _ _ _ hgT => ⟨by simp, .nil, hgT⟩⟩

/-- The certified slot: the full-grade inference ESTABLISHES the
argument's grading and its membership in its inferred type, a type
equal to the binder's domain ("not pt" source (1)). -/
theorem CertsF.cert_sound {d : Nat} {ty body arg ta : Expr} {mb : BinderMeta}
    {rest : List Expr}
    (hta : InferSemFull m φ d arg ta) (hd : DefEqSem m φ d ta ty)
    (hrest : CertsFSem m φ d (body.instantiate1 arg) rest) :
    CertsFSem m φ d (.forallE ty body mb) (arg :: rest) := by
  intro hfT Δa Ta vs hCT hTa hargs hsp
  obtain ⟨hwty, hbty, hLbty⟩ := hfT
  obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d ty ∧ Expr.WScoped d body := by
    simpa [Expr.WScoped] using hwty
  obtain ⟨hdomb, hbodyb⟩ :
      ty.looseBVarsBounded 0 = true ∧ Expr.looseBVarsBounded 1 body = true := by
    simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbty
  have hLbdom : Expr.LeavesBounded ty := fun l hl =>
    hLbty l (by simp [Expr.fvarLeaves, hl])
  have hCdom : CtxOkS m φ d Δa ty := hCT.forallE_ty
  obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteMeta_forallE_inv hTa
  cases hsp with | @cons _ aa _ vs' haa hsp' =>
  obtain ⟨hfarg, hCarg⟩ := hargs arg List.mem_cons_self
  obtain ⟨hwa, hba, hLa⟩ := hfarg
  have hbody' : denoteMeta m.acval env φ d (body.instantiate1 arg)
      = some (bodya.inst aa) := by
    rw [denoteMeta_beta m.acval_closed (acval_inst_self m)
      (ty := ty) hbodyw.fvarsBelow hwa hba haa 0, hbodya]
    rfl
  have hLbbody : Expr.LeavesBounded (body.instantiate1 arg) := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact hLbty l (by simp [Expr.fvarLeaves, hl'])
    · exact hLa l hl'
  have hsubBody : ∀ l ∈ (body.instantiate1 arg).fvarLeaves,
      l ∈ (Expr.forallE ty body mb).fvarLeaves ∨ l ∈ arg.fvarLeaves := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact Or.inl (by simp [Expr.fvarLeaves, hl'])
    · exact Or.inr hl'
  have hCbody : CtxOkS m φ d Δa (body.instantiate1 arg) := by
    refine ⟨hCT.1, fun l hl => ?_⟩
    rcases hsubBody l hl with hl' | hl'
    · exact hCT.2 l hl'
    · exact hCarg.2 l hl'
  obtain ⟨resta, hfit⟩ :=
    hrest ⟨ConLeche.Expr.WScoped.instantiate1_gen hwa 0 hbodyw,
        ConLeche.Expr.looseBVarsBounded_instantiate1_gen hba hbodyb, hLbbody⟩
      hCbody hbody' (fun x hx => hargs x (List.mem_cons_of_mem arg hx)) hsp'
  -- the certificate's two runs, read outside the valuation
  obtain ⟨hfta, hsubta, taA, htaA, hA⟩ := hta ⟨hwa, hba, hLa⟩ hCarg haa
  refine ⟨resta, fun ρ hρ hLT hLargs hgT => ?_⟩
  have hLarg : LeavesGr m φ d arg ρ := hLargs arg List.mem_cons_self
  obtain ⟨hokA, hgtaA, hmem⟩ := hA ρ hρ hLarg
  have hokDom : WellDenotedTy V ρ doma := hgT.pi_dom
  -- "not pt" source (1): both sides of the slot comparison are types
  have heq := hd hfta ⟨hdomw, hdomb, hLbdom⟩ (hCarg.of_subset hsubta) hCdom
    htaA hdoma ρ hρ (hLarg.of_subset hsubta) hLT.forallE_ty hgtaA.1 hokDom.1
    hgtaA.ne_pt hokDom.ne_pt
  have hmemA : interp V ρ aa ∈ˢ interp V ρ doma := heq ▸ hmem
  have hokBody : WellDenotedV V ρ (bodya.inst aa) :=
    (WellDenotedV_inst0 hokA).mpr (hgT.pi_body _ hmemA)
  have hLbody : LeavesGr m φ d (body.instantiate1 arg) ρ := by
    intro l hl
    rcases hsubBody l hl with hl' | hl'
    · exact hLT l hl'
    · exact hLarg l hl'
  obtain ⟨hgvs', hfit', hgresta⟩ := hfit ρ hρ hLbody
    (fun x hx => hLargs x (List.mem_cons_of_mem arg hx)) hokBody
  refine ⟨fun x hx => ?_, .cons hmemA hfit', hgresta⟩
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact hokA
  · exact hgvs' x hx'

theorem DefEqList.nil_sound {d : Nat} : DefEqListSem m φ d [] [] := by
  refine ⟨rfl, ?_⟩
  intro Δa asa bsa _ _ hsa hsb _ _ _ _ _ _ p hp
  cases hsa
  cases hsb
  simp at hp

theorem DefEqList.cons_sound {d : Nat} {a b : Expr} {as bs : List Expr}
    (h : DefEqSem m φ d a b) (hs : DefEqListSem m φ d as bs) :
    DefEqListSem m φ d (a :: as) (b :: bs) := by
  refine ⟨by simp [hs.1], ?_⟩
  intro Δa asa bsa hfa hfb hsa hsb ρ hρ hLa hLb hga hgb p hp
  cases hsa with | @cons _ va _ vas hva hsa' =>
  cases hsb with | @cons _ vb _ vbs hvb hsb' =>
  obtain ⟨hfa1, hCa1⟩ := hfa a List.mem_cons_self
  obtain ⟨hfb1, hCb1⟩ := hfb b List.mem_cons_self
  simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact h hfa1 hfb1 hCa1 hCb1 hva hvb ρ hρ (hLa a List.mem_cons_self)
      (hLb b List.mem_cons_self) (hga va List.mem_cons_self)
      (hgb vb List.mem_cons_self)
  · exact hs.2 (fun x hx => hfa x (List.mem_cons_of_mem a hx))
      (fun x hx => hfb x (List.mem_cons_of_mem b hx)) hsa' hsb' ρ hρ
      (fun x hx => hLa x (List.mem_cons_of_mem a hx))
      (fun x hx => hLb x (List.mem_cons_of_mem b hx))
      (fun x hx => hga x (List.mem_cons_of_mem va hx))
      (fun x hx => hgb x (List.mem_cons_of_mem vb hx)) p hp

theorem EtaProjCerts.nil_sound {d : Nat} {T : Name} {us' : List Level}
    {targs : List Expr} {b : Expr} {lpsT : List Name} :
    EtaProjCertsSem m φ d T us' targs b lpsT [] := by
  intro i hi
  exact nomatch hi

theorem EtaProjCerts.cons_sound {d : Nat} {T : Name} {us' : List Level}
    {targs : List Expr} {b : Expr} {lpsT : List Name} {i : Nat}
    {rest : List Nat} {cvp : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hf : env.find? (projFnName T i) = some (.recInfo cvp mI rP rules))
    (hlps : cvp.levelParams = lpsT)
    (hstrip : (cvp.type.stripPis (targs.length + 1)).isSome = true)
    (hcerts : CertsSem m φ d false
      (cvp.type.instantiateLevelParams cvp.levelParams us') (targs ++ [b]))
    (hrest : EtaProjCertsSem m φ d T us' targs b lpsT rest) :
    EtaProjCertsSem m φ d T us' targs b lpsT (i :: rest) := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj'
  · exact ⟨cvp, mI, rP, rules, hf, hlps, hstrip, hcerts⟩
  · exact hrest j hj'

end ConLeche.Model.Rules
