module

public import Fragment.Consistency
public import Fragment.Install
public import Fragment.Access
public import Fragment.UniformBeta
public import Fragment.Unannot

public section

/-!
# The axiom pin

The fragment's theorems use exactly Lean's three standard axioms and
nothing else — in particular no `sorryAx` and no axiom of the
fragment's own: the library `SetLib` and the level oracle
`LevelOracle` are *class parameters* of every theorem, not axioms.
`whitepaper/fragment-gate.sh` builds this file; a change in the list
is a build error here.
-/

/--
info: 'Fragment.soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.soundness

/--
info: 'Fragment.closed_infer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.closed_infer

/--
info: 'Fragment.install_def' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.install_def

/--
info: 'Fragment.install_ind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.install_ind

/--
info: 'Fragment.accepted_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.accepted_model

/--
info: 'Fragment.no_empty_inductive_inhabitant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.no_empty_inductive_inhabitant

/--
info: 'Fragment.no_empty_prop_inhabitant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.no_empty_prop_inhabitant

/--
info: 'Fragment.Red.iotaNested_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iotaNested_sound

/--
info: 'Fragment.IndSpec.famOp_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.famOp_mono

/--
info: 'Fragment.IndSpec.famOp_acc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.famOp_acc

/--
info: 'Fragment.IndSpec.Fam_psK_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.Fam_psK_mono

/--
info: 'Fragment.IndSpec.Fam_psK_acc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.Fam_psK_acc

/--
info: 'Fragment.IndSpec.contClause_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.contClause_of

/--
info: 'Fragment.lfpP_acc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.lfpP_acc

/--
info: 'Fragment.IndSpec.classLaws_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.classLaws_of

/--
info: 'Fragment.IndSpec.RecGraphN_fun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.RecGraphN_fun

/--
info: 'Fragment.IndSpec.RecGraphN_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.RecGraphN_total

/--
info: 'Fragment.IndSpec.recSemN_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.recSemN_eq

/--
info: 'Fragment.IndSpec.rec1Sem_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.rec1Sem_eq

/--
info: 'Fragment.IndSpec.rec_rule_lawN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.rec_rule_lawN

/--
info: 'Fragment.IndSpec.rec_rule_law1N' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.rec_rule_law1N

/--
info: 'Fragment.install_nest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.install_nest

/--
info: 'Fragment.install_ind_any' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.install_ind_any

/--
info: 'Fragment.AccIter.closed_of_acc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.AccIter.closed_of_acc

/--
info: 'Fragment.lfpFamSet_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.lfpFamSet_eq

/--
info: 'Fragment.lfpFamSet_induction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.lfpFamSet_induction

/--
info: 'Fragment.badEnv_no_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.badEnv_no_model

/--
info: 'Fragment.Red.beta_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.beta_sound

/--
info: 'Fragment.major_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.major_eq

/--
info: 'Fragment.Red.iota_core' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iota_core

/--
info: 'Fragment.DefEq.lam_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEq.lam_sound

/--
info: 'Fragment.DefEq.eta_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEq.eta_sound

/--
info: 'Fragment.DefEq.pi_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEq.pi_sound

/--
info: 'Fragment.lam_congr_untyped_unsound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.lam_congr_untyped_unsound

/--
info: 'Fragment.SetLib.lamV_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.SetLib.lamV_mem

/--
info: 'Fragment.SetLib.lamV_eta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.SetLib.lamV_eta

/--
info: 'Fragment.SetLib.piV_mem_typeU' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.SetLib.piV_mem_typeU

/--
info: 'Fragment.piV_empty_not_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.piV_empty_not_strict

/--
info: 'Fragment.IndSpec.adm_Fam_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.adm_Fam_of

/--
info: 'Fragment.IndSpec.class_reading' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.class_reading
