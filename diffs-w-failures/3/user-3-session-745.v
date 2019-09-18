Time From stdpp Require Import nat_cancel.
Time From iris.bi Require Import bi tactics telescopes.
Time
From iris.proofmode Require Import base modality_instances classes
  ltac_tactics.
Time Set Default Proof Using "Type".
Time Import bi.
Time Section bi_instances.
Time Context {PROP : bi}.
Time Implicit Types P Q R : PROP.
Time Implicit Type mP : option PROP.
Time #[global]
Instance as_emp_valid_emp_valid  P: (AsEmpValid0 (bi_emp_valid P) P) |0.
Time Proof.
Time by rewrite /AsEmpValid.
Time Qed.
Time #[global]
Instance as_emp_valid_entails  P Q: (AsEmpValid0 (P \226\138\162 Q) (P -\226\136\151 Q)).
Time Proof.
Time split.
Time (apply bi.entails_wand).
Time (apply bi.wand_entails).
Time Qed.
Time #[global]
Instance as_emp_valid_equiv  P Q: (AsEmpValid0 (P \226\137\161 Q) (P \226\136\151-\226\136\151 Q)).
Time Proof.
Time split.
Time (apply bi.equiv_wand_iff).
Time (apply bi.wand_iff_equiv).
Time Qed.
Time #[global]
Instance as_emp_valid_forall  {A : Type} (\207\134 : A \226\134\146 Prop) 
 (P : A \226\134\146 PROP):
 ((\226\136\128 x, AsEmpValid (\207\134 x) (P x)) \226\134\146 AsEmpValid (\226\136\128 x, \207\134 x) (\226\136\128 x, P x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /AsEmpValid =>H1).
Time (<ssreflect_plugin::ssrtclintros@0> split =>H2).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply bi.forall_intro =>?).
Time (apply H1, H2).
Time -
Time (intros x).
Time (apply H1).
Time revert H2.
Time by rewrite (bi.forall_elim x).
Time Qed.
Time #[global]
Instance as_emp_valid_embed  `{BiEmbed PROP PROP'} 
 (\207\134 : Prop) (P : PROP):
 (BiEmbed PROP PROP' \226\134\146 AsEmpValid0 \207\134 P \226\134\146 AsEmpValid \207\134 \226\142\161 P \226\142\164).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /AsEmpValid0 /AsEmpValid =>_
 {+}->).
Time rewrite embed_emp_valid //.
Time Qed.
Time #[global]
Instance from_affinely_affine  P: (Affine P \226\134\146 FromAffinely P P).
Time Proof.
Time (intros).
Time by rewrite /FromAffinely affinely_elim.
Time Qed.
Time #[global]
Instance from_affinely_default  P: (FromAffinely (<affine> P) P) |100.
Time Proof.
Time by rewrite /FromAffinely.
Time Qed.
Time #[global]
Instance from_affinely_intuitionistically  P: (FromAffinely (\226\150\161 P) (<pers> P))
 |100.
Time Proof.
Time by rewrite /FromAffinely.
Time Qed.
Time #[global]
Instance into_absorbingly_True : (@IntoAbsorbingly PROP True emp) |0.
Time Proof.
Time by rewrite /IntoAbsorbingly -absorbingly_True_emp absorbingly_pure.
Time Qed.
Time #[global]
Instance into_absorbingly_absorbing  P: (Absorbing P \226\134\146 IntoAbsorbingly P P)
 |1.
Time Proof.
Time (intros).
Time by rewrite /IntoAbsorbingly absorbing_absorbingly.
Time Qed.
Time #[global]
Instance into_absorbingly_intuitionistically  P:
 (IntoAbsorbingly (<pers> P) (\226\150\161 P)) |2.
Time Proof.
Time
by rewrite /IntoAbsorbingly -absorbingly_intuitionistically_into_persistently.
Time Qed.
Time #[global]
Instance into_absorbingly_default  P: (IntoAbsorbingly (<absorb> P) P) |100.
Time Proof.
Time by rewrite /IntoAbsorbingly.
Time Qed.
Time #[global]Instance from_assumption_exact  p P: (FromAssumption p P P) |0.
Time Proof.
Time by rewrite /FromAssumption /= intuitionistically_if_elim.
Time Qed.
Time #[global]
Instance from_assumption_persistently_r  P Q:
 (FromAssumption true P Q \226\134\146 KnownRFromAssumption true P (<pers> Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownRFromAssumption
 /FromAssumption /= =>{+}<-).
Time (apply intuitionistically_persistent).
Time Qed.
Time #[global]
Instance from_assumption_affinely_r  P Q:
 (FromAssumption true P Q \226\134\146 KnownRFromAssumption true P (<affine> Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownRFromAssumption
 /FromAssumption /= =>{+}<-).
Time by rewrite affinely_idemp.
Time Qed.
Time #[global]
Instance from_assumption_intuitionistically_r  P Q:
 (FromAssumption true P Q \226\134\146 KnownRFromAssumption true P (\226\150\161 Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownRFromAssumption
 /FromAssumption /= =>{+}<-).
Time by rewrite intuitionistically_idemp.
Time Qed.
Time #[global]
Instance from_assumption_absorbingly_r  p P Q:
 (FromAssumption p P Q \226\134\146 KnownRFromAssumption p P (<absorb> Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownRFromAssumption
 /FromAssumption /= =>{+}<-).
Time (apply absorbingly_intro).
Time Qed.
Time #[global]
Instance from_assumption_intuitionistically_l  p P 
 Q: (FromAssumption true P Q \226\134\146 KnownLFromAssumption p (\226\150\161 P) Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownLFromAssumption
 /FromAssumption /= =>{+}<-).
Time by rewrite intuitionistically_if_elim.
Time Qed.
Time #[global]
Instance from_assumption_persistently_l_true  P Q:
 (FromAssumption true P Q \226\134\146 KnownLFromAssumption true (<pers> P) Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownLFromAssumption
 /FromAssumption /= =>{+}<-).
Time rewrite intuitionistically_persistently_elim //.
Time Qed.
Time #[global]
Instance from_assumption_persistently_l_false  `{BiAffine PROP} 
 P Q: (FromAssumption true P Q \226\134\146 KnownLFromAssumption false (<pers> P) Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownLFromAssumption
 /FromAssumption /= =>{+}<-).
Time by rewrite intuitionistically_into_persistently.
Time Qed.
Time #[global]
Instance from_assumption_affinely_l_true  p P Q:
 (FromAssumption p P Q \226\134\146 KnownLFromAssumption p (<affine> P) Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownLFromAssumption
 /FromAssumption /= =>{+}<-).
Time by rewrite affinely_elim.
Time Qed.
Time #[global]
Instance from_assumption_intuitionistically_l_true  
 p P Q: (FromAssumption p P Q \226\134\146 KnownLFromAssumption p (\226\150\161 P) Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownLFromAssumption
 /FromAssumption /= =>{+}<-).
Time by rewrite intuitionistically_elim.
Time Qed.
Time #[global]
Instance from_assumption_forall  {A} p (\206\166 : A \226\134\146 PROP) 
 Q x: (FromAssumption p (\206\166 x) Q \226\134\146 KnownLFromAssumption p (\226\136\128 x, \206\166 x) Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownLFromAssumption
 /FromAssumption =>{+}<-).
Time by rewrite forall_elim.
Time Qed.
Time #[global]
Instance from_assumption_bupd  `{BiBUpd PROP} p P 
 Q: (FromAssumption p P Q \226\134\146 KnownRFromAssumption p P (|==> Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownRFromAssumption
 /FromAssumption =>{+}->).
Time (apply bupd_intro).
Time Qed.
Time #[global]Instance into_pure_pure  \207\134: (@IntoPure PROP \226\140\156\207\134\226\140\157 \207\134).
Time Proof.
Time by rewrite /IntoPure.
Time Qed.
Time #[global]
Instance into_pure_pure_and  (\207\1341 \207\1342 : Prop) P1 P2:
 (IntoPure P1 \207\1341 \226\134\146 IntoPure P2 \207\1342 \226\134\146 IntoPure (P1 \226\136\167 P2) (\207\1341 \226\136\167 \207\1342)).
Time Proof.
Time rewrite /IntoPure pure_and.
Time by intros -> ->.
Time Qed.
Time #[global]
Instance into_pure_pure_or  (\207\1341 \207\1342 : Prop) P1 P2:
 (IntoPure P1 \207\1341 \226\134\146 IntoPure P2 \207\1342 \226\134\146 IntoPure (P1 \226\136\168 P2) (\207\1341 \226\136\168 \207\1342)).
Time Proof.
Time rewrite /IntoPure pure_or.
Time by intros -> ->.
Time Qed.
Time #[global]
Instance into_pure_pure_impl  (\207\1341 \207\1342 : Prop) P1 P2:
 (FromPure false P1 \207\1341 \226\134\146 IntoPure P2 \207\1342 \226\134\146 IntoPure (P1 \226\134\146 P2) (\207\1341 \226\134\146 \207\1342)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure /IntoPure pure_impl
 =>{+}<- {+}-> //).
Time Qed.
Time #[global]
Instance into_pure_exist  {A} (\206\166 : A \226\134\146 PROP) (\207\134 : A \226\134\146 Prop):
 ((\226\136\128 x, IntoPure (\206\166 x) (\207\134 x)) \226\134\146 IntoPure (\226\136\131 x, \206\166 x) (\226\136\131 x, \207\134 x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoPure =>Hx).
Time rewrite pure_exist.
Time by setoid_rewrite Hx.
Time Qed.
Time #[global]
Instance into_pure_forall  {A} (\206\166 : A \226\134\146 PROP) (\207\134 : A \226\134\146 Prop):
 ((\226\136\128 x, IntoPure (\206\166 x) (\207\134 x)) \226\134\146 IntoPure (\226\136\128 x, \206\166 x) (\226\136\128 x, \207\134 x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoPure =>Hx).
Time rewrite -pure_forall_2.
Time by setoid_rewrite Hx.
Time Qed.
Time #[global]
Instance into_pure_pure_sep  (\207\1341 \207\1342 : Prop) P1 P2:
 (IntoPure P1 \207\1341 \226\134\146 IntoPure P2 \207\1342 \226\134\146 IntoPure (P1 \226\136\151 P2) (\207\1341 \226\136\167 \207\1342)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoPure =>{+}-> {+}->).
Time by rewrite sep_and pure_and.
Time Qed.
Time #[global]
Instance into_pure_pure_wand  a (\207\1341 \207\1342 : Prop) P1 
 P2: (FromPure a P1 \207\1341 \226\134\146 IntoPure P2 \207\1342 \226\134\146 IntoPure (P1 -\226\136\151 P2) (\207\1341 \226\134\146 \207\1342)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure /IntoPure =>{+}<- {+}->
 /=).
Time rewrite pure_impl.
Time
(<ssreflect_plugin::ssrtclintros@0> apply impl_intro_l, pure_elim_l =>?).
Time rewrite (pure_True \207\1341) //.
Time by rewrite -affinely_affinely_if affinely_True_emp affinely_emp left_id.
Time Qed.
Time #[global]
Instance into_pure_affinely  P \207\134: (IntoPure P \207\134 \226\134\146 IntoPure (<affine> P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoPure =>{+}->).
Time (apply affinely_elim).
Time Qed.
Time #[global]
Instance into_pure_intuitionistically  P \207\134: (IntoPure P \207\134 \226\134\146 IntoPure (\226\150\161 P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoPure =>{+}->).
Time (apply intuitionistically_elim).
Time Qed.
Time #[global]
Instance into_pure_absorbingly  P \207\134: (IntoPure P \207\134 \226\134\146 IntoPure (<absorb> P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoPure =>{+}->).
Time by rewrite absorbingly_pure.
Time Qed.
Time #[global]
Instance into_pure_persistently  P \207\134: (IntoPure P \207\134 \226\134\146 IntoPure (<pers> P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoPure =>{+}->).
Time apply : {}persistently_elim {}.
Time Qed.
Time #[global]
Instance into_pure_embed  `{BiEmbed PROP PROP'} P 
 \207\134: (IntoPure P \207\134 \226\134\146 IntoPure \226\142\161 P \226\142\164 \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoPure =>{+}->).
Time by rewrite embed_pure.
Time Qed.
Time #[global]Instance from_pure_emp : (@FromPure PROP true emp True).
Time Proof.
Time rewrite /FromPure /=.
Time (apply (affine _)).
Time Qed.
Time #[global]Instance from_pure_pure  \207\134: (@FromPure PROP false \226\140\156\207\134\226\140\157 \207\134).
Time Proof.
Time by rewrite /FromPure /=.
Time Qed.
Time #[global]
Instance from_pure_pure_and  a1 a2 (\207\1341 \207\1342 : Prop) 
 P1 P2:
 (FromPure a1 P1 \207\1341
  \226\134\146 FromPure a2 P2 \207\1342
    \226\134\146 FromPure (if a1 then true else a2) (P1 \226\136\167 P2) (\207\1341 \226\136\167 \207\1342)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure pure_and =>{+}<- {+}<-
 /=).
Time rewrite affinely_if_and.
Time (f_equiv; apply affinely_if_flag_mono; destruct a1; naive_solver).
Time Qed.
Time #[global]
Instance from_pure_pure_or  a1 a2 (\207\1341 \207\1342 : Prop) P1 
 P2:
 (FromPure a1 P1 \207\1341
  \226\134\146 FromPure a2 P2 \207\1342
    \226\134\146 FromPure (if a1 then true else a2) (P1 \226\136\168 P2) (\207\1341 \226\136\168 \207\1342)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure pure_or =>{+}<- {+}<-
 /=).
Time rewrite affinely_if_or.
Time (f_equiv; apply affinely_if_flag_mono; destruct a1; naive_solver).
Time Qed.
Time #[global]
Instance from_pure_pure_impl  a (\207\1341 \207\1342 : Prop) P1 
 P2: (IntoPure P1 \207\1341 \226\134\146 FromPure a P2 \207\1342 \226\134\146 FromPure a (P1 \226\134\146 P2) (\207\1341 \226\134\146 \207\1342)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure /IntoPure pure_impl
 =>{+}-> {+}<-).
Time (<ssreflect_plugin::ssrtclintros@0> destruct a =>//=).
Time (apply bi.impl_intro_l).
Time by rewrite affinely_and_r bi.impl_elim_r.
Time Qed.
Time #[global]
Instance from_pure_exist  {A} a (\206\166 : A \226\134\146 PROP) (\207\134 : A \226\134\146 Prop):
 ((\226\136\128 x, FromPure a (\206\166 x) (\207\134 x)) \226\134\146 FromPure a (\226\136\131 x, \206\166 x) (\226\136\131 x, \207\134 x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure =>Hx).
Time rewrite pure_exist affinely_if_exist.
Time by setoid_rewrite Hx.
Time Qed.
Time #[global]
Instance from_pure_forall  {A} a (\206\166 : A \226\134\146 PROP) (\207\134 : A \226\134\146 Prop):
 ((\226\136\128 x, FromPure a (\206\166 x) (\207\134 x)) \226\134\146 FromPure a (\226\136\128 x, \206\166 x) (\226\136\128 x, \207\134 x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure =>Hx).
Time rewrite pure_forall.
Time setoid_rewrite  <- Hx.
Time (<ssreflect_plugin::ssrtclintros@0> destruct a =>//=).
Time (apply affinely_forall).
Time Qed.
Time #[global]
Instance from_pure_pure_sep_true  a1 a2 (\207\1341 \207\1342 : Prop) 
 P1 P2:
 (FromPure a1 P1 \207\1341
  \226\134\146 FromPure a2 P2 \207\1342
    \226\134\146 FromPure (if a1 then a2 else false) (P1 \226\136\151 P2) (\207\1341 \226\136\167 \207\1342)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure =>{+}<- {+}<-).
Time (destruct a1; simpl).
Time -
Time by rewrite pure_and -persistent_and_affinely_sep_l affinely_if_and_r.
Time -
Time
by rewrite pure_and -affinely_affinely_if -persistent_and_affinely_sep_r_1.
Time Qed.
Time #[global]
Instance from_pure_pure_wand  a (\207\1341 \207\1342 : Prop) P1 
 P2:
 (IntoPure P1 \207\1341
  \226\134\146 FromPure a P2 \207\1342
    \226\134\146 TCOr (TCEq a false) (Affine P1) \226\134\146 FromPure a (P1 -\226\136\151 P2) (\207\1341 \226\134\146 \207\1342)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure /IntoPure =>HP1 {+}<-
 Ha /=).
Time (apply wand_intro_l).
Time (destruct a; simpl).
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> destruct Ha as [Ha| ?] ; first 
 inversion Ha).
Time rewrite -persistent_and_affinely_sep_r -(affine_affinely P1) HP1.
Time by rewrite affinely_and_l pure_impl impl_elim_r.
Time -
Time by rewrite HP1 sep_and pure_impl impl_elim_r.
Time Qed.
Time #[global]
Instance from_pure_persistently  P a \207\134:
 (FromPure true P \207\134 \226\134\146 FromPure a (<pers> P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure =>{+}<- /=).
Time
by rewrite persistently_affinely_elim affinely_if_elim persistently_pure.
Time Qed.
Time #[global]
Instance from_pure_affinely_true  a P \207\134:
 (FromPure a P \207\134 \226\134\146 FromPure true (<affine> P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure =>{+}<- /=).
Time by rewrite -affinely_affinely_if affinely_idemp.
Time Qed.
Time #[global]
Instance from_pure_intuitionistically_true  a P \207\134:
 (FromPure a P \207\134 \226\134\146 FromPure true (\226\150\161 P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure =>{+}<- /=).
Time
rewrite -intuitionistically_affinely_elim -affinely_affinely_if
 affinely_idemp.
Time by rewrite intuitionistic_intuitionistically.
Time Qed.
Time #[global]
Instance from_pure_absorbingly  a P \207\134:
 (FromPure a P \207\134 \226\134\146 FromPure false (<absorb> P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure =>{+}<- /=).
Time rewrite -affinely_affinely_if.
Time by rewrite -persistent_absorbingly_affinely_2.
Time Qed.
Time #[global]
Instance from_pure_embed  `{BiEmbed PROP PROP'} a 
 P \207\134: (FromPure a P \207\134 \226\134\146 FromPure a \226\142\161 P \226\142\164 \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure =>{+}<-).
Time by rewrite -embed_pure embed_affinely_if_2.
Time Qed.
Time #[global]
Instance from_pure_bupd  `{BiBUpd PROP} a P \207\134:
 (FromPure a P \207\134 \226\134\146 FromPure a (|==> P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure =>{+}<-).
Time (apply bupd_intro).
Time Qed.
Time #[global]
Instance into_persistent_persistently  p P Q:
 (IntoPersistent true P Q \226\134\146 IntoPersistent p (<pers> P) Q) |0.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoPersistent /= =>{+}->).
Time (destruct p; simpl; auto using persistently_idemp_1).
Time Qed.
Time #[global]
Instance into_persistent_affinely  p P Q:
 (IntoPersistent p P Q \226\134\146 IntoPersistent p (<affine> P) Q) |0.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoPersistent /= =>{+}<-).
Time by rewrite affinely_elim.
Time Qed.
Time #[global]
Instance into_persistent_intuitionistically  p P Q:
 (IntoPersistent true P Q \226\134\146 IntoPersistent p (\226\150\161 P) Q) |0.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoPersistent /= =>{+}<-).
Time
(destruct p; simpl; eauto
  using persistently_mono, intuitionistically_elim,
    intuitionistically_into_persistently_1).
Time Qed.
Time #[global]
Instance into_persistent_embed  `{BiEmbed PROP PROP'} 
 p P Q: (IntoPersistent p P Q \226\134\146 IntoPersistent p \226\142\161 P \226\142\164 \226\142\161 Q \226\142\164) |0.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoPersistent
 -embed_persistently -embed_persistently_if =>{+}-> //).
Time Qed.
Time #[global]Instance into_persistent_here  P: (IntoPersistent true P P) |1.
Time Proof.
Time by rewrite /IntoPersistent.
Time Qed.
Time #[global]
Instance into_persistent_persistent  P:
 (Persistent P \226\134\146 IntoPersistent false P P) |100.
Time Proof.
Time (intros).
Time by rewrite /IntoPersistent.
Time Qed.
Time #[global]
Instance from_modal_affinely  P:
 (FromModal modality_affinely (<affine> P) (<affine> P) P) |2.
Time Proof.
Time by rewrite /FromModal.
Time Qed.
Time #[global]
Instance from_modal_persistently  P:
 (FromModal modality_persistently (<pers> P) (<pers> P) P) |2.
Time Proof.
Time by rewrite /FromModal.
Time Qed.
Time #[global]
Instance from_modal_intuitionistically  P:
 (FromModal modality_intuitionistically (\226\150\161 P) (\226\150\161 P) P) |1.
Time Proof.
Time by rewrite /FromModal.
Time Qed.
Time #[global]
Instance from_modal_intuitionistically_affine_bi  
 P: (BiAffine PROP \226\134\146 FromModal modality_persistently (\226\150\161 P) (\226\150\161 P) P) |0.
Time Proof.
Time (intros).
Time by rewrite /FromModal /= intuitionistically_into_persistently.
Time Qed.
Time #[global]
Instance from_modal_absorbingly  P:
 (FromModal modality_id (<absorb> P) (<absorb> P) P).
Time Proof.
Time by rewrite /FromModal /= -absorbingly_intro.
Time Qed.
Time #[global]
Instance from_modal_embed  `{BiEmbed PROP PROP'} (P : PROP):
 (FromModal (@modality_embed PROP PROP' _) \226\142\161 P \226\142\164 \226\142\161 P \226\142\164 P).
Time Proof.
Time by rewrite /FromModal.
Time Qed.
Time #[global]
Instance from_modal_id_embed  `{BiEmbed PROP PROP'} 
 `(sel : A) P Q:
 (FromModal modality_id sel P Q \226\134\146 FromModal modality_id sel \226\142\161 P \226\142\164 \226\142\161 Q \226\142\164) |100.
Time Proof.
Time by <ssreflect_plugin::ssrtclintros@0> rewrite /FromModal /= =>{+}<-.
Time Qed.
Time #[global]
Instance from_modal_affinely_embed  `{BiEmbed PROP PROP'} 
 `(sel : A) P Q:
 (FromModal modality_affinely sel P Q
  \226\134\146 FromModal modality_affinely sel \226\142\161 P \226\142\164 \226\142\161 Q \226\142\164) |100.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromModal /= =>{+}<-).
Time by rewrite embed_affinely_2.
Time Qed.
Time #[global]
Instance from_modal_persistently_embed  `{BiEmbed PROP PROP'} 
 `(sel : A) P Q:
 (FromModal modality_persistently sel P Q
  \226\134\146 FromModal modality_persistently sel \226\142\161 P \226\142\164 \226\142\161 Q \226\142\164) |100.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromModal /= =>{+}<-).
Time by rewrite embed_persistently.
Time Qed.
Time #[global]
Instance from_modal_intuitionistically_embed  `{BiEmbed PROP PROP'}
 `(sel : A) P Q:
 (FromModal modality_intuitionistically sel P Q
  \226\134\146 FromModal modality_intuitionistically sel \226\142\161 P \226\142\164 \226\142\161 Q \226\142\164) |100.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromModal /= =>{+}<-).
Time by rewrite embed_intuitionistically_2.
Time Qed.
Time #[global]
Instance from_modal_bupd  `{BiBUpd PROP} P:
 (FromModal modality_id (|==> P) (|==> P) P).
Time Proof.
Time by rewrite /FromModal /= -bupd_intro.
Time Qed.
Time #[global]
Instance into_wand_wand'  p q (P Q P' Q' : PROP):
 (IntoWand' p q (P -\226\136\151 Q) P' Q' \226\134\146 IntoWand p q (P -\226\136\151 Q) P' Q') |100.
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance into_wand_impl'  p q (P Q P' Q' : PROP):
 (IntoWand' p q (P \226\134\146 Q) P' Q' \226\134\146 IntoWand p q (P \226\134\146 Q) P' Q') |100.
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance into_wand_wandM'  p q mP (Q P' Q' : PROP):
 (IntoWand' p q (mP -\226\136\151? Q) P' Q' \226\134\146 IntoWand p q (mP -\226\136\151? Q) P' Q') |100.
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance into_wand_wand  p q P Q P':
 (FromAssumption q P P' \226\134\146 IntoWand p q (P' -\226\136\151 Q) P Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromAssumption /IntoWand =>HP).
Time by rewrite HP intuitionistically_if_elim.
Time Qed.
Time #[global]
Instance into_wand_impl_false_false  P Q P':
 (Absorbing P'
  \226\134\146 Absorbing (P' \226\134\146 Q)
    \226\134\146 FromAssumption false P P' \226\134\146 IntoWand false false (P' \226\134\146 Q) P Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromAssumption /IntoWand /= =>?
 ? {+}->).
Time (apply wand_intro_r).
Time by rewrite sep_and impl_elim_l.
Time Qed.
Time #[global]
Instance into_wand_impl_false_true  P Q P':
 (Absorbing P' \226\134\146 FromAssumption true P P' \226\134\146 IntoWand false true (P' \226\134\146 Q) P Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand /FromAssumption /= =>?
 HP).
Time (apply wand_intro_l).
Time rewrite -(intuitionistically_idemp P) HP.
Time
by rewrite -persistently_and_intuitionistically_sep_l persistently_elim
 impl_elim_r.
Time Qed.
Time #[global]
Instance into_wand_impl_true_false  P Q P':
 (Affine P' \226\134\146 FromAssumption false P P' \226\134\146 IntoWand true false (P' \226\134\146 Q) P Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromAssumption /IntoWand /= =>?
 HP).
Time (apply wand_intro_r).
Time rewrite HP sep_and intuitionistically_elim impl_elim_l //.
Time Qed.
Time #[global]
Instance into_wand_impl_true_true  P Q P':
 (FromAssumption true P P' \226\134\146 IntoWand true true (P' \226\134\146 Q) P Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromAssumption /IntoWand /=
 =>{+}<-).
Time (apply wand_intro_l).
Time rewrite sep_and [(\226\150\161 (_ \226\134\146 _))%I]intuitionistically_elim impl_elim_r //.
Time Qed.
Time #[global]
Instance into_wand_wandM  p q mP' P Q:
 (FromAssumption q P (default emp%I mP') \226\134\146 IntoWand p q (mP' -\226\136\151? Q) P Q).
Time Proof.
Time rewrite /IntoWand wandM_sound.
Time exact : {}into_wand_wand {}.
Time Qed.
Time #[global]
Instance into_wand_and_l  p q R1 R2 P' Q':
 (IntoWand p q R1 P' Q' \226\134\146 IntoWand p q (R1 \226\136\167 R2) P' Q').
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand =>?).
Time by rewrite /bi_wand_iff and_elim_l.
Time Qed.
Time #[global]
Instance into_wand_and_r  p q R1 R2 P' Q':
 (IntoWand p q R2 Q' P' \226\134\146 IntoWand p q (R1 \226\136\167 R2) Q' P').
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand =>?).
Time by rewrite /bi_wand_iff and_elim_r.
Time Qed.
Time #[global]
Instance into_wand_forall_prop_true  p (\207\134 : Prop) 
 P: (IntoWand p true (\226\136\128 _ : \207\134, P) \226\140\156\207\134\226\140\157 P).
Time Proof.
Time
rewrite /IntoWand (intuitionistically_if_elim p) /=
 -impl_wand_intuitionistically -pure_impl_forall bi.persistently_elim //.
Time Qed.
Time #[global]
Instance into_wand_forall_prop_false  p (\207\134 : Prop) 
 P: (Absorbing P \226\134\146 IntoWand p false (\226\136\128 _ : \207\134, P) \226\140\156\207\134\226\140\157 P).
Time Proof.
Time (intros ?).
Time rewrite /IntoWand (intuitionistically_if_elim p) /= pure_wand_forall //.
Time Qed.
Time #[global]
Instance into_wand_forall  {A} p q (\206\166 : A \226\134\146 PROP) 
 P Q x: (IntoWand p q (\206\166 x) P Q \226\134\146 IntoWand p q (\226\136\128 x, \206\166 x) P Q).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand =>{+}<-).
Time by rewrite (forall_elim x).
Time Qed.
Time #[global]
Instance into_wand_tforall  {A} p q (\206\166 : tele_arg A \226\134\146 PROP) 
 P Q x: (IntoWand p q (\206\166 x) P Q \226\134\146 IntoWand p q (\226\136\128.. x, \206\166 x) P Q).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand =>{+}<-).
Time by rewrite bi_tforall_forall (forall_elim x).
Time Qed.
Time #[global]
Instance into_wand_affine  p q R P Q:
 (IntoWand p q R P Q \226\134\146 IntoWand p q (<affine> R) (<affine> P) (<affine> Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand /= =>HR).
Time (apply wand_intro_r).
Time (destruct p; simpl in *).
Time -
Time rewrite (affinely_elim R) -(affine_affinely (\226\150\161 R)%I) HR.
Time (destruct q; simpl in *).
Time +
Time rewrite (affinely_elim P) -{+2}(affine_affinely (\226\150\161 P)%I).
Time by rewrite affinely_sep_2 wand_elim_l.
Time +
Time by rewrite affinely_sep_2 wand_elim_l.
Time -
Time rewrite HR.
Time (destruct q; simpl in *).
Time +
Time rewrite (affinely_elim P) -{+2}(affine_affinely (\226\150\161 P)%I).
Time by rewrite affinely_sep_2 wand_elim_l.
Time +
Time by rewrite affinely_sep_2 wand_elim_l.
Time Qed.
Time #[global]
Instance into_wand_affine_args  q R P Q:
 (IntoWand true q R P Q \226\134\146 IntoWand' true q R (<affine> P) (<affine> Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand' /IntoWand /= =>HR).
Time (apply wand_intro_r).
Time rewrite -(affine_affinely (\226\150\161 R)%I) HR.
Time (destruct q; simpl).
Time -
Time rewrite (affinely_elim P) -{+2}(affine_affinely (\226\150\161 P)%I).
Time by rewrite affinely_sep_2 wand_elim_l.
Time -
Time by rewrite affinely_sep_2 wand_elim_l.
Time Qed.
Time #[global]
Instance into_wand_intuitionistically  p q R P Q:
 (IntoWand true q R P Q \226\134\146 IntoWand p q (\226\150\161 R) P Q).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand /= =>{+}->).
Time by rewrite {+1}intuitionistically_if_elim.
Time Qed.
Time #[global]
Instance into_wand_persistently_true  q R P Q:
 (IntoWand true q R P Q \226\134\146 IntoWand true q (<pers> R) P Q).
Time Proof.
Time by rewrite /IntoWand /= intuitionistically_persistently_elim.
Time Qed.
Time #[global]
Instance into_wand_persistently_false  q R P Q:
 (Absorbing R \226\134\146 IntoWand false q R P Q \226\134\146 IntoWand false q (<pers> R) P Q).
Time Proof.
Time (intros ?).
Time by rewrite /IntoWand persistently_elim.
Time Qed.
Time #[global]
Instance into_wand_embed  `{BiEmbed PROP PROP'} p 
 q R P Q: (IntoWand p q R P Q \226\134\146 IntoWand p q \226\142\161 R \226\142\164 \226\142\161 P \226\142\164 \226\142\161 Q \226\142\164).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand
 !embed_intuitionistically_if_2 -embed_wand =>{+}->.
Time Qed.
Time #[global]
Instance into_wand_affine_embed_true  `{BiEmbed PROP PROP'} 
 q (PP QQ RR : PROP):
 (IntoWand true q RR PP QQ
  \226\134\146 IntoWand true q \226\142\161 RR \226\142\164 (<affine> \226\142\161 PP \226\142\164) (<affine> \226\142\161 QQ \226\142\164)) |100.
Time Proof.
Time rewrite /IntoWand /=.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite
 -(intuitionistically_idemp \226\142\161 _ \226\142\164%I) embed_intuitionistically_2 =>{+}->).
Time (apply bi.wand_intro_l).
Time (destruct q; simpl).
Time -
Time rewrite affinely_elim -(intuitionistically_idemp \226\142\161 _ \226\142\164%I).
Time rewrite embed_intuitionistically_2 intuitionistically_sep_2 -embed_sep.
Time by rewrite wand_elim_r intuitionistically_affinely.
Time -
Time
by rewrite intuitionistically_affinely affinely_sep_2 -embed_sep wand_elim_r.
Time Qed.
Time #[global]
Instance into_wand_affine_embed_false  `{BiEmbed PROP PROP'} 
 q (PP QQ RR : PROP):
 (IntoWand false q RR (<affine> PP) QQ
  \226\134\146 IntoWand false q \226\142\161 RR \226\142\164 (<affine> \226\142\161 PP \226\142\164) \226\142\161 QQ \226\142\164) |100.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand /= =>{+}->).
Time by rewrite embed_affinely_2 embed_intuitionistically_if_2 embed_wand.
Time Qed.
Time #[global]
Instance into_wand_bupd  `{BiBUpd PROP} p q R P Q:
 (IntoWand false false R P Q \226\134\146 IntoWand p q (|==> R) (|==> P) (|==> Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand /= =>HR).
Time rewrite !intuitionistically_if_elim HR.
Time (apply wand_intro_l).
Time by rewrite bupd_sep wand_elim_r.
Time Qed.
Time #[global]
Instance into_wand_bupd_persistent  `{BiBUpd PROP} 
 p q R P Q: (IntoWand false q R P Q \226\134\146 IntoWand p q (|==> R) P (|==> Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand /= =>HR).
Time rewrite intuitionistically_if_elim HR.
Time (apply wand_intro_l).
Time by rewrite bupd_frame_l wand_elim_r.
Time Qed.
Time #[global]
Instance into_wand_bupd_args  `{BiBUpd PROP} p q R 
 P Q: (IntoWand p false R P Q \226\134\146 IntoWand' p q R (|==> P) (|==> Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand' /IntoWand /= =>{+}->).
Time (apply wand_intro_l).
Time by rewrite intuitionistically_if_elim bupd_wand_r.
Time Qed.
Time #[global]Instance from_wand_wand  P1 P2: (FromWand (P1 -\226\136\151 P2) P1 P2).
Time Proof.
Time by rewrite /FromWand.
Time Qed.
Time #[global]
Instance from_wand_wandM  mP1 P2:
 (FromWand (mP1 -\226\136\151? P2) (default emp mP1)%I P2).
Time Proof.
Time by rewrite /FromWand wandM_sound.
Time Qed.
Time #[global]
Instance from_wand_embed  `{BiEmbed PROP PROP'} P 
 Q1 Q2: (FromWand P Q1 Q2 \226\134\146 FromWand \226\142\161 P \226\142\164 \226\142\161 Q1 \226\142\164 \226\142\161 Q2 \226\142\164).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /FromWand -embed_wand =>{+}<-.
Time Qed.
Time #[global]Instance from_impl_impl  P1 P2: (FromImpl (P1 \226\134\146 P2) P1 P2).
Time Proof.
Time by rewrite /FromImpl.
Time Qed.
Time #[global]
Instance from_impl_embed  `{BiEmbed PROP PROP'} P 
 Q1 Q2: (FromImpl P Q1 Q2 \226\134\146 FromImpl \226\142\161 P \226\142\164 \226\142\161 Q1 \226\142\164 \226\142\161 Q2 \226\142\164).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /FromImpl -embed_impl =>{+}<-.
Time Qed.
Time #[global]Instance from_and_and  P1 P2: (FromAnd (P1 \226\136\167 P2) P1 P2) |100.
Time Proof.
Time by rewrite /FromAnd.
Time Qed.
Time #[global]
Instance from_and_sep_persistent_l  P1 P1' P2:
 (Persistent P1 \226\134\146 IntoAbsorbingly P1' P1 \226\134\146 FromAnd (P1 \226\136\151 P2) P1' P2) |9.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoAbsorbingly /FromAnd =>?
 {+}->).
Time
rewrite persistent_and_affinely_sep_l_1 {+1}(persistent_persistently_2 P1).
Time
by rewrite absorbingly_elim_persistently -{+2}(intuitionistically_elim P1).
Time Qed.
Time #[global]
Instance from_and_sep_persistent_r  P1 P2 P2':
 (Persistent P2 \226\134\146 IntoAbsorbingly P2' P2 \226\134\146 FromAnd (P1 \226\136\151 P2) P1 P2') |10.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoAbsorbingly /FromAnd =>?
 {+}->).
Time
rewrite persistent_and_affinely_sep_r_1 {+1}(persistent_persistently_2 P2).
Time
by rewrite absorbingly_elim_persistently -{+2}(intuitionistically_elim P2).
Time Qed.
Time #[global]Instance from_and_pure  \207\134 \207\136: (@FromAnd PROP \226\140\156\207\134 \226\136\167 \207\136\226\140\157 \226\140\156\207\134\226\140\157 \226\140\156\207\136\226\140\157).
Time Proof.
Time by rewrite /FromAnd pure_and.
Time Qed.
Time #[global]
Instance from_and_persistently  P Q1 Q2:
 (FromAnd P Q1 Q2 \226\134\146 FromAnd (<pers> P) (<pers> Q1) (<pers> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromAnd =>{+}<-).
Time by rewrite persistently_and.
Time Qed.
Time #[global]
Instance from_and_persistently_sep  P Q1 Q2:
 (FromSep P Q1 Q2 \226\134\146 FromAnd (<pers> P) (<pers> Q1) (<pers> Q2)) |11.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromAnd =>{+}<-).
Time by rewrite -persistently_and persistently_and_sep.
Time Qed.
Time #[global]
Instance from_and_embed  `{BiEmbed PROP PROP'} P Q1 
 Q2: (FromAnd P Q1 Q2 \226\134\146 FromAnd \226\142\161 P \226\142\164 \226\142\161 Q1 \226\142\164 \226\142\161 Q2 \226\142\164).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /FromAnd -embed_and =>{+}<-.
Time Qed.
Time #[global]
Instance from_and_big_sepL_cons_persistent  {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP) 
 l x l':
 (IsCons l x l'
  \226\134\146 Persistent (\206\166 0 x)
    \226\134\146 FromAnd ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y) (\206\166 0 x)
        ([\226\136\151 list] k\226\134\166y \226\136\136 l', \206\166 (S k) y)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsCons =>{+}-> ?).
Time by rewrite /FromAnd big_sepL_cons persistent_and_sep_1.
Time Qed.
Time #[global]
Instance from_and_big_sepL_app_persistent  {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP) 
 l l1 l2:
 (IsApp l l1 l2
  \226\134\146 (\226\136\128 k y, Persistent (\206\166 k y))
    \226\134\146 FromAnd ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y) ([\226\136\151 list] k\226\134\166y \226\136\136 l1, \206\166 k y)
        ([\226\136\151 list] k\226\134\166y \226\136\136 l2, \206\166 (length l1 + k) y)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsApp =>{+}-> ?).
Time by rewrite /FromAnd big_sepL_app persistent_and_sep_1.
Time Qed.
Time #[global]
Instance from_and_big_sepL2_cons_persistent  {A} {B} 
 (\206\166 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP) l1 x1 l1' l2 x2 l2':
 (IsCons l1 x1 l1'
  \226\134\146 IsCons l2 x2 l2'
    \226\134\146 Persistent (\206\166 0 x1 x2)
      \226\134\146 FromAnd ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2) 
          (\206\166 0 x1 x2) ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1';l2', \206\166 (S k) y1 y2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsCons =>{+}-> {+}-> ?).
Time by rewrite /FromAnd big_sepL2_cons persistent_and_sep_1.
Time Qed.
Time #[global]
Instance from_and_big_sepL2_app_persistent  {A} {B} 
 (\206\166 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP) l1 l1' l1'' l2 l2' l2'':
 (IsApp l1 l1' l1''
  \226\134\146 IsApp l2 l2' l2''
    \226\134\146 (\226\136\128 k y1 y2, Persistent (\206\166 k y1 y2))
      \226\134\146 FromAnd ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)
          ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1';l2', \206\166 k y1 y2)
          ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1'';l2'', \206\166 (length l1' + k) y1 y2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsApp =>{+}-> {+}-> ?).
Time rewrite /FromAnd persistent_and_sep_1.
Time (apply wand_elim_l', big_sepL2_app).
Time Qed.
Time #[global]
Instance from_and_big_sepMS_disj_union_persistent  
 `{Countable A} (\206\166 : A \226\134\146 PROP) X1 X2:
 ((\226\136\128 y, Persistent (\206\166 y))
  \226\134\146 FromAnd ([\226\136\151 mset] y \226\136\136 (X1 \226\138\142 X2), \206\166 y) ([\226\136\151 mset] y \226\136\136 X1, \206\166 y)
      ([\226\136\151 mset] y \226\136\136 X2, \206\166 y)).
Time Proof.
Time (intros).
Time by rewrite /FromAnd big_sepMS_disj_union persistent_and_sep_1.
Time Qed.
Time #[global]Instance from_sep_sep  P1 P2: (FromSep (P1 \226\136\151 P2) P1 P2) |100.
Time Proof.
Time by rewrite /FromSep.
Time Qed.
Time #[global]
Instance from_sep_and  P1 P2:
 (TCOr (Affine P1) (Absorbing P2)
  \226\134\146 TCOr (Absorbing P1) (Affine P2) \226\134\146 FromSep (P1 \226\136\167 P2) P1 P2) |101.
Time Proof.
Time (intros).
Time by rewrite /FromSep sep_and.
Time Qed.
Time #[global]Instance from_sep_pure  \207\134 \207\136: (@FromSep PROP \226\140\156\207\134 \226\136\167 \207\136\226\140\157 \226\140\156\207\134\226\140\157 \226\140\156\207\136\226\140\157).
Time Proof.
Time by rewrite /FromSep pure_and sep_and.
Time Qed.
Time #[global]
Instance from_sep_affinely  P Q1 Q2:
 (FromSep P Q1 Q2 \226\134\146 FromSep (<affine> P) (<affine> Q1) (<affine> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromSep =>{+}<-).
Time by rewrite affinely_sep_2.
Time Qed.
Time #[global]
Instance from_sep_intuitionistically  P Q1 Q2:
 (FromSep P Q1 Q2 \226\134\146 FromSep (\226\150\161 P) (\226\150\161 Q1) (\226\150\161 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromSep =>{+}<-).
Time by rewrite intuitionistically_sep_2.
Time Qed.
Time #[global]
Instance from_sep_absorbingly  P Q1 Q2:
 (FromSep P Q1 Q2 \226\134\146 FromSep (<absorb> P) (<absorb> Q1) (<absorb> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromSep =>{+}<-).
Time by rewrite absorbingly_sep.
Time Qed.
Time #[global]
Instance from_sep_persistently  P Q1 Q2:
 (FromSep P Q1 Q2 \226\134\146 FromSep (<pers> P) (<pers> Q1) (<pers> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromSep =>{+}<-).
Time by rewrite persistently_sep_2.
Time Qed.
Time #[global]
Instance from_sep_embed  `{BiEmbed PROP PROP'} P Q1 
 Q2: (FromSep P Q1 Q2 \226\134\146 FromSep \226\142\161 P \226\142\164 \226\142\161 Q1 \226\142\164 \226\142\161 Q2 \226\142\164).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /FromSep -embed_sep =>{+}<-.
Time Qed.
Time #[global]
Instance from_sep_big_sepL_cons  {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP) 
 l x l':
 (IsCons l x l'
  \226\134\146 FromSep ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y) (\206\166 0 x) ([\226\136\151 list] k\226\134\166y \226\136\136 l', \206\166 (S k) y)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsCons =>{+}->).
Time by rewrite /FromSep big_sepL_cons.
Time Qed.
Time #[global]
Instance from_sep_big_sepL_app  {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP) 
 l l1 l2:
 (IsApp l l1 l2
  \226\134\146 FromSep ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y) ([\226\136\151 list] k\226\134\166y \226\136\136 l1, \206\166 k y)
      ([\226\136\151 list] k\226\134\166y \226\136\136 l2, \206\166 (length l1 + k) y)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsApp =>{+}->).
Time by rewrite /FromSep big_opL_app.
Time Qed.
Time #[global]
Instance from_sep_big_sepL2_cons  {A} {B} (\206\166 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP) 
 l1 x1 l1' l2 x2 l2':
 (IsCons l1 x1 l1'
  \226\134\146 IsCons l2 x2 l2'
    \226\134\146 FromSep ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2) 
        (\206\166 0 x1 x2) ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1';l2', \206\166 (S k) y1 y2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsCons =>{+}-> {+}->).
Time by rewrite /FromSep big_sepL2_cons.
Time Qed.
Time #[global]
Instance from_sep_big_sepL2_app  {A} {B} (\206\166 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP) 
 l1 l1' l1'' l2 l2' l2'':
 (IsApp l1 l1' l1''
  \226\134\146 IsApp l2 l2' l2''
    \226\134\146 FromSep ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)
        ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1';l2', \206\166 k y1 y2)
        ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1'';l2'', \206\166 (length l1' + k) y1 y2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsApp =>{+}-> {+}->).
Time (apply wand_elim_l', big_sepL2_app).
Time Qed.
Time #[global]
Instance from_sep_big_sepMS_disj_union  `{Countable A} 
 (\206\166 : A \226\134\146 PROP) X1 X2:
 (FromSep ([\226\136\151 mset] y \226\136\136 (X1 \226\138\142 X2), \206\166 y) ([\226\136\151 mset] y \226\136\136 X1, \206\166 y)
    ([\226\136\151 mset] y \226\136\136 X2, \206\166 y)).
Time Proof.
Time by rewrite /FromSep big_sepMS_disj_union.
Time Qed.
Time #[global]
Instance from_sep_bupd  `{BiBUpd PROP} P Q1 Q2:
 (FromSep P Q1 Q2 \226\134\146 FromSep (|==> P) (|==> Q1) (|==> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromSep =>{+}<-).
Time (apply bupd_sep).
Time Qed.
Time #[global]Instance into_and_and  p P Q: (IntoAnd p (P \226\136\167 Q) P Q) |10.
Time Proof.
Time by rewrite /IntoAnd intuitionistically_if_and.
Time Qed.
Time #[global]
Instance into_and_and_affine_l  P Q Q':
 (Affine P \226\134\146 FromAffinely Q' Q \226\134\146 IntoAnd false (P \226\136\167 Q) P Q').
Time Proof.
Time (intros).
Time rewrite /IntoAnd /=.
Time
by rewrite -(affine_affinely P) affinely_and_l affinely_and
 (from_affinely Q').
Time Qed.
Time #[global]
Instance into_and_and_affine_r  P P' Q:
 (Affine Q \226\134\146 FromAffinely P' P \226\134\146 IntoAnd false (P \226\136\167 Q) P' Q).
Time Proof.
Time (intros).
Time rewrite /IntoAnd /=.
Time
by rewrite -(affine_affinely Q) affinely_and_r affinely_and
 (from_affinely P').
Time Qed.
Time #[global]
Instance into_and_sep  `{BiPositive PROP} P Q: (IntoAnd true (P \226\136\151 Q) P Q).
Time Proof.
Time
rewrite /IntoAnd /= intuitionistically_sep -and_sep_intuitionistically
 intuitionistically_and //.
Time Qed.
Time #[global]
Instance into_and_sep_affine  P Q:
 (TCOr (Affine P) (Absorbing Q)
  \226\134\146 TCOr (Absorbing P) (Affine Q) \226\134\146 IntoAnd true (P \226\136\151 Q) P Q).
Time Proof.
Time (intros).
Time by rewrite /IntoAnd /= sep_and.
Time Qed.
Time #[global]
Instance into_and_pure  p \207\134 \207\136: (@IntoAnd PROP p \226\140\156\207\134 \226\136\167 \207\136\226\140\157 \226\140\156\207\134\226\140\157 \226\140\156\207\136\226\140\157).
Time Proof.
Time by rewrite /IntoAnd pure_and intuitionistically_if_and.
Time Qed.
Time #[global]
Instance into_and_affinely  p P Q1 Q2:
 (IntoAnd p P Q1 Q2 \226\134\146 IntoAnd p (<affine> P) (<affine> Q1) (<affine> Q2)).
Time Proof.
Time rewrite /IntoAnd.
Time (destruct p; simpl).
Time -
Time rewrite -affinely_and !intuitionistically_affinely_elim //.
Time -
Time (intros ->).
Time by rewrite affinely_and.
Time Qed.
Time #[global]
Instance into_and_intuitionistically  p P Q1 Q2:
 (IntoAnd p P Q1 Q2 \226\134\146 IntoAnd p (\226\150\161 P) (\226\150\161 Q1) (\226\150\161 Q2)).
Time Proof.
Time rewrite /IntoAnd.
Time (destruct p; simpl).
Time -
Time rewrite -intuitionistically_and !intuitionistically_idemp //.
Time -
Time (intros ->).
Time by rewrite intuitionistically_and.
Time Qed.
Time #[global]
Instance into_and_persistently  p P Q1 Q2:
 (IntoAnd p P Q1 Q2 \226\134\146 IntoAnd p (<pers> P) (<pers> Q1) (<pers> Q2)).
Time Proof.
Time rewrite /IntoAnd /=.
Time (destruct p; simpl).
Time -
Time rewrite -persistently_and !intuitionistically_persistently_elim //.
Time -
Time (intros ->).
Time by rewrite persistently_and.
Time Qed.
Time #[global]
Instance into_and_embed  `{BiEmbed PROP PROP'} p P 
 Q1 Q2: (IntoAnd p P Q1 Q2 \226\134\146 IntoAnd p \226\142\161 P \226\142\164 \226\142\161 Q1 \226\142\164 \226\142\161 Q2 \226\142\164).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoAnd -embed_and =>HP).
Time (apply intuitionistically_if_intro').
Time by rewrite embed_intuitionistically_if_2 HP intuitionistically_if_elim.
Time Qed.
Time #[global]Instance into_sep_sep  P Q: (IntoSep (P \226\136\151 Q) P Q).
Time Proof.
Time by rewrite /IntoSep.
Time Qed.
Time
Inductive AndIntoSep : PROP \226\134\146 PROP \226\134\146 PROP \226\134\146 PROP \226\134\146 Prop :=
  | and_into_sep_affine :
      forall P Q Q', Affine P \226\134\146 FromAffinely Q' Q \226\134\146 AndIntoSep P P Q Q'
  | and_into_sep : forall P Q, AndIntoSep P (<affine> P)%I Q Q.
Time Existing Class AndIntoSep.
Time #[global]Existing Instance and_into_sep_affine |0.
Time #[global]Existing Instance and_into_sep |2.
Time #[global]
Instance into_sep_and_persistent_l  P P' Q Q':
 (Persistent P \226\134\146 AndIntoSep P P' Q Q' \226\134\146 IntoSep (P \226\136\167 Q) P' Q').
Time Proof.
Time (destruct 2 as [P Q Q'| P Q]; rewrite /IntoSep).
Time -
Time rewrite -(from_affinely Q' Q) -(affine_affinely P) affinely_and_lr.
Time by rewrite persistent_and_affinely_sep_l_1.
Time -
Time by rewrite persistent_and_affinely_sep_l_1.
Time Qed.
Time #[global]
Instance into_sep_and_persistent_r  P P' Q Q':
 (Persistent Q \226\134\146 AndIntoSep Q Q' P P' \226\134\146 IntoSep (P \226\136\167 Q) P' Q').
Time Proof.
Time (destruct 2 as [Q P P'| Q P]; rewrite /IntoSep).
Time -
Time rewrite -(from_affinely P' P) -(affine_affinely Q) -affinely_and_lr.
Time by rewrite persistent_and_affinely_sep_r_1.
Time -
Time by rewrite persistent_and_affinely_sep_r_1.
Time Qed.
Time #[global]Instance into_sep_pure  \207\134 \207\136: (@IntoSep PROP \226\140\156\207\134 \226\136\167 \207\136\226\140\157 \226\140\156\207\134\226\140\157 \226\140\156\207\136\226\140\157).
Time Proof.
Time by rewrite /IntoSep pure_and persistent_and_sep_1.
Time Qed.
Time #[global]
Instance into_sep_embed  `{BiEmbed PROP PROP'} P Q1 
 Q2: (IntoSep P Q1 Q2 \226\134\146 IntoSep \226\142\161 P \226\142\164 \226\142\161 Q1 \226\142\164 \226\142\161 Q2 \226\142\164).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSep -embed_sep =>{+}-> //).
Time Qed.
Time #[global]
Instance into_sep_affinely  `{BiPositive PROP} P Q1 
 Q2: (IntoSep P Q1 Q2 \226\134\146 IntoSep (<affine> P) (<affine> Q1) (<affine> Q2)) |0.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSep /= =>{+}->).
Time by rewrite affinely_sep.
Time Qed.
Time #[global]
Instance into_sep_intuitionistically  `{BiPositive PROP} 
 P Q1 Q2: (IntoSep P Q1 Q2 \226\134\146 IntoSep (\226\150\161 P) (\226\150\161 Q1) (\226\150\161 Q2)) |0.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSep /= =>{+}->).
Time by rewrite intuitionistically_sep.
Time Qed.
Time #[global]
Instance into_sep_affinely_trim  P Q1 Q2:
 (IntoSep P Q1 Q2 \226\134\146 IntoSep (<affine> P) Q1 Q2) |20.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSep /= =>{+}->).
Time by rewrite affinely_elim.
Time Qed.
Time #[global]
Instance into_sep_persistently  `{BiPositive PROP} 
 P Q1 Q2: (IntoSep P Q1 Q2 \226\134\146 IntoSep (<pers> P) (<pers> Q1) (<pers> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSep /= =>{+}->).
Time by rewrite persistently_sep.
Time Qed.
Time #[global]
Instance into_sep_persistently_affine  P Q1 Q2:
 (IntoSep P Q1 Q2
  \226\134\146 TCOr (Affine Q1) (Absorbing Q2)
    \226\134\146 TCOr (Absorbing Q1) (Affine Q2)
      \226\134\146 IntoSep (<pers> P) (<pers> Q1) (<pers> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSep /= =>{+}-> ? ?).
Time by rewrite sep_and persistently_and persistently_and_sep_l_1.
Time Qed.
Time #[global]
Instance into_sep_intuitionistically_affine  P Q1 
 Q2:
 (IntoSep P Q1 Q2
  \226\134\146 TCOr (Affine Q1) (Absorbing Q2)
    \226\134\146 TCOr (Absorbing Q1) (Affine Q2) \226\134\146 IntoSep (\226\150\161 P) (\226\150\161 Q1) (\226\150\161 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSep /= =>{+}-> ? ?).
Time by rewrite sep_and intuitionistically_and and_sep_intuitionistically.
Time Qed.
Time #[global]
Instance into_sep_big_sepL_cons  {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP) 
 l x l':
 (IsCons l x l'
  \226\134\146 IntoSep ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y) (\206\166 0 x) ([\226\136\151 list] k\226\134\166y \226\136\136 l', \206\166 (S k) y)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsCons =>{+}->).
Time by rewrite /IntoSep big_sepL_cons.
Time Qed.
Time #[global]
Instance into_sep_big_sepL_app  {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP) 
 l l1 l2:
 (IsApp l l1 l2
  \226\134\146 IntoSep ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y) ([\226\136\151 list] k\226\134\166y \226\136\136 l1, \206\166 k y)
      ([\226\136\151 list] k\226\134\166y \226\136\136 l2, \206\166 (length l1 + k) y)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsApp =>{+}->).
Time by rewrite /IntoSep big_sepL_app.
Time Qed.
Time #[global]
Instance into_sep_big_sepL2_cons  {A} {B} (\206\166 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP) 
 l1 x1 l1' l2 x2 l2':
 (IsCons l1 x1 l1'
  \226\134\146 IsCons l2 x2 l2'
    \226\134\146 IntoSep ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2) 
        (\206\166 0 x1 x2) ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1';l2', \206\166 (S k) y1 y2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsCons =>{+}-> {+}->).
Time by rewrite /IntoSep big_sepL2_cons.
Time Qed.
Time #[global]
Instance into_sep_big_sepMS_disj_union  `{Countable A} 
 (\206\166 : A \226\134\146 PROP) X1 X2:
 (IntoSep ([\226\136\151 mset] y \226\136\136 (X1 \226\138\142 X2), \206\166 y) ([\226\136\151 mset] y \226\136\136 X1, \206\166 y)
    ([\226\136\151 mset] y \226\136\136 X2, \206\166 y)).
Time Proof.
Time by rewrite /IntoSep big_sepMS_disj_union.
Time Qed.
Time #[global]Instance from_or_or  P1 P2: (FromOr (P1 \226\136\168 P2) P1 P2).
Time Proof.
Time by rewrite /FromOr.
Time Qed.
Time #[global]Instance from_or_pure  \207\134 \207\136: (@FromOr PROP \226\140\156\207\134 \226\136\168 \207\136\226\140\157 \226\140\156\207\134\226\140\157 \226\140\156\207\136\226\140\157).
Time Proof.
Time by rewrite /FromOr pure_or.
Time Qed.
Time #[global]
Instance from_or_affinely  P Q1 Q2:
 (FromOr P Q1 Q2 \226\134\146 FromOr (<affine> P) (<affine> Q1) (<affine> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromOr =>{+}<-).
Time by rewrite affinely_or.
Time Qed.
Time #[global]
Instance from_or_intuitionistically  P Q1 Q2:
 (FromOr P Q1 Q2 \226\134\146 FromOr (\226\150\161 P) (\226\150\161 Q1) (\226\150\161 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromOr =>{+}<-).
Time by rewrite intuitionistically_or.
Time Qed.
Time #[global]
Instance from_or_absorbingly  P Q1 Q2:
 (FromOr P Q1 Q2 \226\134\146 FromOr (<absorb> P) (<absorb> Q1) (<absorb> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromOr =>{+}<-).
Time by rewrite absorbingly_or.
Time Qed.
Time #[global]
Instance from_or_persistently  P Q1 Q2:
 (FromOr P Q1 Q2 \226\134\146 FromOr (<pers> P) (<pers> Q1) (<pers> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromOr =>{+}<-).
Time by rewrite persistently_or.
Time Qed.
Time #[global]
Instance from_or_embed  `{BiEmbed PROP PROP'} P Q1 
 Q2: (FromOr P Q1 Q2 \226\134\146 FromOr \226\142\161 P \226\142\164 \226\142\161 Q1 \226\142\164 \226\142\161 Q2 \226\142\164).
Time Proof.
Time by <ssreflect_plugin::ssrtclintros@0> rewrite /FromOr -embed_or =>{+}<-.
Time Qed.
Time #[global]
Instance from_or_bupd  `{BiBUpd PROP} P Q1 Q2:
 (FromOr P Q1 Q2 \226\134\146 FromOr (|==> P) (|==> Q1) (|==> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromOr =>{+}<-).
Time (apply or_elim; apply bupd_mono; auto using or_intro_l, or_intro_r).
Time Qed.
Time #[global]Instance into_or_or  P Q: (IntoOr (P \226\136\168 Q) P Q).
Time Proof.
Time by rewrite /IntoOr.
Time Qed.
Time #[global]Instance into_or_pure  \207\134 \207\136: (@IntoOr PROP \226\140\156\207\134 \226\136\168 \207\136\226\140\157 \226\140\156\207\134\226\140\157 \226\140\156\207\136\226\140\157).
Time Proof.
Time by rewrite /IntoOr pure_or.
Time Qed.
Time #[global]
Instance into_or_affinely  P Q1 Q2:
 (IntoOr P Q1 Q2 \226\134\146 IntoOr (<affine> P) (<affine> Q1) (<affine> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoOr =>{+}->).
Time by rewrite affinely_or.
Time Qed.
Time #[global]
Instance into_or_intuitionistically  P Q1 Q2:
 (IntoOr P Q1 Q2 \226\134\146 IntoOr (\226\150\161 P) (\226\150\161 Q1) (\226\150\161 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoOr =>{+}->).
Time by rewrite intuitionistically_or.
Time Qed.
Time #[global]
Instance into_or_absorbingly  P Q1 Q2:
 (IntoOr P Q1 Q2 \226\134\146 IntoOr (<absorb> P) (<absorb> Q1) (<absorb> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoOr =>{+}->).
Time by rewrite absorbingly_or.
Time Qed.
Time #[global]
Instance into_or_persistently  P Q1 Q2:
 (IntoOr P Q1 Q2 \226\134\146 IntoOr (<pers> P) (<pers> Q1) (<pers> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoOr =>{+}->).
Time by rewrite persistently_or.
Time Qed.
Time #[global]
Instance into_or_embed  `{BiEmbed PROP PROP'} P Q1 
 Q2: (IntoOr P Q1 Q2 \226\134\146 IntoOr \226\142\161 P \226\142\164 \226\142\161 Q1 \226\142\164 \226\142\161 Q2 \226\142\164).
Time Proof.
Time by <ssreflect_plugin::ssrtclintros@0> rewrite /IntoOr -embed_or =>{+}<-.
Time Qed.
Time #[global]
Instance from_exist_exist  {A} (\206\166 : A \226\134\146 PROP): (FromExist (\226\136\131 a, \206\166 a) \206\166).
Time Proof.
Time by rewrite /FromExist.
Time Qed.
Time #[global]
Instance from_exist_texist  {A} (\206\166 : tele_arg A \226\134\146 PROP):
 (FromExist (\226\136\131.. a, \206\166 a) \206\166).
Time Proof.
Time by rewrite /FromExist bi_texist_exist.
Time Qed.
Time #[global]
Instance from_exist_pure  {A} (\207\134 : A \226\134\146 Prop):
 (@FromExist PROP A \226\140\156\226\136\131 x, \207\134 x\226\140\157 (\206\187 a, \226\140\156\207\134 a\226\140\157)%I).
Time Proof.
Time by rewrite /FromExist pure_exist.
Time Qed.
Time #[global]
Instance from_exist_affinely  {A} P (\206\166 : A \226\134\146 PROP):
 (FromExist P \206\166 \226\134\146 FromExist (<affine> P) (\206\187 a, <affine> \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromExist =>{+}<-).
Time by rewrite affinely_exist.
Time Qed.
Time #[global]
Instance from_exist_intuitionistically  {A} P (\206\166 : A \226\134\146 PROP):
 (FromExist P \206\166 \226\134\146 FromExist (\226\150\161 P) (\206\187 a, \226\150\161 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromExist =>{+}<-).
Time by rewrite intuitionistically_exist.
Time Qed.
Time #[global]
Instance from_exist_absorbingly  {A} P (\206\166 : A \226\134\146 PROP):
 (FromExist P \206\166 \226\134\146 FromExist (<absorb> P) (\206\187 a, <absorb> \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromExist =>{+}<-).
Time by rewrite absorbingly_exist.
Time Qed.
Time #[global]
Instance from_exist_persistently  {A} P (\206\166 : A \226\134\146 PROP):
 (FromExist P \206\166 \226\134\146 FromExist (<pers> P) (\206\187 a, <pers> \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromExist =>{+}<-).
Time by rewrite persistently_exist.
Time Qed.
Time #[global]
Instance from_exist_embed  `{BiEmbed PROP PROP'} {A} 
 P (\206\166 : A \226\134\146 PROP): (FromExist P \206\166 \226\134\146 FromExist \226\142\161 P \226\142\164 (\206\187 a, \226\142\161 \206\166 a \226\142\164%I)).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /FromExist -embed_exist =>{+}<-.
Time Qed.
Time #[global]
Instance from_exist_bupd  `{BiBUpd PROP} {A} P (\206\166 : A \226\134\146 PROP):
 (FromExist P \206\166 \226\134\146 FromExist (|==> P) (\206\187 a, |==> \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromExist =>{+}<-).
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>a).
Time by rewrite -(exist_intro a).
Time Qed.
Time #[global]
Instance into_exist_exist  {A} (\206\166 : A \226\134\146 PROP): (IntoExist (\226\136\131 a, \206\166 a) \206\166).
Time Proof.
Time by rewrite /IntoExist.
Time Qed.
Time #[global]
Instance into_exist_texist  {A} (\206\166 : tele_arg A \226\134\146 PROP):
 (IntoExist (\226\136\131.. a, \206\166 a) \206\166) |10.
Time Proof.
Time by rewrite /IntoExist bi_texist_exist.
Time Qed.
Time #[global]
Instance into_exist_pure  {A} (\207\134 : A \226\134\146 Prop):
 (@IntoExist PROP A \226\140\156\226\136\131 x, \207\134 x\226\140\157 (\206\187 a, \226\140\156\207\134 a\226\140\157)%I).
Time Proof.
Time by rewrite /IntoExist pure_exist.
Time Qed.
Time #[global]
Instance into_exist_affinely  {A} P (\206\166 : A \226\134\146 PROP):
 (IntoExist P \206\166 \226\134\146 IntoExist (<affine> P) (\206\187 a, <affine> \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExist =>HP).
Time by rewrite HP affinely_exist.
Time Qed.
Time #[global]
Instance into_exist_intuitionistically  {A} P (\206\166 : A \226\134\146 PROP):
 (IntoExist P \206\166 \226\134\146 IntoExist (\226\150\161 P) (\206\187 a, \226\150\161 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExist =>HP).
Time by rewrite HP intuitionistically_exist.
Time Qed.
Time #[global]
Instance into_exist_and_pure  P Q \207\134:
 (IntoPureT P \207\134 \226\134\146 IntoExist (P \226\136\167 Q) (\206\187 _ : \207\134, Q)).
Time Proof.
Time (intros (\207\134', (->, ?))).
Time rewrite /IntoExist (into_pure P).
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>H\207\134).
Time by rewrite -(exist_intro H\207\134).
Time Qed.
Time #[global]
Instance into_exist_sep_pure  P Q \207\134:
 (IntoPureT P \207\134
  \226\134\146 TCOr (Affine P) (Absorbing Q) \226\134\146 IntoExist (P \226\136\151 Q) (\206\187 _ : \207\134, Q)).
Time Proof.
Time (intros (\207\134', (->, ?)) ?).
Time rewrite /IntoExist.
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply (pure_elim \207\134'); [ by rewrite (into_pure P); apply sep_elim_l, _ |  ]
 =>?).
Time rewrite -exist_intro //.
Time (apply sep_elim_r, _).
Time Qed.
Time #[global]
Instance into_exist_absorbingly  {A} P (\206\166 : A \226\134\146 PROP):
 (IntoExist P \206\166 \226\134\146 IntoExist (<absorb> P) (\206\187 a, <absorb> \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExist =>HP).
Time by rewrite HP absorbingly_exist.
Time Qed.
Time #[global]
Instance into_exist_persistently  {A} P (\206\166 : A \226\134\146 PROP):
 (IntoExist P \206\166 \226\134\146 IntoExist (<pers> P) (\206\187 a, <pers> \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExist =>HP).
Time by rewrite HP persistently_exist.
Time Qed.
Time #[global]
Instance into_exist_embed  `{BiEmbed PROP PROP'} {A} 
 P (\206\166 : A \226\134\146 PROP): (IntoExist P \206\166 \226\134\146 IntoExist \226\142\161 P \226\142\164 (\206\187 a, \226\142\161 \206\166 a \226\142\164%I)).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /IntoExist -embed_exist =>{+}<-.
Time Qed.
Time #[global]
Instance into_forall_forall  {A} (\206\166 : A \226\134\146 PROP): (IntoForall (\226\136\128 a, \206\166 a) \206\166).
Time Proof.
Time by rewrite /IntoForall.
Time Qed.
Time #[global]
Instance into_forall_tforall  {A} (\206\166 : tele_arg A \226\134\146 PROP):
 (IntoForall (\226\136\128.. a, \206\166 a) \206\166) |10.
Time Proof.
Time by rewrite /IntoForall bi_tforall_forall.
Time Qed.
Time #[global]
Instance into_forall_affinely  {A} P (\206\166 : A \226\134\146 PROP):
 (IntoForall P \206\166 \226\134\146 IntoForall (<affine> P) (\206\187 a, <affine> \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoForall =>HP).
Time by rewrite HP affinely_forall.
Time Qed.
Time #[global]
Instance into_forall_intuitionistically  {A} P (\206\166 : A \226\134\146 PROP):
 (IntoForall P \206\166 \226\134\146 IntoForall (\226\150\161 P) (\206\187 a, \226\150\161 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoForall =>HP).
Time by rewrite HP intuitionistically_forall.
Time Qed.
Time #[global]
Instance into_forall_persistently  {A} P (\206\166 : A \226\134\146 PROP):
 (IntoForall P \206\166 \226\134\146 IntoForall (<pers> P) (\206\187 a, <pers> \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoForall =>HP).
Time by rewrite HP persistently_forall.
Time Qed.
Time #[global]
Instance into_forall_embed  `{BiEmbed PROP PROP'} 
 {A} P (\206\166 : A \226\134\146 PROP): (IntoForall P \206\166 \226\134\146 IntoForall \226\142\161 P \226\142\164 (\206\187 a, \226\142\161 \206\166 a \226\142\164%I)).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /IntoForall -embed_forall
 =>{+}<-.
Time Qed.
Time #[global]
Instance into_forall_impl_pure  a \207\134 P Q:
 (FromPureT a P \207\134
  \226\134\146 TCOr (TCEq a false) (BiAffine PROP) \226\134\146 IntoForall (P \226\134\146 Q) (\206\187 _ : \207\134, Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromPureT /FromPure /IntoForall
 =>- [\207\134' [{+}-> {+}<-]] [{+}->|?] /=).
Time -
Time by rewrite pure_impl_forall.
Time -
Time by rewrite -affinely_affinely_if affine_affinely pure_impl_forall.
Time Qed.
Time #[global]
Instance into_forall_wand_pure  a \207\134 P Q:
 (FromPureT a P \207\134 \226\134\146 IntoForall (P -\226\136\151 Q) (\206\187 _ : \207\134, Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromPureT /FromPure /IntoForall
 =>- [\207\134' [{+}-> {+}<-]] /=).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>? /=).
Time rewrite -affinely_affinely_if.
Time by rewrite -(pure_intro _ True%I) // /bi_affinely right_id emp_wand.
Time Qed.
Time #[global]
Instance into_forall_wand  P Q:
 (IntoForall (P -\226\136\151 Q) (\206\187 _ : bi_emp_valid P, Q)) |10.
Time Proof.
Time rewrite /IntoForall.
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>{+}<-).
Time rewrite emp_wand //.
Time Qed.
Time #[global]
Instance into_forall_impl  `{!BiAffine PROP} P Q:
 (IntoForall (P \226\134\146 Q) (\206\187 _ : bi_emp_valid P, Q)) |10.
Time Proof.
Time rewrite /IntoForall.
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>{+}<-).
Time rewrite -True_emp True_impl //.
Time Qed.
Time #[global]
Instance from_forall_forall  {A} (\206\166 : A \226\134\146 PROP): (FromForall (\226\136\128 x, \206\166 x)%I \206\166).
Time Proof.
Time by rewrite /FromForall.
Time Qed.
Time #[global]
Instance from_forall_tforall  {A} (\206\166 : tele_arg A \226\134\146 PROP):
 (FromForall (\226\136\128.. x, \206\166 x)%I \206\166).
Time Proof.
Time by rewrite /FromForall bi_tforall_forall.
Time Qed.
Time #[global]
Instance from_forall_pure  {A} (\207\134 : A \226\134\146 Prop):
 (@FromForall PROP A \226\140\156\226\136\128 a : A, \207\134 a\226\140\157%I (\206\187 a, \226\140\156\207\134 a\226\140\157)%I).
Time Proof.
Time by rewrite /FromForall pure_forall.
Time Qed.
Time #[global]
Instance from_forall_pure_not  (\207\134 : Prop):
 (@FromForall PROP \207\134 \226\140\156\194\172 \207\134\226\140\157%I (\206\187 a : \207\134, False)%I).
Time Proof.
Time by rewrite /FromForall pure_forall.
Time Qed.
Time #[global]
Instance from_forall_impl_pure  P Q \207\134:
 (IntoPureT P \207\134 \226\134\146 FromForall (P \226\134\146 Q)%I (\206\187 _ : \207\134, Q)%I).
Time Proof.
Time (intros (\207\134', (->, ?))).
Time by rewrite /FromForall -pure_impl_forall (into_pure P).
Time Qed.
Time #[global]
Instance from_forall_wand_pure  P Q \207\134:
 (IntoPureT P \207\134
  \226\134\146 TCOr (Affine P) (Absorbing Q) \226\134\146 FromForall (P -\226\136\151 Q)%I (\206\187 _ : \207\134, Q)%I).
Time Proof.
Time (intros (\207\134', (->, ?)) [| ]; rewrite /FromForall; apply wand_intro_r).
Time -
Time
rewrite -(affine_affinely P) (into_pure P) -persistent_and_affinely_sep_r.
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim_r =>?).
Time by rewrite forall_elim.
Time -
Time by rewrite (into_pure P) -pure_wand_forall wand_elim_l.
Time Qed.
Time #[global]
Instance from_forall_intuitionistically  `{BiAffine PROP} 
 {A} P (\206\166 : A \226\134\146 PROP): (FromForall P \206\166 \226\134\146 FromForall (\226\150\161 P) (\206\187 a, \226\150\161 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromForall =>{+}<-).
Time setoid_rewrite intuitionistically_into_persistently.
Time by rewrite persistently_forall.
Time Qed.
Time #[global]
Instance from_forall_persistently  {A} P (\206\166 : A \226\134\146 PROP):
 (FromForall P \206\166 \226\134\146 FromForall (<pers> P)%I (\206\187 a, <pers> \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromForall =>{+}<-).
Time by rewrite persistently_forall.
Time Qed.
Time #[global]
Instance from_forall_embed  `{BiEmbed PROP PROP'} 
 {A} P (\206\166 : A \226\134\146 PROP): (FromForall P \206\166 \226\134\146 FromForall \226\142\161 P \226\142\164%I (\206\187 a, \226\142\161 \206\166 a \226\142\164%I)).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /FromForall -embed_forall
 =>{+}<-.
Time Qed.
Time #[global]
Instance into_inv_embed  {PROP' : bi} `{BiEmbed PROP PROP'} 
 P N: (IntoInv P N \226\134\146 IntoInv \226\142\161 P \226\142\164 N) := { }.
Time #[global]
Instance elim_modal_wand  \207\134 p p' P P' Q Q' R:
 (ElimModal \207\134 p p' P P' Q Q' \226\134\146 ElimModal \207\134 p p' P P' (R -\226\136\151 Q) (R -\226\136\151 Q')).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /ElimModal =>H H\207\134).
Time (apply wand_intro_r).
Time
(rewrite wand_curry -assoc (comm _ (\226\150\161?p' _)%I) -wand_curry wand_elim_l; auto).
Time Qed.
Time #[global]
Instance elim_modal_wandM  \207\134 p p' P P' Q Q' mR:
 (ElimModal \207\134 p p' P P' Q Q' \226\134\146 ElimModal \207\134 p p' P P' (mR -\226\136\151? Q) (mR -\226\136\151? Q')).
Time Proof.
Time rewrite /ElimModal !wandM_sound.
Time exact : {}elim_modal_wand {}.
Time Qed.
Time #[global]
Instance elim_modal_forall  {A} \207\134 p p' P P' (\206\166 \206\168 : A \226\134\146 PROP):
 ((\226\136\128 x, ElimModal \207\134 p p' P P' (\206\166 x) (\206\168 x))
  \226\134\146 ElimModal \207\134 p p' P P' (\226\136\128 x, \206\166 x) (\226\136\128 x, \206\168 x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /ElimModal =>H ?).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>a).
Time (rewrite (forall_elim a); auto).
Time Qed.
Time #[global]
Instance elim_modal_absorbingly_here  p P Q:
 (Absorbing Q \226\134\146 ElimModal True p false (<absorb> P) P Q Q).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /ElimModal =>? _).
Time
by rewrite intuitionistically_if_elim absorbingly_sep_l wand_elim_r
 absorbing_absorbingly.
Time Qed.
Time #[global]
Instance elim_modal_bupd  `{BiBUpd PROP} p P Q:
 (ElimModal True p false (|==> P) P (|==> Q) (|==> Q)).
Time Proof.
Time
by rewrite /ElimModal intuitionistically_if_elim bupd_frame_r wand_elim_r
 bupd_trans.
Time Qed.
Time #[global]
Instance elim_modal_embed_bupd_goal  `{BiEmbedBUpd PROP PROP'} 
 p p' \207\134 (P P' : PROP') (Q Q' : PROP):
 (ElimModal \207\134 p p' P P' (|==> \226\142\161 Q \226\142\164)%I (|==> \226\142\161 Q' \226\142\164)%I
  \226\134\146 ElimModal \207\134 p p' P P' \226\142\161 |==> Q \226\142\164 \226\142\161 |==> Q' \226\142\164).
Time Proof.
Time by rewrite /ElimModal !embed_bupd.
Time Qed.
Time #[global]
Instance elim_modal_embed_bupd_hyp  `{BiEmbedBUpd PROP PROP'} 
 p p' \207\134 (P : PROP) (P' Q Q' : PROP'):
 (ElimModal \207\134 p p' (|==> \226\142\161 P \226\142\164)%I P' Q Q'
  \226\134\146 ElimModal \207\134 p p' \226\142\161 |==> P \226\142\164 P' Q Q').
Time Proof.
Time by rewrite /ElimModal !embed_bupd.
Time Qed.
Time #[global]
Instance add_modal_wand  P P' Q R: (AddModal P P' Q \226\134\146 AddModal P P' (R -\226\136\151 Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /AddModal =>H).
Time (apply wand_intro_r).
Time by rewrite wand_curry -assoc (comm _ P') -wand_curry wand_elim_l.
Time Qed.
Time #[global]
Instance add_modal_wandM  P P' Q mR:
 (AddModal P P' Q \226\134\146 AddModal P P' (mR -\226\136\151? Q)).
Time Proof.
Time rewrite /AddModal wandM_sound.
Time exact : {}add_modal_wand {}.
Time Qed.
Time #[global]
Instance add_modal_forall  {A} P P' (\206\166 : A \226\134\146 PROP):
 ((\226\136\128 x, AddModal P P' (\206\166 x)) \226\134\146 AddModal P P' (\226\136\128 x, \206\166 x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /AddModal =>H).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>a).
Time by rewrite (forall_elim a).
Time Qed.
Time #[global]
Instance add_modal_embed_bupd_goal  `{BiEmbedBUpd PROP PROP'} 
 (P P' : PROP') (Q : PROP):
 (AddModal P P' (|==> \226\142\161 Q \226\142\164)%I \226\134\146 AddModal P P' \226\142\161 |==> Q \226\142\164).
Time Proof.
Time by rewrite /AddModal !embed_bupd.
Time Qed.
Time #[global]
Instance add_modal_bupd  `{BiBUpd PROP} P Q: (AddModal (|==> P) P (|==> Q)).
Time Proof.
Time by rewrite /AddModal bupd_frame_r wand_elim_r bupd_trans.
Time Qed.
Time #[global]
Instance elim_inv_acc_without_close  {X : Type} \207\134 
 Pinv Pin M1 M2 \206\177 \206\178 m\206\179 Q (Q' : X \226\134\146 PROP):
 (IntoAcc (X:=X) Pinv \207\134 Pin M1 M2 \206\177 \206\178 m\206\179
  \226\134\146 ElimAcc (X:=X) M1 M2 \206\177 \206\178 m\206\179 Q Q' \226\134\146 ElimInv \207\134 Pinv Pin \206\177 None Q Q').
Time Proof.
Time rewrite /ElimAcc /IntoAcc /ElimInv.
Time iIntros ( Hacc Helim H\207\134 ) "(Hinv & Hin & Hcont)".
Time iApply (Helim with "[Hcont]").
Time -
Time iIntros ( x ) "H\206\177".
Time iApply "Hcont".
Time (iSplitL; simpl; done).
Time -
Time iApply (Hacc with "Hinv Hin").
Time done.
Time Qed.
Time #[global]
Instance elim_inv_acc_with_close  {X : Type} \207\1341 \207\1342 
 Pinv Pin M1 M2 \206\177 \206\178 m\206\179 Q Q':
 (IntoAcc Pinv \207\1341 Pin M1 M2 \206\177 \206\178 m\206\179
  \226\134\146 (\226\136\128 R, ElimModal \207\1342 false false (M1 R) R Q Q')
    \226\134\146 ElimInv (X:=X) (\207\1341 \226\136\167 \207\1342) Pinv Pin \206\177
        (Some (\206\187 x, \206\178 x -\226\136\151 M2 (pm_default emp (m\206\179 x))))%I Q 
        (\206\187 _, Q')).
Time Proof.
Time rewrite /ElimAcc /IntoAcc /ElimInv.
Time iIntros ( Hacc Helim [? ?] ) "(Hinv & Hin & Hcont)".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (Hacc with "Hinv Hin") as ( x )
 "[H\206\177 Hclose]" ; first  done).
Time iApply "Hcont".
Time (simpl).
Time (iSplitL "H\206\177"; done).
Time Qed.
Time #[global]
Instance into_embed_embed  {PROP' : bi} `{BiEmbed PROP PROP'} 
 P: (IntoEmbed \226\142\161 P \226\142\164 P).
Time Proof.
Time by rewrite /IntoEmbed.
Time Qed.
Time #[global]
Instance into_embed_affinely  `{BiEmbedBUpd PROP PROP'} 
 (P : PROP') (Q : PROP):
 (IntoEmbed P Q \226\134\146 IntoEmbed (<affine> P) (<affine> Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoEmbed =>{+}->).
Time by rewrite embed_affinely_2.
Time Qed.
Time End bi_instances.
