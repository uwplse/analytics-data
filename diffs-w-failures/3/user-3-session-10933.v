Time From stdpp Require Import coPset.
Time From iris.bi Require Import interface derived_laws_sbi big_op plainly.
Time Import interface.bi derived_laws_bi.bi derived_laws_sbi.bi.
Time Class BUpd (PROP : Type) : Type :=
         bupd : PROP \226\134\146 PROP.
Time Instance: (Params (@bupd) 2) := { }.
Time Hint Mode BUpd !: typeclass_instances.
Time Notation "|==> Q" := (bupd Q) : bi_scope.
Time Notation "P ==\226\136\151 Q" := (P \226\138\162 |==> Q) (only parsing) : stdpp_scope.
Time Notation "P ==\226\136\151 Q" := (P -\226\136\151 |==> Q)%I : bi_scope.
Time
Class FUpd (PROP : Type) : Type :=
    fupd : coPset \226\134\146 coPset \226\134\146 PROP \226\134\146 PROP.
Time Instance: (Params (@fupd) 4) := { }.
Time Hint Mode FUpd !: typeclass_instances.
Time Notation "|={ E1 , E2 }=> Q" := (fupd E1 E2 Q) : bi_scope.
Time Notation "P ={ E1 , E2 }=\226\136\151 Q" := (P -\226\136\151 |={E1,E2}=> Q)%I : bi_scope.
Time Notation "P ={ E1 , E2 }=\226\136\151 Q" := (P -\226\136\151 |={E1,E2}=> Q) : stdpp_scope.
Time Notation "|={ E }=> Q" := (fupd E E Q) : bi_scope.
Time Notation "P ={ E }=\226\136\151 Q" := (P -\226\136\151 |={E}=> Q)%I : bi_scope.
Time Notation "P ={ E }=\226\136\151 Q" := (P -\226\136\151 |={E}=> Q) : stdpp_scope.
Time
Notation "|={ E1 , E2 , E3 }\226\150\183=> Q" := (|={E1,E2}=> \226\150\183 (|={E2,E3}=> Q))%I :
  bi_scope.
Time
Notation "P ={ E1 , E2 , E3 }\226\150\183=\226\136\151 Q" := (P -\226\136\151 |={E1,E2,E3}\226\150\183=> Q)%I : bi_scope.
Time Notation "|={ E1 , E2 }\226\150\183=> Q" := (|={E1,E2,E1}\226\150\183=> Q)%I : bi_scope.
Time
Notation "P ={ E1 , E2 }\226\150\183=\226\136\151 Q" := (P \226\138\162 |={E1,E2,E1}\226\150\183=> Q) 
  (only parsing) : stdpp_scope.
Time Notation "P ={ E1 , E2 }\226\150\183=\226\136\151 Q" := (P -\226\136\151 |={E1,E2,E1}\226\150\183=> Q)%I : bi_scope.
Time Notation "|={ E }\226\150\183=> Q" := (|={E,E}\226\150\183=> Q)%I : bi_scope.
Time Notation "P ={ E }\226\150\183=\226\136\151 Q" := (P ={E,E}\226\150\183=\226\136\151 Q)%I : bi_scope.
Time
Notation "|={ E1 , E2 }\226\150\183=>^ n Q" := (Nat.iter n (\206\187 P, |={E1,E2}\226\150\183=> P) Q)%I :
  bi_scope.
Time
Notation "P ={ E1 , E2 }\226\150\183=\226\136\151^ n Q" := (P \226\138\162 |={E1,E2}\226\150\183=>^n Q)%I
  (only parsing) : stdpp_scope.
Time
Notation "P ={ E1 , E2 }\226\150\183=\226\136\151^ n Q" := (P -\226\136\151 |={E1,E2}\226\150\183=>^n Q)%I : bi_scope.
Time
Record BiBUpdMixin (PROP : bi) `(BUpd PROP) :={bi_bupd_mixin_bupd_ne :
                                                NonExpansive
                                                 (bupd (PROP:=PROP));
                                               bi_bupd_mixin_bupd_intro :
                                                forall P : PROP, P ==\226\136\151 P;
                                               bi_bupd_mixin_bupd_mono :
                                                forall P Q : PROP,
                                                (P \226\138\162 Q) \226\134\146 (|==> P) ==\226\136\151 Q;
                                               bi_bupd_mixin_bupd_trans :
                                                forall P : PROP,
                                                (|==> |==> P) ==\226\136\151 P;
                                               bi_bupd_mixin_bupd_frame_r :
                                                forall P R : PROP,
                                                (|==> P) \226\136\151 R ==\226\136\151 P \226\136\151 R}.
Time
Record BiFUpdMixin (PROP : sbi) `(FUpd PROP) :={bi_fupd_mixin_fupd_ne :
                                                 forall E1 E2,
                                                 NonExpansive
                                                 (fupd (PROP:=PROP) E1 E2);
                                                bi_fupd_mixin_fupd_intro_mask :
                                                 forall E1 E2 (P : PROP),
                                                 E2 \226\138\134 E1
                                                 \226\134\146 
                                                 P
                                                 \226\138\162 |={E1,E2}=> |={E2,E1}=> P;
                                                bi_fupd_mixin_except_0_fupd :
                                                 forall E1 E2 (P : PROP),
                                                 \226\151\135 
                                                 (|={E1,E2}=> P) ={E1,E2}=\226\136\151 P;
                                                bi_fupd_mixin_fupd_mono :
                                                 forall E1 E2 (P Q : PROP),
                                                 (P \226\138\162 Q)
                                                 \226\134\146 
                                                 (|={E1,E2}=> P)
                                                 \226\138\162 |={E1,E2}=> Q;
                                                bi_fupd_mixin_fupd_trans :
                                                 forall E1 E2 E3 (P : PROP),
                                                 (|={E1,E2}=> |={E2,E3}=> P)
                                                 \226\138\162 |={E1,E3}=> P;
                                                bi_fupd_mixin_fupd_mask_frame_r' :
                                                 forall E1 E2 Ef (P : PROP),
                                                 E1 ## Ef
                                                 \226\134\146 
                                                 (|={E1,E2}=> \226\140\156E2 ## Ef\226\140\157 \226\134\146 P)
                                                 ={
                                                 E1 \226\136\170 Ef,
                                                 E2 \226\136\170 Ef}=\226\136\151 P;
                                                bi_fupd_mixin_fupd_frame_r :
                                                 forall E1 E2 (P R : PROP),
                                                 (|={E1,E2}=> P) \226\136\151 R
                                                 ={E1,E2}=\226\136\151 
                                                 P \226\136\151 R}.
Time
Class BiBUpd (PROP : bi) :={bi_bupd_bupd :> BUpd PROP;
                            bi_bupd_mixin : BiBUpdMixin PROP bi_bupd_bupd}.
Time Hint Mode BiBUpd !: typeclass_instances.
Time Arguments bi_bupd_bupd : simpl never.
Time
Class BiFUpd (PROP : sbi) :={bi_fupd_fupd :> FUpd PROP;
                             bi_fupd_mixin : BiFUpdMixin PROP bi_fupd_fupd}.
Time Hint Mode BiFUpd !: typeclass_instances.
Time Arguments bi_fupd_fupd : simpl never.
Time
Class BiBUpdFUpd (PROP : sbi) `{BiBUpd PROP} `{BiFUpd PROP} :=
    bupd_fupd : forall E (P : PROP), (|==> P) ={E}=\226\136\151 P.
Time Hint Mode BiBUpdFUpd ! - -: typeclass_instances.
Time
Class BiBUpdPlainly (PROP : sbi) `{!BiBUpd PROP} `{!BiPlainly PROP} :=
    bupd_plainly : forall P : PROP, (|==> \226\150\160 P) -\226\136\151 P.
Time Hint Mode BiBUpdPlainly ! - -: typeclass_instances.
Time
Class BiFUpdPlainly (PROP : sbi) `{!BiFUpd PROP} `{!BiPlainly PROP} :={
 fupd_plainly_mask_empty : forall E (P : PROP), (|={E,\226\136\133}=> \226\150\160 P) \226\138\162 |={E}=> P;
 fupd_plainly_keep_l :
  forall E (P R : PROP), (R ={E}=\226\136\151 \226\150\160 P) \226\136\151 R \226\138\162 |={E}=> P \226\136\151 R;
 fupd_plainly_later : forall E (P : PROP), \226\150\183 (|={E}=> \226\150\160 P) \226\138\162 |={E}=> \226\150\183 \226\151\135 P;
 fupd_plainly_forall_2 :
  forall E {A} (\206\166 : A \226\134\146 PROP), (\226\136\128 x, |={E}=> \226\150\160 \206\166 x) \226\138\162 |={E}=> \226\136\128 x, \206\166 x}.
Time Hint Mode BiBUpdFUpd ! - -: typeclass_instances.
Time Section bupd_laws.
Time Context `{BiBUpd PROP}.
Time Implicit Type P : PROP.
Time #[global]Instance bupd_ne : (NonExpansive (@bupd PROP _)).
Time Proof.
Time (eapply bi_bupd_mixin_bupd_ne, bi_bupd_mixin).
Time Qed.
Time Lemma bupd_intro P : P ==\226\136\151 P.
Time Proof.
Time (eapply bi_bupd_mixin_bupd_intro, bi_bupd_mixin).
Time Qed.
Time Lemma bupd_mono (P Q : PROP) : (P \226\138\162 Q) \226\134\146 (|==> P) ==\226\136\151 Q.
Time Proof.
Time (eapply bi_bupd_mixin_bupd_mono, bi_bupd_mixin).
Time Qed.
Time Lemma bupd_trans (P : PROP) : (|==> |==> P) ==\226\136\151 P.
Time Proof.
Time (eapply bi_bupd_mixin_bupd_trans, bi_bupd_mixin).
Time Qed.
Time Lemma bupd_frame_r (P R : PROP) : (|==> P) \226\136\151 R ==\226\136\151 P \226\136\151 R.
Time Proof.
Time (eapply bi_bupd_mixin_bupd_frame_r, bi_bupd_mixin).
Time Qed.
Time End bupd_laws.
Time Section fupd_laws.
Time Context `{BiFUpd PROP}.
Time Implicit Type P : PROP.
Time #[global]Instance fupd_ne  E1 E2: (NonExpansive (@fupd PROP _ E1 E2)).
Time Proof.
Time (eapply bi_fupd_mixin_fupd_ne, bi_fupd_mixin).
Time Qed.
Time
Lemma fupd_intro_mask E1 E2 (P : PROP) :
  E2 \226\138\134 E1 \226\134\146 P \226\138\162 |={E1,E2}=> |={E2,E1}=> P.
Time Proof.
Time (eapply bi_fupd_mixin_fupd_intro_mask, bi_fupd_mixin).
Time Qed.
Time Lemma except_0_fupd E1 E2 (P : PROP) : \226\151\135 (|={E1,E2}=> P) ={E1,E2}=\226\136\151 P.
Time Proof.
Time (eapply bi_fupd_mixin_except_0_fupd, bi_fupd_mixin).
Time Qed.
Time
Lemma fupd_mono E1 E2 (P Q : PROP) :
  (P \226\138\162 Q) \226\134\146 (|={E1,E2}=> P) \226\138\162 |={E1,E2}=> Q.
Time Proof.
Time (eapply bi_fupd_mixin_fupd_mono, bi_fupd_mixin).
Time Qed.
Time
Lemma fupd_trans E1 E2 E3 (P : PROP) :
  (|={E1,E2}=> |={E2,E3}=> P) \226\138\162 |={E1,E3}=> P.
Time Proof.
Time (eapply bi_fupd_mixin_fupd_trans, bi_fupd_mixin).
Time Qed.
Time
Lemma fupd_mask_frame_r' E1 E2 Ef (P : PROP) :
  E1 ## Ef \226\134\146 (|={E1,E2}=> \226\140\156E2 ## Ef\226\140\157 \226\134\146 P) ={E1 \226\136\170 Ef,E2 \226\136\170 Ef}=\226\136\151 P.
Time Proof.
Time (eapply bi_fupd_mixin_fupd_mask_frame_r', bi_fupd_mixin).
Time Qed.
Time
Lemma fupd_frame_r E1 E2 (P R : PROP) : (|={E1,E2}=> P) \226\136\151 R ={E1,E2}=\226\136\151 P \226\136\151 R.
Time Proof.
Time (eapply bi_fupd_mixin_fupd_frame_r, bi_fupd_mixin).
Time Qed.
Time End fupd_laws.
Time Section bupd_derived.
Time Context `{BiBUpd PROP}.
Time Implicit Types P Q R : PROP.
Time #[global]
Instance bupd_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (bupd (PROP:=PROP))) :=
 (ne_proper _).
Time #[global]
Instance bupd_mono' : (Proper ((\226\138\162) ==> (\226\138\162)) (bupd (PROP:=PROP))).
Time Proof.
Time (intros P Q; apply bupd_mono).
Time Qed.
Time #[global]
Instance bupd_flip_mono' :
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (bupd (PROP:=PROP))).
Time Proof.
Time (intros P Q; apply bupd_mono).
Time Qed.
Time Lemma bupd_frame_l R Q : R \226\136\151 (|==> Q) ==\226\136\151 R \226\136\151 Q.
Time Proof.
Time (rewrite !(comm _ R); apply bupd_frame_r).
Time Qed.
Time Lemma bupd_wand_l P Q : (P -\226\136\151 Q) \226\136\151 (|==> P) ==\226\136\151 Q.
Time Proof.
Time by rewrite bupd_frame_l wand_elim_l.
Time Qed.
Time Lemma bupd_wand_r P Q : (|==> P) \226\136\151 (P -\226\136\151 Q) ==\226\136\151 Q.
Time Proof.
Time by rewrite bupd_frame_r wand_elim_r.
Time Qed.
Time Lemma bupd_sep P Q : (|==> P) \226\136\151 (|==> Q) ==\226\136\151 P \226\136\151 Q.
Time Proof.
Time by rewrite bupd_frame_r bupd_frame_l bupd_trans.
Time Qed.
Time #[global]
Instance bupd_homomorphism :
 (MonoidHomomorphism bi_sep bi_sep (flip (\226\138\162)) (bupd (PROP:=PROP))).
Time Proof.
Time (split; [ split |  ]; try apply _).
Time (apply bupd_sep).
Time (apply bupd_intro).
Time Qed.
Time
Lemma big_sepL_bupd {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP) l :
  ([\226\136\151 list] k\226\134\166x \226\136\136 l, |==> \206\166 k x) \226\138\162 |==> [\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x.
Time Proof.
Time by rewrite (big_opL_commute _).
Time Qed.
Time
Lemma big_sepM_bupd {A} `{Countable K} (\206\166 : K \226\134\146 A \226\134\146 PROP) 
  l : ([\226\136\151 map] k\226\134\166x \226\136\136 l, |==> \206\166 k x) \226\138\162 |==> [\226\136\151 map] k\226\134\166x \226\136\136 l, \206\166 k x.
Time Proof.
Time by rewrite (big_opM_commute _).
Time Qed.
Time
Lemma big_sepS_bupd `{Countable A} (\206\166 : A \226\134\146 PROP) 
  l : ([\226\136\151 set] x \226\136\136 l, |==> \206\166 x) \226\138\162 |==> [\226\136\151 set] x \226\136\136 l, \206\166 x.
Time Proof.
Time by rewrite (big_opS_commute _).
Time Qed.
Time
Lemma big_sepMS_bupd `{Countable A} (\206\166 : A \226\134\146 PROP) 
  l : ([\226\136\151 mset] x \226\136\136 l, |==> \206\166 x) \226\138\162 |==> [\226\136\151 mset] x \226\136\136 l, \206\166 x.
Time Proof.
Time by rewrite (big_opMS_commute _).
Time Qed.
Time End bupd_derived.
Time Section bupd_derived_sbi.
Time Context {PROP : sbi} `{BiBUpd PROP}.
Time Implicit Types P Q R : PROP.
Time Lemma except_0_bupd P : \226\151\135 (|==> P) \226\138\162 |==> \226\151\135 P.
Time Proof.
Time rewrite /sbi_except_0.
Time (apply or_elim; eauto using bupd_mono, or_intro_r).
Time by rewrite -bupd_intro -or_intro_l.
Time Qed.
Time Section bupd_plainly.
Time Context `{BiBUpdPlainly PROP}.
Time Lemma bupd_plain P `{!Plain P} : (|==> P) \226\138\162 P.
Time Proof.
Time by rewrite {+1}(plain P) bupd_plainly.
Time Qed.
Time
Lemma bupd_forall {A} (\206\166 : A \226\134\146 PROP) `{\226\136\128 x, Plain (\206\166 x)} :
  (|==> \226\136\128 x, \206\166 x) \226\138\163\226\138\162 (\226\136\128 x, |==> \206\166 x).
Time Proof.
Time (apply (anti_symm _)).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time by rewrite (forall_elim x).
Time -
Time rewrite -bupd_intro.
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time by rewrite (forall_elim x) bupd_plain.
Time Qed.
Time End bupd_plainly.
Time End bupd_derived_sbi.
Time Section fupd_derived.
Time Context `{BiFUpd PROP}.
Time Implicit Types P Q R : PROP.
Time #[global]
Instance fupd_proper  E1 E2: (Proper ((\226\137\161) ==> (\226\137\161)) (fupd (PROP:=PROP) E1 E2))
 := (ne_proper _).
Time #[global]
Instance fupd_mono'  E1 E2: (Proper ((\226\138\162) ==> (\226\138\162)) (fupd (PROP:=PROP) E1 E2)).
Time Proof.
Time (intros P Q; apply fupd_mono).
Time Qed.
Time #[global]
Instance fupd_flip_mono'  E1 E2:
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (fupd (PROP:=PROP) E1 E2)).
Time Proof.
Time (intros P Q; apply fupd_mono).
Time Qed.
Time Lemma fupd_intro E P : P ={E}=\226\136\151 P.
Time Proof.
Time by rewrite {+1}(fupd_intro_mask E E P) // fupd_trans.
Time Qed.
Time
Lemma fupd_intro_mask' E1 E2 :
  E2 \226\138\134 E1 \226\134\146 (|={E1,E2}=> |={E2,E1}=> bi_emp (PROP:=PROP))%I.
Time Proof.
Time exact : {}fupd_intro_mask {}.
Time Qed.
Time Lemma fupd_except_0 E1 E2 P : (|={E1,E2}=> \226\151\135 P) ={E1,E2}=\226\136\151 P.
Time Proof.
Time by rewrite {+1}(fupd_intro E2 P) except_0_fupd fupd_trans.
Time Qed.
Time Lemma fupd_frame_l E1 E2 R Q : R \226\136\151 (|={E1,E2}=> Q) ={E1,E2}=\226\136\151 R \226\136\151 Q.
Time Proof.
Time (rewrite !(comm _ R); apply fupd_frame_r).
Time Qed.
Time Lemma fupd_wand_l E1 E2 P Q : (P -\226\136\151 Q) \226\136\151 (|={E1,E2}=> P) ={E1,E2}=\226\136\151 Q.
Time Proof.
Time by rewrite fupd_frame_l wand_elim_l.
Time Qed.
Time Lemma fupd_wand_r E1 E2 P Q : (|={E1,E2}=> P) \226\136\151 (P -\226\136\151 Q) ={E1,E2}=\226\136\151 Q.
Time Proof.
Time by rewrite fupd_frame_r wand_elim_r.
Time Qed.
Time
Lemma fupd_mask_weaken E1 E2 P `{!Absorbing P} : E2 \226\138\134 E1 \226\134\146 P ={E1,E2}=\226\136\151 P.
Time Proof.
Time (intros ?).
Time rewrite -{+1}(right_id emp%I bi_sep P%I).
Time rewrite (fupd_intro_mask E1 E2 emp%I) //.
Time by rewrite fupd_frame_l sep_elim_l.
Time Qed.
Time
Lemma fupd_trans_frame E1 E2 E3 P Q :
  (Q ={E2,E3}=\226\136\151 emp) \226\136\151 (|={E1,E2}=> Q \226\136\151 P) ={E1,E3}=\226\136\151 P.
Time Proof.
Time rewrite fupd_frame_l assoc -(comm _ Q) wand_elim_r.
Time by rewrite fupd_frame_r left_id fupd_trans.
Time Qed.
Time
Lemma fupd_elim E1 E2 E3 P Q :
  (Q -\226\136\151 |={E2,E3}=> P) \226\134\146 (|={E1,E2}=> Q) -\226\136\151 |={E1,E3}=> P.
Time Proof.
Time (intros ->).
Time rewrite fupd_trans //.
Time Qed.
Time
Lemma fupd_mask_frame_r E1 E2 Ef P :
  E1 ## Ef \226\134\146 (|={E1,E2}=> P) ={E1 \226\136\170 Ef,E2 \226\136\170 Ef}=\226\136\151 P.
Time Proof.
Time (intros ?).
Time rewrite -fupd_mask_frame_r' //.
Time f_equiv.
Time (apply impl_intro_l, and_elim_r).
Time Qed.
Time Lemma fupd_mask_mono E1 E2 P : E1 \226\138\134 E2 \226\134\146 (|={E1}=> P) ={E2}=\226\136\151 P.
Time Proof.
Time (intros (Ef, (->, ?))%subseteq_disjoint_union_L).
Time by apply fupd_mask_frame_r.
Time Qed.
Time
Lemma fupd_mask_frame E E' E1 E2 P :
  E1 \226\138\134 E \226\134\146 (|={E1,E2}=> |={E2 \226\136\170 E \226\136\150 E1,E'}=> P) -\226\136\151 |={E,E'}=> P.
Time Proof.
Time (intros ?).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (fupd_mask_frame_r _ _ (E \226\136\150 E1)) ;
 last  set_solver).
Time rewrite fupd_trans.
Time by replace (E1 \226\136\170 E \226\136\150 E1) with E by by apply union_difference_L.
Time Qed.
Time
Lemma fupd_mask_frame_acc E E' E1 E2 P Q :
  E1 \226\138\134 E
  \226\134\146 (|={E1,E1 \226\136\150 E2}=> Q)
    -\226\136\151 (Q
        -\226\136\151 |={E \226\136\150 E2,E'}=> (\226\136\128 R, (|={E1 \226\136\150 E2,E1}=> R) -\226\136\151 |={E \226\136\150 E2,E}=> R)
                           -\226\136\151 P) -\226\136\151 |={E,E'}=> P.
Time Proof.
Time (intros HE).
Time (apply wand_intro_r).
Time rewrite fupd_frame_r.
Time rewrite wand_elim_r.
Time clear Q.
Time
(<ssreflect_plugin::ssrtclseq@0> <ssreflect_plugin::ssrtclseq@0> rewrite
 -(fupd_mask_frame E E') ; first  apply fupd_mono ; last  done).
Time rewrite -[X in X -\226\136\151 _](right_id emp%I).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 (fupd_intro_mask (E1 \226\136\150 E2 \226\136\170 E \226\136\150 E1) (E \226\136\150 E2) emp%I) ; last  first).
Time {
Time rewrite {+1}(union_difference_L _ _ HE).
Time set_solver.
Time }
Time rewrite fupd_frame_l fupd_frame_r.
Time (apply fupd_elim).
Time (apply fupd_mono).
Time
(<ssreflect_plugin::ssrtclseq@0> <ssreflect_plugin::ssrtclseq@0>
 eapply wand_apply ; last  <ssreflect_plugin::ssrtclseq@0> 
 apply sep_mono ; first  reflexivity ; first  reflexivity).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>R).
Time (apply wand_intro_r).
Time rewrite fupd_frame_r.
Time (apply fupd_elim).
Time rewrite left_id.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (fupd_mask_frame_r _ _ (E \226\136\150 E1)) ;
 last  set_solver +).
Time rewrite {+4}(union_difference_L _ _ HE).
Time done.
Time Qed.
Time Lemma fupd_mask_same E E1 P : E = E1 \226\134\146 (|={E}=> P) -\226\136\151 |={E,E1}=> P.
Time Proof.
Time (intros <-).
Time done.
Time Qed.
Time Lemma fupd_sep E P Q : (|={E}=> P) \226\136\151 (|={E}=> Q) ={E}=\226\136\151 P \226\136\151 Q.
Time Proof.
Time by rewrite fupd_frame_r fupd_frame_l fupd_trans.
Time Qed.
Time #[global]
Instance fupd_homomorphism  E:
 (MonoidHomomorphism bi_sep bi_sep (flip (\226\138\162)) (fupd (PROP:=PROP) E E)).
Time Proof.
Time (split; [ split |  ]; try apply _).
Time (apply fupd_sep).
Time (apply fupd_intro).
Time Qed.
Time
Lemma big_sepL_fupd {A} E (\206\166 : nat \226\134\146 A \226\134\146 PROP) l :
  ([\226\136\151 list] k\226\134\166x \226\136\136 l, |={E}=> \206\166 k x) ={E}=\226\136\151 [\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x.
Time Proof.
Time by rewrite (big_opL_commute _).
Time Qed.
Time
Lemma big_sepM_fupd `{Countable K} {A} E (\206\166 : K \226\134\146 A \226\134\146 PROP) 
  m : ([\226\136\151 map] k\226\134\166x \226\136\136 m, |={E}=> \206\166 k x) ={E}=\226\136\151 [\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x.
Time Proof.
Time by rewrite (big_opM_commute _).
Time Qed.
Time
Lemma big_sepS_fupd `{Countable A} E (\206\166 : A \226\134\146 PROP) 
  X : ([\226\136\151 set] x \226\136\136 X, |={E}=> \206\166 x) ={E}=\226\136\151 [\226\136\151 set] x \226\136\136 X, \206\166 x.
Time Proof.
Time by rewrite (big_opS_commute _).
Time Qed.
Time
Lemma big_sepMS_fupd `{Countable A} E (\206\166 : A \226\134\146 PROP) 
  l : ([\226\136\151 mset] x \226\136\136 l, |={E}=> \206\166 x) \226\138\162 |={E}=> [\226\136\151 mset] x \226\136\136 l, \206\166 x.
Time Proof.
Time by rewrite (big_opMS_commute _).
Time Qed.
Time
Lemma step_fupd_wand E1 E2 E3 P Q :
  (|={E1,E2,E3}\226\150\183=> P) -\226\136\151 (P -\226\136\151 Q) -\226\136\151 |={E1,E2,E3}\226\150\183=> Q.
Time Proof.
Time (apply wand_intro_l).
Time
by rewrite (later_intro (P -\226\136\151 Q)%I) fupd_frame_l -later_sep fupd_frame_l
 wand_elim_l.
Time Qed.
Time
Lemma step_fupd_mask_frame_r E1 E2 E3 Ef P :
  E1 ## Ef
  \226\134\146 E2 ## Ef \226\134\146 (|={E1,E2,E3}\226\150\183=> P) \226\138\162 |={E1 \226\136\170 Ef,E2 \226\136\170 Ef,E3 \226\136\170 Ef}\226\150\183=> P.
Time Proof.
Time (intros).
Time rewrite -fupd_mask_frame_r //.
Time (do 2 f_equiv).
Time by apply fupd_mask_frame_r.
Time Qed.
Time
Lemma step_fupd_mask_mono E1 E2 F1 F2 P :
  F1 \226\138\134 F2 \226\134\146 E1 \226\138\134 E2 \226\134\146 (|={E1,F2}\226\150\183=> P) \226\138\162 |={E2,F1}\226\150\183=> P.
Time Proof.
Time (intros ? ?).
Time rewrite -(emp_sep (|={E1,F2}\226\150\183=> P)%I).
Time rewrite (fupd_intro_mask E2 E1 emp%I) //.
Time rewrite fupd_frame_r -(fupd_trans E2 E1 F1).
Time f_equiv.
Time rewrite fupd_frame_l -(fupd_trans E1 F2 F1).
Time f_equiv.
Time rewrite (fupd_intro_mask F2 F1 (|={_,_}=> emp)%I) //.
Time rewrite fupd_frame_r.
Time f_equiv.
Time rewrite [X in (X \226\136\151 _)%I]later_intro -later_sep.
Time f_equiv.
Time rewrite fupd_frame_r -(fupd_trans F1 F2 E2).
Time f_equiv.
Time rewrite fupd_frame_l -(fupd_trans F2 E1 E2).
Time f_equiv.
Time by rewrite fupd_frame_r left_id.
Time Qed.
Time Lemma step_fupd_intro E1 E2 P : E2 \226\138\134 E1 \226\134\146 \226\150\183 P -\226\136\151 |={E1,E2}\226\150\183=> P.
Time Proof.
Time (intros).
Time by rewrite -(step_fupd_mask_mono E2 _ _ E2) // -!fupd_intro.
Time Qed.
Time
Lemma step_fupd_frame_l E1 E2 R Q :
  R \226\136\151 (|={E1,E2}\226\150\183=> Q) -\226\136\151 |={E1,E2}\226\150\183=> R \226\136\151 Q.
Time Proof.
Time rewrite fupd_frame_l.
Time (apply fupd_mono).
Time rewrite [P in P \226\136\151 _ \226\138\162 _](later_intro R) -later_sep fupd_frame_l.
Time by apply later_mono, fupd_mono.
Time Qed.
Time
Lemma step_fupd_fupd E E' P : (|={E,E'}\226\150\183=> P) \226\138\163\226\138\162 (|={E,E'}\226\150\183=> |={E}=> P).
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time -
Time by rewrite -fupd_intro.
Time -
Time by rewrite fupd_trans.
Time Qed.
Time
Lemma step_fupdN_mono E1 E2 n P Q :
  (P \226\138\162 Q) \226\134\146 (|={E1,E2}\226\150\183=>^n P) \226\138\162 |={E1,E2}\226\150\183=>^n Q.
Time Proof.
Time (intros HPQ).
Time (<ssreflect_plugin::ssrtclintros@0> induction n as [| n IH] =>//=).
Time rewrite IH //.
Time Qed.
Time
Lemma step_fupdN_wand E1 E2 n P Q :
  (|={E1,E2}\226\150\183=>^n P) -\226\136\151 (P -\226\136\151 Q) -\226\136\151 |={E1,E2}\226\150\183=>^n Q.
Time Proof.
Time (apply wand_intro_l).
Time (<ssreflect_plugin::ssrtclintros@0> induction n as [| n IH] =>/=).
Time {
Time by rewrite wand_elim_l.
Time }
Time rewrite -IH -fupd_frame_l later_sep -fupd_frame_l.
Time
by <ssreflect_plugin::ssrtclseq@0> apply sep_mono ; first  apply later_intro.
Time Qed.
Time
Lemma step_fupdN_S_fupd n E P :
  (|={E,\226\136\133}\226\150\183=>^(S n) P) \226\138\163\226\138\162 (|={E,\226\136\133}\226\150\183=>^(S n) |={E}=> P).
Time Proof.
Time
(apply (anti_symm (\226\138\162)); rewrite !Nat_iter_S_r; apply step_fupdN_mono; rewrite
  -step_fupd_fupd //).
Time Qed.
Time
Lemma step_fupdN_frame_l E1 E2 n R Q :
  R \226\136\151 (|={E1,E2}\226\150\183=>^n Q) -\226\136\151 |={E1,E2}\226\150\183=>^n R \226\136\151 Q.
Time Proof.
Time (induction n as [| n IH]; simpl; [ done |  ]).
Time rewrite step_fupd_frame_l IH //=.
Time Qed.
Time Section fupd_plainly_derived.
Time Context `{BiPlainly PROP} `{!BiFUpdPlainly PROP}.
Time Lemma fupd_plainly_mask E E' P : (|={E,E'}=> \226\150\160 P) \226\138\162 |={E}=> P.
Time Proof.
Time rewrite -(fupd_plainly_mask_empty).
Time (apply fupd_elim, (fupd_mask_weaken _ _ _)).
Time set_solver.
Time Qed.
Time Lemma fupd_plainly_elim E P : \226\150\160 P ={E}=\226\136\151 P.
Time Proof.
Time by rewrite (fupd_intro E (\226\150\160 P)%I) fupd_plainly_mask.
Time Qed.
Time Lemma fupd_plainly_keep_r E P R : R \226\136\151 (R ={E}=\226\136\151 \226\150\160 P) \226\138\162 |={E}=> R \226\136\151 P.
Time Proof.
Time by rewrite !(comm _ R) fupd_plainly_keep_l.
Time Qed.
Time Lemma fupd_plain_mask_empty E P `{!Plain P} : (|={E,\226\136\133}=> P) \226\138\162 |={E}=> P.
Time Proof.
Time by rewrite {+1}(plain P) fupd_plainly_mask_empty.
Time Qed.
Time Lemma fupd_plain_mask E E' P `{!Plain P} : (|={E,E'}=> P) \226\138\162 |={E}=> P.
Time Proof.
Time by rewrite {+1}(plain P) fupd_plainly_mask.
Time Qed.
Time
Lemma fupd_plain_keep_l E P R `{!Plain P} : (R ={E}=\226\136\151 P) \226\136\151 R \226\138\162 |={E}=> P \226\136\151 R.
Time Proof.
Time by rewrite {+1}(plain P) fupd_plainly_keep_l.
Time Qed.
Time
Lemma fupd_plain_keep_r E P R `{!Plain P} : R \226\136\151 (R ={E}=\226\136\151 P) \226\138\162 |={E}=> R \226\136\151 P.
Time Proof.
Time by rewrite {+1}(plain P) fupd_plainly_keep_r.
Time Qed.
Time Lemma fupd_plain_later E P `{!Plain P} : \226\150\183 (|={E}=> P) \226\138\162 |={E}=> \226\150\183 \226\151\135 P.
Time Proof.
Time by rewrite {+1}(plain P) fupd_plainly_later.
Time Qed.
Time
Lemma fupd_plain_forall_2 E {A} (\206\166 : A \226\134\146 PROP) `{!\226\136\128 x, Plain (\206\166 x)} :
  (\226\136\128 x, |={E}=> \206\166 x) \226\138\162 |={E}=> \226\136\128 x, \206\166 x.
Time Proof.
Time rewrite -fupd_plainly_forall_2.
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_mono =>x).
Time by rewrite {+1}(plain (\206\166 _)).
Time Qed.
Time
Lemma fupd_plainly_laterN E n P `{HP : !Plain P} :
  \226\150\183^n (|={E}=> P) \226\138\162 |={E}=> \226\150\183^n \226\151\135 P.
Time Proof.
Time revert P HP.
Time (<ssreflect_plugin::ssrtclintros@0> induction n as [| n IH] =>P ? /=).
Time -
Time by rewrite -except_0_intro.
Time -
Time rewrite -!later_laterN !laterN_later.
Time rewrite fupd_plain_later.
Time by rewrite IH except_0_later.
Time Qed.
Time
Lemma fupd_plain_forall E1 E2 {A} (\206\166 : A \226\134\146 PROP) `{!\226\136\128 x, Plain (\206\166 x)} :
  E2 \226\138\134 E1 \226\134\146 (|={E1,E2}=> \226\136\128 x, \206\166 x) \226\138\163\226\138\162 (\226\136\128 x, |={E1,E2}=> \206\166 x).
Time Proof.
Time (intros).
Time (apply (anti_symm _)).
Time {
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time by rewrite (forall_elim x).
Time }
Time trans (\226\136\128 x, |={E1}=> \206\166 x)%I.
Time {
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_mono =>x).
Time by rewrite fupd_plain_mask.
Time }
Time rewrite fupd_plain_forall_2.
Time (apply fupd_elim).
Time rewrite {+1}(plain (\226\136\128 x, \206\166 x)) (fupd_mask_weaken E1 E2 (\226\150\160 _)%I) //.
Time (apply fupd_elim).
Time by rewrite fupd_plainly_elim.
Time Qed.
Time
Lemma fupd_plain_forall' E {A} (\206\166 : A \226\134\146 PROP) `{!\226\136\128 x, Plain (\206\166 x)} :
  (|={E}=> \226\136\128 x, \206\166 x) \226\138\163\226\138\162 (\226\136\128 x, |={E}=> \206\166 x).
Time Proof.
Time by apply fupd_plain_forall.
Time Qed.
Time Lemma step_fupd_plain E E' P `{!Plain P} : (|={E,E'}\226\150\183=> P) ={E}=\226\136\151 \226\150\183 \226\151\135 P.
Time Proof.
Time rewrite -(fupd_plain_mask _ E' (\226\150\183 \226\151\135 P)%I).
Time (apply fupd_elim).
Time by rewrite fupd_plain_mask -fupd_plain_later.
Time Qed.
Time
Lemma step_fupdN_plain E E' n P `{!Plain P} :
  (|={E,E'}\226\150\183=>^n P) ={E}=\226\136\151 \226\150\183^n \226\151\135 P.
Time Proof.
Time (induction n as [| n IH]).
Time -
Time by rewrite -fupd_intro -except_0_intro.
Time -
Time rewrite Nat_iter_S step_fupd_fupd IH !fupd_trans step_fupd_plain.
Time (apply fupd_mono).
Time (destruct n as [| n]; simpl).
Time *
Time by rewrite except_0_idemp.
Time *
Time by rewrite except_0_later.
Time Qed.
Time
Lemma step_fupd_plain_forall E1 E2 {A} (\206\166 : A \226\134\146 PROP) 
  `{!\226\136\128 x, Plain (\206\166 x)} :
  E2 \226\138\134 E1 \226\134\146 (|={E1,E2}\226\150\183=> \226\136\128 x, \206\166 x) \226\138\163\226\138\162 (\226\136\128 x, |={E1,E2}\226\150\183=> \206\166 x).
Time Proof.
Time (intros).
Time (apply (anti_symm _)).
Time {
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time by rewrite (forall_elim x).
Time }
Time trans (\226\136\128 x, |={E1}=> \226\150\183 \226\151\135 \206\166 x)%I.
Time {
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_mono =>x).
Time by rewrite step_fupd_plain.
Time }
Time rewrite -fupd_plain_forall'.
Time (apply fupd_elim).
Time rewrite -(fupd_except_0 E2 E1) -step_fupd_intro //.
Time by rewrite -later_forall -except_0_forall.
Time Qed.
Time End fupd_plainly_derived.
Time End fupd_derived.
