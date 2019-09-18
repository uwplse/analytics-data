Time From iris.algebra Require Import functions gmap.
Time From iris.base_logic.lib Require Export iprop.
Time From iris.algebra Require Import proofmode_classes.
Time Set Default Proof Using "Type".
Time Import uPred.
Time
Class inG (\206\163 : gFunctors) (A : cmraT) :=
 InG {inG_id : gid \206\163; inG_prf : A = \206\163 inG_id (iPreProp \206\163) _}.
Time Arguments inG_id {_} {_} _.
Time Lemma subG_inG \206\163 (F : gFunctor) : subG F \206\163 \226\134\146 inG \206\163 (F (iPreProp \206\163) _).
Time Proof.
Time move  {}=>/(_ 0%fin) /= [j {+}->].
Time by exists j.
Time Qed.
Time
Ltac
 solve_inG :=
  intros;
   lazymatch goal with
   | H:subG (?x\206\163 _ _ _ _) _ |- _ => try unfold x\206\163 in H
   | H:subG (?x\206\163 _ _ _) _ |- _ => try unfold x\206\163 in H
   | H:subG (?x\206\163 _ _) _ |- _ => try unfold x\206\163 in H
   | H:subG (?x\206\163 _) _ |- _ => try unfold x\206\163 in H
   | H:subG ?x\206\163 _ |- _ => try unfold x\206\163 in H
   end;
   repeat
    match goal with
    | H:subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
    end;
   repeat
    match goal with
    | H:subG _ _ |- _ => move : {}H {}; apply subG_inG in H || clear H
    end; intros; try done; split; assumption || by apply _.
Time
Definition iRes_singleton {\206\163} {A} {i : inG \206\163 A} (\206\179 : gname) 
  (a : A) : iResUR \206\163 :=
  discrete_fun_singleton (inG_id i) {[\206\179 := cmra_transport inG_prf a]}.
Time Instance: (Params (@iRes_singleton) 4) := { }.
Time
Definition own_def `{!inG \206\163 A} (\206\179 : gname) (a : A) : 
  iProp \206\163 := uPred_ownM (iRes_singleton \206\179 a).
Time Definition own_aux : seal (@own_def).
Time by eexists.
Time Qed.
Time Definition own {\206\163} {A} {i} := own_aux.(unseal) \206\163 A i.
Time Definition own_eq : @own = @own_def := own_aux.(seal_eq).
Time Instance: (Params (@own) 4) := { }.
Time Typeclasses Opaque own.
Time Section global.
Time Context `{Hin : !inG \206\163 A}.
Time Implicit Type a : A.
Time #[global]
Instance iRes_singleton_ne  \206\179: (NonExpansive (@iRes_singleton \206\163 A _ \206\179)).
Time Proof.
Time by intros n a a' Ha; apply discrete_fun_singleton_ne; rewrite Ha.
Time Qed.
Time
Lemma iRes_singleton_op \206\179 a1 a2 :
  iRes_singleton \206\179 (a1 \226\139\133 a2) \226\137\161 iRes_singleton \206\179 a1 \226\139\133 iRes_singleton \206\179 a2.
Time Proof.
Time
by rewrite /iRes_singleton discrete_fun_op_singleton op_singleton
 cmra_transport_op.
Time Qed.
Time #[global]Instance own_ne  \206\179: (NonExpansive (@own \206\163 A _ \206\179)).
Time Proof.
Time rewrite !own_eq.
Time solve_proper.
Time Qed.
Time #[global]
Instance own_proper  \206\179: (Proper ((\226\137\161) ==> (\226\138\163\226\138\162)) (@own \206\163 A _ \206\179)) :=
 (ne_proper _).
Time Lemma own_op \206\179 a1 a2 : own \206\179 (a1 \226\139\133 a2) \226\138\163\226\138\162 own \206\179 a1 \226\136\151 own \206\179 a2.
Time Proof.
Time by rewrite !own_eq /own_def -ownM_op iRes_singleton_op.
Time Qed.
Time Lemma own_mono \206\179 a1 a2 : a2 \226\137\188 a1 \226\134\146 own \206\179 a1 \226\138\162 own \206\179 a2.
Time Proof.
Time move  {}=>[c {+}->].
Time by rewrite own_op sep_elim_l.
Time Qed.
Time #[global]
Instance own_mono'  \206\179: (Proper (flip (\226\137\188) ==> (\226\138\162)) (@own \206\163 A _ \206\179)).
Time Proof.
Time (intros a1 a2).
Time (apply own_mono).
Time Qed.
Time Lemma own_valid \206\179 a : own \206\179 a \226\138\162 \226\156\147 a.
Time Proof.
Time rewrite !own_eq /own_def ownM_valid /iRes_singleton.
Time
rewrite discrete_fun_validI (forall_elim (inG_id _))
 discrete_fun_lookup_singleton.
Time rewrite gmap_validI (forall_elim \206\179) lookup_singleton option_validI.
Time
by <ssreflect_plugin::ssrtclseq@0> trans
 (\226\156\147 cmra_transport inG_prf a : iProp \206\163)%I ; last  
 destruct inG_prf.
Time Qed.
Time Lemma own_valid_2 \206\179 a1 a2 : own \206\179 a1 -\226\136\151 own \206\179 a2 -\226\136\151 \226\156\147 (a1 \226\139\133 a2).
Time Proof.
Time (apply wand_intro_r).
Time by rewrite -own_op own_valid.
Time Qed.
Time
Lemma own_valid_3 \206\179 a1 a2 a3 :
  own \206\179 a1 -\226\136\151 own \206\179 a2 -\226\136\151 own \206\179 a3 -\226\136\151 \226\156\147 (a1 \226\139\133 a2 \226\139\133 a3).
Time Proof.
Time (do 2 apply wand_intro_r).
Time by rewrite -!own_op own_valid.
Time Qed.
Time Lemma own_valid_r \206\179 a : own \206\179 a \226\138\162 own \206\179 a \226\136\151 \226\156\147 a.
Time Proof.
Time apply : {}bi.persistent_entails_r {}.
Time (apply own_valid).
Time Qed.
Time Lemma own_valid_l \206\179 a : own \206\179 a \226\138\162 \226\156\147 a \226\136\151 own \206\179 a.
Time Proof.
Time by rewrite comm -own_valid_r.
Time Qed.
Time #[global]Instance own_timeless  \206\179 a: (Discrete a \226\134\146 Timeless (own \206\179 a)).
Time Proof.
Time (rewrite !own_eq /own_def; apply _).
Time Qed.
Time #[global]
Instance own_core_persistent  \206\179 a: (CoreId a \226\134\146 Persistent (own \206\179 a)).
Time Proof.
Time (rewrite !own_eq /own_def; apply _).
Time Qed.
Time Lemma later_own \206\179 a : \226\150\183 own \206\179 a -\226\136\151 \226\151\135 (\226\136\131 b, own \206\179 b \226\136\167 \226\150\183 (a \226\137\161 b)).
Time Proof.
Time rewrite own_eq /own_def later_ownM.
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>r).
Time (assert (NonExpansive (\206\187 r : iResUR \206\163, r (inG_id Hin) !! \206\179))).
Time {
Time (intros n r1 r2 Hr).
Time f_equiv.
Time by specialize (Hr (inG_id _)).
Time }
Time rewrite (f_equiv (\206\187 r : iResUR \206\163, r (inG_id Hin) !! \206\179) _ r).
Time
rewrite {+1}/iRes_singleton discrete_fun_lookup_singleton lookup_singleton.
Time rewrite option_equivI.
Time
(<ssreflect_plugin::ssrtclseq@0> case  Hb: {}(r (inG_id _) !! \206\179) {} =>
 [b|] ; last  first).
Time {
Time by rewrite and_elim_r /sbi_except_0 -or_intro_l.
Time }
Time
rewrite -except_0_intro -(exist_intro (cmra_transport (eq_sym inG_prf) b)).
Time (apply and_mono).
Time -
Time rewrite /iRes_singleton.
Time
(assert
  (\226\136\128 {A A' : cmraT} (Heq : A' = A) (a : A),
     cmra_transport Heq (cmra_transport (eq_sym Heq) a) = a) 
  as -> by by intros ? ? ->).
Time (<ssreflect_plugin::ssrtclintros@0> apply ownM_mono =>/=).
Time exists (discrete_fun_insert (inG_id _) (delete \206\179 (r (inG_id Hin))) r).
Time (intros i').
Time rewrite discrete_fun_lookup_op.
Time (destruct (decide (i' = inG_id _)) as [->| ?]).
Time +
Time rewrite discrete_fun_lookup_insert discrete_fun_lookup_singleton.
Time (intros \206\179').
Time rewrite lookup_op.
Time (destruct (decide (\206\179' = \206\179)) as [->| ?]).
Time *
Time by rewrite lookup_singleton lookup_delete Hb.
Time *
Time by rewrite lookup_singleton_ne // lookup_delete_ne // left_id.
Time +
Time rewrite discrete_fun_lookup_insert_ne //.
Time by rewrite discrete_fun_lookup_singleton_ne // left_id.
Time -
Time (apply later_mono).
Time
by
 assert
  (\226\136\128 {A A' : cmraT} (Heq : A' = A) (a' : A') (a : A),
     cmra_transport Heq a' \226\137\161 a
     \226\138\162@{ iPropI \206\163} a' \226\137\161 cmra_transport (eq_sym Heq) a) 
  as -> by by intros ? ? ->.
Time Qed.
Time
Lemma own_alloc_strong a (P : gname \226\134\146 Prop) :
  pred_infinite P \226\134\146 \226\156\147 a \226\134\146 (|==> \226\136\131 \206\179, \226\140\156P \206\179\226\140\157 \226\136\167 own \206\179 a)%I.
Time Proof.
Time (intros HP Ha).
Time
rewrite
 -(bupd_mono (\226\136\131 m, \226\140\156\226\136\131 \206\179, P \206\179 \226\136\167 m = iRes_singleton \206\179 a\226\140\157 \226\136\167 uPred_ownM m)%I).
Time -
Time rewrite /uPred_valid /bi_emp_valid (ownM_unit emp).
Time
(<ssreflect_plugin::ssrtclseq@0>
  eapply bupd_ownM_updateP, (discrete_fun_singleton_updateP_empty (inG_id _))
  ; first  eapply alloc_updateP_strong', cmra_transport_valid, Ha;
  naive_solver).
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>m;
  <ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>- 
  [\206\179 [Hfresh {+}->]]).
Time by rewrite !own_eq /own_def -(exist_intro \206\179) pure_True // left_id.
Time Qed.
Time
Lemma own_alloc_cofinite a (G : gset gname) :
  \226\156\147 a \226\134\146 (|==> \226\136\131 \206\179, \226\140\156\206\179 \226\136\137 G\226\140\157 \226\136\167 own \206\179 a)%I.
Time Proof.
Time (intros Ha).
Time
(<ssreflect_plugin::ssrtclintros@0> apply (own_alloc_strong a (\206\187 \206\179, \206\179 \226\136\137 G))
 =>//).
Time (apply (pred_infinite_set (C:=gset gname))).
Time (intros E).
Time (set (i := fresh (G \226\136\170 E))).
Time exists i.
Time (apply not_elem_of_union, is_fresh).
Time Qed.
Time Lemma own_alloc a : \226\156\147 a \226\134\146 (|==> \226\136\131 \206\179, own \206\179 a)%I.
Time Proof.
Time (intros Ha).
Time (rewrite /uPred_valid /bi_emp_valid (own_alloc_cofinite a \226\136\133) //; [  ]).
Time (<ssreflect_plugin::ssrtclintros@0> apply bupd_mono, exist_mono =>?).
Time eauto using and_elim_r.
Time Qed.
Time
Lemma own_updateP P \206\179 a : a ~~>: P \226\134\146 own \206\179 a ==\226\136\151 \226\136\131 a', \226\140\156P a'\226\140\157 \226\136\167 own \206\179 a'.
Time Proof.
Time (intros Ha).
Time rewrite !own_eq.
Time
rewrite
 -(bupd_mono (\226\136\131 m, \226\140\156\226\136\131 a', m = iRes_singleton \206\179 a' \226\136\167 P a'\226\140\157 \226\136\167 uPred_ownM m)%I).
Time -
Time
(<ssreflect_plugin::ssrtclseq@0>
 eapply bupd_ownM_updateP, discrete_fun_singleton_updateP ; first  by
 eapply singleton_updateP', cmra_transport_updateP', Ha).
Time naive_solver.
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>m;
  <ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>- 
  [a' [{+}-> HP]]).
Time rewrite -(exist_intro a').
Time by apply and_intro; [ apply pure_intro |  ].
Time Qed.
Time Lemma own_update \206\179 a a' : a ~~> a' \226\134\146 own \206\179 a ==\226\136\151 own \206\179 a'.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> intros; rewrite (own_updateP (a' =)) ; last 
 by apply cmra_update_updateP).
Time
by
 <ssreflect_plugin::ssrtclintros@0> apply bupd_mono, exist_elim =>a'';
  <ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>{+}->.
Time Qed.
Time
Lemma own_update_2 \206\179 a1 a2 a' :
  a1 \226\139\133 a2 ~~> a' \226\134\146 own \206\179 a1 -\226\136\151 own \206\179 a2 ==\226\136\151 own \206\179 a'.
Time Proof.
Time (intros).
Time (apply wand_intro_r).
Time rewrite -own_op.
Time by apply own_update.
Time Qed.
Time
Lemma own_update_3 \206\179 a1 a2 a3 a' :
  a1 \226\139\133 a2 \226\139\133 a3 ~~> a' \226\134\146 own \206\179 a1 -\226\136\151 own \206\179 a2 -\226\136\151 own \206\179 a3 ==\226\136\151 own \206\179 a'.
Time Proof.
Time (intros).
Time (do 2 apply wand_intro_r).
Time rewrite -!own_op.
Time by apply own_update.
Time Qed.
Time End global.
Time Arguments own_valid {_} {_} [_] _ _.
Time Arguments own_valid_2 {_} {_} [_] _ _ _.
Time Arguments own_valid_3 {_} {_} [_] _ _ _ _.
Time Arguments own_valid_l {_} {_} [_] _ _.
Time Arguments own_valid_r {_} {_} [_] _ _.
Time Arguments own_updateP {_} {_} [_] _ _ _ _.
Time Arguments own_update {_} {_} [_] _ _ _ _.
Time Arguments own_update_2 {_} {_} [_] _ _ _ _ _.
Time Arguments own_update_3 {_} {_} [_] _ _ _ _ _ _.
Time Lemma own_unit A `{!inG \206\163 (A : ucmraT)} \206\179 : (|==> own \206\179 \206\181)%I.
Time Proof.
Time rewrite /uPred_valid /bi_emp_valid (ownM_unit emp) !own_eq /own_def.
Time (apply bupd_ownM_update, discrete_fun_singleton_update_empty).
Time
(<ssreflect_plugin::ssrtclseq@0>
 apply (alloc_unit_singleton_update (cmra_transport inG_prf \206\181)) ; last  done).
Time -
Time (apply cmra_transport_valid, ucmra_unit_valid).
Time -
Time (intros x; destruct inG_prf).
Time by rewrite left_id.
Time Qed.
Time
Instance own_cmra_sep_homomorphism  `{!inG \206\163 (A : ucmraT)}:
 (WeakMonoidHomomorphism op uPred_sep (\226\137\161) (own \206\179)).
Time Proof.
Time (split; try apply _).
Time (apply own_op).
Time Qed.
Time Section proofmode_classes.
Time Context `{!inG \206\163 A}.
Time Implicit Types a b : A.
Time #[global]
Instance into_sep_own  \206\179 a b1 b2:
 (IsOp a b1 b2 \226\134\146 IntoSep (own \206\179 a) (own \206\179 b1) (own \206\179 b2)).
Time Proof.
Time (intros).
Time by rewrite /IntoSep (is_op a) own_op.
Time Qed.
Time #[global]
Instance into_and_own  p \206\179 a b1 b2:
 (IsOp a b1 b2 \226\134\146 IntoAnd p (own \206\179 a) (own \206\179 b1) (own \206\179 b2)).
Time Proof.
Time (intros).
Time by rewrite /IntoAnd (is_op a) own_op sep_and.
Time Qed.
Time #[global]
Instance from_sep_own  \206\179 a b1 b2:
 (IsOp a b1 b2 \226\134\146 FromSep (own \206\179 a) (own \206\179 b1) (own \206\179 b2)).
Time Proof.
Time (intros).
Time by rewrite /FromSep -own_op -is_op.
Time Qed.
Time #[global]
Instance from_and_own_persistent  \206\179 a b1 b2:
 (IsOp a b1 b2
  \226\134\146 TCOr (CoreId b1) (CoreId b2) \226\134\146 FromAnd (own \206\179 a) (own \206\179 b1) (own \206\179 b2)).
Time Proof.
Time (intros ? Hb).
Time rewrite /FromAnd (is_op a) own_op.
Time (destruct Hb; by rewrite persistent_and_sep).
Time Qed.
Time End proofmode_classes.
