Time From iris.algebra Require Export cmra.
Time From iris.algebra Require Import proofmode_classes.
Time From iris.algebra Require Export cmra.
Time From stdpp Require Export list gmap.
Time From iris.algebra Require Import list.
Time From iris.algebra Require Import updates local_updates.
Time From iris.base_logic Require Import base_logic.
Time From iris.base_logic Require Import base_logic.
Time Set Default Proof Using "Type".
Time Inductive counting :=
       | Count : forall z : Z, _
       | CountBot : _.
Time #[local]Open Scope Z.
Time
Instance counting_valid : (Valid counting) :=
 (\206\187 x, match x with
       | Count _ => True
       | CountBot => False
       end).
Time
Instance counting_validN : (ValidN counting) :=
 (\206\187 n x, match x with
         | Count _ => True
         | CountBot => False
         end).
Time Instance counting_pcore : (PCore counting) := (\206\187 x, None).
Time
Instance counting_op : (Op counting) :=
 (\206\187 x y,
    match x, y with
    | Count z1, Count z2 =>
        if decide (z1 >= 0 \226\136\167 z2 >= 0) then CountBot
        else if decide ((z1 >= 0 \226\136\168 z2 >= 0) \226\136\167 z1 + z2 < 0) then CountBot
             else Count (z1 + z2)
    | _, _ => CountBot
    end).
Time Canonical Structure countingC := leibnizC counting.
Time #[local]
Ltac
 by_cases :=
  repeat <ssreflect_plugin::ssrtclintros@0>
   match goal with
   | H:counting |- _ => destruct H
   end =>//=; repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=;
   try lia.
Time Lemma counting_ra_mixin : RAMixin counting.
Time Proof.
Time (split; try apply _; try done).
Time From iris.base_logic Require Import base_logic.
Time #[local]Arguments validN _ _ _ !_ /.
Time #[local]Arguments valid _ _ !_ /.
Time #[local]Arguments op _ _ _ !_ /.
Time #[local]Arguments pcore _ _ !_ /.
Time From iris.algebra Require Import proofmode_classes.
Time Set Default Proof Using "Type".
Time Section cofe.
Time Context `{Countable K} {A : ofeT}.
Time Implicit Type m : gmap K A.
Time Implicit Type i : K.
Time
Instance gmap_dist : (Dist (gmap K A)) :=
 (\206\187 n m1 m2, \226\136\128 i, m1 !! i \226\137\161{n}\226\137\161 m2 !! i).
Time Definition gmap_ofe_mixin : OfeMixin (gmap K A).
Time
Record agree (A : Type) : Type :={agree_car : list A;
                                  agree_not_nil :
                                   bool_decide (agree_car = []) = false}.
Time Arguments agree_car {_} _.
Time Arguments agree_not_nil {_} _.
Time #[local]Coercion agree_car : agree >-> list.
Time
Definition to_agree {A} (a : A) : agree A :=
  {| agree_car := [a]; agree_not_nil := eq_refl |}.
Time Lemma elem_of_agree {A} (x : agree A) : \226\136\131 a, a \226\136\136 agree_car x.
Time Proof.
Time (destruct x as [[| a ?] ?]; set_solver +).
Time Proof.
Time split.
Time -
Time (intros m1 m2; split).
Time +
Time by intros Hm n k; apply equiv_dist.
Time +
Time (intros Hm k; apply equiv_dist; intros n; apply Hm).
Time Qed.
Time Lemma agree_eq {A} (x y : agree A) : agree_car x = agree_car y \226\134\146 x = y.
Time Proof.
Time -
Time (intros n; split).
Time +
Time by intros m k.
Time +
Time by intros m1 m2 ? k.
Time (destruct x as [a ?], y as [b ?]; simpl).
Time (intros ->; f_equal).
Time (apply (proof_irrel _)).
Time Qed.
Time Section agree.
Time #[local]Set Default Proof Using "Type".
Time Context {A : ofeT}.
Time Implicit Types a b : A.
Time Implicit Types x y : agree A.
Time
Instance agree_dist : (Dist (agree A)) :=
 (\206\187 n x y,
    (\226\136\128 a, a \226\136\136 agree_car x \226\134\146 \226\136\131 b, b \226\136\136 agree_car y \226\136\167 a \226\137\161{n}\226\137\161 b)
    \226\136\167 (\226\136\128 b, b \226\136\136 agree_car y \226\134\146 \226\136\131 a, a \226\136\136 agree_car x \226\136\167 a \226\137\161{n}\226\137\161 b)).
Time Instance agree_equiv : (Equiv (agree A)) := (\206\187 x y, \226\136\128 n, x \226\137\161{n}\226\137\161 y).
Time Definition agree_ofe_mixin : OfeMixin (agree A).
Time Proof.
Time split.
Time -
Time done.
Time +
Time by intros m1 m2 m3 ? ? k; trans m2 !! k.
Time -
Time (intros n; split; rewrite /dist /agree_dist).
Time +
Time (intros x; split; eauto).
Time -
Time by intros n m1 m2 ? k; apply dist_S.
Time -
Time (intros x y z).
Time rewrite /op /counting_op.
Time Qed.
Time Canonical Structure gmapC : ofeT := OfeT (gmap K A) gmap_ofe_mixin.
Time #[program]
Definition gmap_chain (c : chain gmapC) (k : K) : 
  chain (optionC A) := {| chain_car := fun n => c n !! k |}.
Time by_cases.
Time Next Obligation.
Time by intros c k n i ?; apply (chain_cauchy c).
Time Qed.
Time
Definition gmap_compl `{Cofe A} : Compl gmapC :=
  \206\187 c, map_imap (\206\187 i _, compl (gmap_chain c i)) (c 0).
Time #[global, program]
Instance gmap_cofe  `{Cofe A}: (Cofe gmapC) := {| compl := gmap_compl |}.
Time Next Obligation.
Time (intros ? n c k).
Time rewrite /compl /gmap_compl lookup_imap.
Time +
Time (intros x y [? ?]).
Time naive_solver eauto.
Time +
Time (intros x y z [H1 H1'] [H2 H2']; split).
Time *
Time (intros a ?).
Time (destruct (H1 a) as (b, (?, ?)); auto).
Time (destruct (H2 b) as (c, (?, ?)); eauto).
Time by <ssreflect_plugin::ssrtclseq@0> exists c; split ; last  etrans.
Time *
Time (intros a ?).
Time (destruct (H2' a) as (b, (?, ?)); auto).
Time (destruct (H1' b) as (c, (?, ?)); eauto).
Time by <ssreflect_plugin::ssrtclseq@0> exists c; split ; last  etrans.
Time -
Time (intros n x y [? ?]; split; naive_solver eauto using dist_S).
Time Qed.
Time Canonical Structure agreeC := OfeT (agree A) agree_ofe_mixin.
Time
Instance agree_validN : (ValidN (agree A)) :=
 (\206\187 n x,
    match agree_car x with
    | [a] => True
    | _ => \226\136\128 a b, a \226\136\136 agree_car x \226\134\146 b \226\136\136 agree_car x \226\134\146 a \226\137\161{n}\226\137\161 b
    end).
Time Instance agree_valid : (Valid (agree A)) := (\206\187 x, \226\136\128 n, \226\156\147{n} x).
Time #[program]
Instance agree_op : (Op (agree A)) :=
 (\206\187 x y, {| agree_car := agree_car x ++ agree_car y |}).
Time Next Obligation.
Time by intros [[| ? ?]] y.
Time Qed.
Time Instance agree_pcore : (PCore (agree A)) := Some.
Time
Lemma agree_validN_def n x :
  \226\156\147{n} x \226\134\148 (\226\136\128 a b, a \226\136\136 agree_car x \226\134\146 b \226\136\136 agree_car x \226\134\146 a \226\137\161{n}\226\137\161 b).
Time Proof.
Time rewrite /validN /agree_validN.
Time (destruct (agree_car _) as [| ? [| ? ?]]; auto).
Time (setoid_rewrite elem_of_list_singleton; naive_solver).
Time Qed.
Time Instance agree_comm : (Comm (\226\137\161) (@op (agree A) _)).
Time Proof.
Time
(intros x y n; <ssreflect_plugin::ssrtclintros@0> split =>a /=;
  setoid_rewrite elem_of_app; naive_solver).
Time Qed.
Time Instance agree_assoc : (Assoc (\226\137\161) (@op (agree A) _)).
Time Proof.
Time
(intros x y z n; <ssreflect_plugin::ssrtclintros@0> split =>a /=;
  repeat setoid_rewrite elem_of_app; naive_solver).
Time Qed.
Time Lemma agree_idemp (x : agree A) : x \226\139\133 x \226\137\161 x.
Time Proof.
Time
(intros n; <ssreflect_plugin::ssrtclintros@0> split =>a /=; setoid_rewrite
  elem_of_app; naive_solver).
Time Qed.
Time
Instance agree_validN_ne  n:
 (Proper (dist n ==> impl) (@validN (agree A) _ n)).
Time Proof.
Time
(intros x y [H H']; rewrite /impl !agree_validN_def; intros Hv a b Ha Hb).
Time (destruct (H' a) as (a', (?, <-)); auto).
Time (destruct (H' b) as (b', (?, <-)); auto).
Time Qed.
Time
Instance agree_validN_proper  n:
 (Proper (equiv ==> iff) (@validN (agree A) _ n)).
Time Proof.
Time move  {}=>x y /equiv_dist H.
Time by split; rewrite (H n).
Time f_equal.
Time lia.
Time -
Time (intros x y).
Time rewrite /op /counting_op.
Time by_cases.
Time Qed.
Time Instance agree_op_ne'  x: (NonExpansive (op x)).
Time Proof.
Time
(intros n y1 y2 [H H']; <ssreflect_plugin::ssrtclintros@0> split =>a /=;
  setoid_rewrite elem_of_app; naive_solver).
Time f_equal.
Time lia.
Time -
Time (intros x y).
Time rewrite /op /counting_op /valid.
Time by_cases.
Time Qed.
Time Canonical Structure countingR := discreteR counting counting_ra_mixin.
Time #[global]Instance counting_cmra_discrete : (CmraDiscrete countingR).
Time Proof.
Time (apply discrete_cmra_discrete).
Time Qed.
Time Lemma counting_op' (x y : countingR) : x \226\139\133 y = counting_op x y.
Time Proof.
Time done.
Time Qed.
Time Lemma counting_valid' (x : countingR) : \226\156\147 x \226\134\148 counting_valid x.
Time Proof.
Time done.
Time Qed.
Time Lemma counting_validN' n (x : countingR) : \226\156\147{n} x \226\134\148 counting_validN n x.
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance is_op_counting  z:
 (z >= 0 \226\134\146 IsOp' (Count z) (Count (z + 1)) (Count (- 1))).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IsOp' /IsOp counting_op' =>?).
Time rewrite //=.
Time Qed.
Time by_cases.
Time Instance agree_op_ne : (NonExpansive2 (@op (agree A) _)).
Time Proof.
Time by intros n x1 x2 Hx y1 y2 Hy; rewrite Hy !(comm _ _ y2) Hx.
Time Qed.
Time f_equal.
Time lia.
Time
Instance agree_op_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) op) :=
 (ne_proper_2 _).
Time Lemma agree_included (x y : agree A) : x \226\137\188 y \226\134\148 y \226\137\161 x \226\139\133 y.
Time Proof.
Time (split; [  | by intros ?; exists y ]).
Time by intros [z Hz]; rewrite Hz assoc agree_idemp.
Time Qed.
Time #[global]
Instance is_op_counting'  (n : nat):
 (IsOp' (Count n) (Count (S n)) (Count (- 1))).
Time Proof.
Time rewrite /IsOp' /IsOp counting_op' //=.
Time by_cases.
Time Qed.
Time Lemma agree_op_invN n (x1 x2 : agree A) : \226\156\147{n} (x1 \226\139\133 x2) \226\134\146 x1 \226\137\161{n}\226\137\161 x2.
Time Proof.
Time rewrite agree_validN_def /=.
Time
(<ssreflect_plugin::ssrtclintros@0> setoid_rewrite elem_of_app =>Hv;
  <ssreflect_plugin::ssrtclintros@0> split =>a Ha).
Time f_equal.
Time lia.
Time Qed.
Time #[global]Instance counting_id_free  (z : counting): (IdFree z).
Time Proof.
Time (intros y).
Time rewrite counting_op' counting_validN'.
Time by_cases.
Time -
Time (destruct (elem_of_agree x2); naive_solver).
Time (destruct y; by_cases; intros _; inversion 1).
Time -
Time (destruct (elem_of_agree x1); naive_solver).
Time lia.
Time Qed.
Time #[global]Instance counting_full_exclusive : (Exclusive (Count 0)).
Time Proof.
Time (intros y).
Time rewrite counting_validN' counting_op'.
Time (<ssreflect_plugin::ssrtclintros@0> destruct y =>//=; by_cases).
Time Qed.
Time Definition agree_cmra_mixin : CmraMixin (agree A).
Time Proof.
Time (apply cmra_total_mixin; try apply _ || by eauto).
Time Qed.
Time -
Time (intros n x; rewrite !agree_validN_def; eauto using dist_S).
Time -
Time (intros x).
Time (apply agree_idemp).
Time -
Time (intros n x y; rewrite !agree_validN_def /=).
Time (setoid_rewrite elem_of_app; naive_solver).
Time -
Time (intros n x y1 y2 Hval Hx; exists x,x; simpl; split).
Time +
Time by rewrite agree_idemp.
Time +
Time
by
 move : {}Hval {}; rewrite Hx; move  {}=>/agree_op_invN {+}->; rewrite
  agree_idemp.
Time Qed.
Time Canonical Structure agreeR : cmraT := CmraT (agree A) agree_cmra_mixin.
Time #[global]Instance agree_cmra_total : (CmraTotal agreeR).
Time Proof.
Time (rewrite /CmraTotal; eauto).
Time Qed.
Time #[global]Instance agree_core_id  (x : agree A): (CoreId x).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]
Instance agree_cmra_discrete : (OfeDiscrete A \226\134\146 CmraDiscrete agreeR).
Time Proof.
Time (intros HD).
Time split.
Time -
Time
(intros x y [H H'] n; <ssreflect_plugin::ssrtclintros@0> split =>a;
  setoid_rewrite  <- (discrete_iff_0 _ _); auto).
Time -
Time
(intros x; <ssreflect_plugin::ssrtclintros@0> rewrite agree_validN_def =>Hv n).
Time (<ssreflect_plugin::ssrtclintros@0> apply agree_validN_def =>a b ? ?).
Time (apply discrete_iff_0; auto).
Time Qed.
Time #[global]Instance to_agree_ne : (NonExpansive to_agree).
Time Proof.
Time
(intros n a1 a2 Hx; <ssreflect_plugin::ssrtclintros@0> split =>b /=;
  setoid_rewrite elem_of_list_singleton; naive_solver).
Time Qed.
Time #[global]
Instance to_agree_proper : (Proper ((\226\137\161) ==> (\226\137\161)) to_agree) := (ne_proper _).
Time #[global]
Instance to_agree_discrete  a: (Discrete a \226\134\146 Discrete (to_agree a)).
Time Proof.
Time (intros ? y [H H'] n; split).
Time -
Time (intros a' ->%elem_of_list_singleton).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (H a) as [b ?] ; first  by left).
Time exists b.
Time by rewrite -discrete_iff_0.
Time -
Time (intros b Hb).
Time (destruct (H' b) as (b', (->%elem_of_list_singleton, ?)); auto).
Time exists a.
Time by rewrite elem_of_list_singleton -discrete_iff_0.
Time Qed.
Time #[global]Instance to_agree_injN  n: (Inj (dist n) (dist n) to_agree).
Time Proof.
Time move  {}=>a b [_] /=.
Time setoid_rewrite elem_of_list_singleton.
Time naive_solver.
Time Qed.
Time #[global]Instance to_agree_inj : (Inj (\226\137\161) (\226\137\161) to_agree).
Time Proof.
