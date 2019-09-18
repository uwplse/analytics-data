Time From iris.proofmode Require Import coq_tactics environments.
Time From iris.algebra Require Import proofmode_classes.
Time From iris.base_logic Require Export base_logic.
Time From iris.algebra Require Export cmra.
Time From iris.algebra Require Import list.
Time From stdpp Require Export strings.
Time Set Default Proof Using "Type".
Time Delimit Scope proof_scope with env.
Time Arguments Envs _ _%proof_scope _%proof_scope _.
Time Arguments Enil {_}.
Time Arguments Esnoc {_} _%proof_scope _%string _%I.
Time Notation "" := Enil (only printing) : proof_scope.
Time
Notation "\206\147 H : P" := (Esnoc \206\147 (INamed H) P%I)
  (at level 1, P  at level 200, left associativity,
   format "\206\147 H  :  '[' P ']' '//'", only printing) : proof_scope.
Time
Notation "\206\147 '_' : P" := (Esnoc \206\147 (IAnon _) P%I)
  (at level 1, P  at level 200, left associativity,
   format "\206\147 '_'  :  '[' P ']' '//'", only printing) : proof_scope.
Time
Notation
  "\206\147 '--------------------------------------' \226\150\161 \206\148 '--------------------------------------' \226\136\151 Q" :=
  (envs_entails (Envs \206\147 \206\148 _) Q%I)
  (at level 1, Q  at level 200, left associativity,
   format "\206\147 '--------------------------------------' \226\150\161 '//' \206\148 '--------------------------------------' \226\136\151 '//' Q '//'",
   only printing) : stdpp_scope.
Time
Notation "\206\148 '--------------------------------------' \226\136\151 Q" :=
  (envs_entails (Envs Enil \206\148 _) Q%I)
  (at level 1, Q  at level 200, left associativity,
   format "\206\148 '--------------------------------------' \226\136\151 '//' Q '//'",
   only printing) : stdpp_scope.
Time
Notation "\206\147 '--------------------------------------' \226\150\161 Q" :=
  (envs_entails (Envs \206\147 Enil _) Q%I)
  (at level 1, Q  at level 200, left associativity,
   format "\206\147 '--------------------------------------' \226\150\161 '//' Q '//'",
   only printing) : stdpp_scope.
Time
Notation "'--------------------------------------' \226\136\151 Q" :=
  (envs_entails (Envs Enil Enil _) Q%I)
  (at level 1, Q  at level 200,
   format "'--------------------------------------' \226\136\151 '//' Q '//'",
   only printing) : stdpp_scope.
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
Time From iris.algebra Require Import gmap.
Time From iris.algebra Require cofe_solver.
Time From iris.base_logic Require Import base_logic.
Time Set Default Proof Using "Type".
Time
Structure gFunctor :=
 GFunctor {gFunctor_F :> rFunctor;
           gFunctor_contractive : rFunctorContractive gFunctor_F}.
Time Arguments GFunctor _ {_}.
Time Existing Instance gFunctor_contractive.
Time Add Printing Constructor gFunctor.
Time Definition gFunctors := {n : nat & fin n \226\134\146 gFunctor}.
Time Definition gid (\206\163 : gFunctors) := fin (projT1 \206\163).
Time
Definition gFunctors_lookup (\206\163 : gFunctors) : gid \206\163 \226\134\146 gFunctor := projT2 \206\163.
Time Coercion gFunctors_lookup : gFunctors >-> Funclass.
Time Definition gname := positive.
Time Canonical Structure gnameO := leibnizO gname.
Time
Definition iResF (\206\163 : gFunctors) : urFunctor :=
  discrete_funURF (\206\187 i, gmapURF gname (\206\163 i)).
Time Module gFunctors.
Time Definition nil : gFunctors := existT 0 (fin_0_inv _).
Time
Definition singleton (F : gFunctor) : gFunctors :=
  existT 1 (fin_S_inv (\206\187 _, gFunctor) F (fin_0_inv _)).
Time
Definition app (\206\1631 \206\1632 : gFunctors) : gFunctors :=
  existT (projT1 \206\1631 + projT1 \206\1632) (fin_plus_inv _ (projT2 \206\1631) (projT2 \206\1632)).
Time End gFunctors.
Time Coercion gFunctors.singleton : gFunctor >-> gFunctors.
Time Notation "#[ ]" := gFunctors.nil (format "#[ ]").
Time
Notation "#[ \206\1631 ; .. ; \206\163n ]" :=
  (gFunctors.app \206\1631 .. (gFunctors.app \206\163n gFunctors.nil) ..).
Time
Class subG (\206\1631 \206\1632 : gFunctors) :=
    in_subG : forall i, {j | \206\1631 i = \206\1632 j}.
Time #[local]Arguments validN _ _ _ !_ /.
Time #[local]Arguments valid _ _ !_ /.
Time #[local]Arguments op _ _ _ !_ /.
Time #[local]Arguments pcore _ _ !_ /.
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
Time Hint Mode subG ! +: typeclass_instances.
Time
Lemma subG_inv \206\1631 \206\1632 \206\163 : subG (gFunctors.app \206\1631 \206\1632) \206\163 \226\134\146 subG \206\1631 \206\163 * subG \206\1632 \206\163.
Time Qed.
Time Lemma agree_eq {A} (x y : agree A) : agree_car x = agree_car y \226\134\146 x = y.
Time Proof.
Time (destruct x as [a ?], y as [b ?]; simpl).
Time Proof.
Time (move  {}=>H; split).
Time -
Time (move  {}=>i; move : {}H {} =>/(_ (Fin.L _ i)) [j] /=).
Time (rewrite fin_plus_inv_L; eauto).
Time -
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
Time (move  {}=>i; move : {}H {} =>/(_ (Fin.R _ i)) [j] /=).
Time (rewrite fin_plus_inv_R; eauto).
Time Qed.
Time Instance subG_refl  \206\163: (subG \206\163 \206\163).
Time Proof.
Time split.
Time -
Time done.
Time Proof.
Time (move  {}=>i; by exists i).
Time Qed.
Time
Instance subG_app_l  \206\163 \206\1631 \206\1632: (subG \206\163 \206\1631 \226\134\146 subG \206\163 (gFunctors.app \206\1631 \206\1632)).
Time Proof.
Time (move  {}=>H i; move : {}H {} =>/(_ i) [j ?]).
Time exists (Fin.L _ j).
Time by rewrite /= fin_plus_inv_L.
Time -
Time (intros n; split; rewrite /dist /agree_dist).
Time +
Time (intros x; split; eauto).
Time Qed.
Time
Instance subG_app_r  \206\163 \206\1631 \206\1632: (subG \206\163 \206\1632 \226\134\146 subG \206\163 (gFunctors.app \206\1631 \206\1632)).
Time Proof.
Time (move  {}=>H i; move : {}H {} =>/(_ i) [j ?]).
Time exists (Fin.R _ j).
Time by rewrite /= fin_plus_inv_R.
Time Qed.
Time +
Time (intros x y [? ?]).
Time naive_solver eauto.
Time Module Type iProp_solution_sig.
Time Parameter (iPreProp : gFunctors \226\134\146 ofeT).
Time #[global]Declare Instance iPreProp_cofe  {\206\163}: (Cofe (iPreProp \206\163)).
Time
Definition iResUR (\206\163 : gFunctors) : ucmraT :=
  discrete_funUR (\206\187 i, gmapUR gname (\206\163 i (iPreProp \206\163) _)).
Time Notation iProp \206\163:= (uPredO (iResUR \206\163)).
Time Notation iPropI \206\163:= (uPredI (iResUR \206\163)).
Time Notation iPropSI \206\163:= (uPredSI (iResUR \206\163)).
Time Parameter (iProp_unfold : \226\136\128 {\206\163}, iProp \206\163 -n> iPreProp \206\163).
Time Parameter (iProp_fold : \226\136\128 {\206\163}, iPreProp \206\163 -n> iProp \206\163).
Time
Parameter
  (iProp_fold_unfold : \226\136\128 {\206\163} (P : iProp \206\163), iProp_fold (iProp_unfold P) \226\137\161 P).
Time
Parameter
  (iProp_unfold_fold :
     \226\136\128 {\206\163} (P : iPreProp \206\163), iProp_unfold (iProp_fold P) \226\137\161 P).
Time End iProp_solution_sig.
Time Module Export iProp_solution: iProp_solution_sig.
Time Import cofe_solver.
Time
Definition iProp_result (\206\163 : gFunctors) : solution (uPredOF (iResF \206\163)) :=
  solver.result _.
Time Definition iPreProp (\206\163 : gFunctors) : ofeT := iProp_result \206\163.
Time #[global]Instance iPreProp_cofe  {\206\163}: (Cofe (iPreProp \206\163)) := _.
Time
Definition iResUR (\206\163 : gFunctors) : ucmraT :=
  discrete_funUR (\206\187 i, gmapUR gname (\206\163 i (iPreProp \206\163) _)).
Time Notation iProp \206\163:= (uPredO (iResUR \206\163)).
Time
Definition iProp_unfold {\206\163} : iProp \206\163 -n> iPreProp \206\163 :=
  solution_fold (iProp_result \206\163).
Time Definition iProp_fold {\206\163} : iPreProp \206\163 -n> iProp \206\163 := solution_unfold _.
Time
Lemma iProp_fold_unfold {\206\163} (P : iProp \206\163) : iProp_fold (iProp_unfold P) \226\137\161 P.
Time Proof.
Time (apply solution_unfold_fold).
Time +
Time (intros x y z [H1 H1'] [H2 H2']; split).
Time *
Time (intros a ?).
Time (destruct (H1 a) as (b, (?, ?)); auto).
Time Qed.
Time
Lemma iProp_unfold_fold {\206\163} (P : iPreProp \206\163) :
  iProp_unfold (iProp_fold P) \226\137\161 P.
Time Proof.
Time (apply solution_fold_unfold).
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
Time End iProp_solution.
Time
Lemma iProp_unfold_equivI {\206\163} (P Q : iProp \206\163) :
  iProp_unfold P \226\137\161 iProp_unfold Q \226\138\162@{ iPropI \206\163} P \226\137\161 Q.
Time Proof.
Time rewrite -{+2}(iProp_fold_unfold P) -{+2}(iProp_fold_unfold Q).
Time Qed.
Time Canonical Structure agreeO := OfeT (agree A) agree_ofe_mixin.
Time
Instance agree_validN : (ValidN (agree A)) :=
 (\206\187 n x,
    match agree_car x with
    | [a] => True
    | _ => \226\136\128 a b, a \226\136\136 agree_car x \226\134\146 b \226\136\136 agree_car x \226\134\146 a \226\137\161{n}\226\137\161 b
    end).
Time apply : {}bi.f_equiv {}.
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
Time Qed.
Time Instance agree_op_ne'  x: (NonExpansive (op x)).
Time Proof.
Time
(intros n y1 y2 [H H']; <ssreflect_plugin::ssrtclintros@0> split =>a /=;
  setoid_rewrite elem_of_app; naive_solver).
Time Qed.
Time Instance agree_op_ne : (NonExpansive2 (@op (agree A) _)).
Time Proof.
Time by intros n x1 x2 Hx y1 y2 Hy; rewrite Hy !(comm _ _ y2) Hx.
Time Qed.
Time
Instance agree_op_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) op) :=
 (ne_proper_2 _).
Time Lemma agree_included (x y : agree A) : x \226\137\188 y \226\134\148 y \226\137\161 x \226\139\133 y.
Time Proof.
Time (split; [  | by intros ?; exists y ]).
Time by intros [z Hz]; rewrite Hz assoc agree_idemp.
Time Qed.
Time Lemma agree_op_invN n (x1 x2 : agree A) : \226\156\147{n} (x1 \226\139\133 x2) \226\134\146 x1 \226\137\161{n}\226\137\161 x2.
Time Proof.
Time rewrite agree_validN_def /=.
Time
(<ssreflect_plugin::ssrtclintros@0> setoid_rewrite elem_of_app =>Hv;
  <ssreflect_plugin::ssrtclintros@0> split =>a Ha).
Time -
Time (destruct (elem_of_agree x2); naive_solver).
Time -
Time (destruct (elem_of_agree x1); naive_solver).
Time Qed.
Time Definition agree_cmra_mixin : CmraMixin (agree A).
Time Proof.
Time (apply cmra_total_mixin; try apply _ || by eauto).
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
Time (intros a b ?).
Time (<ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n).
Time by apply to_agree_injN, equiv_dist.
Time Qed.
Time Lemma to_agree_uninjN n x : \226\156\147{n} x \226\134\146 \226\136\131 a, to_agree a \226\137\161{n}\226\137\161 x.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite agree_validN_def =>Hv).
Time (destruct (elem_of_agree x) as [a ?]).
Time
(exists a; <ssreflect_plugin::ssrtclintros@0> split =>b /=; setoid_rewrite
  elem_of_list_singleton; naive_solver).
Time Qed.
Time Lemma to_agree_uninj x : \226\156\147 x \226\134\146 \226\136\131 a, to_agree a \226\137\161 x.
Time Proof.
Time (rewrite /valid /agree_valid; setoid_rewrite agree_validN_def).
Time (destruct (elem_of_agree x) as [a ?]).
Time
(exists a; <ssreflect_plugin::ssrtclintros@0> split =>b /=; setoid_rewrite
  elem_of_list_singleton; naive_solver).
Time Qed.
Time Lemma agree_valid_includedN n x y : \226\156\147{n} y \226\134\146 x \226\137\188{n} y \226\134\146 x \226\137\161{n}\226\137\161 y.
Time Proof.
Time (move  {}=>Hval [z Hy]; move : {}Hval {}; rewrite Hy).
Time by move  {}=>/agree_op_invN {+}->; rewrite agree_idemp.
Time Qed.
Time Lemma to_agree_included a b : to_agree a \226\137\188 to_agree b \226\134\148 a \226\137\161 b.
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> split ; last  by intros ->).
Time (intros (x, Heq)).
Time (<ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n).
Time (destruct (Heq n) as [_ Hincl]).
Time
by <ssreflect_plugin::ssrtclseq@0>
 destruct (Hincl a) as (?, (->%elem_of_list_singleton, ?)) ; first 
 set_solver +.
Time Qed.
Time #[global]Instance agree_cancelable  x: (Cancelable x).
Time Proof.
Time (intros n y z Hv Heq).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (to_agree_uninjN n x) as [x' EQx] ;
 first  by eapply cmra_validN_op_l).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (to_agree_uninjN n y) as [y' EQy] ;
 first  by eapply cmra_validN_op_r).
Time (destruct (to_agree_uninjN n z) as [z' EQz]).
Time {
Time (eapply (cmra_validN_op_r n x z)).
Time by rewrite -Heq.
Time }
Time (assert (Hx'y' : x' \226\137\161{n}\226\137\161 y')).
Time {
Time (apply (inj to_agree), agree_op_invN).
Time by rewrite EQx EQy.
Time }
Time (assert (Hx'z' : x' \226\137\161{n}\226\137\161 z')).
Time {
Time (apply (inj to_agree), agree_op_invN).
Time by rewrite EQx EQz -Heq.
Time }
Time by rewrite -EQy -EQz -Hx'y' -Hx'z'.
Time Qed.
Time Lemma agree_op_inv x y : \226\156\147 (x \226\139\133 y) \226\134\146 x \226\137\161 y.
Time Proof.
Time (intros ?).
Time (<ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n).
Time by apply agree_op_invN, cmra_valid_validN.
Time Qed.
Time Lemma agree_op_inv' a b : \226\156\147 (to_agree a \226\139\133 to_agree b) \226\134\146 a \226\137\161 b.
Time Proof.
Time by intros ?%(inj _)%agree_op_inv.
Time Qed.
Time
Lemma agree_op_invL' `{!LeibnizEquiv A} a b :
  \226\156\147 (to_agree a \226\139\133 to_agree b) \226\134\146 a = b.
Time Proof.
Time by intros ?%leibniz_equiv%agree_op_inv'.
Time Qed.
Time
Lemma agree_equivI {M} a b : to_agree a \226\137\161 to_agree b \226\138\163\226\138\162@{ uPredI M} a \226\137\161 b.
Time Proof.
Time uPred.unseal.
Time (do 2 split).
Time -
Time (intros Hx).
Time exact : {}to_agree_injN {}.
Time -
Time (intros Hx).
Time exact : {}to_agree_ne {}.
Time Qed.
Time Lemma agree_validI {M} x y : \226\156\147 (x \226\139\133 y) \226\138\162@{ uPredI M} x \226\137\161 y.
Time Proof.
Time
(uPred.unseal; <ssreflect_plugin::ssrtclintros@0> split =>r n _ ?; by apply
  : {}agree_op_invN {}).
Time Qed.
Time Lemma to_agree_uninjI {M} x : \226\156\147 x \226\138\162@{ uPredI M} \226\136\131 a, to_agree a \226\137\161 x.
Time Proof.
Time uPred.unseal.
Time (<ssreflect_plugin::ssrtclintros@0> split =>n y _).
Time exact : {}to_agree_uninjN {}.
Time Qed.
Time End agree.
Time Instance: (Params (@to_agree) 1) := { }.
Time Arguments agreeO : clear implicits.
Time Arguments agreeR : clear implicits.
Time #[program]
Definition agree_map {A} {B} (f : A \226\134\146 B) (x : agree A) : 
  agree B := {| agree_car := f <$> agree_car x |}.
Time Next Obligation.
Time by intros A B f [[| ? ?] ?].
Time Qed.
Time Lemma agree_map_id {A} (x : agree A) : agree_map id x = x.
Time Proof.
Time (apply agree_eq).
Time by rewrite /= list_fmap_id.
Time Qed.
Time
Lemma agree_map_compose {A} {B} {C} (f : A \226\134\146 B) (g : B \226\134\146 C) 
  (x : agree A) : agree_map (g \226\136\152 f) x = agree_map g (agree_map f x).
Time Proof.
Time (apply agree_eq).
Time by rewrite /= list_fmap_compose.
Time Qed.
Time
Lemma agree_map_to_agree {A} {B} (f : A \226\134\146 B) (x : A) :
  agree_map f (to_agree x) = to_agree (f x).
Time Proof.
Time by apply agree_eq.
Time Qed.
Time Section agree_map.
Time Context {A B : ofeT} (f : A \226\134\146 B) {Hf : NonExpansive f}.
Time Instance agree_map_ne : (NonExpansive (agree_map f)).
Time Proof.
Time
(intros n x y [H H']; <ssreflect_plugin::ssrtclintros@0> split =>b /=;
  setoid_rewrite elem_of_list_fmap).
Time -
Time (intros (a, (->, ?))).
Time (destruct (H a) as (a', (?, ?)); auto).
Time naive_solver.
Time -
Time (intros (a, (->, ?))).
Time (destruct (H' a) as (a', (?, ?)); auto).
Time naive_solver.
Time Qed.
Time
Instance agree_map_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (agree_map f)) :=
 (ne_proper _).
Time
Lemma agree_map_ext (g : A \226\134\146 B) x :
  (\226\136\128 a, f a \226\137\161 g a) \226\134\146 agree_map f x \226\137\161 agree_map g x.
Time Proof  using (Hf).
Time
(intros Hfg n; <ssreflect_plugin::ssrtclintros@0> split =>b /=;
  setoid_rewrite elem_of_list_fmap).
Time -
Time (intros (a, (->, ?))).
Time exists (g a).
Time (rewrite Hfg; eauto).
Time -
Time (intros (a, (->, ?))).
Time exists (f a).
Time (rewrite -Hfg; eauto).
Time Qed.
Time #[global]Instance agree_map_morphism : (CmraMorphism (agree_map f)).
Time Proof  using (Hf).
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  apply _).
Time -
Time (intros n x).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !agree_validN_def =>Hv b b' /=).
Time (intros (a, (->, ?))%elem_of_list_fmap (a', (->, ?))%elem_of_list_fmap).
Time (apply Hf; eauto).
Time -
Time done.
Time -
Time
(intros x y n; <ssreflect_plugin::ssrtclintros@0> split =>b /=; rewrite
  !fmap_app; setoid_rewrite elem_of_app; eauto).
Time Qed.
Time End agree_map.
Time
Definition agreeO_map {A} {B} (f : A -n> B) : agreeO A -n> agreeO B :=
  OfeMor (agree_map f : agreeO A \226\134\146 agreeO B).
Time Instance agreeO_map_ne  A B: (NonExpansive (@agreeO_map A B)).
Time Proof.
Time
(intros n f g Hfg x; <ssreflect_plugin::ssrtclintros@0> split =>b /=;
  setoid_rewrite elem_of_list_fmap; naive_solver).
Time Qed.
Time #[program]
Definition agreeRF (F : oFunctor) : rFunctor :=
  {|
  rFunctor_car := fun A _ B _ => agreeR (oFunctor_car F A B);
  rFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  agreeO_map (oFunctor_map F fg) |}.
Time Next Obligation.
Time (intros ? A1 ? A2 ? B1 ? B2 ? n ? ? ?; simpl).
Time by apply agreeO_map_ne, oFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x; simpl).
Time rewrite -{+2}(agree_map_id x).
Time (<ssreflect_plugin::ssrtclintros@0> apply (agree_map_ext _) =>y).
Time by rewrite oFunctor_id.
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl).
Time rewrite -agree_map_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply (agree_map_ext _) =>y;
  apply oFunctor_compose).
Time Qed.
Time
Instance agreeRF_contractive  F:
 (oFunctorContractive F \226\134\146 rFunctorContractive (agreeRF F)).
Time Proof.
Time (intros ? A1 ? A2 ? B1 ? B2 ? n ? ? ?; simpl).
Time by apply agreeO_map_ne, oFunctor_contractive.
Time Qed.
