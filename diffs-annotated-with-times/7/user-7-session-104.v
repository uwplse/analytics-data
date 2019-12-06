Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Definition sem_sub (t1 t2 : ty) := forall k : nat, ||-[ k][t1]<= [t2].
Notation "'||-' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub t1 t2) (at level 50) : btjm_scope.
Lemma sem_sub__refint_eXrefX : ||- [TRef tint]<= [TExist vX (TRef tX)].
Proof.
(intros k).
(destruct k; intros w1; exists 1; intros v Hm).
-
(apply match_ty_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
(simpl).
exists tint.
constructor.
-
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
(simpl).
exists t'.
(split; intros w; exists w; tauto).
Qed.
Lemma sem_sub__eXrefX_eYrefY : ||- [TExist vX (TRef tX)]<= [TExist vY (TRef tY)].
Proof.
(intros k; intros w1; exists w1; intros v Hm).
(destruct w1).
-
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hmx]).
(apply match_ty_exist).
exists tx.
assumption.
Qed.
Lemma sem_eq_k__exists_not : forall (k : nat) (t : ty), exists t' : ty, ~ ||-[ k][t']= [t].
Proof.
(intros k t).
(induction k; induction t).
admit.
admit.
-
(destruct IHt1 as [t'1 Hnot1]).
exists t'1.
(intros Hcontra).
Admitted.
Lemma not_sem_sub__refeXrefX_eYrefrefY : ~ ||- [TRef (TExist vX (TRef tX))]<= [TExist vY (TRef (TRef tY))].
Proof.
(intros Hcontra).
specialize (Hcontra 2 1).
(destruct Hcontra as [w Hcontra]).
(assert (Hm : |-[ 2, 1] TRef (TExist vX (TRef tX)) <$ TRef (TExist vX (TRef tX))) by (apply match_ty_value_type__reflexive; constructor)).
(unfold sem_sub_k_w in Hcontra).
specialize (Hcontra _ Hm).
clear Hm.
(destruct w).
-
(apply Hcontra).
-
(apply match_ty_exist__inv in Hcontra).
(destruct Hcontra as [t Hcontra]).
(assert (Heq : [vY := t] TRef (TRef tY) = TRef (TRef t)) by reflexivity).
(rewrite Heq in Hcontra).
clear Heq.
(apply match_ty_ref__inv in Hcontra).
(destruct Hcontra as [t' [Heq Href]]).
(inversion Heq; subst).
clear Heq.
(unfold sem_eq_k in Href).
(destruct Href as [Href _]).
specialize (Href 1).
(destruct Href as [w2 Hsem]).
(destruct (sem_eq_k__exists_not 0 t) as [t' Hnoteq]).
(assert (Hm : |-[ 1, 1] TRef tint <$ TExist vX (TRef tX))).
{
(simpl).
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-08-20 12:26:27.450000.*)

