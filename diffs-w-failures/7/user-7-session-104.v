Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Unset Silent.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Set Silent.
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
Unset Silent.
Notation "'||-' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub t1 t2) (at level 50) : btjm_scope.
Lemma sem_sub__refint_eXrefX : ||- [TRef tint]<= [TExist vX (TRef tX)].
Proof.
Show.
(intros k).
Set Printing Width 148.
(destruct k; intros w1; exists 1; intros v Hm).
-
Set Printing Width 148.
Set Silent.
(apply match_ty_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
(simpl).
exists tint.
constructor.
-
Unset Silent.
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
Show.
Set Printing Width 148.
(simpl).
exists t'.
Show.
Set Printing Width 148.
Set Silent.
(split; intros w; exists w; tauto).
Unset Silent.
Qed.
Lemma sem_sub__eXrefX_eYrefY : ||- [TExist vX (TRef tX)]<= [TExist vY (TRef tY)].
Set Silent.
Set Printing Width 148.
(intros k; intros w1; exists w1; intros v Hm).
Show.
Show.
Set Printing Width 148.
(destruct w1).
Show.
Set Silent.
-
Unset Silent.
(apply match_ty_exist__0_inv in Hm; contradiction).
-
Show.
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hmx]).
(apply match_ty_exist).
exists tx.
assumption.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Lemma sem_eq_k__exists_not : forall (k : nat) (t : ty), exists t' : ty, ~ ||-[ k][t']= [t].
Proof.
(intros k t).
(induction k; induction t).
admit.
admit.
-
Set Printing Width 148.
(destruct IHt2 as [t'2 Hnot2]).
Show.
Set Silent.
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
(assert (Hm : |-[ 1, 1] TRef t' <$ TExist vX (TRef tX))).
{
(apply match_ty_exist).
exists t'.
(apply match_ty_value_type__reflexive).
constructor.
}
specialize (Hsem _ Hm).
(destruct w2).
contradiction.
(apply match_ty_ref__inv in Hsem).
(destruct Hsem as [tx [Heqx Href]]).
(inversion Heqx; subst).
clear Heqx.
contradiction.
Qed.
Lemma sem_sub__eunion__unione : forall (X : id) (t1 t2 : ty), ||- [TExist X (TUnion t1 t2)]<= [TUnion (TExist X t1) (TExist X t2)].
Unset Silent.
Proof.
(intros X t1 t2 k).
(intros w1).
exists w1.
(intros v Hm).
(destruct w1).
-
Set Silent.
(apply match_ty_exist__0_inv in Hm).
Unset Silent.
contradiction.
-
(apply match_ty_exist__inv in Hm).
Set Silent.
(destruct Hm as [tx Hmx]).
Unset Silent.
(simpl in Hmx).
(apply match_ty_union__inv in Hmx).
(destruct Hmx as [Hmx| Hmx]; [ apply match_ty_union_1 | apply match_ty_union_2 ]; apply match_ty_exist; exists tx; assumption).
Qed.
Set Silent.
Lemma sem_sub__unione__eunion : forall (X : id) (t1 t2 : ty), ||- [TUnion (TExist X t1) (TExist X t2)]<= [TExist X (TUnion t1 t2)].
Proof.
Unset Silent.
(intros X t1 t2 k).
Set Silent.
(intros w1).
exists w1.
Show.
Set Printing Width 148.
(apply match_ty_union__inv in Hm).
Set Printing Width 148.
(destruct Hm as [Hm| Hm]).
Show.
Set Silent.
-
(destruct w1).
Unset Silent.
(v Hm).
