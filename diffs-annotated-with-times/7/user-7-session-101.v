Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0270a.BaseDefs.
Require Import BetaJulia.Sub0270a.BaseMatchProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Lemma sem_sub__refint_eXrefX : ||- [TRef tint]<= [TExist vX (TRef tX)].
Proof.
exists 1.
(intros k; destruct k; intros v Hm).
-
(apply match_ty_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
(simpl).
exists tint.
constructor.
-
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
exists t'.
(apply match_ty_value_type__reflexive).
constructor.
Qed.
Lemma sem_sub__eXrefX_eYrefY : ||- [TExist vX (TRef tX)]<= [TExist vY (TRef tY)].
Proof.
exists 1.
(intros k v Hm).
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hmx]).
(apply match_ty_exist).
exists tx.
assumption.
Qed.
Lemma match_ty__exists_not_matching : forall (t : ty) (w k : nat), exists v : ty, ~ |-[ w, k] v <$ t.
Proof.
(induction t; intros w k).
-
exists (TPair (TCName c) (TCName c)).
(intros Hcontra).
(apply match_ty_cname__inv in Hcontra).
(inversion Hcontra).
-
(destruct (IHt1 w k) as [v1 Hcontra1]).
(destruct (IHt2 w k) as [v2 Hcontra2]).
exists (TPair v1 v2).
(intros Hcontra).
(apply match_ty_pair__inv in Hcontra).
(destruct Hcontra as [v1' [v2' [Heq [Hmq Hmw]]]]).
(inversion Heq; subst).
contradiction.
-
Abort.
Lemma not_sem_sub__refeXrefX_eYrefrefY : ~ ||- [TRef (TExist vX (TRef tX))]<= [TExist vY (TRef (TRef tY))].
Proof.
(intros Hcontra).
(destruct Hcontra as [w Hcontra]).
specialize (Hcontra 2).
(assert (Hm : |-[ w, 2] TRef (TExist vX (TRef tX)) <$ TRef (TExist vX (TRef tX))) by (apply match_ty_value_type__reflexive; constructor)).
specialize (Hcontra _ Hm).
clear Hm.
(destruct w).
-
(apply match_ty_exist__0_inv in Hcontra).
(apply match_ty_ref__inv in Hcontra).
(destruct Hcontra as [t' [Heq Href]]).
(inversion Heq; subst).
clear Heq.
(assert (Hm : |-[ 0, 1] TRef tX <$ TRef tX) by (apply match_ty_value_type__reflexive; constructor)).
specialize (Href (TRef tX)).
(destruct Href as [Href _]).
specialize (Href Hm).
clear Hm.
(apply match_ty_ref__inv in Href).
(destruct Href as [t' [Heq Href]]).
(inversion Heq; subst).
clear Heq.
(assert (Hm : |-[ 0, 0] TEV vX <$ TEV vX) by (apply match_ty_value_type__reflexive; constructor)).
specialize (Href (TEV vX)).
(destruct Href as [Href _]).
specialize (Href Hm).
clear Hm.
(simpl in Href).
(inversion Href).
-
(apply match_ty_exist__inv in Hcontra).
(destruct Hcontra as [t Hcontra]).
(assert (Heq : [vY := t] TRef (TRef tY) = TRef (TRef ([vY := t] tY))) by reflexivity).
(rewrite Heq).
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-08-20 08:39:47.980000.*)

