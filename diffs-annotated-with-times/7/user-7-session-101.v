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
Lemma sem_sub__refint_eXrefX :
  forall w1 : nat, exists w2 : nat, forall (k : nat) (v : ty), |-[ w1, k] v <$ TRef tint -> |-[ w2, k] v <$ TExist vX (TRef tX).
Proof.
(intros w1).
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
Lemma sem_sub__eXrefX_eYrefY :
  forall w1 : nat, exists w2 : nat, forall (k : nat) (v : ty), |-[ w1, k] v <$ TExist vX (TRef tX) -> |-[ w2, k] v <$ TExist vY (TRef tY).
Proof.
(intros w1).
(induction w1).
-
exists 1.
(intros k v Hm).
(apply match_ty_exist__0_inv in Hm).
(apply match_ty_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
(apply match_ty_exist).
exists t'.
(apply match_ty_value_type__reflexive).
constructor.
-
exists (S w1).
(intros k v Hm).
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hmx]).
(apply match_ty_exist).
exists tx.
assumption.
Qed.
Lemma not_sem_sub__refeXrefX_eYrefrefY :
  (forall w1 : nat,
   exists w2 : nat, forall (k : nat) (v : ty), |-[ w1, k] v <$ TRef (TExist vX (TRef tX)) -> |-[ w2, k] v <$ TExist vY (TRef (TRef tY))) -> False.
Proof.
(intros Hcontra).
specialize (Hcontra 1).
(destruct Hcontra as [w Hcontra]).
(assert (Hm : |-[ 1, 2] TRef (TExist vX (TRef tX)) <$ TRef (TExist vX (TRef tX))) by (apply match_ty_value_type__reflexive; constructor)).
specialize (Hcontra _ _ Hm).
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
(assert (Heq : [vY := t] TRef (TRef tY) = TRef (TRef t)) by reflexivity).
(rewrite Heq in Hcontra).
clear Heq.
(apply match_ty_ref__inv in Hcontra).
(destruct Hcontra as [t' [Heq Href]]).
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-08-20 10:01:43.960000.*)

