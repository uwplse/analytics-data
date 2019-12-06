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
exists w1.
(intros k v Hm).
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hmx]).
(destruct w1).
+
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-08-20 09:57:55.680000.*)

