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
exists (TRef t).
(intros Hcontra).
(destruct Hcontra as [Hsem1 Hsem2]).
specialize (Hsem1 1).
(destruct Hsem1 as [w2 Hsem1]).
(assert (Hm : |-[ k, 1] TRef t <$ TRef t) by (apply match_ty_value_type__reflexive; constructor)).
specialize (Hsem1 _ Hm).
(destruct k, w2, t; try (solve [ simpl in Hsem1; contraidction ])).
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-08-20 12:40:53.150000.*)

