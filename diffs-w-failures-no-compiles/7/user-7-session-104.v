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
Set Printing Width 148.
Set Silent.
Lemma sem_eq_k__exists_not : forall (k : nat) (t : ty), exists t' : ty, ~ ||-[ k][t']= [t].
Proof.
Show.
Set Printing Width 148.
exists (TRef t).
Show.
(intros Hcontra).
Show.
(destruct Hcontra as [Hsem1 Hsem2]).
Show.
specialize (Hsem1 1).
Show.
(destruct Hsem1 as [w2 Hsem1]).
Show.
Set Printing Width 148.
(assert (Hm : |-[ k, 1] TRef t <$ TRef t) by (apply match_ty_value_type__reflexive; constructor)).
Show.
specialize (Hsem1 _ Hm).
Show.
(destruct k, w2, t; try (solve [ simpl in Hsem1; contraidction ])).
