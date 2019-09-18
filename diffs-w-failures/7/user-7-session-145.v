Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import BetaJulia.Sub0280a.BaseProps.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Require Import BetaJulia.Sub0280a.BaseSemSubProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Lemma sem_sub_k_exist_fresh_l : forall (k : nat) (X : id) (t : ty), fresh_in_ty X t -> ||-[ k][TExist X t]<= [t].
Proof.
(intros k X t Hfresh).
(intros w1).
exists w1.
(intros v Hm).
(destruct w1).
-
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(simpl in Hm).
(rewrite subs_fresh_in_ty in Hm; try assumption).
(eapply match_ty__ge_w).
eassumption.
(repeat constructor).
Qed.
Lemma sem_sub_k_exist_fresh_r : forall (k : nat) (X : id) (t : ty), fresh_in_ty X t -> ||-[ k][t]<= [TExist X t].
Proof.
(intros k X t Hfresh).
(intros w1).
exists (S w1).
(intros v Hm).
(apply match_ty_exist).
exists (TEV X).
(rewrite subs_fresh_in_ty; assumption).
Qed.
Lemma sem_sub_exist_fresh_l : forall (X : id) (t : ty), fresh_in_ty X t -> ||- [TExist X t]<= [t].
Proof.
(intros X t Hfresh k).
(apply sem_sub_k_exist_fresh_l).
assumption.
Qed.
Lemma sem_sub_k_exist_pair : forall (k : nat) (X : id) (t1 t2 : ty), ||-[ k][TExist X (TPair t1 t2)]<= [TPair (TExist X t1) (TExist X t2)].
Proof.
(intros k X t1 t2 w1).
exists w1.
(intros v Hm).
(destruct w1).
-
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(simpl in Hm).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_pair; apply match_ty_exist; exists tx; assumption).
Qed.
Lemma sem_sub_exist_pair : forall (X : id) (t1 t2 : ty), ||- [TExist X (TPair t1 t2)]<= [TPair (TExist X t1) (TExist X t2)].
Proof.
(intros X t1 t2 k).
(apply sem_sub_k_exist_pair).
Qed.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Lemma match_ty_ev__match_ty_any :
  forall (k w : nat) (X : id) (t : ty), fresh_in_ty X t -> |-[ k, w] TEV X <$ t -> forall v : ty, value_type v -> |-[ k, w] v <$ t.
Proof.
Show.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
(intros k w).
Unset Silent.
generalize dependent k.
(induction w).
admit.
(intros k X t HX Hm v Hv).
(induction t).
admit.
admit.
admit.
admit.
-
Show.
Set Printing Width 148.
Set Silent.
(apply match_ty_exist__inv in Hm).
Unset Silent.
(destruct Hm as [tx Hm]).
Show.
Search -IdSet.In.
Show.
Set Silent.
(destruct (beq_idP X i)).
+
Unset Silent.
subst.
(apply match_ty_exist).
exists tx.
Set Printing Width 148.
(apply IHw with i; try assumption).
Set Silent.
Abort.
Lemma sem_sub_fresh_var__sem_sub_any :
  forall (X : id) (t t' : ty) (X' : id),
  IdSet.In X (FV t) -> fresh_in_ty X' t' -> ||- [[X := TVar X'] t]<= [t'] -> forall tx : ty, ||- [[X := tx] t]<= [t'].
Proof.
(intros X t).
(intros t' X' HX HX' Hsem tx).
(intros k w1).
specialize (Hsem k w1).
(destruct Hsem as [w2 Hsem]).
exists w2.
Unset Silent.
(intros v Hm).
Set Silent.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Lemma sem_sub_fresh_var__sem_sub_exist' :
  forall (X : id) (t t' : ty) (X' : id),
  IdSet.In X (FV t) -> fresh_in_ty X' t' -> ||- [[X := TVar X'] t]<= [t'] -> forall tx : ty, ||- [[X := tx] t]<= [t'].
Proof.
(intros X t t' X' HX HX' Hsem tx).
(intros k w1).
specialize (Hsem k w1).
(destruct Hsem as [w2 Hsem]).
exists w2.
(intros v Hm).
(induction w1).
Abort.
Unset Silent.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Unset Silent.
Lemma xxx :
  forall (X : id) (w1 : nat) (t : ty) (k w2 : nat) (t' : ty) (X' : id),
  IdSet.In X (FV t) ->
  fresh_in_ty X' t' ->
  (forall v, |-[ k, w1] v <$ [X := TVar X'] t -> |-[ k, w2] v <$ t') -> forall tx : ty, forall v, |-[ k, w1] v <$ [X := tx] t -> |-[ k, w2] v <$ t'.
Set Silent.
Proof.
(intros X w1).
(induction w1).
Unset Silent.
admit.
Set Silent.
(intros t).
Unset Silent.
(induction t).
Set Silent.
admit.
admit.
admit.
Unset Silent.
admit.
-
Set Printing Width 148.
(intros k w2 t' X' HX HX' Hsem).
(intros tx v Hm).
