Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Set Printing Width 148.
Set Silent.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Set Printing Width 148.
Set Silent.
Lemma match_ty_pair : forall (v1 v2 t1 t2 : ty) (k w : nat), |-[ k, w] v1 <$ t1 -> |-[ k, w] v2 <$ t2 -> |-[ k, w] TPair v1 v2 <$ TPair t1 t2.
Proof.
Unset Silent.
(intros v1 v2 t1 t2 k w Hm1 Hm2).
(destruct k, w; split; assumption).
Set Silent.
Qed.
Lemma match_ty_union_1 : forall (v t1 t2 : ty) (k w : nat), |-[ k, w] v <$ t1 -> |-[ k, w] v <$ TUnion t1 t2.
Unset Silent.
Proof.
(intros v t1 t2 k w Hm).
Show.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
(destruct k, w, v; left; assumption).
Set Silent.
Qed.
Lemma match_ty_union_2 : forall (v t1 t2 : ty) (k w : nat), |-[ k, w] v <$ t2 -> |-[ k, w] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k w Hm).
Unset Silent.
(destruct k, w, v; right; assumption).
Set Silent.
Qed.
Unset Silent.
Lemma match_ty_exist : forall (v : ty) (X : id) (t : ty) (k w : nat), (exists tx : ty, |-[ k, w] v <$ [X := tx] t) -> |-[ k, S w] v <$ TExist X t.
Proof.
(intros v X t k w Hex).
(destruct k, v; assumption).
Set Printing Width 148.
Set Silent.
Lemma match_ty_cname__inv : forall (v : ty) (c : cname) (k w : nat), |-[ k, w] v <$ TCName c -> v = TCName c.
Proof.
(intros v c k w Hm).
(destruct k, w, v; simpl in Hm; subst; reflexivity || contradiction).
Qed.
Lemma match_ty_pair__inv :
  forall (v t1 t2 : ty) (k w : nat), |-[ k, w] v <$ TPair t1 t2 -> exists v1 v2 : ty, v = TPair v1 v2 /\ |-[ k, w] v1 <$ t1 /\ |-[ k, w] v2 <$ t2.
Set Printing Width 148.
(intros v t1 t2 k w Hm).
Set Printing Width 148.
(destruct k, w, v; simpl in Hm; contradiction || (exists v1,v2; split; [ reflexivity | tauto ])).
Set Printing Width 148.
Set Silent.
Lemma match_ty_union__inv : forall (v t1 t2 : ty) (k w : nat), |-[ k, w] v <$ TUnion t1 t2 -> |-[ k, w] v <$ t1 \/ |-[ k, w] v <$ t2.
Proof.
Unset Silent.
(intros v t1 t2 k w Hm).
(destruct k, w, v; assumption).
Qed.
Set Silent.
Lemma match_ty_ref__weak_inv : forall (v t : ty) (k w : nat), |-[ k, w] v <$ TRef t -> exists t' : ty, v = TRef t'.
Unset Silent.
Proof.
Set Silent.
Set Printing Width 148.
(destruct k, w, v; simpl in Hm; contradiction || (exists v; reflexivity)).
Qed.
Set Silent.
Lemma match_ty_ref__inv : forall (v t : ty) (k w : nat), |-[ S k, w] v <$ TRef t -> exists t' : ty, v = TRef t' /\ ||-[ k][t']= [t].
Unset Silent.
Proof.
Set Silent.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
(destruct v; try (solve [ destruct k, w; simpl in Hm; contradiction ])).
Show.
exists v.
split.
Show.
reflexivity.
Show.
Show.
Set Printing Width 148.
Set Printing Width 148.
(destruct w; auto).
Show.
Qed.
Set Silent.
Lemma match_ty_exist__0_inv : forall (v : ty) (X : id) (t : ty) (k : nat), |-[ k, 0] v <$ TExist X t -> False.
Set Printing Width 148.
(intros v X t k Hm).
(destruct k, v; simpl in Hm; contradiction).
Qed.
Set Silent.
Lemma match_ty_exist__inv :
  forall (v : ty) (X : id) (t : ty) (k w : nat), |-[ k, S w] v <$ TExist X t -> exists tx : ty, |-[ k, w] v <$ [X := tx] t.
Unset Silent.
Proof.
(intros v X t k w).
(destruct k, v; assumption).
