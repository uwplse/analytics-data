Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma match_ty_pair : forall (v1 v2 t1 t2 : ty) (k w : nat), |-[ k, w] v1 <$ t1 -> |-[ k, w] v2 <$ t2 -> |-[ k, w] TPair v1 v2 <$ TPair t1 t2.
Proof.
(intros v1 v2 t1 t2 k w Hm1 Hm2).
(destruct k, w; split; assumption).
Qed.
Lemma match_ty_union_1 : forall (v t1 t2 : ty) (k w : nat), |-[ k, w] v <$ t1 -> |-[ k, w] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k w Hm).
(destruct k, w, v; left; assumption).
Qed.
Lemma match_ty_union_2 : forall (v t1 t2 : ty) (k w : nat), |-[ k, w] v <$ t2 -> |-[ k, w] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k w Hm).
(destruct k, w, v; right; assumption).
Qed.
Lemma match_ty_exist : forall (v : ty) (X : id) (t : ty) (k w : nat), (exists tx : ty, |-[ k, w] v <$ [X := tx] t) -> |-[ k, S w] v <$ TExist X t.
Proof.
(intros v X t k w Hex).
(destruct k, v; assumption).
Qed.
Lemma match_ty_cname__inv : forall (v : ty) (c : cname) (k w : nat), |-[ k, w] v <$ TCName c -> v = TCName c.
Proof.
(intros v c k w Hm).
(destruct k, w, v; simpl in Hm; subst; reflexivity || contradiction).
Qed.
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-08-20 11:44:03.780000.*)

