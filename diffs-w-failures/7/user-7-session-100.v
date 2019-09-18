Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0270a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Unset Silent.
Set Silent.
Lemma match_ty_pair : forall (v1 v2 t1 t2 : ty) (w k : nat), |-[ w, k] v1 <$ t1 -> |-[ w, k] v2 <$ t2 -> |-[ w, k] TPair v1 v2 <$ TPair t1 t2.
Unset Silent.
Proof.
(intros v1 v2 t1 t2 w k Hm1 Hm2).
(destruct k; split; assumption).
(destruct w; destruct k; split; assumption).
Qed.
Set Silent.
Lemma match_ty_union_1 : forall (v t1 t2 : ty) (w k : nat), |-[ w, k] v <$ t1 -> |-[ w, k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 w k Hm).
Unset Silent.
(destruct w; destruct k; destruct v; left; assumption).
Qed.
Set Silent.
Lemma match_ty_union_2 : forall (v t1 t2 : ty) (w k : nat), |-[ w, k] v <$ t2 -> |-[ w, k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 w k Hm).
Unset Silent.
(destruct w; destruct k; destruct v; right; assumption).
Qed.
Set Silent.
Lemma match_ty_exist : forall (v : ty) (X : id) (t : ty) (w k : nat), (exists tx : ty, |-[ w, k] v <$ [X := tx] t) -> |-[ S w, k] v <$ TExist X t.
Unset Silent.
Proof.
(intros v X t w k Hex).
(destruct k; destruct v; assumption).
Qed.
Set Silent.
Lemma match_ty_cname__inv : forall (v : ty) (c : cname) (w k : nat), |-[ w, k] v <$ TCName c -> v = TCName c.
Proof.
Unset Silent.
(intros v; induction v; try (solve [ intros c w k Hm; destruct w; destruct k; contradiction ])).
(intros c0 w k Hm).
(destruct w; destruct k; simpl in Hm; subst; reflexivity).
Qed.
Set Silent.
Lemma match_ty_pair__inv :
  forall (v t1 t2 : ty) (w k : nat), |-[ w, k] v <$ TPair t1 t2 -> exists v1 v2 : ty, v = TPair v1 v2 /\ |-[ w, k] v1 <$ t1 /\ |-[ w, k] v2 <$ t2.
Proof.
Unset Silent.
(intros v; induction v; try (solve [ intros t1 t2 k Hm; destruct w; destruct k; contradiction ])).
