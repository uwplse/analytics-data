Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.AltMatchDef.
Require Import BetaJulia.BasicTactics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Close Scope btjm.
Unset Silent.
Open Scope btjmi.
Set Silent.
Lemma match_ty_i_pair : forall (v1 v2 t1 t2 : ty) (k : nat), |-[ k] v1 <$ t1 -> |-[ k] v2 <$ t2 -> |-[ k] TPair v1 v2 <$ TPair t1 t2.
Proof.
(intros v1 v2 t1 t2 k Hm1 Hm2).
(destruct k; split; assumption).
Qed.
Lemma match_ty_i_union_1 : forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ t1 -> |-[ k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; left; assumption).
Qed.
Lemma match_ty_i_union_2 : forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ t2 -> |-[ k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; right; assumption).
Qed.
Lemma match_ty_i_cname__inv : forall (v : ty) (c : cname) (k : nat), |-[ k] v <$ TCName c -> v = TCName c.
Proof.
Unset Silent.
(intros v; induction v; try (solve [ intros c k Hm; destruct k; contradiction ])).
Set Silent.
(intros c0 k Hm).
(destruct k; simpl in Hm; subst; reflexivity).
Unset Silent.
Qed.
Set Silent.
Lemma match_ty_i_pair__inv :
  forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ TPair t1 t2 -> exists v1 v2 : ty, v = TPair v1 v2 /\ |-[ k] v1 <$ t1 /\ |-[ k] v2 <$ t2.
Proof.
Unset Silent.
(intros v; induction v; try (solve [ intros t1 t2 k Hm; destruct k; contradiction ])).
Set Silent.
(intros t1 t2 k Hm).
exists v1,v2.
(split; try reflexivity).
(destruct k; simpl in Hm; assumption).
Unset Silent.
Qed.
Set Silent.
Lemma match_ty_i_union__inv : forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ TUnion t1 t2 -> |-[ k] v <$ t1 \/ |-[ k] v <$ t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; assumption).
Unset Silent.
Qed.
