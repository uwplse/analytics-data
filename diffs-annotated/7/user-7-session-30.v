Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.BaseProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm_scope.
Lemma match_ty_cname__inv : forall (v : ty) (c : cname) (k : nat), |-[ k] v <$ TCName c -> v = TCName c.
Proof.
(intros v; induction v; try (solve [ intros c k Hm; destruct k; contradiction ])).
(intros c0 k Hm).
(destruct k; reflexivity).
(destruct k; simpl in Hm; subst; reflexivity).
Lemma match_ty_pair__inv :
  forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ TPair t1 t2 -> exists v1 v2 : ty, v = TPair v1 v2 /\ |-[ k] v1 <$ t1 /\ |-[ k] v2 <$ t2.
Proof.
(intros v; induction v; try (solve [ intros t1 t2 k Hm; destruct k; contradiction ])).
(intros t1 t2 k Hm).
exists v1,v2.
(split; try reflexivity).
(simpl in Hm).
(* Failed. *)
