Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
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
Lemma match_ty_pair : forall (v1 v2 t1 t2 : ty) (w k : nat), |-[ w, k] v1 <$ t1 -> |-[ w, k] v2 <$ t2 -> |-[ w, k] TPair v1 v2 <$ TPair t1 t2.
Proof.
(intros v1 v2 t1 t2 w k Hm1 Hm2).
(destruct k; split; assumption).
(* Auto-generated comment: Failed. *)
