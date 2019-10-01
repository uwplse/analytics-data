Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0281a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjt.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Lemma free_in_ty__decidable : forall (X : id) (t : ty), Decidable.decidable (free_in_ty X t).
Proof.
(intros X t).
(unfold free_in_ty).
Search -IdSet.In.
(apply IdSetProps.Dec.MSetDecideAuxiliary.dec_In).
Qed.
Lemma fresh_in_ty__decidable : forall (X : id) (t : ty), Decidable.decidable (fresh_in_ty X t).
Proof.
