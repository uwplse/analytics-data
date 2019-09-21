Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0281a.BaseDefs.
Require Import BetaJulia.Sub0281a.BaseProps.
Require Import BetaJulia.Sub0281a.BaseMatchProps.
Require Import BetaJulia.Sub0281a.BaseSemSubProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Lemma build_v : forall (X X' : id) (w : nat) (tx t v : ty), |-[ w] v <$ [X := tx] t -> exists v' : ty, |-[ w] v' <$ [X := TVar X'] t.
Proof.
(intros X X' w tx t).
Unset Silent.
(induction t; intros v Hm).
Set Silent.
-
exists (TCName c).
Unset Silent.
(apply match_ty_cname).
Set Silent.
-
Unset Silent.
Show.
Set Printing Width 148.
Set Silent.
(simpl in *).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(destruct (IHt1 _ Hm1) as [v1' Hm1']).
(destruct (IHt2 _ Hm2) as [v2' Hm2']).
exists (TPair v1' v2').
(apply match_ty_pair; assumption).
-
Unset Silent.
(simpl in *).
(apply match_ty_union__inv in Hm).
(destruct Hm as [Hm| Hm]; [ destruct (IHt1 _ Hm) as [v' Hm'] | destruct (IHt2 _ Hm) as [v' Hm'] ]; exists v';
  [ apply match_ty_union_1 | apply match_ty_union_2 ]; assumption).
-
