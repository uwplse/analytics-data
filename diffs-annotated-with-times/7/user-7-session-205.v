Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
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
Open Scope btjm.
Theorem sub_d__semantic_sound : forall t1 t2 : ty, |- t1 << t2 -> ||- [t1]<= [t2].
Proof.
(intros t1 t2 Hsub).
(induction Hsub).
-
(apply sem_sub__refl).
-
(apply sem_sub__trans with t2; assumption).
-
(apply sem_sub_pair; assumption).
-
(apply sem_sub_union; assumption).
-
(apply sem_sub_union_1).
(apply sem_sub__refl).
-
(apply sem_sub_union_2).
(apply sem_sub__refl).
-
(intros w1).
exists w1.
(intros v Hm).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_union__inv in Hm1).
(destruct Hm1; [ apply match_ty_union_1 | apply match_ty_union_2 ]; auto using match_ty_pair).
-
(intros w1).
exists w1.
(intros v Hm).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_union_1 | apply match_ty_union_2 ]; auto using match_ty_pair).
-
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-09-04 08:07:29.530000.*)

