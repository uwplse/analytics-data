Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.BaseProps.
Require Import BetaJulia.Sub0250a.MatchProps.
Unset Silent.
Set Silent.
Require Import BetaJulia.Sub0250a.AltMatchDef.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Theorem sub_d__semantic_sound : forall t1 t2 : ty, |- t1 << t2 -> ||- [t1]<= [t2].
Proof.
(intros t1 t2 Hsub).
(unfold sem_sub).
(induction Hsub; intros k v Hm).
-
assumption.
-
(unfold sem_sub_k in *).
auto.
-
Unset Silent.
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
Set Printing Width 148.
(unfold sem_sub_k in *).
auto using match_ty_pair.
Set Silent.
-
Unset Silent.
Show.
(apply match_ty_union__inv in Hm).
(destruct Hm; [ apply IHHsub1 | apply IHHsub2 ]; assumption).
-
(apply match_ty_union_1; assumption).
-
(apply match_ty_union_2; assumption).
-
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_union__inv in Hm1).
(destruct Hm1; [ apply match_ty_union_1 | apply match_ty_union_2 ]; auto using match_ty_pair).
-
Set Silent.
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_union__inv in Hm2).
Unset Silent.
(destruct Hm2; [ apply match_ty_union_1 | apply match_ty_union_2 ]; auto using match_ty_pair).
Set Silent.
-
Unset Silent.
Show.
(destruct k).
(destruct v; contradiction).
(apply match_ty_ref__inv in Hm).
(destruct Hm as [tx [Heq [[Hdept Hdeptx] Href]]]; subst).
(simpl).
split.
