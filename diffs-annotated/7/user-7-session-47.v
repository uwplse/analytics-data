Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.BaseProps.
Require Import BetaJulia.Sub0250a.MatchProps.
Require Import BetaJulia.Sub0250a.DeclSubProps.
Require Import BetaJulia.Sub0250a.AltMatchDef.
Require Import BetaJulia.Sub0250a.AltMatchProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
-
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(unfold sem_sub_k in *).
auto using match_ty_pair.
-
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
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_union_1 | apply match_ty_union_2 ]; auto using match_ty_pair).
-
(destruct k).
(destruct v; contradiction).
(apply match_ty_ref__inv in Hm).
(destruct Hm as [tx [Heq [[Hdept Hdeptx] Href]]]; subst).
(simpl).
split.
+
(assert (Heq : | t' | = | t |) by (apply sub_d_eq__inv_depth_eq; assumption)).
(rewrite Heq).
tauto.
+
(assert (Heq : ||-[ k][t]= [t']) by (apply sem_sub_k__sem_eq_k; auto)).
(eapply sem_eq_k__trans; eassumption).
Qed.
Close Scope btjm.
Open Scope btjmi.
Theorem sub_d__semantic_i_sound : forall t1 t2 : ty, |- t1 << t2 -> ||- [t1]<= [t2].
Proof.
(intros t1 t2 Hsub).
(unfold sem_sub_i).
(induction Hsub; intros k v Hm).
-
assumption.
-
(unfold sem_sub_k_i in *).
auto.
-
(apply match_ty_i_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(unfold sem_sub_k_i in *).
auto using match_ty_i_pair.
-
(apply match_ty_i_union__inv in Hm).
(destruct Hm; [ apply IHHsub1 | apply IHHsub2 ]; assumption).
-
(apply match_ty_i_union_1; assumption).
-
(apply match_ty_i_union_2; assumption).
-
(apply match_ty_i_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_i_union__inv in Hm1).
(destruct Hm1; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; auto using match_ty_i_pair).
-
(apply match_ty_i_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_i_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; auto using match_ty_i_pair).
-
(destruct k).
(destruct v; contradiction).
(* Failed. *)
