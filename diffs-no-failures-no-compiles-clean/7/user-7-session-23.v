Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.BaseProps.
Require Import BetaJulia.Sub0250a.MatchProps.
Require Import BetaJulia.Sub0250a.SemSubProps.
Require Import BetaJulia.Sub0250a.DeclSubProps.
Require Import BetaJulia.Sub0250a.AltMatchProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Theorem sub_d__semantic_sound : forall t1 t2 : ty, |- t1 << t2 -> ||- [t1]<= [t2].
Proof.
(intros t1 t2 Hsub).
(unfold sem_sub).
(induction Hsub; intros k v Hv Hm).
-
assumption.
-
specialize (IHHsub1 k).
specialize (IHHsub2 k).
auto.
-
specialize (IHHsub1 k).
specialize (IHHsub2 k).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(inversion Hv; subst).
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
{
(pose proof (sub_d_equal__inv_depth_equal _ _ Hsub1 Hsub2) as Heq).
(rewrite <- Heq).
tauto.
}
(assert (Href' : ||-[ k][t]= [t'])).
{
(intros v Hval; split; intros Hm; [ apply IHHsub1 | apply IHHsub2 ]; assumption).
}
(eapply sem_eq_k__trans; eassumption).
Qed.
Theorem sub_d__semantic_complete : forall t1 t2 : ty, ||- [t1]<= [t2] -> |- t1 << t2.
Proof.
(intros t1 t2 Hsem).
(apply SD_Trans with (MkNF( t1))).
(apply mk_nf__sub_d2; assumption).
(apply nf_sem_sub__sub_d).
(apply mk_nf__in_nf).
(eapply sem_sub__trans; try eassumption).
(apply sem_eq__sem_sub).
(apply sem_eq__comm).
(apply mk_nf__sem_eq; assumption).
Qed.
Theorem sem_sub_i__sem_sub_deq : forall t1 t2 : ty, (||- [t1]<= [t2])%btjmi -> (||- [t1]<= [t2])%btjmdeq.
