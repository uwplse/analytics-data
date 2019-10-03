Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0282a.BaseDefs.
Require Import BetaJulia.Sub0282a.BaseProps.
Require Import BetaJulia.Sub0282a.BaseMatchProps.
Require Import BetaJulia.Sub0282a.BaseSemSubProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Lemma build_v_full :
  forall (X X' : id) (tx : ty) (w : nat) (t v : ty),
  wf_ty tx ->
  b_free_in_ty X t ->
  |-[ w] v <$ [BX := tx] t ->
  exists v' : ty,
    |-[ w] v' <$ [BX := TFVar X'] t /\
    (forall (w' : nat) (t' : ty),
     |-[ w'] v' <$ t' -> (not_f_free_in_ty X' t' -> exists w2, |-[ w2] v <$ t') /\ (f_free_in_ty X' t' -> exists w2, |-[ w2] v <$ [FX' := tx] t')).
Proof.
Abort.
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
Search -b_free_in_ty.
(destruct (b_free_in_ty__dec X t) as [HX| HX]).
2: {
idtac.
Search -not_b_free_in_ty.
(rewrite b_subst_not_b_free_in_ty in IHHsub; try assumption).
(induction w1).
(* Auto-generated comment: Failed. *)

