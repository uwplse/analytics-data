Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma sem_sub_k_pair : forall (k : nat) (t1 t2 t1' t2' : ty), ||-[ k][t1]<= [t1'] -> ||-[ k][t2]<= [t2'] -> ||-[ k][TPair t1 t2]<= [TPair t1' t2'].
Proof.
(intros k t1 t2 t1' t2' Hsem1 Hsem2).
(intros w1).
(specialize (Hsem1 w1); specialize (Hsem2 w1)).
(destruct Hsem1 as [w21 Hsem1]; destruct Hsem2 as [w22 Hsem2]).
exists (Nat.max w21 w22).
(intros v Hm).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(specialize (Hsem1 _ Hm1); specialize (Hsem2 _ Hm2)).
(apply match_ty_pair; eapply match_ty__ge_w; try eassumption).
(apply Nat.le_max_l).
(apply Nat.le_max_r).
Qed.
Lemma sem_sub_pair : forall t1 t2 t1' t2' : ty, ||- [t1]<= [t1'] -> ||- [t2]<= [t2'] -> ||- [TPair t1 t2]<= [TPair t1' t2'].
Proof.
(intros t1 t2 t1' t2' Hem1 Hsem2 k).
(apply sem_sub_k_pair; auto).
Qed.
Lemma sem_sub_k_union : forall (k : nat) (t1 t2 t' : ty), ||-[ k][t1]<= [t'] -> ||-[ k][t2]<= [t'] -> ||-[ k][TUnion t1 t2]<= [t'].
Proof.
(intros k t1 t2 t' Hsem1 Hsem2).
(intros w1).
(specialize (Hsem1 w1); specialize (Hsem2 w1)).
(destruct Hsem1 as [w21 Hsem1]; destruct Hsem2 as [w22 Hsem2]).
exists (Nat.max w21 w22).
(intros v Hm).
(apply match_ty_union__inv in Hm).
(destruct Hm as [Hm| Hm]; [ specialize (Hsem1 _ Hm) | specialize (Hsem2 _ Hm) ]; [ apply match_ty_union_1 | apply match_ty_union_2 ];
  eapply match_ty__ge_w; try eassumption).
(destruct Hm as [Hm| Hm]; [ specialize (Hsem1 _ Hm) | specialize (Hsem2 _ Hm) ]; [ apply Hsem1 | apply Hsem2 ]; eapply match_ty__ge_w;
  try eassumption).
(* Failed. *)
