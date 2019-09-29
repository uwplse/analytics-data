Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.BaseProps.
Require Import BetaJulia.Sub0250a.MatchProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm_scope.
Lemma value_sem_sub_k_union__inv :
  forall v : ty, value_type v -> forall (k : nat) (ta tb : ty), ||-[ k][v]<= [TUnion ta tb] -> ||-[ k][v]<= [ta] \/ ||-[ k][v]<= [tb].
Proof.
(intros v Hv k ta tb Hsem).
(destruct (match_ty_value_type_r v Hv k) as [Hcontra| Hdep]).
-
(left; intros v' Hm').
(exfalso; apply Hcontra; eauto).
-
(unfold sem_sub_k in Hsem).
(assert (Hm : |-[ k] v <$ v) by (apply match_ty_value_type__reflexive; assumption)).
specialize (Hsem _ Hm).
(apply match_ty_union__inv in Hsem).
(destruct Hsem; [ left | right ]; unfold sem_sub_k; intros v' Hm'; apply match_ty__transitive_on_value_type with v; assumption).
Qed.
Lemma sem_sub_k_pair__inv :
  forall (t1 t2 t1' t2' : ty) (k : nat),
  | TPair t1 t2 | <= k -> ||-[ k][TPair t1 t2]<= [TPair t1' t2'] -> ||-[ k][t1]<= [t1'] /\ ||-[ k][t2]<= [t2'].
Proof.
(intros t1 t2 t1' t2' k Hdep Hsem).
(unfold sem_sub_k in Hsem).
(destruct (max_inv_depth_le__inv _ _ _ Hdep) as [Hdep1 Hdep2]).
(destruct (value_type_matching_ty__exists t1 k Hdep1) as [pv1 Hpv1]).
(destruct (value_type_matching_ty__exists t2 k Hdep2) as [pv2 Hpv2]).
(split; intros v Hm;
  [ assert (Hmp : |-[ k] TPair v pv2 <$ TPair t1 t2) by (apply match_ty_pair; assumption)
  | assert (Hmp : |-[ k] TPair pv1 v <$ TPair t1 t2) by (apply match_ty_pair; assumption) ]; specialize (Hsem _ Hmp);
  apply match_ty_pair__inv in Hsem; destruct Hsem as [v1 [v2 [Heq [Hm1 Hm2]]]]; inversion Heq; subst; assumption).
Qed.
Theorem mk_nf__sem_eq_k : forall (k : nat) (t : ty), ||-[ k][t]= [MkNF( t)].
Proof.
(apply match_ty_nf).
Qed.
Lemma mk_nf__sem_sub_k_l : forall (k : nat) (t : ty), ||-[ k][MkNF( t)]<= [t].
Proof.
(intros k t).
(apply sem_eq_k__sem_sub_k).
(apply mk_nf__sem_eq_k).
Qed.
Lemma mk_nf__sem_sub_k_r : forall (k : nat) (t : ty), ||-[ k][t]<= [MkNF( t)].
Proof.
(intros k t).
(apply sem_eq_k__sem_sub_k).
(apply mk_nf__sem_eq_k).
