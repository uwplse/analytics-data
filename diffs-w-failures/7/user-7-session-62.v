Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
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
Unset Silent.
Proof.
