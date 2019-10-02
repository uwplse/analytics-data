Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.AltMatchDef.
Require Import BetaJulia.BasicTactics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Close Scope btjm.
Open Scope btjmi.
Lemma match_ty_i_pair : forall (v1 v2 t1 t2 : ty) (k : nat), |-[ k] v1 <$ t1 -> |-[ k] v2 <$ t2 -> |-[ k] TPair v1 v2 <$ TPair t1 t2.
Proof.
(intros v1 v2 t1 t2 k Hm1 Hm2).
(destruct k; split; assumption).
Qed.
Lemma match_ty_i_union_1 : forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ t1 -> |-[ k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; left; assumption).
Qed.
Lemma match_ty_i_union_2 : forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ t2 -> |-[ k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; right; assumption).
Qed.
Lemma match_ty_i__reflexive : forall v : ty, value_type v -> forall k : nat, |-[ k] v <$ v.
Proof.
(intros v Hv; induction Hv; intros k).
-
(destruct k; reflexivity).
-
(apply match_ty_i_pair; auto).
-
(destruct k).
constructor.
(simpl).
tauto.
Qed.
Lemma sem_sub_k_i__trans : forall (k : nat) (t1 t2 t3 : ty), ||-[ k][t1]<= [t2] -> ||-[ k][t2]<= [t3] -> ||-[ k][t1]<= [t3].
Proof.
auto with DBBetaJulia.
Qed.
Lemma sem_sub_k_i__sem_eq_k_i : forall (k : nat) (t1 t2 : ty), ||-[ k][t1]<= [t2] -> ||-[ k][t2]<= [t1] -> ||-[ k][t1]= [t2].
Proof.
(intros k t1 t2 Hsem1 Hsem2).
(split; auto).
Qed.
Lemma sem_eq_k_i__trans : forall (k : nat) (t1 t2 t3 : ty), ||-[ k][t1]= [t2] -> ||-[ k][t2]= [t3] -> ||-[ k][t1]= [t3].
Proof.
(intros k t1 t2 t3 Hsem1 Hsem2).
(unfold sem_eq_k in *).
(intros v).
specialize (Hsem1 v).
specialize (Hsem2 v).
tauto.
Qed.
Lemma cname_sem_sub_k_i__sub_d : forall (k : nat) (c : cname) (t2 : ty), ||-[ k][TCName c]<= [t2] -> |- TCName c << t2.
Proof.
(intros k c t2).
(assert (Hva : value_type (TCName c)) by constructor).
(assert (Hma : |-[ k] TCName c <$ TCName c) by (apply match_ty_i__reflexive; assumption)).
(induction t2; intros Hsem; try (solve [ specialize (Hsem _ Hma); destruct k; simpl in Hsem; subst; constructor || contradiction ])).
-
(apply value_sem_sub_k_i_union__inv in Hsem; try assumption).
(* Failed. *)
