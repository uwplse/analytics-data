Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import BetaJulia.Sub0280a.BaseProps.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Require Import BetaJulia.Sub0280a.BaseSemSubProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Lemma sem_sub_k_exist_fresh_l : forall (k : nat) (X : id) (t : ty), fresh_in_ty X t -> ||-[ k][TExist X t]<= [t].
Proof.
(intros k X t Hfresh).
(intros w1).
exists w1.
(intros v Hm).
(destruct w1).
-
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(simpl in Hm).
(rewrite subs_fresh_in_ty in Hm; try assumption).
(eapply match_ty__ge_w).
eassumption.
(repeat constructor).
Qed.
Lemma sem_sub_k_exist_fresh_r : forall (k : nat) (X : id) (t : ty), fresh_in_ty X t -> ||-[ k][t]<= [TExist X t].
Proof.
(intros k X t Hfresh).
(intros w1).
exists (S w1).
(intros v Hm).
(apply match_ty_exist).
exists (TEV X).
(rewrite subs_fresh_in_ty; assumption).
Qed.
Lemma sem_sub_exist_fresh_l : forall (X : id) (t : ty), fresh_in_ty X t -> ||- [TExist X t]<= [t].
Proof.
(intros X t Hfresh k).
(apply sem_sub_k_exist_fresh_l).
assumption.
Qed.
Lemma sem_sub_k_exist_pair : forall (k : nat) (X : id) (t1 t2 : ty), ||-[ k][TExist X (TPair t1 t2)]<= [TPair (TExist X t1) (TExist X t2)].
Proof.
(intros k X t1 t2 w1).
exists w1.
(intros v Hm).
(destruct w1).
-
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(simpl in Hm).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_pair; apply match_ty_exist; exists tx; assumption).
Qed.
Lemma sem_sub_exist_pair : forall (X : id) (t1 t2 : ty), ||- [TExist X (TPair t1 t2)]<= [TPair (TExist X t1) (TExist X t2)].
Proof.
(intros X t1 t2 k).
(apply sem_sub_k_exist_pair).
Qed.
Lemma sem_sub_k_fresh_var__sem_sub_exist :
  forall (X : id) (t t' : ty) (X' : id), fresh_in_ty X' t' -> ||- [[X := TVar X'] t]<= [t'] -> ||- [TExist X t]<= [t'].
Proof.
(intros X t).
(induction t).
-
(intros t' X' Hfresh Hsem).
(simpl in *).
(apply sem_sub__trans with (TCName c); try assumption).
(apply sem_sub_exist_fresh_l).
(unfold fresh_in_ty, fresh).
(simpl).
(pose proof (IdSetFacts.empty_iff X) as H).
tauto.
-
(intros t' X' Hfresh Hsem).
(simpl in *).
(induction t').
+
(intros k; destruct (match_ty__exists_w_v (TPair ([X := TVar X'] t1) ([X := TVar X'] t2)) k) as [w [v Hm]]; specialize (Hsem k w);
  destruct Hsem as [w2 Hsem]; specialize (Hsem _ Hm); apply match_ty_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_cname__inv in Hsem).
(inversion Hsem).
+
clear IHt'1 IHt'2.
(apply sem_sub_pair__inv in Hsem).
(destruct Hsem as [Hsem1 Hsem2]).
(destruct (fresh_in_ty_pair__inv _ _ _ Hfresh) as [Hfresh1 Hfresh2]).
specialize (IHt1 _ _ Hfresh1 Hsem1).
specialize (IHt2 _ _ Hfresh2 Hsem2).
(apply sem_sub__trans with (TPair (TExist X t1) (TExist X t2))).
(apply sem_sub_exist_pair).
(apply sem_sub_pair; assumption).
+
(intros k w1).
admit.
+
admit.
+
(* Failed. *)
