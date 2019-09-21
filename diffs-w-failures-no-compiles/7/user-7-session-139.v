Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
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
Set Printing Width 148.
Set Silent.
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
Set Printing Width 148.
Set Silent.
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
Unset Silent.
Proof.
(intros X t Hfresh k).
Set Printing Width 148.
Set Silent.
(apply sem_sub_k_exist_fresh_l).
Unset Silent.
assumption.
Qed.
Set Silent.
Lemma sem_sub_k_fresh_var__sem_sub_exist :
  forall (X : id) (t t' : ty) (X' : id), fresh_in_ty X' t' -> ||- [[X := TVar X'] t]<= [t'] -> ||- [TExist X t]<= [t'].
Proof.
(intros X t).
(induction t).
-
(intros t' X' Hfresh Hsem).
(simpl in *).
(apply sem_sub__trans with (TCName c); try assumption).
Unset Silent.
(apply sem_sub_exist_fresh_l).
(unfold fresh_in_ty, fresh).
(simpl).
Search -IdSet.empty.
Check IdSetFacts.empty_iff.
(pose proof (IdSetFacts.empty_iff X) as H).
tauto.
-
Set Silent.
(intros t' X' Hfresh Hsem).
Unset Silent.
(simpl in *).
Set Printing Width 148.
Set Printing Width 148.
(induction t'; intros k; destruct (match_ty__exists_w_v (TPair ([X := TVar X'] t1) ([X := TVar X'] t2)) k) as [w [v Hm]]; specialize (Hsem k w);
  destruct Hsem as [w2 Hsem]; specialize (Hsem _ Hm); apply match_ty_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
Set Silent.
+
Unset Silent.
(apply match_ty_cname__inv in Hsem).
(inversion Hsem).
+
