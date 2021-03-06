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
Lemma match_ty_ev__match_ty_any :
  forall (k w : nat) (X : id) (t : ty), fresh_in_ty X t -> |-[ k, w] TEV X <$ t -> forall v : ty, value_type v -> |-[ k, w] v <$ t.
Proof.
(intros k w).
generalize dependent k.
(induction w).
admit.
(intros k X t HX Hm v Hv).
(induction t).
admit.
admit.
admit.
admit.
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(destruct (beq_idP X i)).
+
subst.
(apply match_ty_exist).
exists tx.
(apply IHw with i; try assumption).
Abort.
Lemma sem_sub_fresh_var__sem_sub_any :
  forall (X : id) (t t' : ty) (X' : id),
  IdSet.In X (FV t) -> fresh_in_ty X' t' -> ||- [[X := TVar X'] t]<= [t'] -> forall tx : ty, ||- [[X := tx] t]<= [t'].
Proof.
(intros X t).
(intros t' X' HX HX' Hsem tx).
(intros k w1).
specialize (Hsem k w1).
(destruct Hsem as [w2 Hsem]).
exists w2.
(intros v Hm).
Abort.
Lemma sem_sub_fresh_var__sem_sub_exist' :
  forall (X : id) (t t' : ty) (X' : id),
  IdSet.In X (FV t) -> fresh_in_ty X' t' -> ||- [[X := TVar X'] t]<= [t'] -> forall tx : ty, ||- [[X := tx] t]<= [t'].
Proof.
(intros X t t' X' HX HX' Hsem tx).
(intros k w1).
specialize (Hsem k w1).
(destruct Hsem as [w2 Hsem]).
exists w2.
(intros v Hm).
(induction w1).
Abort.
Lemma xxx :
  forall (X : id) (w1 : nat) (t : ty) (k w2 : nat) (t' : ty) (X' : id),
  IdSet.In X (FV t) ->
  fresh_in_ty X' t' ->
  (forall v, |-[ k, w1] v <$ [X := TVar X'] t -> |-[ k, w2] v <$ t') -> forall tx : ty, forall v, |-[ k, w1] v <$ [X := tx] t -> |-[ k, w2] v <$ t'.
Proof.
(intros X w1).
(induction w1).
admit.
(intros t).
(intros k w2 t' X' HX HX' Hsem).
(intros tx v Hm).
Abort.
Lemma sem_sub_fresh_var__sem_sub_exist :
  forall (X : id) (t t' : ty) (X' : id), IdSet.In X (FV t) -> fresh_in_ty X' t' -> ||- [[X := TVar X'] t]<= [t'] -> ||- [TExist X t]<= [t'].
Proof.
(intros X t).
(induction t).
-
(intros t' X' Hfresh Hsem).
(simpl in *).
(apply sem_sub__trans; try assumption).
(apply sem_sub_exist_fresh_l).
(unfold fresh_in_ty, fresh).
(simpl).
(pose proof (IdSetFacts.empty_iff X) as H).
tauto.
-
(intros t' X' Hfresh Hfresh' Hsem).
(simpl in *).
(induction t').
+
(intros k).
(destruct (match_ty__exists_w_v (TPair ([X := TVar X'] t1) ([X := TVar X'] t2)) k) as [w [v Hm]]).
(specialize (Hsem k w); destruct Hsem as [w2 Hsem]; specialize (Hsem _ Hm); apply match_ty_pair__inv in Hm;
  destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_cname__inv in Hsem).
(inversion Hsem).
+
clear IHt'1 IHt'2.
(apply sem_sub_pair__inv in Hsem).
(destruct Hsem as [Hsem1 Hsem2]).
(destruct (fresh_in_ty_pair__inv _ _ _ Hfresh') as [Hfresh1 Hfresh2]).
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-08-29 07:45:43.310000.*)

