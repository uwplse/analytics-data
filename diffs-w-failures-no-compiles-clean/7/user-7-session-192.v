Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0281a.BaseDefs.
Require Import BetaJulia.Sub0281a.BaseProps.
Require Import BetaJulia.Sub0281a.BaseMatchProps.
Require Import BetaJulia.Sub0281a.BaseSemSubProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Lemma fresh_in_ty_var__neq : forall X Y : id, fresh_in_ty X (TVar Y) -> X <> Y.
Proof.
(intros X Y H).
(unfold fresh_in_ty, fresh in H).
(simpl in H).
(destruct (beq_idP X Y)).
-
Check IdSetFacts.singleton_2.
symmetry in e.
(pose proof (IdSetFacts.singleton_2 e)).
contradiction.
-
assumption.
Lemma match_ty_subst_fresh : forall (X : id) (s : ty) (w : nat) (t v : ty), fresh_in_ty X t -> |-[ w] v <$ t -> |-[ w] v <$ [X := s] t.
Proof.
(intros X s; induction w; induction t; intros v HX Hm;
  try (solve
   [ rewrite subst_cname in *; assumption
   | rewrite subst_pair; destruct (fresh_in_ty_pair__inv _ _ _ HX) as [HX1 HX2]; apply match_ty_pair__inv in Hm;
      destruct Hm as [v1 [v2 [heq [Hm1 Hm2]]]]; subst; apply match_ty_pair; auto
   | rewrite subst_union; destruct (fresh_in_ty_union__inv _ _ _ HX) as [HX1 HX2]; apply match_ty_union__inv in Hm; destruct Hm as [Hm| Hm];
      [ apply match_ty_union_1 | apply match_ty_union_2 ]; auto
   | pose proof (fresh_in_ty_var__neq _ _ HX) as HXi; rewrite subst_var_neq; assumption
   | rewrite subst_ev in *; assumption ])).
-
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(rewrite subst_equation).
(destruct (beq_idP X i) as [HXi| HXi]; try assumption).
(destruct (IdSet.mem i (FV s))).
+
(remember (gen_fresh (IdSet.union (FV s) (IdSet.add X (FV t)))) as z).
(apply match_ty_exist__inv in Hm).
(destruct Hm as [ti Hm]).
(apply match_ty_exist).
exists ti.
Lemma build_v_full :
  forall (X X' : id) (tx : ty) (w : nat) (t v : ty),
  |-[ w] v <$ [X := tx] t ->
  exists v' : ty,
    |-[ w] v' <$ [X := TVar X'] t /\
    (forall (w' : nat) (t' : ty), |-[ w'] v' <$ t' -> (fresh_in_ty X' t' -> |-[ w'] v <$ t') /\ (free_in_ty X' t' -> |-[ w'] v <$ [X' := tx] t')).
Proof.
(intros X X' tx).
(induction w; induction t; intros v Hm).
-
exists v.
split.
assumption.
(induction w'; induction t'; intros Hm'; try (solve [ destruct v; contradiction || tauto ])).
+
(rewrite subst_union).
(apply match_ty_union__inv in Hm'; destruct Hm' as [Hm'| Hm']; [ pose proof IHt'1 as IHt' | pose proof IHt'2 as IHt' ]; specialize (IHt' Hm');
  destruct IHt' as [IHt'a IHt'b]; split; intros HX').
*
(destruct (fresh_in_ty_union__inv _ _ _ HX') as [HX'1 HX'2]).
(apply match_ty_union_1; auto).
*
(destruct (either_free_or_fresh_in_ty X' t'1) as [HXt'1| HXt'1]).
(apply match_ty_union_1; auto).
admit.
*
admit.
*
admit.
+
admit.
+
(apply match_ty_exist__inv in Hm').
(destruct Hm' as [ti Hm']).
specialize (IHw' _ Hm').
(split; intros HX').
{
(apply match_ty_exist).
exists ti.
assumption.
}
{
