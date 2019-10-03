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
Lemma subst_nested :
  forall (X Y : id) (tX tY : ty), X <> Y -> fresh_in_ty Y tX -> forall t : ty, [X := tX] ([Y := tY] t) = [Y := [X := tX] tY] ([X := tX] t).
Proof.
(intros X Y tX tY Hneq HYfresh t).
(induction t; try reflexivity).
-
(repeat rewrite subst_pair).
(rewrite IHt1, IHt2).
reflexivity.
-
(repeat rewrite subst_union).
(rewrite IHt1, IHt2).
reflexivity.
-
(destruct (beq_idP Y i) as [HY| HY]).
+
subst.
(destruct (beq_idP X i) as [HX| HX]).
*
subst.
contradiction.
*
(rewrite subst_exist_eq).
(rewrite subst_exist_neq; try assumption).
(rewrite subst_exist_eq).
reflexivity.
+
(destruct (beq_idP X i) as [HX| HX]).
*
subst.
(repeat rewrite subst_exist_eq).
(destruct (IdSetProps.In_dec i (FV tY)) as [Hin| Hin]).
{
(pose proof (IdSetFacts.mem_1 Hin) as Hmem).
Check subst_equation.
(rewrite (subst_equation Y tY)).
(rewrite (false_beq_id _ _ HY)).
(rewrite Hmem).
(remember (gen_fresh (IdSet.union (FV tY) (IdSet.add Y (FV t)))) as z).
Abort.
Lemma build_v_full :
  forall (X X' : id) (w : nat) (t v : ty) (tx : ty),
  |-[ w] v <$ [X := tx] t ->
  exists v' : ty, |-[ w] v' <$ [X := TVar X'] t /\ (forall (w' : nat) (t' : ty), |-[ w'] v' <$ t' -> |-[ w'] v <$ [X' := tx] t').
Proof.
(intros X X').
(induction w; induction t; intros v tx Hm).
-
exists v.
split.
assumption.
(apply match_ty_cname__inv in Hm; subst).
(induction w'; induction t'; intros Hm; try assumption || contradiction).
+
(rewrite subst_union).
(apply match_ty_union__inv in Hm).
(destruct Hm as [Hm| Hm]; [ apply match_ty_union_1 | apply match_ty_union_2 ]; tauto).
+
(rewrite subst_union).
(apply match_ty_union__inv in Hm).
(destruct Hm as [Hm| Hm]; [ apply match_ty_union_1 | apply match_ty_union_2 ]; tauto).
+
(destruct (beq_idP X' i) as [Hbeq| Hbeq]).
*
subst.
(rewrite subst_exist_eq).
assumption.
*
(apply match_ty_exist__inv in Hm).
(destruct Hm as [ti Hm]).
(destruct (IdSetProps.In_dec i (FV tx)) as [Hin| Hin]).
{
(pose proof (IdSetFacts.mem_1 Hin) as Hmem).
(rewrite subst_equation).
(pose proof (false_beq_id _ _ Hbeq) as Hneq).
(rewrite Hneq).
(rewrite Hmem).
(remember (gen_fresh (IdSet.union (FV tx) (IdSet.add X' (FV t')))) as Z).
exists ([X' := tx] ti).
specialize (IHw' _ Hm).
(* Auto-generated comment: Failed. *)

