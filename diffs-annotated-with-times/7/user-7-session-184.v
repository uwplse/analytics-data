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
(rewrite (subst_equation Y tY)).
(rewrite (false_beq_id _ _ HY)).
(rewrite Hmem).
(remember (gen_fresh (IdSet.union (FV tY) (IdSet.add Y (FV t)))) as z).
Abort.
Lemma build_v_full :
  forall (X X' : id) (w : nat) (t v : ty) (tx : ty),
  |-[ w] v <$ [X := tx] t -> exists v' : ty, |-[ w] v' <$ [X := TVar X'] t /\ (forall (w' : nat) (t' : ty), |-[ w'] v' <$ t' -> |-[ w'] v <$ t').
Proof.
(intros X X').
(induction w; induction t; intros v tx Hm).
-
exists v.
split.
assumption.
tauto.
-
(rewrite subst_pair in *).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
specialize (IHt1 _ _ Hm1).
specialize (IHt2 _ _ Hm2).
(destruct IHt1 as [v1' [Hm1' IHt1]]).
(destruct IHt2 as [v2' [Hm2' IHt2]]).
exists (TPair v1' v2').
split.
(apply match_ty_pair; assumption).
(induction w'; induction t'; intros Hm'; try contradiction).
+
(apply match_ty_pair_pair__inv in Hm').
(destruct Hm' as [Hm'1 Hm'2]).
(apply match_ty_pair; auto).
+
(apply match_ty_union__inv in Hm').
(destruct Hm' as [Hm'| Hm']; [ apply match_ty_union_1 | apply match_ty_union_2 ]; tauto).
+
(apply match_ty_pair_pair__inv in Hm').
(destruct Hm' as [Hm'1 Hm'2]).
(apply match_ty_pair; auto).
+
(apply match_ty_union__inv in Hm').
(destruct Hm' as [Hm'| Hm']; [ apply match_ty_union_1 | apply match_ty_union_2 ]; tauto).
+
(apply match_ty_exist__inv in Hm').
(destruct Hm' as [ti Hm']).
exists ti.
auto.
-
admit.
-
(pose proof (subst_exist X tx i t) as Heq).
(destruct Heq as [Z [tz Heq]]).
(rewrite Heq in Hm).
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(destruct (beq_idP X i) as [HXi| HXi]).
+
subst.
(rewrite subst_var_eq in *).
exists (TEV X').
split.
reflexivity.
(induction w'; induction t'; intros Hm'; try contradiction).
*
(apply match_ty_union__inv in Hm').
(destruct Hm' as [Hm'| Hm']; [ apply match_ty_union_1 | apply match_ty_union_2 ]; tauto).
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-09-02 07:51:02.170000.*)

