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
Lemma build_v : forall (X X' : id) (tx : ty) (w : nat) (t v : ty), |-[ w] v <$ [X := tx] t -> exists v' : ty, |-[ w] v' <$ [X := TVar X'] t.
Proof.
(intros X X' tx).
(induction w; induction t; intros v Hm; try (solve [ exists v; assumption ])).
-
(rewrite subst_pair in *).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(destruct (IHt1 _ Hm1) as [v1' Hm1']).
(destruct (IHt2 _ Hm2) as [v2' Hm2']).
exists (TPair v1' v2').
(apply match_ty_pair; assumption).
-
(rewrite subst_union in *).
(apply match_ty_union__inv in Hm).
(destruct Hm as [Hm| Hm]; [ destruct (IHt1 _ Hm) as [v' Hm'] | destruct (IHt2 _ Hm) as [v' Hm'] ]; exists v';
  [ apply match_ty_union_1 | apply match_ty_union_2 ]; assumption).
-
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(destruct (beq_idP X i) as [Hbeq| Hbeq]).
+
subst.
exists (TEV X').
(rewrite subst_var_eq).
reflexivity.
+
exists v.
(rewrite (subst_var_neq _ _ _ Hbeq) in Hm).
(rewrite (subst_var_neq _ _ _ Hbeq)).
assumption.
-
(rewrite subst_pair in *).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(destruct (IHt1 _ Hm1) as [v1' Hm1']).
(destruct (IHt2 _ Hm2) as [v2' Hm2']).
exists (TPair v1' v2').
(apply match_ty_pair; assumption).
-
(rewrite subst_union in *).
(apply match_ty_union__inv in Hm).
(destruct Hm as [Hm| Hm]; [ destruct (IHt1 _ Hm) as [v' Hm'] | destruct (IHt2 _ Hm) as [v' Hm'] ]; exists v';
  [ apply match_ty_union_1 | apply match_ty_union_2 ]; assumption).
-
(destruct (beq_idP X i) as [Hbeq| Hbeq]).
+
subst.
(rewrite subst_exist_eq in *).
(exists v; assumption).
+
(rewrite (subst_exist_neq _ _ _ _ Hbeq) in Hm).
(rewrite (subst_exist_neq _ _ _ _ Hbeq)).
(apply match_ty_exist__inv in Hm).
(destruct Hm as [ti Hm]).
(rewrite subst_neq__permute in Hm).
specialize (IHw _ _ Hm).
(destruct IHw as [v' Hm']).
(rewrite subst_neq__permute in Hm').
exists v'.
(apply match_ty_exist).
exists ti.
assumption.
assumption.
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
(rewrite (subst_exist_neq _ _ _ _ Hbeq)).
(apply match_ty_exist__inv in Hm).
(destruct Hm as [ti Hm]).
exists ti.
assumption.
