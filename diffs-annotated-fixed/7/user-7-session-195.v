Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0282a.BaseDefs.
Require Import BetaJulia.Sub0282a.BaseProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma match_ty_cname : forall (c : cname) (w : nat), |-[ w] TCName c <$ TCName c.
Proof.
(intros c w).
(destruct w; reflexivity).
Qed.
Lemma match_ty_pair : forall (v1 v2 t1 t2 : ty) (w : nat), |-[ w] v1 <$ t1 -> |-[ w] v2 <$ t2 -> |-[ w] TPair v1 v2 <$ TPair t1 t2.
Proof.
(intros v1 v2 t1 t2 w Hm1 Hm2).
(destruct w; split; assumption).
Qed.
Lemma match_ty_union_1 : forall (v t1 t2 : ty) (w : nat), |-[ w] v <$ t1 -> |-[ w] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 w Hm).
(destruct w, v; left; assumption).
Qed.
Lemma match_ty_union_2 : forall (v t1 t2 : ty) (w : nat), |-[ w] v <$ t2 -> |-[ w] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 w Hm).
(destruct w, v; right; assumption).
Qed.
Lemma match_ty_exist :
  forall (v : ty) (X : id) (t : ty) (w : nat), (exists tx : ty, wf_ty tx /\ |-[ w] v <$ [BX := tx] t) -> |-[ S w] v <$ TExist X t.
Proof.
(intros v X t w Hex).
(destruct v; assumption).
Qed.
Lemma match_ty_fvar : forall (X : id) (w : nat), |-[ w] TEV X <$ TFVar X.
Proof.
(intros X w).
(destruct w; reflexivity).
Qed.
Lemma match_ty_ev : forall (X : id) (w : nat), |-[ w] TEV X <$ TEV X.
Proof.
(intros X w).
(destruct w; reflexivity).
Qed.
Lemma match_ty_cname__inv : forall (v : ty) (c : cname) (w : nat), |-[ w] v <$ TCName c -> v = TCName c.
Proof.
(intros v c w Hm).
(destruct w, v; simpl in Hm; subst; reflexivity || contradiction).
Qed.
Lemma match_ty_pair__inv :
  forall (v t1 t2 : ty) (w : nat), |-[ w] v <$ TPair t1 t2 -> exists v1 v2 : ty, v = TPair v1 v2 /\ |-[ w] v1 <$ t1 /\ |-[ w] v2 <$ t2.
Proof.
(intros v t1 t2 w Hm).
(destruct w, v; simpl in Hm; contradiction || (exists v1,v2; split; [ reflexivity | tauto ])).
Qed.
Lemma match_ty_pair_pair__inv : forall (v1 v2 t1 t2 : ty) (w : nat), |-[ w] TPair v1 v2 <$ TPair t1 t2 -> |-[ w] v1 <$ t1 /\ |-[ w] v2 <$ t2.
Proof.
(intros v1 v2 t1 t2 w Hm).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1' [v2' [Heq [Hm1 Hm2]]]]).
(inversion Heq; subst).
tauto.
Qed.
Lemma match_ty_union__inv : forall (v t1 t2 : ty) (w : nat), |-[ w] v <$ TUnion t1 t2 -> |-[ w] v <$ t1 \/ |-[ w] v <$ t2.
Proof.
(intros v t1 t2 w Hm).
(destruct w, v; assumption).
Qed.
Lemma match_ty_exist__0_inv : forall (v : ty) (X : id) (t : ty), |-[ 0] v <$ TExist X t -> False.
Proof.
(intros v X t Hm).
(destruct v; simpl in Hm; contradiction).
Qed.
Lemma match_ty_exist__inv :
  forall (v : ty) (X : id) (t : ty) (w : nat), |-[ S w] v <$ TExist X t -> exists tx : ty, wf_ty tx /\ |-[ w] v <$ [BX := tx] t.
Lemma match_ty_fbar__inv : forall (v : ty) (X : id) (w : nat), |-[ w] v <$ TBVar X -> False.
Lemma match_ty_bvar__inv : forall (v : ty) (X : id) (w : nat), |-[ w] v <$ TBVar X -> False.
Proof.
(intros v X w Hm).
(destruct w, v; simpl in Hm; assumption).
Qed.
Lemma match_ty_fvar__inv : forall (v : ty) (X : id) (w : nat), |-[ w] v <$ TFVar X -> v = TEV X.
Proof.
(intros v X w Hm).
(destruct w, v; simpl in Hm; subst; reflexivity || contradiction).
Qed.
Lemma match_ty_ev__inv : forall (v : ty) (X : id) (w : nat), |-[ w] v <$ TEV X -> v = TEV X.
Proof.
(intros v X w Hm).
(destruct w, v; simpl in Hm; subst; reflexivity || contradiction).
Qed.
Theorem match_ty__value_type_l : forall (w : nat) (v t : ty), |-[ w] v <$ t -> value_type v.
Proof.
Qed.
Lemma match_ty_value_type__reflexive : forall v : ty, value_type v -> forall w : nat, |-[ w] v <$ v.
Proof.
(intros v Hv; induction Hv; intros w).
-
(destruct w; reflexivity).
-
(apply match_ty_pair; auto).
-
(destruct w; reflexivity).
Qed.
Lemma match_ty__ge_w : forall (w : nat) (t : ty) (v : ty), |-[ w] v <$ t -> forall w' : nat, w <= w' -> |-[ w'] v <$ t.
Proof.
-
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx [Hwf Hmx]]).
(destruct w').
(inversion Hle).
(apply match_ty_exist).
exists tx.
(apply IHw).
assumption.
(apply le_S_n; assumption).
Qed.
Lemma match_ty__exists_w_v : forall t : ty, exists (w : nat) (v : ty), |-[ w] v <$ t.
Proof.
Lemma match_ty__match_ty_f_subst_int : forall (X : id) (w : nat) (t v : ty), |-[ w] v <$ t -> exists v' : ty, |-[ w] v' <$ [BX := tint] t.
Proof.
(intros X; induction w; induction t; intros v;
  try (solve
   [ intros Hm; exists v; assumption
   | intros Hm; apply match_ty_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst; destruct (IHt1 _ Hm1) as [v1' Hm1'];
      destruct (IHt2 _ Hm2) as [v2' Hm2']; exists (TPair v1' v2'); rewrite subst_pair; apply match_ty_pair; assumption
   | intros Hm; apply match_ty_union__inv in Hm; destruct Hm as [Hm| Hm]; [ destruct (IHt1 _ Hm) as [v' Hm'] | destruct (IHt2 _ Hm) as [v' Hm'] ];
      exists v'; rewrite subst_union; [ apply match_ty_union_1 | apply match_ty_union_2 ]; assumption
   | intros Hm; destruct (beq_idP X i);
      [ subst; rewrite subst_var_eq; exists tint; reflexivity | rewrite subst_var_neq; try assumption; exists v; assumption ] ])).
(* Auto-generated comment: Succeeded. *)

