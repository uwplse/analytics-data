Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Definition sem_sub (t1 t2 : ty) := forall k : nat, ||-[ k][t1]<= [t2].
Notation "'||-' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub t1 t2) (at level 50) : btjm_scope.
Lemma sem_sub__refint_eXrefX : ||- [TRef tint]<= [TExist vX (TRef tX)].
Proof.
(intros k).
(destruct k; intros w1; exists 1; intros v Hm).
-
(apply match_ty_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
(simpl).
exists tint.
constructor.
-
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
(simpl).
exists t'.
(split; intros w; exists w; tauto).
Qed.
Lemma sem_sub__eXrefX_eYrefY : ||- [TExist vX (TRef tX)]<= [TExist vY (TRef tY)].
Proof.
(intros k; intros w1; exists w1; intros v Hm).
(destruct w1).
-
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hmx]).
(apply match_ty_exist).
exists tx.
assumption.
Qed.
Lemma not_sem_sub__refint_refflt : ~ ||- [TRef tint]<= [TRef tflt].
Proof.
(intros Hcontra).
specialize (Hcontra 1 0).
(destruct Hcontra as [w2 Hcontra]).
(assert (Hm : |-[ 1, 0] TRef tint <$ TRef tint) by (apply match_ty_value_type__reflexive; constructor)).
specialize (Hcontra _ Hm).
clear Hm.
(apply match_ty_ref__inv in Hcontra).
(destruct Hcontra as [t' [Heq Hcontra]]).
(inversion Heq; subst).
clear Heq.
(destruct Hcontra as [Hcontra _]).
(assert (Hm : |-[ 0, 0] tint <$ tint) by (apply match_ty_value_type__reflexive; constructor)).
specialize (Hcontra 0).
(destruct Hcontra as [w2' Hcontra]).
specialize (Hcontra _ Hm).
(apply match_ty_cname__inv in Hcontra).
(inversion Hcontra).
Qed.
Lemma sem_sub__eunion__unione : forall (X : id) (t1 t2 : ty), ||- [TExist X (TUnion t1 t2)]<= [TUnion (TExist X t1) (TExist X t2)].
Proof.
(intros X t1 t2 k).
(intros w1).
exists w1.
(intros v Hm).
(destruct w1).
-
(apply match_ty_exist__0_inv in Hm).
contradiction.
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hmx]).
(simpl in Hmx).
(apply match_ty_union__inv in Hmx).
(destruct Hmx as [Hmx| Hmx]; [ apply match_ty_union_1 | apply match_ty_union_2 ]; apply match_ty_exist; exists tx; assumption).
Qed.
Lemma sem_sub__unione__eunion : forall (X : id) (t1 t2 : ty), ||- [TUnion (TExist X t1) (TExist X t2)]<= [TExist X (TUnion t1 t2)].
Proof.
(intros X t1 t2 k).
(intros w1).
exists w1.
(intros v Hm).
(apply match_ty_union__inv in Hm).
(destruct Hm as [Hm| Hm]).
-
(destruct w1).
+
(apply match_ty_exist__0_inv in Hm).
contradiction.
+
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hmx]).
(simpl in Hmx).
(apply match_ty_exist).
exists tx.
(apply match_ty_union_1).
assumption.
-
(destruct w1).
+
(apply match_ty_exist__0_inv in Hm).
contradiction.
+
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hmx]).
(simpl in Hmx).
(apply match_ty_exist).
exists tx.
(apply match_ty_union_2).
assumption.
Qed.
Reserved Notation "'|' t '|'" (at level 20).
Fixpoint inv_depth (t : ty) :=
  match t with
  | TCName _ => 0
  | TPair t1 t2 => Nat.max (| t1 |) (| t2 |)
  | TUnion t1 t2 => Nat.max (| t1 |) (| t2 |)
  | TRef t' => 1 + | t' |
  | TExist _ t' => | t' |
  | TVar _ => 0
  | TEV _ => 0
  end
where "'|' t '|'" := (inv_depth t) : btjt_scope.
Lemma max_inv_depth_le__inv : forall (t1 t2 : ty) (k : nat), Nat.max (| t1 |) (| t2 |) <= k -> | t1 | <= k /\ | t2 | <= k.
Proof.
(intros t1 t2 k Hle).
(split; [ eapply Nat.max_lub_l | eapply Nat.max_lub_r ]; eassumption).
Qed.
Lemma match_ty__inv_depth : forall (w k : nat) (v t : ty), | v | <= k -> |-[ k, w] v <$ t -> | v | <= | t |.
Proof.
(intros w k).
(induction k).
(intros v t Hdep Hm).
(inversion Hdep; subst).
(rewrite H0).
(apply le_0_n).
(intros v t).
generalize dependent v.
(induction t; intros v Hdep Hm).
-
(apply match_ty_cname__inv in Hm; subst).
constructor.
-
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(simpl).
(destruct (max_inv_depth_le__inv _ _ _ Hdep) as [Hdep1 Hdep2]).
(apply Nat.max_le_compat; [ apply IHt1 | apply IHt2 ]; assumption).
-
(apply match_ty_union__inv in Hm).
(destruct Hm as [Hm| Hm]; [ apply Nat.le_trans with (| t1 |) | apply Nat.le_trans with (| t2 |) ]; auto).
(apply Nat.le_max_l).
(apply Nat.le_max_r).
-
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
admit.
-
(destruct w).
(apply match_ty_exist__0_inv in Hm).
contradiction.
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hmx]).
Abort.
Lemma match_ty__ge_w : forall (w : nat) (t : ty) (k : nat) (v : ty), |-[ k, w] v <$ t -> forall w' : nat, w <= w' -> |-[ k, w'] v <$ t.
Proof.
(induction w; induction t; intros k v Hm w' Hle).
-
(apply match_ty_cname__inv in Hm).
subst.
(apply match_ty_cname).
-
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_pair; [ eapply IHt1 | eapply IHt2 ]; eauto).
-
(apply match_ty_union__inv in Hm).
(destruct Hm as [Hm| Hm]; [ apply match_ty_union_1 | apply match_ty_union_2 ]; eauto).
-
(destruct k).
+
(apply match_ty_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
(destruct w'; constructor).
+
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
(destruct w'; assumption).
-
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(apply match_ty_var__inv in Hm; subst).
(apply match_ty_var).
-
(apply match_ty_ev__inv in Hm; subst).
(apply match_ty_ev).
-
(apply match_ty_cname__inv in Hm).
subst.
(apply match_ty_cname).
-
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_pair; [ eapply IHt1 | eapply IHt2 ]; eauto).
-
(apply match_ty_union__inv in Hm).
(destruct Hm as [Hm| Hm]; [ apply match_ty_union_1 | apply match_ty_union_2 ]; eauto).
-
(destruct k).
+
(apply match_ty_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
(destruct w'; constructor).
+
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
(destruct w'; assumption).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hmx]).
(destruct w').
(inversion Hle).
(destruct Hcontra as [v Hcontra]).
(apply match_ty_pair__inv in Hcontra).
(destruct Hcontra as [v1 [v2 [Heq [Hm1 Hm2]]]]).
subst.
(apply IHt1).
(* Failed. *)
