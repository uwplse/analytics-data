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
Lemma sem_eq_k_inv_depth__exists_not : forall (k : nat) (t : ty), | t | <= k -> exists t' : ty, ~ ||-[ k][t']= [t].
Proof.
(intros k t).
exists (TRef t).
(intros Hcontra).
(destruct Hcontra as [Hsem1 Hsem2]).
specialize (Hsem1 1).
(destruct Hsem1 as [w2 Hsem1]).
(assert (Hm : |-[ k, 1] TRef t <$ TRef t) by (apply match_ty_value_type__reflexive; constructor)).
specialize (Hsem1 _ Hm).
(destruct k, w2, t; try (solve [ simpl in Hsem1; contradiction ])).
