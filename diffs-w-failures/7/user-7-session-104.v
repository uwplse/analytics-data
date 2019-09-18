Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Unset Silent.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Set Silent.
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
Unset Silent.
Notation "'||-' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub t1 t2) (at level 50) : btjm_scope.
Lemma sem_sub__refint_eXrefX : ||- [TRef tint]<= [TExist vX (TRef tX)].
Proof.
Show.
(intros k).
Set Printing Width 148.
(destruct k; intros w1; exists 1; intros v Hm).
-
Set Printing Width 148.
Set Silent.
(apply match_ty_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
(simpl).
exists tint.
constructor.
-
Unset Silent.
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
Show.
Set Printing Width 148.
(simpl).
exists t'.
Show.
Set Printing Width 148.
Set Silent.
(split; intros w; exists w; tauto).
Unset Silent.
Qed.
Lemma sem_sub__eXrefX_eYrefY : ||- [TExist vX (TRef tX)]<= [TExist vY (TRef tY)].
Set Silent.
Set Printing Width 148.
(intros k; intros w1; exists w1; intros v Hm).
Show.
Show.
Set Printing Width 148.
(destruct w1).
Show.
Set Silent.
-
Unset Silent.
(apply match_ty_exist__0_inv in Hm; contradiction).
-
Show.
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hmx]).
(apply match_ty_exist).
exists tx.
assumption.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Reserved Notation "'|' t '|'" (at level 20).
Unset Silent.
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
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Lemma max_inv_depth_le__inv : forall (t1 t2 : ty) (k : nat), Nat.max (| t1 |) (| t2 |) <= k -> | t1 | <= k /\ | t2 | <= k.
Proof.
(intros t1 t2 k Hle).
(split; [ eapply Nat.max_lub_l | eapply Nat.max_lub_r ]; eassumption).
Unset Silent.
Qed.
Set Silent.
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
Unset Silent.
(simpl).
Set Printing Width 148.
Set Printing Width 148.
(destruct (max_inv_depth_le__inv _ _ _ Hdep) as [Hdep1 Hdep2]).
Set Printing Width 148.
(apply Nat.max_le_compat; [ apply IHt1 | apply IHt2 ]; assumption).
-
Set Silent.
Set Printing Width 148.
(destruct Hm as [Hm| Hm]; [ apply Nat.le_trans with (| t1 |) | apply Nat.le_trans with (| t2 |) ]; auto).
Show.
Set Printing Width 148.
Set Printing Width 148.
(apply Nat.le_max_l).
(apply Nat.le_max_r).
-
Show.
(apply match_ty_ref__inv in Hm).
Show.
(destruct Hm as [t' [Heq Href]]; subst).
Show.
admit.
-
Show.
(destruct w).
Show.
(apply match_ty_exist__0_inv in Hm).
Show.
contradiction.
Show.
(apply match_ty_exist in Hm).
