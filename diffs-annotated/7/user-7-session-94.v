Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0260a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Lemma match_ty_exist__inv : forall (v : ty) (X : id) (t : ty) (k : nat), |-[ S k] v <$ TExist X t -> exists tx : ty, |-[ k] v <$ [X := tx] t.
(intros v; induction v; intros X t k Hm; assumption).
Qed.
Theorem match_ty__value_type_l : forall (v t : ty) (k : nat), |-[ k] v <$ t -> value_type v.
Proof.
(intros v t).
generalize dependent v.
(induction t; intros v k Hm).
-
(apply match_ty_cname__inv in Hm; subst).
constructor.
-
(apply match_ty_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(constructor; [ eapply IHt1 | eapply IHt2 ]; eauto).
-
(apply match_ty_union__inv in Hm; destruct Hm as [Hm1| Hm2]; [ eapply IHt1 | eapply IHt2 ]; eauto).
-
(apply match_ty_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
constructor.
-
(destruct k).
contradiction.
(* Failed. *)
