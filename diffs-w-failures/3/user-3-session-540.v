Require Import Arith.
Require Import Bool.
Require Import List.
Require Import EquivDec.
Set Implicit Arguments.
Definition maybe_holds T (p : T -> Prop) : option T -> Prop :=
  fun mt => match mt with
            | Some t => p t
            | None => True
            end.
Theorem holds_in_none_eq :
  forall T (p : T -> Prop) mt, mt = None -> maybe_holds p mt.
Proof.
(intros; subst).
(simpl; auto).
Qed.
Theorem holds_in_some :
  forall T (p : T -> Prop) (v : T), p v -> maybe_holds p (Some v).
Proof.
(simpl; auto).
Qed.
Theorem holds_in_some_eq :
  forall T (p : T -> Prop) (v : T) mt, mt = Some v -> p v -> maybe_holds p mt.
Proof.
(intros; subst).
(simpl; auto).
Qed.
Theorem holds_some_inv_eq :
  forall T (p : T -> Prop) mt v, mt = Some v -> maybe_holds p mt -> p v.
Proof.
(intros; subst).
auto.
Qed.
Theorem pred_weaken :
  forall T (p p' : T -> Prop) mt,
  maybe_holds p mt -> (forall t, p t -> p' t) -> maybe_holds p' mt.
Proof.
(unfold maybe_holds; destruct mt; eauto).
Qed.
Notation "m ?|= F" := (maybe_holds F m) (at level 20, F  at level 50).
Definition missing {T} : T -> Prop := fun _ => False.
Theorem pred_missing :
  forall T (p : T -> Prop) mt, mt ?|= missing -> mt ?|= p.
Proof.
(unfold missing; intros).
(eapply pred_weaken; eauto).
contradiction.
Qed.
