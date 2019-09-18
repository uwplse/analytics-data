Require Import List.
Require Import Proofs.Tactics.
Fixpoint All {T} (l : list T) (P : T -> Prop) : Prop :=
  match l with
  | nil => True
  | cons x l' => P x /\ All l' P
  end.
Lemma All_forall :
  forall T (l : list T) (P : T -> Prop), All l P -> forall x, In x l -> P x.
Proof.
(induction l; intros).
-
solve_by_inversion.
-
(destruct H).
(inv H0).
+
assumption.
+
(apply IHl; assumption).
Qed.
Lemma forall_All :
  forall T (l : list T) (P : T -> Prop), (forall x, In x l -> P x) -> All l P.
Proof.
(induction l; intros; constructor; intuition).
Qed.
