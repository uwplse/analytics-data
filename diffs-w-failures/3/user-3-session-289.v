From Coq Require Import Morphisms.
From Tactical Require Import ProofAutomation.
From Transitions Require Import Relations.
Import RelationNotations.
Generalizable Variables all.
Class NonError {A} {B} {T} (r : relation A B T) :=
    non_erroring : forall x, ~ r x (Err B T).
Instance nonError_bind  `{NonError A B T1 r1}
 `{forall x, @NonError B C T2 (r2 x)}: (NonError (and_then r1 r2)).
Proof.
(unfold NonError, not, and_then in *).
(intuition idtac; propositional; eauto).
Qed.
Instance nonError_or  `{NonError A B T r1} `{!NonError r2}:
 (NonError (r1 + r2)%rel).
Proof.
(unfold NonError, not, rel_or in *; intros).
(intuition idtac; propositional; eauto).
Qed.
Instance nonError_equiv : (Proper (@requiv A B T ==> iff) NonError).
Proof.
firstorder.
Qed.
Instance nonError_star  `{NonError A A T r1}: (NonError (seq_star r1)).
Proof.
(unfold NonError, not in *; intros).
(remember (Err A T)).
(induction H0; try congruence; eauto).
Qed.
Instance nonError_bind_star  `{forall x, @NonError A A T (r1 x)}:
 (forall x, NonError (bind_star r1 x)).
Proof.
(unfold NonError, not in *; intros).
(remember (Err A T)).
(induction H0; try congruence; eauto).
Qed.
Instance nonError_puts  `(f : A -> A): (NonError (puts f)).
Proof.
(unfold NonError, not, puts; intros).
congruence.
Qed.
Instance nonError_reads  `(f : A -> T): (NonError (reads f)).
Proof.
(unfold NonError, not, reads; intros).
congruence.
Qed.
Instance nonError_none : (@NonError A A T none).
Proof.
(unfold NonError, not, none; intros).
auto.
Qed.
Definition rel_apply `(r : relation A B T) : A -> B -> T -> Prop :=
  fun s s' v => r s (Val s' v).
