From Coq Require Import Morphisms.
From Tactical Require Import ProofAutomation.
From Tactical Require Import ProofAutomation.
From Transitions Require Import Relations.
From Transitions Require Import Relations.
Import RelationNotations.
Generalizable Variables all.
Class NonError {A} {B} {T} (r : relation A B T) :=
    non_erroring : forall x, ~ r x (Err B T).
From Transitions Require Import Lens.
Set Implicit Arguments.
Generalizable Variables all.
Arguments Err {B} {T}.
Definition transition A B T := A -> Return B T.
Definition comp {A} {B} {T1} {C} {T2} (t1 : transition A B T1)
  (t2 : T1 -> transition B C T2) : transition A C T2 :=
  fun a => match t1 a with
           | Val b x => t2 x b
           | Err => Err
           end.
Instance nonError_bind  `{NonError A B T1 r1}
 `{forall x, @NonError B C T2 (r2 x)}: (NonError (and_then r1 r2)).
Proof.
(unfold NonError, not, and_then in *).
(intuition idtac; propositional; eauto).
Class Deterministic `(r : relation A B T) (t : transition A B T) :={
 det_iff : forall s s', r s s' <-> s' = t s}.
Arguments det_iff {A} {B} {T} r t {Deterministic} s s'.
Instance puts_Deterministic  `(f : A -> A):
 (Deterministic (puts f) (fun x => Val (f x) tt)).
Proof.
(constructor; unfold puts; intros).
intuition auto.
Qed.
Qed.
Instance nonError_or  `{NonError A B T r1} `{!NonError r2}:
 (NonError (r1 + r2)%rel).
Proof.
(unfold NonError, not, rel_or in *; intros).
(intuition idtac; propositional; eauto).
Instance reads_Deterministic  `(f : A -> T):
 (Deterministic (reads f) (fun x => Val x (f x))).
Proof.
(constructor; unfold reads; intros).
intuition auto.
Qed.
Theorem det_exact `{Deterministic A B T r t} :
  forall s s', r s s' -> s' = t s.
Proof.
(intros).
(pose proof (det_iff r t s s'); firstorder).
Qed.
Instance nonError_equiv : (Proper (@requiv A B T ==> iff) NonError).
Proof.
firstorder.
Qed.
Qed.
Theorem det_complete `{Deterministic A B T r t} :
  forall s s', s' = t s -> r s s'.
Proof.
(intros).
(pose proof (det_iff r t s (t s)); firstorder).
Qed.
Instance nonError_star  `{NonError A A T r1}: (NonError (seq_star r1)).
Proof.
(unfold NonError, not in *; intros).
(remember (Err A T)).
(induction H0; try congruence; eauto).
Qed.
Ltac
 det_exact_any :=
  match goal with
  | Hdet:Deterministic ?r ?t, Hr:?r _ _
    |- _ => apply (@det_exact _ _ _ r t Hdet) in Hr
  | H:_ |- _ => apply det_exact in H
  end.
Instance and_then_Deterministic  `(r1 : relation A B T)
 (f1 : transition A B T) `(r2 : T -> relation B C T')
 (f2 : T -> transition B C T') {Hr1 : Deterministic r1 f1}
 {Hr2 : forall x, Deterministic (r2 x) (f2 x)}:
 (Deterministic (and_then r1 r2) (comp f1 f2)).
Proof.
(constructor; unfold and_then, comp; intros).
(destruct_with_eqn f1 s; simpl; eauto).
-
(destruct s'; simpl; split;
  repeat
   match goal with
   | _ => det_exact_any
   | _ => progress descend
   | _ => progress propositional
   | _ => progress intuition eauto using det_complete
   end; try congruence).
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
(apply det_complete; eauto).
(right; descend; intuition eauto using det_complete).
(apply det_complete; eauto).
-
(destruct s';
  repeat
   match goal with
   | H:_ |- _ => apply det_exact in H
   | |- exists _, _ => descend
   | _ => progress propositional
   | _ => progress intuition eauto using det_complete
   end; try congruence).
(left; apply det_complete; congruence).
Grab Existential Variables.
congruence.
congruence.
Qed.
Instance error_Deterministic : (Deterministic (@error A B T) (fun _ => Err)).
Proof.
(intros).
(constructor; intuition).
Qed.
Instance zoom_Deterministic  A C (lens : Lens A C) 
 (lens_wf : LensWf lens) T (r : relation C C T) f 
 {Hr : Deterministic r f}:
 (Deterministic (zoom proj inj r)
    (fun x : A =>
     match f (proj x) with
     | Val x' t => Val (inj x' x) t
     | Err => Err
     end)).
Proof.
(constructor; unfold zoom; intuition idtac).
-
(destruct s'; intuition auto;
  repeat det_exact_any || simpl_match || congruence).
-
(destruct_with_eqn f (proj s);
  repeat det_exact_any || simpl_match || congruence).
intuition.
(apply det_complete).
(rewrite Heqr0).
(rewrite proj_inj; congruence).
(rewrite proj_inj; congruence).
(apply det_complete; auto).
Qed.
