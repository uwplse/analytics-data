Time From stdpp Require Export tactics.
Time Set Default Proof Using "Type".
Time Section orders.
Time Context {A} {R : relation A}.
Time Implicit Types X Y : A.
Time Infix "\226\138\134" := R.
Time Notation "X \226\138\136 Y" := (\194\172 X \226\138\134 Y).
Time Infix "\226\138\130" := (strict R).
Time Lemma reflexive_eq `{!Reflexive R} X Y : X = Y \226\134\146 X \226\138\134 Y.
Time Proof.
Time by intros <-.
Time Qed.
Time Lemma anti_symm_iff `{!PartialOrder R} X Y : X = Y \226\134\148 R X Y \226\136\167 R Y X.
Time Proof.
Time split.
Time by intros ->.
Time by intros [? ?]; apply (anti_symm _).
Time Qed.
Time Lemma strict_spec X Y : X \226\138\130 Y \226\134\148 X \226\138\134 Y \226\136\167 Y \226\138\136 X.
Time Proof.
Time done.
Time Qed.
Time Lemma strict_include X Y : X \226\138\130 Y \226\134\146 X \226\138\134 Y.
Time Proof.
Time by intros [? _].
Time Qed.
Time Lemma strict_ne X Y : X \226\138\130 Y \226\134\146 X \226\137\160 Y.
Time Proof.
Time by intros [? ?] <-.
Time Qed.
Time Lemma strict_ne_sym X Y : X \226\138\130 Y \226\134\146 Y \226\137\160 X.
Time Proof.
Time by intros [? ?] <-.
Time Qed.
Time
Lemma strict_transitive_l `{!Transitive R} X Y Z : X \226\138\130 Y \226\134\146 Y \226\138\134 Z \226\134\146 X \226\138\130 Z.
Time Proof.
Time (intros [? HXY] ?).
Time (split; [ by trans Y |  ]).
Time (contradict HXY).
Time by trans Z.
Time Qed.
Time
Lemma strict_transitive_r `{!Transitive R} X Y Z : X \226\138\134 Y \226\134\146 Y \226\138\130 Z \226\134\146 X \226\138\130 Z.
Time Proof.
Time (intros ? [? HYZ]).
Time (split; [ by trans Y |  ]).
Time (contradict HYZ).
Time by trans X.
Time Qed.
Time #[global]Instance: (Irreflexive (strict R)).
Time Proof.
Time firstorder.
Time Qed.
Time #[global]Instance: (Transitive R \226\134\146 StrictOrder (strict R)).
Time Proof.
Time (split; try apply _).
Time eauto using strict_transitive_r, strict_include.
Time Qed.
Time #[global]
Instance preorder_subset_dec_slow  `{!RelDecision R}:
 (RelDecision (strict R)) |100.
Time Proof.
Time solve_decision.
Time Defined.
Time Lemma strict_spec_alt `{!AntiSymm (=) R} X Y : X \226\138\130 Y \226\134\148 X \226\138\134 Y \226\136\167 X \226\137\160 Y.
Time Proof.
Time split.
Time -
Time (intros [? HYX]).
Time split.
Time done.
Time by intros <-.
Time -
Time (intros [? HXY]).
Time split.
Time done.
Time by contradict HXY; apply (anti_symm R).
Time Qed.
Time Lemma po_eq_dec `{!PartialOrder R} `{!RelDecision R} : EqDecision A.
Time Proof.
Time
(refine (\206\187 X Y, cast_if_and (decide (X \226\138\134 Y)) (decide (Y \226\138\134 X)));
  abstract (rewrite anti_symm_iff; tauto)).
Time Defined.
Time Lemma total_not `{!Total R} X Y : X \226\138\136 Y \226\134\146 Y \226\138\134 X.
Time Proof.
Time (intros).
Time (destruct (total R X Y); tauto).
Time Qed.
Time Lemma total_not_strict `{!Total R} X Y : X \226\138\136 Y \226\134\146 Y \226\138\130 X.
Time Proof.
Time (red; auto using total_not).
Time Qed.
Time #[global]
Instance trichotomy_total  `{!Trichotomy (strict R)} 
 `{!Reflexive R}: (Total R).
Time Proof.
Time (intros X Y).
Time
(destruct (trichotomy (strict R) X Y) as [[? ?]| [<-| [? ?]]]; intuition).
Time Qed.
Time End orders.
Time Section strict_orders.
Time Context {A} {R : relation A}.
Time Implicit Types X Y : A.
Time Infix "\226\138\130" := R.
Time Lemma irreflexive_eq `{!Irreflexive R} X Y : X = Y \226\134\146 \194\172 X \226\138\130 Y.
Time Proof.
Time (intros ->).
Time (apply (irreflexivity R)).
Time Qed.
Time Lemma strict_anti_symm `{!StrictOrder R} X Y : X \226\138\130 Y \226\134\146 Y \226\138\130 X \226\134\146 False.
Time Proof.
Time (intros).
Time (apply (irreflexivity R X)).
Time by trans Y.
Time Qed.
Time #[global]
Instance trichotomyT_dec  `{!TrichotomyT R} `{!StrictOrder R}:
 (RelDecision R) :=
 (\206\187 X Y,
    match trichotomyT R X Y with
    | inleft (left H) => left H
    | inleft (right H) => right (irreflexive_eq _ _ H)
    | inright H => right (strict_anti_symm _ _ H)
    end).
Time #[global]
Instance trichotomyT_trichotomy  `{!TrichotomyT R}: (Trichotomy R).
Time Proof.
Time (intros X Y).
Time (destruct (trichotomyT R X Y) as [[| ]| ]; tauto).
Time Qed.
Time End strict_orders.
Time
Ltac
 simplify_order :=
  repeat
   match goal with
   | _ =>
       progress simplify_eq /=
   | H:?R ?x ?x |- _ => by destruct (irreflexivity _ _ H)
   | H1:?R ?x ?y
     |- _ =>
         match goal with
         | H2:R y x
           |- _ => assert (x = y) by by apply (anti_symm R); clear H1 H2
         | H2:R y ?z
           |- _ => unless R x z by done; assert (R x z) by by trans y
         end
   end.
