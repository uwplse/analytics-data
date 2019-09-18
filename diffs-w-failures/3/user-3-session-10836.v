Time From stdpp Require Export base tactics.
Time From stdpp Require Export tactics.
Time Set Default Proof Using "Type".
Time Notation fin := Fin.t.
Time Notation FS := Fin.FS.
Time Delimit Scope fin_scope with fin.
Time Arguments Fin.FS _ _%fin : assert.
Time Notation "0" := Fin.F1 : fin_scope.
Time Notation "1" := (FS 0) : fin_scope.
Time Notation "2" := (FS 1) : fin_scope.
Time Notation "3" := (FS 2) : fin_scope.
Time Notation "4" := (FS 3) : fin_scope.
Time Notation "5" := (FS 4) : fin_scope.
Time Notation "6" := (FS 5) : fin_scope.
Time Notation "7" := (FS 6) : fin_scope.
Time Notation "8" := (FS 7) : fin_scope.
Time Notation "9" := (FS 8) : fin_scope.
Time Notation "10" := (FS 9) : fin_scope.
Time
Fixpoint fin_to_nat {n} (i : fin n) : nat :=
  match i with
  | 0%fin => 0
  | FS i => S (fin_to_nat i)
  end.
Time Coercion fin_to_nat : fin >-> nat.
Time Notation fin_of_nat := Fin.of_nat_lt.
Time Notation fin_rect2 := Fin.rect2.
Time Instance fin_dec  {n}: (EqDecision (fin n)).
Time Proof.
Time
(refine
  (fin_rect2 (\206\187 n (i j : fin n), {i = j} + {i \226\137\160 j}) 
     (\206\187 _, left _) (\206\187 _ _, right _) (\206\187 _ _, right _) 
     (\206\187 _ _ _ H, cast_if H)); abstract (f_equal; by auto using Fin.FS_inj)).
Time Defined.
Time Notation fin_0_inv := Fin.case0.
Time
Definition fin_S_inv {n} (P : fin (S n) \226\134\146 Type) (H0 : P 0%fin)
  (HS : \226\136\128 i, P (FS i)) (i : fin (S n)) : P i.
Time Proof.
Time revert P H0 HS.
Time
refine match i with
       | 0%fin => \206\187 _ H0 _, H0
       | FS i => \206\187 _ _ HS, HS i
       end.
Time Defined.
Time
Ltac
 inv_fin i :=
  let T := type of i in
  match eval hnf in T with
  | fin ?n =>
      match eval hnf in n with
      | 0 =>
          revert dependent i;
           match goal with
           | |- \226\136\128 i, @?P i => apply (fin_0_inv P)
           end
      | S ?n =>
          revert dependent i;
           match goal with
           | |- \226\136\128 i, @?P i => apply (fin_S_inv P)
           end
      end
  end.
Time Instance FS_inj : (Inj (=) (=) (@FS n)).
Time Proof.
Time (intros n i j).
Time (apply Fin.FS_inj).
Time Qed.
Time Instance fin_to_nat_inj : (Inj (=) (=) (@fin_to_nat n)).
Time Proof.
Time (intros n i).
Time (induction i; intros j; inv_fin j; intros; f_equal /=; auto with lia).
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
Time Qed.
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
Time Lemma fin_to_nat_lt {n} (i : fin n) : fin_to_nat i < n.
Time Proof.
Time (induction i; simpl; lia).
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
Time Lemma fin_to_of_nat n m (H : n < m) : fin_to_nat (fin_of_nat H) = n.
Time Proof.
Time revert m H.
Time (induction n; intros [| ?]; simpl; auto; intros; exfalso; lia).
Time Qed.
Time #[global]Instance: (Transitive R \226\134\146 StrictOrder (strict R)).
Time Proof.
Time (split; try apply _).
Time eauto using strict_transitive_r, strict_include.
Time Qed.
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
Time
Lemma fin_of_to_nat {n} (i : fin n) H : @fin_of_nat (fin_to_nat i) n H = i.
Time Proof.
Time (apply (inj fin_to_nat), fin_to_of_nat).
Time Qed.
Time
Fixpoint fin_plus_inv {n1 n2} :
\226\136\128 (P : fin (n1 + n2) \226\134\146 Type) (H1 : \226\136\128 i1 : fin n1, P (Fin.L n2 i1)) 
  (H2 : \226\136\128 i2, P (Fin.R n1 i2)) (i : fin (n1 + n2)), 
  P i :=
  match n1 with
  | 0 => \206\187 P H1 H2 i, H2 i
  | S n =>
      \206\187 P H1 H2, fin_S_inv P (H1 0%fin) (fin_plus_inv _ (\206\187 i, H1 (FS i)) H2)
  end.
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
Time
Lemma fin_plus_inv_L {n1} {n2} (P : fin (n1 + n2) \226\134\146 Type)
  (H1 : \226\136\128 i1 : fin n1, P (Fin.L _ i1)) (H2 : \226\136\128 i2, P (Fin.R _ i2))
  (i : fin n1) : fin_plus_inv P H1 H2 (Fin.L n2 i) = H1 i.
Time Proof.
Time revert P H1 H2 i.
Time (induction n1 as [| n1 IH]; intros P H1 H2 i; inv_fin i; simpl; auto).
Time Defined.
Time (intros i).
Time Lemma total_not `{!Total R} X Y : X \226\138\136 Y \226\134\146 Y \226\138\134 X.
Time Proof.
Time (intros).
Time (destruct (total R X Y); tauto).
Time Qed.
Time Lemma total_not_strict `{!Total R} X Y : X \226\138\136 Y \226\134\146 Y \226\138\130 X.
Time Proof.
Time (red; auto using total_not).
Time (apply (IH (\206\187 i, P (FS i)))).
Time Qed.
Time
Lemma fin_plus_inv_R {n1} {n2} (P : fin (n1 + n2) \226\134\146 Type)
  (H1 : \226\136\128 i1 : fin n1, P (Fin.L _ i1)) (H2 : \226\136\128 i2, P (Fin.R _ i2))
  (i : fin n2) : fin_plus_inv P H1 H2 (Fin.R n1 i) = H2 i.
Time Proof.
Time
(revert P H1 H2 i; induction n1 as [| n1 IH]; intros P H1 H2 i; simpl; auto).
Time Qed.
Time #[global]
Instance trichotomy_total  `{!Trichotomy (strict R)} 
 `{!Reflexive R}: (Total R).
Time Proof.
Time (intros X Y).
Time
(destruct (trichotomy (strict R) X Y) as [[? ?]| [<-| [? ?]]]; intuition).
Time (apply (IH (\206\187 i, P (FS i)))).
Time Qed.
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
