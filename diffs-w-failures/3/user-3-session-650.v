Time From stdpp Require Export base tactics.
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
Time Qed.
Time Lemma fin_to_nat_lt {n} (i : fin n) : fin_to_nat i < n.
Time Proof.
Time (induction i; simpl; lia).
Time Qed.
Time Lemma fin_to_of_nat n m (H : n < m) : fin_to_nat (fin_of_nat H) = n.
Time Proof.
Time revert m H.
Time (induction n; intros [| ?]; simpl; auto; intros; exfalso; lia).
Time Qed.
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
Time
Lemma fin_plus_inv_L {n1} {n2} (P : fin (n1 + n2) \226\134\146 Type)
  (H1 : \226\136\128 i1 : fin n1, P (Fin.L _ i1)) (H2 : \226\136\128 i2, P (Fin.R _ i2))
  (i : fin n1) : fin_plus_inv P H1 H2 (Fin.L n2 i) = H1 i.
Time Proof.
Time revert P H1 H2 i.
Time (induction n1 as [| n1 IH]; intros P H1 H2 i; inv_fin i; simpl; auto).
Time (intros i).
Time (apply (IH (\206\187 i, P (FS i)))).
Time Qed.
Time
Lemma fin_plus_inv_R {n1} {n2} (P : fin (n1 + n2) \226\134\146 Type)
  (H1 : \226\136\128 i1 : fin n1, P (Fin.L _ i1)) (H2 : \226\136\128 i2, P (Fin.R _ i2))
  (i : fin n2) : fin_plus_inv P H1 H2 (Fin.R n1 i) = H2 i.
Time Proof.
Time
(revert P H1 H2 i; induction n1 as [| n1 IH]; intros P H1 H2 i; simpl; auto).
Time (apply (IH (\206\187 i, P (FS i)))).
Time Qed.
