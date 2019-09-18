Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.
Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.
Eval vm_compute in next_weekday friday.
Eval vm_compute in next_weekday (next_weekday saturday).
Example test_next_weekday : next_weekday (next_weekday saturday) = tuesday.
Proof.
(simpl).
reflexivity.
Qed.
Inductive bool : Type :=
  | true : bool
  | false : bool.
Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
Example test_orb1 : orb true false = true.
Proof.
(simpl).
reflexivity.
Qed.
Example test_orb2 : orb false false = false.
Proof.
(simpl).
reflexivity.
Qed.
Example test_orb3 : orb false true = true.
Proof.
(simpl).
reflexivity.
Qed.
Example test_orb4 : orb true true = true.
Proof.
(simpl).
reflexivity.
Qed.
Infix "&&" := andb.
Infix "||" := orb.
Example test_orb5 : false || false || true = true.
Proof.
(simpl).
reflexivity.
Qed.
Definition nandb (b1 : bool) (b2 : bool) : bool := negb (andb b1 b2).
Example test_nandb1 : nandb true false = true.
Proof.
reflexivity.
Qed.
Example test_nandb2 : nandb false false = true.
Proof.
reflexivity.
Qed.
Example test_nandb3 : nandb false true = true.
Proof.
reflexivity.
Qed.
Example test_nandb4 : nandb true true = false.
Proof.
reflexivity.
Qed.
Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
  andb b1 (andb b2 b3).
Example test_andb31 : andb3 true true true = true.
Proof.
reflexivity.
Qed.
Example test_andb32 : andb3 false true true = false.
Proof.
reflexivity.
Qed.
Example test_andb33 : andb3 true false true = false.
Proof.
reflexivity.
Qed.
Example test_andb34 : andb3 true true false = false.
Proof.
reflexivity.
Qed.
Check true.
Check negb true.
Check negb.
Module NatPlayground.
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
Inductive nat' : Type :=
  | stop : nat'
  | tick : nat' -> nat'.
Definition pred (n : nat) : nat := match n with
                                   | O => O
                                   | S n' => n'
                                   end.
End NatPlayground.
Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
Check S (S (S (S O))).
Eval vm_compute in minustwo 4.
Check S.
Check pred.
Check minustwo.
Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.
Definition oddb (n : nat) : bool := negb (evenb n).
Example test_oddb1 : oddb 1 = true.
Proof.
(simpl).
reflexivity.
Qed.
Example test_oddb2 : oddb 4 = false.
Proof.
(simpl).
reflexivity.
Qed.
Module NatPlayground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
Eval vm_compute in plus 3 2.
Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.
Example test_mult1 : mult 3 3 = 9.
Proof.
(simpl).
reflexivity.
Qed.
Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.
End NatPlayground2.
Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n => S n * factorial n
  end.
Example test_factorial1 : factorial 3 = 6.
Proof.
reflexivity.
Qed.
Example test_factorial2 : factorial 5 = mult 10 12.
Proof.
reflexivity.
Qed.
Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.
Check 0 + 1 + 1.
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.
Example test_leb1 : leb 2 2 = true.
Proof.
(simpl).
reflexivity.
Qed.
Example test_leb2 : leb 2 4 = true.
Proof.
(simpl).
reflexivity.
Qed.
Example test_leb3 : leb 4 2 = false.
Proof.
(simpl).
reflexivity.
Qed.
Definition blt_nat (n m : nat) : bool := andb (leb n m) (negb (beq_nat n m)).
Admitted.
