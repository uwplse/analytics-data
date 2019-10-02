Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqrgOFGf"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0fX9cg"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq9lMGz6"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqffP7li"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqNwhrpP"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Eval vm_compute in next_weekday friday.
Eval vm_compute in next_weekday (next_weekday saturday).
Example test_next_weekday : next_weekday (next_weekday saturday) = tuesday.
Proof.
(simpl).
reflexivity.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq9LPHYG"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Inductive bool : Type :=
  | true : bool
  | false : bool.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqCm0Ylq"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqD0BjMA"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqhW4PYd"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq77SK15"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqHM9ZQc"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqmC9vCu"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqn5nig8"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqCJcKe4"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Definition nandb (b1 : bool) (b2 : bool) : bool := negb (andb b1 b2).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqEGZdnC"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqOPvcFz"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Example test_nandb1 : nandb true false = true.
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
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqnizFJz"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq45TQne"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqPuN122"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n => S n * factorial n
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqgAprxE"
Print Ltac Signatures.
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n => S n * factorial n
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqhcOYTV"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqnF37o3"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqPsRcAC"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqNrIR18"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqPaKGLc"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq8K97sB"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqTZCIKX"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqXV1VEx"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Example test_blt_nat1 : blt_nat 2 2 = false.
Proof.
reflexivity.
Qed.
Example test_blt_nat2 : blt_nat 2 4 = true.
Proof.
reflexivity.
Qed.
Example test_blt_nat3 : blt_nat 4 2 = false.
Proof.
reflexivity.
Qed.
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
(intros n).
(simpl).
reflexivity.
Qed.
Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
(intros n).
reflexivity.
Qed.
Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
(intros n).
reflexivity.
Qed.
Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
(intros n).
reflexivity.
Qed.
Theorem plus_n_O : forall n, n = n + 0.
Proof.
(intros n).
(simpl).
Abort.
Theorem plus_id_example : forall n m : nat, n = m -> n + n = m + m.
Proof.
(intros n m).
(intros H).
(rewrite H).
reflexivity.
Qed.
Theorem plus_id_exercise :
  forall n m o : nat, n = m -> m = o -> n + m = m + o.
Proof.
(intros n m o).
(intros Hnm Hmo).
(rewrite Hnm).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqjUqYct"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem mult_0_plus : forall n m : nat, (0 + n) * m = n * m.
Proof.
(intros n m).
(rewrite plus_O_n).
reflexivity.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqHphtrC"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem mult_S_1 : forall n m : nat, m = S n -> m * (1 + n) = m * m.
Proof.
(intros n m H).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqWodqr2"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem plus_1_neq_0_firsttry : forall n : nat, beq_nat (n + 1) 0 = false.
Proof.
(intros n).
(simpl).
Abort.
Theorem plus_1_neq_0 : forall n : nat, beq_nat (n + 1) 0 = false.
Proof.
(intros n).
(destruct n as [| n']).
-
reflexivity.
-
reflexivity.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqAYo8fW"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem negb_involutive : forall b : bool, negb (negb b) = b.
Proof.
(intros b).
(destruct b).
-
reflexivity.
-
reflexivity.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqyDcTts"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
(intros b c).
(destruct b).
-
(destruct c).
+
reflexivity.
+
reflexivity.
-
(destruct c).
+
reflexivity.
+
reflexivity.
Qed.
Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
(intros b c).
(destruct b).
{
(destruct c).
{
reflexivity.
}
{
reflexivity.
}
}
{
(destruct c).
{
reflexivity.
}
{
reflexivity.
}
}
Qed.
Theorem andb3_exchange : forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
(intros b c d).
(destruct b).
-
(destruct c).
{
(destruct d).
-
reflexivity.
-
reflexivity.
}
{
(destruct d).
-
reflexivity.
-
reflexivity.
}
-
(destruct c).
{
(destruct d).
-
reflexivity.
-
reflexivity.
}
{
(destruct d).
-
reflexivity.
-
reflexivity.
}
Qed.
Theorem plus_1_neq_0' : forall n : nat, beq_nat (n + 1) 0 = false.
Proof.
(intros [| n]).
-
reflexivity.
-
reflexivity.
Qed.
Theorem andb_commutative'' : forall b c, andb b c = andb c b.
Proof.
(intros [] []).
-
reflexivity.
-
reflexivity.
-
reflexivity.
-
reflexivity.
Qed.
Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
Proof.
(intros b [] H).
-
reflexivity.
-
(destruct H).
(destruct b).
reflexivity.
(* Auto-generated comment: Succeeded. *)

