Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqiqJ1eg"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Export LF.Basics.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqYd0Dwj"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqBud0eu"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Theorem plus_n_O_firsttry : forall n : nat, n = n + 0.
Proof.
(intros n).
(simpl).
Abort.
Theorem plus_n_O_secondtry : forall n : nat, n = n + 0.
Proof.
(intros n).
(destruct n as [| n']).
-
reflexivity.
-
(simpl).
Abort.
Theorem plus_n_O : forall n : nat, n = n + 0.
Proof.
(intros n).
(induction n as [| n' IHn']).
-
reflexivity.
-
(simpl).
(rewrite <- IHn').
reflexivity.
Qed.
Theorem minus_diag : forall n, minus n n = 0.
Proof.
(intros n).
(induction n as [| n' IHn']).
-
(simpl).
reflexivity.
-
(simpl).
(rewrite IHn').
reflexivity.
Qed.
Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
(intros n).
(induction n as [| n' IHn']).
-
reflexivity.
-
(simpl).
(rewrite IHn').
reflexivity.
Qed.
Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + S m.
Proof.
(intros n m).
(induction n as [| n' IHn']).
-
reflexivity.
-
(simpl).
(rewrite IHn').
reflexivity.
Qed.
Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
(intros n m).
(induction n as [| n' IHn']).
-
(rewrite <- plus_n_O).
reflexivity.
-
(simpl).
(rewrite IHn').
(rewrite plus_n_Sm).
reflexivity.
Qed.
Theorem plus_assoc : forall n m p : nat, n + (m + p) = n + m + p.
Proof.
(intros n m p).
(induction n as [| n' IHn']).
-
reflexivity.
-
(simpl).
(rewrite IHn').
reflexivity.
Qed.
Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
Lemma double_plus : forall n, double n = n + n.
Proof.
(intros n).
(induction n as [| n' IHn']).
-
reflexivity.
-
(simpl).
(rewrite IHn').
(rewrite plus_n_Sm).
reflexivity.
Qed.
Theorem evenb_S : forall n : nat, evenb (S n) = negb (evenb n).
Proof.
(intros n).
(induction n as [| n' IHn']).
-
reflexivity.
-
(rewrite IHn').
(rewrite negb_involutive).
reflexivity.
Qed.
Theorem mult_0_plus' : forall n m : nat, (0 + n) * m = n * m.
Proof.
(intros n m).
(assert (H : 0 + n = n)).
{
reflexivity.
}
(rewrite H).
reflexivity.
Qed.
Theorem plus_rearrange_firsttry :
  forall n m p q : nat, n + m + (p + q) = m + n + (p + q).
Proof.
(intros n m p q).
(rewrite plus_comm).
Abort.
Theorem plus_rearrange :
  forall n m p q : nat, n + m + (p + q) = m + n + (p + q).
Proof.
(intros n m p q).
(assert (H : n + m = m + n)).
{
(rewrite plus_comm).
reflexivity.
}
(rewrite H).
reflexivity.
Qed.
Theorem plus_assoc' : forall n m p : nat, n + (m + p) = n + m + p.
Proof.
(intros n m p).
(induction n as [| n' IHn']).
reflexivity.
(simpl).
(rewrite IHn').
reflexivity.
Qed.
Theorem plus_assoc'' : forall n m p : nat, n + (m + p) = n + m + p.
Proof.
(intros n m p).
(induction n as [| n' IHn']).
-
reflexivity.
-
(simpl).
(rewrite IHn').
reflexivity.
Qed.
Theorem plus_swap : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
(intros n m p).
(rewrite plus_assoc).
(assert (n + m = m + n)).
{
(rewrite plus_comm).
reflexivity.
}
(rewrite H).
(rewrite plus_assoc).
reflexivity.
Qed.
(induction n as [| n' IHn']).
-
(simpl).
(rewrite plus_n_O).
