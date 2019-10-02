Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqK73ZR4"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Export LF.Basics.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqlFYuhd"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqmEY83A"
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
(rewrite plus_n_Sm).
reflexivity.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq47VNZe"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem plus_assoc : forall n m p : nat, n + (m + p) = n + m + p.
Proof.
(intros n).
(intros n m p).
(induction n as [| n' IHn']).
-
reflexivity.
-
(simpl).
(rewrite IHn').
reflexivity.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq9Gqob8"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqJu1qaR"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqVPJVRS"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqqLzzYh"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqOtw1A1"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coquIn0vd"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq2rSjgk"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqjz4HSm"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem mult_comm : forall m n : nat, m * n = n * m.
Proof.
(intros m n).
(induction m as [| m' IHm']).
(simpl).
Check mult_n_O.
(rewrite <- mult_n_O).
reflexivity.
(* Auto-generated comment: Succeeded. *)

