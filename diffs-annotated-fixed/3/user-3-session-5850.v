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
(induction n as [| n' IHn']).
-
(intros m p).
reflexivity.
-
(intros m p).
(rewrite IHn').
(* Auto-generated comment: Failed. *)

