Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqqDFGzi"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Export Contexts.
Require Export HOASCircuits.
Require Export HOASLib.
Require Export DBCircuits.
Require Export Quantum.
Require Export Denotation.
Require Import Setoid.
Lemma denote_box_compat :
  forall (safe : bool) (W1 W2 : WType) (c : Box W1 W2) \207\129 \207\129',
  \207\129 == \207\129' -> denote_box safe c \207\129 == denote_box safe c \207\129'.
Proof.
(intros).
(destruct c).
(unfold denote_box; simpl).
(rewrite add_fresh_split; simpl).
(remember (add_fresh_pat W1 []) as p).
(induction (c p)).
-
matrix_denote.
(match goal with
 | |- ?A => let A' := restore_dims_rec tac A in
            replace
            A
            with
            A'
 end).
