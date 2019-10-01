Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqs12aPa"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Export LF.Induction.
Module NatList.
Inductive natprod : Type :=
    pair : nat -> nat -> natprod.
Check pair 3 5.
Definition fst (p : natprod) : nat := match p with
                                      | pair x y => x
                                      end.
Definition snd (p : natprod) : nat := match p with
                                      | pair x y => y
                                      end.
Eval vm_compute in fst (pair 3 5).
Notation "( x , y )" := (pair x y).
Eval vm_compute in fst (3, 5).
Definition fst' (p : natprod) : nat := match p with
                                       | (x, y) => x
                                       end.
Definition snd' (p : natprod) : nat := match p with
                                       | (x, y) => y
                                       end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.
Theorem surjective_pairing' :
  forall n m : nat, (n, m) = (fst (n, m), snd (n, m)).
Proof.
reflexivity.
Qed.
Theorem surjective_pairing_stuck : forall p : natprod, p = (fst p, snd p).
Proof.
(simpl).
Abort.
Theorem surjective_pairing : forall p : natprod, p = (fst p, snd p).
Proof.
(intros p).
(destruct p as [n m]).
(simpl).
reflexivity.
Qed.
Theorem snd_fst_is_swap : forall p : natprod, (snd p, fst p) = swap_pair p.
Proof.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqjo1a2t"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqoemFZB"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
(destruct p as [n m]).
(simpl).
reflexivity.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqoAeqEL"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem fst_swap_is_snd : forall p : natprod, fst (swap_pair p) = snd p.
Proof.
(destruct p as [n m]).
(simpl).
reflexivity.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqQZNFc3"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqglLWz9"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq19vlI9"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition mylist := cons 1 (cons 2 (cons 3 nil)).
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0uIgCx"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqZ5O4Re"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition mylist1 := 1 :: 2 :: 3 :: nil.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqSJdzVM"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq5Zg3PD"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1; 2; 3].
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqBGERh0"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqBGkalG"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: repeat n count'
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqbnY9WH"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqnFbxs3"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqS3p7nv"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqtJjrud"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: app t l2
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqXJy0Pa"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqmmf28h"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Notation "x ++ y" := (app x y) (right associativity, at level 60).
Example test_app1 : [1; 2; 3] ++ [4; 5] = [1; 2; 3; 4; 5].
Proof.
reflexivity.
Qed.
Example test_app2 : nil ++ [4; 5] = [4; 5].
Proof.
reflexivity.
Qed.
Example test_app3 : [1; 2; 3] ++ nil = [1; 2; 3].
Proof.
reflexivity.
Qed.
Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqSi5oIm"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqjbve1B"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqkEwuOj"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | [ ] => [ ]
  | h :: t => if beq_nat h 0 then nonzeros t else h :: nonzeros t
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqVB4pW3"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqiALUuH"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Example test_nonzeros : nonzeros [0; 1; 0; 2; 3; 0; 0] = [1; 2; 3].
Proof.
reflexivity.
Qed.
Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | [ ] => [ ]
  | h :: t => if oddb h then h :: oddmembers t else oddmembers t
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq2blqVv"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqaOYrJb"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Example test_oddmembers : oddmembers [0; 1; 0; 2; 3; 0; 0] = [1; 3].
Proof.
reflexivity.
Qed.
Qed.
Definition member (v : nat) (s : bag) : bool := blt_nat 0 (count v s).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqgtU38m"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqUzqehC"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Example test_member1 : member 1 [1; 4; 1] = true.
Proof.
reflexivity.
Qed.
Example test_member2 : member 2 [1; 4; 1] = false.
Proof.
reflexivity.
Qed.
Fixpoint remove_one (v : nat) (s : bag) : bag.
Admitted.
Example test_remove_one1 : count 5 (remove_one 5 [2; 1; 5; 4; 1]) = 0.
Admitted.
Example test_remove_one2 : count 5 (remove_one 5 [2; 1; 4; 1]) = 0.
Admitted.
Example test_remove_one3 : count 4 (remove_one 5 [2; 1; 4; 5; 1; 4]) = 2.
Admitted.
Example test_remove_one4 : count 5 (remove_one 5 [2; 1; 5; 4; 5; 1; 4]) = 1.
Admitted.
Fixpoint remove_all (v : nat) (s : bag) : bag.
Admitted.
Example test_remove_all1 : count 5 (remove_all 5 [2; 1; 5; 4; 1]) = 0.
Admitted.
Example test_remove_all2 : count 5 (remove_all 5 [2; 1; 4; 1]) = 0.
Admitted.
Example test_remove_all3 : count 4 (remove_all 5 [2; 1; 4; 5; 1; 4]) = 2.
Admitted.
Example test_remove_all4 :
  count 5 (remove_all 5 [2; 1; 5; 4; 5; 1; 4; 5; 1; 4]) = 0.
Admitted.
Fixpoint subset (s1 : bag) (s2 : bag) : bool.
Admitted.
Example test_subset1 : subset [1; 2] [2; 1; 4; 1] = true.
Admitted.
Example test_subset2 : subset [1; 2; 2] [2; 1; 4; 1] = false.
Admitted.
Theorem nil_app : forall l : natlist, [ ] ++ l = l.
Proof.
reflexivity.
Qed.
Theorem tl_length_pred : forall l : natlist, pred (length l) = length (tl l).
Proof.
(intros l).
(destruct l as [| n l']).
-
reflexivity.
-
reflexivity.
(rewrite IHl; auto).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq2rsX3F"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem app_assoc4 :
  forall l1 l2 l3 l4 : natlist,
  l1 ++ l2 ++ l3 ++ l4 = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
(rewrite app_assoc).
(* Failed. *)
