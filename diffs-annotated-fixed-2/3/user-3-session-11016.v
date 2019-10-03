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
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqbK4Fkh"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Example test_hd1 : hd 0 [1; 2; 3] = 1.
Proof.
reflexivity.
Qed.
Example test_hd2 : hd 0 [ ] = 0.
Proof.
reflexivity.
Qed.
Example test_tl : tl [1; 2; 3] = [2; 3].
Proof.
reflexivity.
Qed.
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
Definition countoddmembers (l : natlist) : nat := length (oddmembers l).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq04MTFC"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqSz8SI9"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Example test_countoddmembers1 : countoddmembers [1; 0; 3; 1; 4; 5] = 4.
Proof.
reflexivity.
Qed.
Example test_countoddmembers2 : countoddmembers [0; 2; 4] = 0.
Proof.
reflexivity.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq5V3PVz"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Example test_countoddmembers3 : countoddmembers nil = 0.
Proof.
reflexivity.
Qed.
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | l1, [ ] => l1
  | [ ], l2 => l2
  | x :: xs, y :: ys => x :: y :: alternate xs ys
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq8zaKPL"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqYTDp6B"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Example test_alternate1 : alternate [1; 2; 3] [4; 5; 6] = [1; 4; 2; 5; 3; 6].
Proof.
reflexivity.
Qed.
Example test_alternate2 : alternate [1] [4; 5; 6] = [1; 4; 5; 6].
Proof.
reflexivity.
Qed.
Example test_alternate3 : alternate [1; 2; 3] [4] = [1; 4; 2; 3].
Proof.
reflexivity.
Qed.
Example test_alternate4 : alternate [ ] [20; 30] = [20; 30].
Proof.
reflexivity.
Qed.
Definition bag := natlist.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqae6duK"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqQOVHPd"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | [ ] => 0
  | x :: s => (if beq_nat x v then 1 else 0) + count v s
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqZJhIxJ"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqmV969N"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Example test_count1 : count 1 [1; 2; 3; 1; 4; 1] = 3.
Proof.
reflexivity.
Qed.
Example test_count2 : count 6 [1; 2; 3; 1; 4; 1] = 0.
Proof.
reflexivity.
Qed.
Definition sum : bag -> bag -> bag := app.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqJaAeme"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqxgre7c"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Example test_sum1 : count 1 (sum [1; 2; 3] [1; 4; 1]) = 3.
Proof.
reflexivity.
Qed.
Definition add (v : nat) (s : bag) : bag := v :: s.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq89QAr9"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqydWFWT"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Example test_add1 : count 1 (add 1 [1; 4; 1]) = 3.
Proof.
reflexivity.
Qed.
Example test_add2 : count 5 (add 1 [1; 4; 1]) = 0.
Proof.
reflexivity.
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
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqLdE67B"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem app_assoc :
  forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.
Proof.
(intros l1 l2 l3).
(induction l1 as [| n l1' IHl1']).
-
reflexivity.
-
(simpl).
(rewrite IHl1').
reflexivity.
Qed.
Fixpoint rev (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1 : rev [1; 2; 3] = [3; 2; 1].
Proof.
reflexivity.
Qed.
Example test_rev2 : rev nil = nil.
Proof.
reflexivity.
Qed.
Theorem rev_length_firsttry : forall l : natlist, length (rev l) = length l.
Proof.
(intros l).
(induction l as [| n l' IHl']).
-
reflexivity.
-
(simpl).
(rewrite <- IHl').
Abort.
Theorem app_length :
  forall l1 l2 : natlist, length (l1 ++ l2) = length l1 + length l2.
Proof.
(intros l1 l2).
(induction l1 as [| n l1' IHl1']).
-
reflexivity.
-
(simpl).
(rewrite IHl1').
reflexivity.
Qed.
Theorem rev_length : forall l : natlist, length (rev l) = length l.
Proof.
(intros l).
(induction l as [| n l' IHl']).
-
reflexivity.
-
(simpl).
(rewrite app_length, plus_comm).
(simpl).
(rewrite IHl').
reflexivity.
Qed.
Theorem app_nil_r : forall l : natlist, l ++ [ ] = l.
Proof.
(induction l).
-
(simpl).
reflexivity.
-
(simpl).
(rewrite IHl).
reflexivity.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqLlCnnf"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem rev_app_distr :
  forall l1 l2 : natlist, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
(induction l1; simpl; intros).
-
(rewrite app_nil_r; auto).
-
(rewrite IHl1; simpl).
(rewrite app_assoc).
(* Auto-generated comment: Succeeded. *)

