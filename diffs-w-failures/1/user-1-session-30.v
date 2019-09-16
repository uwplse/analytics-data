Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 63.
Require Import Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Set Silent.
Require Import Orders.
Require Import FunInd.
Require Import Recdef.
Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import Coq.Program.Equality.
Unset Silent.
Require Import Math.
#[local]Coercion is_true : bool >-> Sortclass.
Module Sort.
Parameter (t : Type).
Parameter (leb : t -> t -> bool).
Notation "a <=? b" := (leb a b).
Notation "! a " := (negb a) (at level 10).
Parameter
  (leb_total :
     forall x y : t, (x <=? y) = true \/ (y <=? x) = true).
Parameter (leb_trans : Transitive leb).
Module SF.
Fixpoint insert (i : t) (l : list t) :=
  match l with
  | nil => i :: nil
  | h :: t => if i <=? h then i :: l else h :: insert i t
  end.
Fixpoint insertion_sort (l : list t) : list t :=
  match l with
  | nil => nil
  | h :: t => insert h (insertion_sort t)
  end.
End SF.
Recursive Extraction SF.insertion_sort.
Module SF_Proofs.
Import SF.
Create HintDb sf discriminated.
Print Permutation.
Hint Constructors Permutation: sf.
Theorem insertion_sort_permutation :
  forall l, Permutation l (insertion_sort l).
Proof with (simpl; eauto with sf).
(induction l) ...
Show Proof.
Print HintDb core.
Print HintDb sf.
Abort.
Lemma insert_permutation :
  forall a l, Permutation (a :: l) (insert a l).
Proof with (simpl; eauto with sf).
(induction l) ...
Set Silent.
(destruct (a <=? a0)) ...
Unset Silent.
Qed.
