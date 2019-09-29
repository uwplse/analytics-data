Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqfgfAxQ"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Arith.
Require Import RelationClasses.
Require Import List.
Require Import Helpers.
Set Implicit Arguments.
Axiom (bytes : nat -> Type).
Axiom (bytes_dec : forall n, EqualDec (bytes n)).
Existing Instance bytes_dec.
Axiom (bytes0 : forall n, bytes n).
Axiom (bytes1 : forall n, bytes n).
Axiom (bytes_differ : forall n, n > 0 -> bytes0 n <> bytes1 n).
Definition bnull : bytes 0 := bytes0 0.
Axiom (bappend : forall n1 n2, bytes n1 -> bytes n2 -> bytes (n1 + n2)).
Axiom (bsplit : forall n1 n2, bytes (n1 + n2) -> bytes n1 * bytes n2).
Arguments bsplit {n1} {n2} bs.
Axiom
  (bsplit_bappend :
     forall n1 n2 (b1 : bytes n1) (b2 : bytes n2),
     bsplit (bappend b1 b2) = (b1, b2)).
Fixpoint bsplit_list {n} {m} : bytes (n * m) -> list (bytes m) :=
  match n with
  | O => fun _ => nil
  | S n' =>
      fun bs : bytes (S n' * m) =>
      let (this, rest) := bsplit bs in this :: bsplit_list rest
  end.
Extraction Language Haskell.
Extract Constant bytes =>  "Data.ByteString.ByteString".
Extract Constant bytes_dec =>  "(\n b1 b2 -> b1 Prelude.== b2)".
Extract Constant bytes0 => 
 "(\n -> Data.ByteString.replicate (Prelude.fromIntegral n) 0)".
Extract Constant bappend => 
 "(\_ _ bs1 bs2 -> Data.ByteString.append bs1 bs2)".
Extract Constant bsplit => 
 "(\n1 _ bs -> Data.ByteString.splitAt (Prelude.fromIntegral n1) bs)".
Definition blockbytes := 1024.
Definition block := bytes blockbytes.
Definition block0 : block := bytes0 _.
Definition block1 : block := bytes1 _.
Theorem block0_block1_differ : block0 <> block1.
Proof.
(apply bytes_differ).
(unfold blockbytes).
lia.
Qed.
Hint Resolve block0_block1_differ: core.
Opaque blockbytes.
Definition disk := list block.
Definition empty_disk : disk := nil.
Definition addr := nat.
Definition diskGet (d : disk) (a : addr) : option block := nth_error d a.
Definition diskSize (d : disk) : nat := length d.
Fixpoint diskUpd d (a : addr) b : disk :=
  match d with
  | nil => nil
  | db :: drest =>
      match a with
      | O => b :: drest
      | S a' => db :: diskUpd drest a' b
      end
  end.
Definition diskShrink (d : disk) : disk := firstn (length d - 1) d.
Fixpoint diskGets (d : disk) (a : addr) (count : nat) : 
list (option block) :=
  match count with
  | O => nil
  | S count' => diskGet d a :: diskGets d (a + 1) count'
  end.
Fixpoint diskUpds (d : disk) (a : addr) (blocks : list block) : disk :=
  match blocks with
  | nil => d
  | b :: blocks' => diskUpd (diskUpds d (a + 1) blocks') a b
  end.
Theorem disk_inbounds_exists :
  forall a d, a < diskSize d -> exists b, diskGet d a = Some b.
Proof.
(unfold diskSize).
(intros).
(case_eq (diskGet d a); intros; eauto).
(apply nth_error_None in H0).
lia.
Qed.
Theorem disk_inbounds_not_none :
  forall a d, a < diskSize d -> diskGet d a = None -> False.
Proof.
(unfold diskSize).
(intros).
(apply nth_error_None in H0).
lia.
Qed.
Theorem disk_none_oob : forall a d, diskGet d a = None -> ~ a < diskSize d.
Proof.
(intros).
(destruct (lt_dec a (diskSize d)); eauto).
(exfalso; eapply disk_inbounds_not_none; eauto).
Qed.
Theorem disk_oob_eq : forall d a, ~ a < diskSize d -> diskGet d a = None.
Proof.
(unfold diskSize).
(induction d; simpl; intros).
-
(induction a; eauto).
-
(destruct a0; simpl).
+
lia.
+
(eapply IHd).
lia.
Qed.
Theorem maybe_eq_None_is_True T (v : T) : maybe_eq None v = True.
Proof.
reflexivity.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqK9XXUW"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqGp9zNc"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Qed.
Hint Rewrite maybe_eq_None_is_True : upd.
