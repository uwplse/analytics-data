Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqXpOheL"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Arith.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq3kEyCN"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqhif6W1"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Require Import Omega.
Require Import Recdef.
Require Import String.
Require Import List.
Require Import Program.Tactics.
Require Import Relation_Operators.
Require Import Ascii.
Require Import Program.
Require Import Bool.
Require Import Sorting.Permutation.
Section CharacterFacts.
Definition ascii_eq (a b : ascii) : bool :=
  match (a, b) with
  | (Ascii a1 a2 a3 a4 a5 a6 a7 a8, Ascii b1 b2 b3 b4 b5 b6 b7 b8) =>
      eqb a1 b1 && eqb a2 b2 && eqb a3 b3 && eqb a4 b4 && eqb a5 b5 &&
      eqb a6 b6 && eqb a7 b7 && eqb a8 b8
  end.
Lemma ascii_eq_refl (a : ascii) : ascii_eq a a = true.
Proof.
(destruct a; unfold ascii_eq; repeat rewrite eqb_reflx; simpl; auto).
Qed.
Lemma ascii_eq_iff a b : ascii_eq a b = true <-> a = b.
Proof.
(split; intros).
-
(unfold ascii_eq in H; destruct a; destruct b;
  repeat rewrite andb_true_iff in *; destruct_pairs;
  rewrite eqb_true_iff in *; congruence).
-
(rewrite H; apply ascii_eq_refl).
Qed.
End CharacterFacts.
Section StringFacts.
Lemma append_nil_l s : ("" ++ s)%string = s.
Proof.
(simpl; auto).
Qed.
Lemma append_nil_r s : (s ++ "")%string = s.
Proof.
(induction s; simpl; try rewrite IHs; auto).
Qed.
Lemma append_assoc s1 s2 s3 :
  (s1 ++ s2 ++ s3)%string = ((s1 ++ s2) ++ s3)%string.
Proof.
(induction s1; simpl; try rewrite IHs1; auto).
Qed.
Lemma append_comm_cons a s1 s2 :
  (String a s1 ++ s2)%string = String a (s1 ++ s2)%string.
Proof.
(induction s1; simpl; auto).
Qed.
Definition strlen := String.length.
Lemma append_strlen_l s1 s2 : strlen s1 <= strlen (s1 ++ s2).
Proof.
(induction s1; simpl; try rewrite IHs1; omega).
Qed.
Lemma append_strlen_r s1 s2 : strlen s2 <= strlen (s1 ++ s2).
Proof.
(induction s1; simpl; try rewrite IHs1; omega).
Qed.
End StringFacts.
Inductive regex : Set :=
  | EMPTY : regex
  | ANY : regex
  | CHAR : ascii -> regex
  | CONCAT : regex -> regex -> regex
  | OR : regex -> regex -> regex
  | STAR : regex -> regex.
Inductive regex_match : regex -> string -> Prop :=
  | empty_regex_match : regex_match EMPTY ""
  | any_regex_match : forall a : ascii, regex_match ANY (String a "")
  | char_regex_match : forall a : ascii, regex_match (CHAR a) (String a "")
  | concat_regex_match :
      forall (r1 r2 : regex) (s1 s2 : string),
      regex_match r1 s1 ->
      regex_match r2 s2 -> regex_match (CONCAT r1 r2) (s1 ++ s2)
  | or_regex_match :
      forall (r1 r2 : regex) (s : string),
      regex_match r1 s \/ regex_match r2 s -> regex_match (OR r1 r2) s
  | star_regex_match_empty : forall r : regex, regex_match (STAR r) ""
  | star_regex_match_rec_dec :
      forall (r : regex) (s1 s2 : string),
      regex_match r s1 ->
      regex_match (STAR r) s2 -> regex_match (STAR r) (s1 ++ s2).
Hint Constructors regex_match.
Example example1 : regex_match EMPTY "".
Proof.
auto.
Qed.
Example example2 : regex_match ANY "a".
Proof.
auto.
Qed.
Example example3 : regex_match (CHAR "a") "a".
Proof.
auto.
Qed.
Example example4 : regex_match (CONCAT (CHAR "a") ANY) "ab".
Proof.
(assert (Hsplit : ("ab" = "a" ++ "b")%string) by auto).
(rewrite Hsplit).
auto.
Qed.
Example example5 : regex_match (OR (CHAR "a") (CHAR "b")) "b".
Proof.
auto.
Qed.
Example example6 : regex_match (STAR (CHAR "a")) "aaa".
Proof.
(assert (Hsplit1 : ("aaa" = "a" ++ "aa")%string) by auto).
(rewrite Hsplit1).
(repeat (constructor; auto)).
(assert (Hsplit2 : ("aa" = "a" ++ "a")%string) by auto).
(rewrite Hsplit2; repeat (constructor; auto)).
(rewrite <- append_nil_r; auto).
Qed.
Inductive regex_match_length : regex -> string -> nat -> Prop :=
  | empty_regex_match_length : regex_match_length EMPTY "" 0
  | any_regex_match_length :
      forall a : ascii, regex_match_length ANY (String a "") 1
  | char_regex_match_length :
      forall a : ascii, regex_match_length (CHAR a) (String a "") 1
  | concat_regex_match_length :
      forall (r1 r2 : regex) (s1 s2 : string),
      regex_match_length r1 s1 (String.length s1) ->
      regex_match_length r2 s2 (String.length s2) ->
      regex_match_length (CONCAT r1 r2) (s1 ++ s2) (String.length (s1 ++ s2))
  | or_regex_match_length :
      forall (r1 r2 : regex) (s : string),
      regex_match_length r1 s (String.length s) \/
      regex_match_length r2 s (String.length s) ->
      regex_match_length (OR r1 r2) s (String.length s)
  | star_regex_match_length_empty :
      forall r : regex, regex_match_length (STAR r) "" 0
  | star_regex_match_length_nonempty :
      forall (r : regex) (s1 s2 : string),
      regex_match_length r s1 (String.length s1) ->
      regex_match_length (STAR r) s2 (String.length s2) ->
      regex_match_length (STAR r) (s1 ++ s2) (String.length (s1 ++ s2)).
Hint Constructors regex_match_length.
Theorem regex_match_is_explicit :
  forall (r : regex) (s : string),
  regex_match r s <-> regex_match_length r s (String.length s).
Proof.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqW22qF9"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqQhOyyi"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
