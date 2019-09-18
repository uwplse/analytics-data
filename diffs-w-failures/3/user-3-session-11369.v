Require Import Arith.
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
