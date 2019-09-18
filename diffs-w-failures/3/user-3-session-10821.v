Time
Require Export Tactical.Abstract Tactical.DependentEq
  Tactical.ExistentialVariants Tactical.Misc Tactical.Propositional
  Tactical.SimplMatch.
Require Extraction.
Require Import Array.Array.
Time From RecordUpdate Require Export RecordSet.
Time Export RecordSetNotations.
From Classes Require Import Classes.
From Array Require Export Array.
From Coq Require Import List.
From Coq Require Import Omega.
Require Init.Nat.
From Classes Require Import EqualDec.
Import EqualDecNotation.
Set Implicit Arguments.
Section Array.
Context (A : Type).
Notation array := (list A).
Implicit Types (l : array) (n : nat) (x : A).
Notation assign := (Array.assign (A:=A)).
Fixpoint massign (ws : list (nat * A)) l : array :=
  match ws with
  | nil => l
  | (n, v) :: ws' => massign ws' (assign l n v)
  end.
Fixpoint ws_lookup (ws : list (nat * A)) n : option A :=
  match ws with
  | nil => None
  | (n', v) :: ws' =>
      match ws_lookup ws' n with
      | Some v' => Some v'
      | None => if n == n' then Some v else None
      end
  end.
Theorem massign_not_in ws :
  forall l n, ws_lookup ws n = None -> index (massign ws l) n = index l n.
Proof.
(induction ws; simpl; intros; auto).
(destruct a as [a v]).
(destruct_with_eqn ws_lookup ws n; try congruence).
(destruct (n == a); try congruence).
Set Implicit Arguments.
Axiom (bytes : nat -> Type).
Axiom (bytes_dec : forall n, EqualDec (bytes n)).
Existing Instance bytes_dec.
Axiom (bytes0 : forall n, bytes n).
Extraction Language Haskell.
Extract Constant bytes =>  "Data.ByteString.ByteString".
Extract Constant bytes_dec =>  "(\n b1 b2 -> b1 Prelude.== b2)".
Extract Constant bytes0 => 
 "(\n -> Data.ByteString.replicate (Prelude.fromIntegral n) 0)".
Definition blockbytes := 1024.
(erewrite IHws; eauto; array).
Definition block := bytes blockbytes.
Definition block0 : block := bytes0 _.
Instance bytes_default  n: (Default (bytes n)) := (bytes0 n).
Instance block_default : (Default block) := _.
Opaque blockbytes.
Definition disk := list block.
Definition addr := nat.
Qed.
Theorem length_massign ws : forall l, length (massign ws l) = length l.
Proof.
(induction ws; simpl; intros; auto).
(destruct a).
(rewrite IHws; array).
Qed.
Hint Rewrite length_massign : length.
Theorem massign_oob ws :
  forall l n, n >= length l -> index (massign ws l) n = None.
Proof.
(induction ws; simpl; intros; array).
(destruct a).
(rewrite IHws; array).
Qed.
Theorem massign_in ws l n v :
  n < length l -> ws_lookup ws n = Some v -> index (massign ws l) n = Some v.
Proof.
generalize dependent v.
generalize dependent n.
generalize dependent l.
(induction ws; simpl; intros).
-
congruence.
-
(destruct a as [a v']).
destruct_with_eqn ws_lookup ws n.
(inversion H0; subst; clear H0).
(erewrite IHws; eauto; array).
(destruct (n == a); subst; try congruence).
(inversion H0; subst; clear H0).
(rewrite massign_not_in by auto; array).
Qed.
Theorem massign_idempotent ws l : massign ws (massign ws l) = massign ws l.
Proof.
(apply index_ext_eq; intros).
(destruct (lt_dec n (length l))).
destruct_with_eqn ws_lookup ws n.
(erewrite ?massign_in by (eauto; array); auto).
(rewrite ?massign_not_in by auto; auto).
(rewrite ?massign_oob by (array; omega); auto).
Qed.
Theorem massign_snoc ws a v :
  forall l, massign (ws ++ (a, v) :: nil) l = assign (massign ws l) a v.
Proof.
(induction ws; simpl; intros; auto).
(destruct a0 as [a' v']).
(rewrite IHws; array).
Qed.
End Array.
Hint Rewrite length_massign : length.
Hint Rewrite massign_not_in using (solve [ auto; congruence ]) : array.
Hint Rewrite massign_snoc : array.
