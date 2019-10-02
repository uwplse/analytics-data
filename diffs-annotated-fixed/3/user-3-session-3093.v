Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0GxnR9"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Warnings "-notation-overridden,-parsing".
From LF Require Export Poly.
Theorem silly1 :
  forall n m o p : nat, n = m -> [n; o] = [n; p] -> [n; o] = [m; p].
Proof.
(intros n m o p eq1 eq2).
(rewrite <- eq1).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq8MHwvx"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqaiqItp"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
(apply eq2).
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqtyo153"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqG7JHHd"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Theorem silly2 :
  forall n m o p : nat,
  n = m -> (forall q r : nat, q = r -> [q; o] = [r; p]) -> [n; o] = [m; p].
Proof.
(intros n m o p eq1 eq2).
(apply eq2).
(apply eq1).
Qed.
Theorem silly2a :
  forall n m : nat,
  (n, n) = (m, m) ->
  (forall q r : nat, (q, q) = (r, r) -> [q] = [r]) -> [n] = [m].
Proof.
(intros n m eq1 eq2).
(apply eq2).
(apply eq1).
Qed.
Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  oddb 3 = true -> evenb 4 = true.
Proof.
Admitted.
Theorem silly3_firsttry :
  forall n : nat, true = (n =? 5) -> (S (S n) =? 7) = true.
Proof.
(intros n H).
symmetry.
(simpl).
(apply H).
Qed.
Theorem rev_exercise1 : forall l l' : list nat, l = rev l' -> l' = rev l.
Proof.
Admitted.
Example trans_eq_example :
  forall a b c d e f : nat,
  [a; b] = [c; d] -> [c; d] = [e; f] -> [a; b] = [e; f].
Proof.
(intros a b c d e f eq1 eq2).
(rewrite eq1).
(rewrite eq2).
reflexivity.
Qed.
Theorem trans_eq : forall (X : Type) (n m o : X), n = m -> m = o -> n = o.
Proof.
(intros X n m o eq1 eq2).
(rewrite eq1).
(rewrite eq2).
reflexivity.
Qed.
Example trans_eq_example' :
  forall a b c d e f : nat,
  [a; b] = [c; d] -> [c; d] = [e; f] -> [a; b] = [e; f].
Proof.
(intros a b c d e f eq1 eq2).
(apply trans_eq with (m := [c; d])).
(apply eq1).
(apply eq2).
Qed.
Example trans_eq_exercise :
  forall n m o p : nat, m = minustwo o -> n + p = m -> n + p = minustwo o.
Proof.
Admitted.
Theorem S_injective : forall n m : nat, S n = S m -> n = m.
Proof.
(intros n m H1).
(assert (H2 : n = pred (S n))).
{
reflexivity.
}
(rewrite H2).
(rewrite H1).
reflexivity.
Qed.
Theorem S_injective' : forall n m : nat, S n = S m -> n = m.
Proof.
(intros n m H).
injection H.
(intros Hnm).
(apply Hnm).
Qed.
Theorem injection_ex1 : forall n m o : nat, [n; m] = [o; o] -> [n] = [m].
Proof.
(intros n m o H).
injection H.
(intros H1 H2).
(rewrite H1).
(rewrite H2).
reflexivity.
Qed.
Theorem injection_ex2 : forall n m : nat, [n] = [m] -> n = m.
Proof.
(intros n m H).
injection H as Hnm.
(rewrite Hnm).
reflexivity.
Qed.
Example injection_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j -> y :: l = x :: j -> x = y.
Proof.
Admitted.
Theorem eqb_0_l : forall n, (0 =? n) = true -> n = 0.
Proof.
(intros n).
(destruct n as [| n'] eqn:E).
-
(intros H).
reflexivity.
-
(simpl).
(intros H).
discriminate H.
Qed.
Theorem discriminate_ex1 : forall n : nat, S n = O -> 2 + 2 = 5.
Proof.
(intros n contra).
discriminate contra.
Qed.
Theorem discriminate_ex2 : forall n m : nat, false = true -> [n] = [m].
Proof.
(intros n m contra).
discriminate contra.
Qed.
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X), x :: y :: l = [ ] -> x = z.
Proof.
Admitted.
Theorem f_equal :
  forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y.
Proof.
(intros A B f x y eq).
(rewrite eq).
reflexivity.
Qed.
Theorem S_inj :
  forall (n m : nat) (b : bool), (S n =? S m) = b -> (n =? m) = b.
Proof.
(intros n m b H).
(simpl in H).
(apply H).
Qed.
Theorem silly3' :
  forall n : nat,
  ((n =? 5) = true -> (S (S n) =? 7) = true) ->
  true = (n =? 5) -> true = (S (S n) =? 7).
Proof.
(intros n eq H).
symmetry in H.
(apply eq in H).
symmetry in H.
(apply H).
Qed.
Theorem plus_n_n_injective : forall n m, n + n = m + m -> n = m.
Proof.
(intros n).
(induction n as [| n']).
Admitted.
Theorem double_injective_FAILED : forall n m, double n = double m -> n = m.
Proof.
(intros n m).
(induction n as [| n']).
-
(simpl).
(intros eq).
(destruct m as [| m'] eqn:E).
+
reflexivity.
+
discriminate eq.
-
(intros eq).
(destruct m as [| m'] eqn:E).
+
discriminate eq.
+
(apply f_equal).
Abort.
Theorem double_injective : forall n m, double n = double m -> n = m.
Proof.
(intros n).
(induction n as [| n']).
-
(simpl).
(intros m eq).
(destruct m as [| m'] eqn:E).
+
reflexivity.
+
discriminate eq.
-
(simpl).
(intros m eq).
(destruct m as [| m'] eqn:E).
+
(simpl).
discriminate eq.
+
(apply f_equal).
(apply IHn').
injection eq as goal.
(apply goal).
Qed.
Theorem eqb_true : forall n m, (n =? m) = true -> n = m.
Proof.
Admitted.
Definition manual_grade_for_informal_proof : option (nat * string) := None.
Theorem double_injective_take2_FAILED :
  forall n m, double n = double m -> n = m.
Proof.
(intros n m).
(induction m as [| m']).
-
(simpl).
(intros eq).
(destruct n as [| n'] eqn:E).
+
reflexivity.
+
discriminate eq.
-
(intros eq).
(destruct n as [| n'] eqn:E).
+
discriminate eq.
+
(apply f_equal).
Abort.
Theorem double_injective_take2 : forall n m, double n = double m -> n = m.
Proof.
(intros n m).
generalize dependent n.
(induction m as [| m']).
-
(simpl).
(intros n eq).
(destruct n as [| n'] eqn:E).
+
reflexivity.
+
discriminate eq.
-
(intros n eq).
(destruct n as [| n'] eqn:E).
+
discriminate eq.
+
(apply f_equal).
(apply IHm').
injection eq as goal.
(apply goal).
Qed.
Theorem eqb_id_true : forall x y, eqb_id x y = true -> x = y.
Proof.
(intros [m] [n]).
(simpl).
(intros H).
(assert (H' : m = n)).
{
(apply eqb_true).
(apply H).
}
(rewrite H').
reflexivity.
Qed.
Theorem nth_error_after_last :
  forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
Admitted.
Definition square n := n * n.
Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
(intros n m).
(simpl).
(unfold square).
(rewrite mult_assoc).
(assert (H : n * m * n = n * n * m)).
{
(rewrite mult_comm).
(apply mult_assoc).
}
(rewrite H).
(rewrite mult_assoc).
reflexivity.
Qed.
Definition foo (x : nat) := 5.
Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
(intros m).
(simpl).
reflexivity.
Qed.
Definition bar x := match x with
                    | O => 5
                    | S _ => 5
                    end.
Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
(intros m).
(simpl).
Abort.
Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
(intros m).
(destruct m eqn:E).
-
(simpl).
reflexivity.
-
(simpl).
reflexivity.
Qed.
Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
(intros m).
(unfold bar).
(destruct m eqn:E).
-
reflexivity.
-
reflexivity.
Qed.
Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false else if n =? 5 then false else false.
Theorem sillyfun_false : forall n : nat, sillyfun n = false.
Proof.
(intros n).
(unfold sillyfun).
(destruct (n =? 3) eqn:E1).
-
reflexivity.
-
(destruct (n =? 5) eqn:E2).
+
reflexivity.
+
reflexivity.
Qed.
Fixpoint split {X Y : Type} (l : list (X * Y)) : list X * list Y :=
  match l with
  | [ ] => ([ ], [ ])
  | (x, y) :: t => match split t with
                   | (lx, ly) => (x :: lx, y :: ly)
                   end
  end.
Theorem combine_split :
  forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
(intros X Y).
(intros l).
(induction l as [| n l' IHl']).
-
(simpl).
(intros l1 l2 H).
injection H as H1 H2.
(rewrite <- H1, <- H2).
reflexivity.
Search -".}".
(* Auto-generated comment: Failed. *)

