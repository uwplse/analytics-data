Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqgqcW3A"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Psatz.
Require Import String.
Require Import Program.
Require Export Complex.
Require Import List.
Require Import Setoid.
Require Import Omega.
Local Open Scope nat_scope.
Definition Matrix (m n : nat) := nat -> nat -> C.
Arguments Matrix m%nat n%nat.
Notation Vector n:= (Matrix n 1).
Notation Square n:= (Matrix n n).
Definition WF_Matrix {m n : nat} (A : Matrix m n) : Prop :=
  forall x y, x >= m \/ y >= n -> A x y = C0.
Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop :=
  forall i j, i < m -> j < n -> A i j = B i j.
Infix "==" := mat_equiv (at level 80) : matrix_scope.
Open Scope matrix_scope.
Lemma mat_equiv_refl : forall {m} {n} (A : Matrix m n), A == A.
Proof.
(intros m n A i j Hi Hj).
reflexivity.
Qed.
Lemma mat_equiv_sym : forall {m} {n} (A B : Matrix m n), A == B -> B == A.
Proof.
(intros m n A B H i j Hi Hj).
(rewrite H; easy).
Qed.
Lemma mat_equiv_trans :
  forall {m} {n} (A B C : Matrix m n), A == B -> B == C -> A == C.
Proof.
(intros m n A B C HAB HBC i j Hi Hj).
(rewrite HAB; trivial).
(apply HBC; easy).
Qed.
Add Parametric Relation  m n : Matrix m n @mat_equiv m n reflexivity proved by
 mat_equiv_refl symmetry proved by mat_equiv_sym transitivity proved by
 mat_equiv_trans as mat_equiv_rel.
Lemma mat_equiv_ex : forall {m} {n} (A B C : Matrix m n), A == B -> A == C -> B == C.
Proof.
(intros m n A B C HAB HAC).
(rewrite <- HAB).
(apply HAC).
Qed.
Lemma mat_equiv_eq :
  forall {m n : nat} (A B : Matrix m n),
  WF_Matrix A -> WF_Matrix B -> mat_equiv A B -> A = B.
Proof.
(intros m n A' B' WFA WFB Eq).
(apply functional_extensionality; intros i).
(apply functional_extensionality; intros j).
(unfold mat_equiv in Eq).
(bdestruct (i <? m)).
(bdestruct (j <? n)).
+
(apply Eq; easy).
+
(rewrite WFA, WFB; trivial; right; try lia).
+
(rewrite WFA, WFB; trivial; left; try lia).
Qed.
Open Scope nat_scope.
Open Scope R_scope.
Open Scope C_scope.
Bind Scope matrix_scope with Matrix.
Delimit Scope matrix_scope with M.
Open Scope matrix_scope.
Parameter (print_C : C -> string).
Fixpoint print_row {m n} i j (A : Matrix m n) : string :=
  match j with
  | 0 => "\n"
  | S j' => print_C (A i j') ++ ", " ++ print_row i j' A
  end.
Fixpoint print_rows {m n} i j (A : Matrix m n) : string :=
  match i with
  | 0 => ""
  | S i' => print_row i' n A ++ print_rows i' n A
  end.
Definition print_matrix {m} {n} (A : Matrix m n) : string := print_rows m n A.
Definition list2D_to_matrix (l : list (list C)) :
  Matrix (length l) (length (hd [] l)) := fun x y => nth y (nth x l []) 0%R.
Lemma WF_list2D_to_matrix :
  forall m n li,
  length li = m ->
  (forall li', In li' li -> length li' = n) -> @WF_Matrix m n (list2D_to_matrix li).
Proof.
(intros m n li L F x y [l| r]).
-
(unfold list2D_to_matrix).
(rewrite (nth_overflow _ [])).
(destruct y; easy).
(rewrite L).
(apply l).
-
(unfold list2D_to_matrix).
(rewrite (nth_overflow _ C0)).
easy.
(destruct (nth_in_or_default x li []) as [IN| DEF]).
(apply F in IN).
(rewrite IN).
(apply r).
(rewrite DEF).
(simpl; lia).
Qed.
Definition M23 : Matrix 2 3 :=
  fun x y =>
  match (x, y) with
  | (0, 0) => 1
  | (0, 1) => 2
  | (0, 2) => 3
  | (1, 0) => 4
  | (1, 1) => 5
  | (1, 2) => 6
  | _ => 0
  end.
Definition M23' : Matrix 2 3 :=
  list2D_to_matrix [[RtoC 1; RtoC 2; RtoC 3]; [RtoC 4; RtoC 5; RtoC 6]].
Lemma M23eq : M23 == M23'.
Proof.
(intros i j Hi Hj).
(compute).
(do 4 (try destruct i; try destruct j; simpl; trivial)).
Qed.
Notation "m =? n" := (Nat.eqb m n) (at level 70) : matrix_scope.
Notation "m <? n" := (Nat.ltb m n) (at level 70) : matrix_scope.
Notation "m <=? n" := (Nat.leb m n) (at level 70) : matrix_scope.
Definition Zero {m n : nat} : Matrix m n := fun x y => 0.
Definition I (n : nat) : Square n := fun x y => if x =? y then 1 else 0.
Fixpoint Csum (f : nat -> C) (n : nat) : C :=
  match n with
  | 0 => 0
  | S n' => Csum f n' + f n'
  end.
Definition trace {n : nat} (A : Square n) : C := Csum (fun k => A k k) n.
Definition scale {m n : nat} (r : C) (A : Matrix m n) : 
  Matrix m n := fun i j => (r * A i j)%C.
Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun i j => A i j + B i j.
Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : 
  Matrix m o := fun i j => Csum (fun k => A i k * B k j) n.
Definition kron {m n o p : nat} (A : Matrix m n) (B : Matrix o p) :
  Matrix (m * o) (n * p) :=
  fun i j => (A (i / o) (j / p))%nat * (B (i mod o) (j mod p))%nat.
Definition transpose {m} {n} (A : Matrix m n) : Matrix n m := fun i j => A j i.
Definition adjoint {m} {n} (A : Matrix m n) : Matrix n m := fun i j => (A j i) ^*.
Definition dot {n : nat} (A : Vector n) (B : Vector n) : C :=
  Mmult (transpose A) B O O.
Definition inner_product {n} (u v : Vector n) : C := Mmult (adjoint u) v O O.
Definition outer_product {n} (u v : Vector n) : Square n := Mmult u (adjoint v).
Fixpoint kron_n n {m1 m2} (A : Matrix m1 m2) : Matrix (m1 ^ n) (m2 ^ n) :=
  match n with
  | 0 => I 1
  | S n' => kron A (kron_n n' A)
  end.
Fixpoint big_kron {m n} (As : list (Matrix m n)) :
Matrix (m ^ length As) (n ^ length As) :=
  match As with
  | [] => I 1
  | A :: As' => kron A (big_kron As')
  end.
Notation "\206\163^ n f" := (Csum f n) (at level 60) : matrix_scope.
Infix ".+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix ".*" := scale (at level 40, left associativity) : matrix_scope.
Infix "\195\151" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "\226\138\151" := kron (at level 40, left associativity) : matrix_scope.
Notation "A \226\138\164" := (transpose A) (at level 0) : matrix_scope.
Notation "A \226\128\160" := (adjoint A) (at level 0) : matrix_scope.
Infix "\226\136\152" := dot (at level 40, left associativity) : matrix_scope.
Notation "\226\159\168 A , B \226\159\169" := (inner_product A B) : matrix_scope.
Notation "n \226\168\130 A" := (kron_n n A) (at level 30, no associativity) : matrix_scope.
Notation "\226\168\130 A" := (big_kron A) (at level 60) : matrix_scope.
Hint Unfold Zero I trace dot Mplus scale Mmult kron transpose adjoint: U_db.
Ltac
 solve_end :=
  match goal with
  | H:lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.
Ltac
 by_cell :=
  intros;
   (let i := fresh "i" in
    let j := fresh "j" in
    let Hi := fresh "Hi" in
    let Hj := fresh "Hj" in
    intros i j Hi Hj; try solve_end;
     repeat (destruct i as [| i]; simpl; [  | apply lt_S_n in Hi ]; try solve_end);
     clear Hi;
     repeat (destruct j as [| j]; simpl; [  | apply lt_S_n in Hj ]; try solve_end);
     clear Hj).
Ltac lma := by_cell; lca.
Lemma test_lma : 0 .* I 4 == Zero.
Proof.
lma.
Qed.
Lemma Csum_0 : forall f n, (forall x, f x = 0) -> Csum f n = 0.
Proof.
(intros).
(induction n).
-
reflexivity.
-
(simpl).
(rewrite IHn, H).
lca.
Qed.
Lemma Csum_1 : forall f n, (forall x, f x = 1) -> Csum f n = INR n.
Proof.
(intros).
(induction n).
-
reflexivity.
-
(simpl).
(rewrite IHn, H).
(destruct n; lca).
Qed.
Lemma Csum_constant : forall c n, Csum (fun x => c) n = INR n * c.
Proof.
(intros c n).
(induction n).
+
(simpl; lca).
+
(simpl).
(rewrite IHn).
(destruct n; lca).
Qed.
Lemma Csum_eq : forall f g n, f = g -> Csum f n = Csum g n.
Proof.
(intros f g n H).
subst.
reflexivity.
Qed.
Lemma Csum_0_bounded :
  forall f n, (forall x, (x < n)%nat -> f x = C0) -> Csum f n = 0.
Proof.
(intros).
(induction n).
-
reflexivity.
-
(simpl).
(rewrite IHn, H).
lca.
lia.
(intros).
(apply H).
lia.
Qed.
Lemma Csum_eq_bounded :
  forall f g n, (forall x, (x < n)%nat -> f x = g x) -> Csum f n = Csum g n.
Proof.
(intros f g n H).
(induction n).
+
(simpl).
reflexivity.
+
(simpl).
(rewrite H by lia).
(rewrite IHn by (intros; apply H; lia)).
reflexivity.
Qed.
Lemma Csum_plus : forall f g n, Csum (fun x => f x + g x) n = Csum f n + Csum g n.
Proof.
(intros f g n).
(induction n).
+
(simpl).
lca.
+
(simpl).
(rewrite IHn).
lca.
Qed.
Lemma Csum_mult_l : forall c f n, c * Csum f n = Csum (fun x => c * f x) n.
Proof.
(intros c f n).
(induction n).
+
(simpl; lca).
+
(simpl).
(rewrite Cmult_plus_dist_l).
(rewrite IHn).
reflexivity.
Qed.
Lemma Csum_mult_r : forall c f n, Csum f n * c = Csum (fun x => f x * c) n.
Proof.
(intros c f n).
(induction n).
+
(simpl; lca).
+
(simpl).
(rewrite Cmult_plus_dist_r).
(rewrite IHn).
reflexivity.
Qed.
Lemma Csum_conj_distr : forall f n, (Csum f n) ^* = Csum (fun x => (f x) ^*) n.
Proof.
(intros f n).
(induction n).
+
(simpl; lca).
+
(simpl).
(rewrite Cconj_plus_dist).
(rewrite IHn).
reflexivity.
Qed.
Lemma Csum_extend_r : forall n f, Csum f n + f n = Csum f (S n).
Proof.
reflexivity.
Qed.
Lemma Csum_extend_l : forall n f, f O + Csum (fun x => f (S x)) n = Csum f (S n).
Proof.
(intros n f).
(induction n).
+
(simpl; lca).
+
(simpl).
(rewrite Cplus_assoc).
(rewrite IHn).
(simpl).
reflexivity.
Qed.
Lemma Csum_unique :
  forall (f : nat -> C) (k : C) (n x : nat),
  (x < n)%nat -> f x = k -> (forall x', x <> x' -> f x' = 0) -> Csum f n = k.
Proof.
(intros f k).
(induction n).
-
(intros x H; lia).
-
(intros x H H0 H1).
(simpl).
(destruct (x =? n)%nat eqn:E).
+
(apply Nat.eqb_eq in E).
subst.
(rewrite Csum_0_bounded).
lca.
(intros x L).
(apply H1).
lia.
+
(apply Nat.eqb_neq in E).
(rewrite H1 by lia).
(rewrite (IHn x); trivial).
lca.
lia.
Qed.
Lemma Csum_sum :
  forall m n f, Csum f (m + n) = Csum f m + Csum (fun x => f (m + x)%nat) n.
Proof.
(intros m n f).
(induction m).
+
(simpl).
(rewrite Cplus_0_l).
reflexivity.
+
(simpl).
(rewrite IHm).
(repeat rewrite <- Cplus_assoc).
(remember (fun y => f (m + y)%nat) as g).
replace (f m) with g O by (subst; rewrite plus_0_r; reflexivity).
replace (f (m + n)%nat) with g n by (subst; reflexivity).
replace (Csum (fun x : nat => f (S (m + x))) n) with Csum (fun x : nat => g (S x)) n.
2: {
(apply Csum_eq).
subst.
(apply functional_extensionality).
(intros; rewrite <- plus_n_Sm).
reflexivity.
}
(rewrite Csum_extend_l).
(rewrite Csum_extend_r).
reflexivity.
Qed.
Lemma Csum_product :
  forall m n f g,
  n <> O ->
  Csum f m * Csum g n = Csum (fun x => f (x / n)%nat * g (x mod n)%nat) (m * n).
Proof.
(intros).
(induction m).
+
(simpl; lca).
+
(simpl).
(rewrite Cmult_plus_dist_r).
(rewrite IHm).
clear IHm.
(rewrite Csum_mult_l).
(remember (fun x : nat => f (x / n)%nat * g (x mod n)%nat) as h).
replace (Csum (fun x : nat => f m * g x) n) with
 Csum (fun x : nat => h (m * n + x)%nat) n.
2: {
subst.
(apply Csum_eq_bounded).
(intros x Hx).
(rewrite Nat.div_add_l by assumption).
(rewrite Nat.div_small; trivial).
(rewrite plus_0_r).
(rewrite Nat.add_mod by assumption).
(rewrite Nat.mod_mul by assumption).
(rewrite plus_0_l).
(repeat rewrite Nat.mod_small; trivial).
}
(rewrite <- Csum_sum).
(rewrite plus_comm).
reflexivity.
Qed.
Lemma Csum_ge_0 : forall f n, (forall x, 0 <= fst (f x)) -> 0 <= fst (Csum f n).
Proof.
(intros f n H).
(induction n).
-
(simpl).
lra.
-
(simpl in *).
(rewrite <- Rplus_0_r  at 1).
(apply Rplus_le_compat; easy).
Qed.
Lemma Csum_member_le :
  forall (f : nat -> C) (n : nat),
  (forall x, 0 <= fst (f x)) -> forall x, (x < n)%nat -> fst (f x) <= fst (Csum f n).
Proof.
(intros f).
(induction n).
-
(intros H x Lt).
(inversion Lt).
-
(intros H x Lt).
(bdestruct (Nat.ltb x n)).
+
(simpl).
(rewrite <- Rplus_0_r  at 1).
(apply Rplus_le_compat).
(apply IHn; easy).
(apply H).
+
(assert (E : x = n) by lia).
(rewrite E).
(simpl).
(rewrite <- Rplus_0_l  at 1).
(apply Rplus_le_compat).
(apply Csum_ge_0; easy).
lra.
Qed.
Lemma trace_compat : forall {n} (A A' : Square n), A == A' -> trace A = trace A'.
Proof.
(intros n A A' H).
(apply Csum_eq_bounded).
(intros x Hx).
(rewrite H; easy).
Qed.
Lemma scale_compat :
  forall {m} {n} (c c' : C) (A A' : Matrix m n),
  c = c' -> A == A' -> c .* A == c' .* A'.
Proof.
(intros m n c c' A A' Hc HA).
(intros i j Hi Hj).
(unfold scale).
(rewrite Hc, HA; easy).
Qed.
Lemma Mplus_compat :
  forall {m} {n} (A A' B B' : Matrix m n), A == A' -> B == B' -> A .+ B == A' .+ B'.
Proof.
(intros m n A A' B B' HA HB i j Hi Hj).
(unfold Mplus).
(rewrite HA, HB; try lia).
easy.
Qed.
Lemma Mmult_compat :
  forall {m} {n} {o} (A A' : Matrix m n) (B B' : Matrix n o),
  A == A' -> B == B' -> A \195\151 B == A' \195\151 B'.
Proof.
(intros m n o A A' B B' HA HB i j Hi Hj).
(unfold Mmult).
(apply Csum_eq_bounded; intros x Hx).
(rewrite HA, HB; easy).
Qed.
Lemma kron_compat :
  forall {m} {n} {o} {p} (A A' : Matrix m n) (B B' : Matrix o p),
  A == A' -> B == B' -> A \226\138\151 B == A' \226\138\151 B'.
Proof.
(intros m n o p A A' B B' HA HB).
(intros i j Hi Hj).
(unfold kron).
(assert (Ho : o <> O)).
(intros F).
(rewrite F in *).
lia.
(assert (Hp : p <> O)).
(intros F).
(rewrite F in *).
lia.
(rewrite HA, HB).
easy.
-
(apply Nat.mod_upper_bound; easy).
-
(apply Nat.mod_upper_bound; easy).
-
(apply Nat.div_lt_upper_bound; lia).
-
(apply Nat.div_lt_upper_bound; lia).
Qed.
Lemma transpose_compat :
  forall {m} {n} (A A' : Matrix m n), A == A' -> (A) \226\138\164 == (A') \226\138\164.
Proof.
(intros m n A A' H).
(intros i j Hi Hj).
(unfold transpose).
(rewrite H; easy).
Qed.
Lemma adjoint_compat :
  forall {m} {n} (A A' : Matrix m n), A == A' -> (A) \226\128\160 == (A') \226\128\160.
Proof.
(intros m n A A' H).
(intros i j Hi Hj).
(unfold adjoint).
(rewrite H; easy).
Qed.
Add Parametric Morphism  n : @trace n with signature mat_equiv ==> eq as trace_mor.
Proof.
(intros; apply trace_compat; easy).
Qed.
Add Parametric Morphism  m n : @scale m n with signature
 eq ==> mat_equiv ==> mat_equiv as Mscale_mor.
Proof.
(intros; apply scale_compat; easy).
Qed.
Add Parametric Morphism  m n : @Mplus m n with signature
 mat_equiv ==> mat_equiv ==> mat_equiv as Mplus_mor.
Proof.
(intros).
(apply Mplus_compat; easy).
Qed.
Add Parametric Morphism  m n o : @Mmult m n o with signature
 mat_equiv ==> mat_equiv ==> mat_equiv as Mmult_mor.
Proof.
(intros).
(apply Mmult_compat; easy).
Qed.
Add Parametric Morphism  m n o p : @kron m n o p with signature
 mat_equiv ==> mat_equiv ==> mat_equiv as kron_mor.
Proof.
(intros).
(apply kron_compat; easy).
Qed.
Add Parametric Morphism  m n : @transpose m n with signature 
 mat_equiv ==> mat_equiv as transpose_mor.
Proof.
(intros).
(apply transpose_compat; easy).
Qed.
Add Parametric Morphism  m n : @adjoint m n with signature 
 mat_equiv ==> mat_equiv as adjoint_mor.
Proof.
(intros).
(apply adjoint_compat; easy).
Qed.
Lemma dim0_l : forall {n : nat} (A : Matrix 0 n), A == Zero.
Proof.
lma.
Qed.
Lemma dim0_r : forall {n : nat} (A : Matrix n 0), A == Zero.
Proof.
lma.
Qed.
Lemma dim0 : forall A : Matrix 0 0, A == Zero.
Proof.
(apply dim0_l).
Qed.
Lemma I0_Zero : I 0 == Zero.
Proof.
(apply dim0).
Qed.
Lemma trace_plus_dist :
  forall {n : nat} (A B : Square n), trace (A .+ B) = trace A + trace B.
Proof.
(intros).
(unfold trace, Mplus).
(induction n).
-
(simpl).
lca.
-
(simpl).
(rewrite IHn).
lca.
Qed.
Lemma trace_mult_dist :
  forall {n : nat} (p : C) (A : Square n), trace (p .* A) = p * trace A.
Proof.
(intros).
(unfold trace, scale).
(induction n).
-
(simpl).
lca.
-
(simpl).
(rewrite IHn).
lca.
Qed.
Lemma Mplus_0_l : forall {m n : nat} (A : Matrix m n), Zero .+ A == A.
Proof.
lma.
Qed.
Lemma Mplus_0_r : forall {m n : nat} (A : Matrix m n), A .+ Zero == A.
Proof.
lma.
Qed.
Lemma Mmult_0_l : forall {m n o : nat} (A : Matrix n o), @Zero m n \195\151 A == Zero.
Proof.
(intros m n o A i j Hi Hj).
(unfold Mmult, Zero).
(rewrite Csum_0_bounded).
easy.
(intros).
lca.
Qed.
Lemma Mmult_0_r : forall {m n o : nat} (A : Matrix m n), A \195\151 @Zero n o == Zero.
Proof.
(intros m n o A i j Hi Hj).
(unfold Mmult, Zero).
(rewrite Csum_0_bounded).
easy.
(intros).
lca.
Qed.
Lemma Mmult_1_l : forall {m n : nat} (A : Matrix m n), I m \195\151 A == A.
Proof.
(intros m n A i j Hi Hj).
(unfold Mmult).
(eapply Csum_unique).
(apply Hi).
(unfold I).
(rewrite Nat.eqb_refl).
lca.
(intros x Hx).
(unfold I).
(apply Nat.eqb_neq in Hx).
(rewrite Hx).
lca.
Qed.
Lemma Mmult_1_r : forall {m n : nat} (A : Matrix m n), A \195\151 I n == A.
Proof.
(intros m n A i j Hi Hj).
(unfold Mmult).
(eapply Csum_unique).
(apply Hj).
(unfold I).
(rewrite Nat.eqb_refl).
lca.
(intros x Hx).
(unfold I).
(apply Nat.eqb_neq in Hx).
(rewrite Nat.eqb_sym).
(rewrite Hx).
lca.
Qed.
Lemma kron_0_l : forall {m n o p : nat} (A : Matrix o p), @Zero m n \226\138\151 A == Zero.
Proof.
lma.
Qed.
Lemma kron_0_r : forall {m n o p : nat} (A : Matrix m n), A \226\138\151 @Zero o p == Zero.
Proof.
lma.
Qed.
Lemma kron_1_r : forall {m n : nat} (A : Matrix m n), A \226\138\151 I 1 == A.
Proof.
(intros m n A i j Hi Hj).
(unfold I, kron).
(rewrite 2!Nat.div_1_r).
(rewrite 2!Nat.mod_1_r).
(simpl; lca).
Qed.
Lemma kron_1_l : forall {m n : nat} (A : Matrix m n), I 1 \226\138\151 A == A.
Proof.
(intros m n A i j Hi Hj).
(unfold I, kron).
(rewrite 2!Nat.mod_small by lia).
(rewrite 2!Nat.div_small by lia).
(simpl; lca).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqMwSMS6"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
