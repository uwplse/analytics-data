Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqwTuAtQ"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqsTgTFG"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASLib.
Require Import Denotation.
Require Import Composition.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import Ancilla.
Require Import SemanticLib.
Require Import List.
Set Bullet Behavior Strict Subproofs.
Global Unset Asymmetric Patterns.
Delimit Scope matrix_scope with M.
Require Import Omega.
Close Scope matrix_scope.
Open Scope circ_scope.
Open Scope nat_scope.
Definition unitary_at1 n (U : Unitary Qubit) (i : Var) (pf : i < n) :
  Box (n \226\168\130 Qubit) (n \226\168\130 Qubit).
Proof.
gen n U.
(induction i as [| i]; intros n pf U).
*
(destruct n as [| n]; [ omega |  ]).
(simpl).
refine (box_ q \226\135\146 (let_ (q, qs)\226\134\144 q; let_ q \226\134\144 _X $ q; (q, qs))).
*
(destruct n as [| n]; [ omega |  ]).
(simpl).
refine (box_ q \226\135\146 (let_ (q, qs)\226\134\144 q; let_ qs \226\134\144 IHi n _ U $ qs; (q, qs))).
omega.
Defined.
Lemma unitary_at1_WT :
  forall n (U : Unitary Qubit) i (pf : i < n), Typed_Box (unitary_at1 n U i pf).
Proof.
(intros n U i pf).
gen n U.
(induction i; intros n pf U).
*
(simpl).
(destruct n as [| n]; [ omega |  ]).
type_check.
*
(simpl).
(destruct n as [| n]; [ omega |  ]).
(simpl).
type_check.
(apply IHi).
type_check.
Qed.
Definition X_at n i (pf : i < n) := unitary_at1 n _X i pf.
Lemma X_at_WT : forall n i pf, Typed_Box (X_at n i pf).
Proof.
(intros; apply unitary_at1_WT).
Qed.
Lemma lt_leS_le : forall i j k, i < j -> j <= S k -> i <= k.
Proof.
(intros).
omega.
Qed.
Lemma strong_induction' :
  forall P : nat -> Type,
  (forall n : nat, (forall k : nat, k < n -> P k) -> P n) ->
  forall n i, i <= n -> P i.
Proof.
(intros P H).
(induction n).
-
(intros i H0).
(assert (i0 : i = 0)).
{
(inversion H0).
reflexivity.
}
subst.
(apply H).
(intros).
(absurd False; [ auto | inversion H1 ]).
-
(intros i Hi).
(apply H).
(intros k Hk).
(apply IHn).
(apply (lt_leS_le _ _ _ Hk Hi)).
Defined.
Theorem strong_induction :
  forall P : nat -> Type,
  (forall n : nat, (forall k : nat, k < n -> P k) -> P n) -> forall n : nat, P n.
Proof.
(intros P H n).
(apply (strong_induction' P H n)).
constructor.
Defined.
Transparent strong_induction.
Lemma le_hprop : forall (a b : nat) (pf1 pf2 : a <= b), pf1 = pf2.
Proof.
(induction a as [| a]; induction b as [| b]; intros pf1 pf2).
*
dependent destruction pf1.
dependent destruction pf2.
reflexivity.
*
dependent destruction pf1.
dependent destruction pf2.
(apply f_equal).
(apply IHb).
*
dependent destruction pf1.
*
dependent destruction pf1.
+
dependent destruction pf2.
++
reflexivity.
++
omega.
+
dependent destruction pf2.
++
omega.
++
(apply f_equal).
(apply IHb).
Qed.
Lemma lt_hprop : forall (a b : nat) (pf1 pf2 : a < b), pf1 = pf2.
Proof.
(intros).
(apply le_hprop).
Qed.
Lemma False_hprop : forall pf1 pf2 : False, pf1 = pf2.
Proof.
(destruct pf1).
Qed.
Lemma nat_neq_hprop : forall (m n : nat) (pf1 pf2 : m <> n), pf1 = pf2.
Proof.
(intros m n pf1 pf2).
(apply functional_extensionality).
(intros pf_eq).
(apply False_hprop).
Qed.
Definition CNOT_at_i0 (n j : nat) (pf_j : 0 < j) (pf_n : j < n) :
  Box (n \226\168\130 Qubit) (n \226\168\130 Qubit).
Proof.
gen n.
(induction j as [| [| j']]; intros n pf_n).
*
omega.
*
(destruct n as [| [| n']]; try omega).
exact
 (box_ q \226\135\146 (let_ (q0, (q1, qs))\226\134\144 q; let_ (q0, q1)\226\134\144 CNOT $ (q0, q1); (q0, (q1, qs)))).
*
(destruct n as [| [| n']]; try omega).
refine
 (box_ q
  \226\135\146 (let_ (q0, (q1, qs))\226\134\144 q;
     let_ (q0, qs)\226\134\144 IHj _ (S n') _ $ (q0, qs); (q0, (q1, qs)))).
+
(apply Nat.lt_0_succ).
+
(apply lt_S_n).
auto.
Defined.
Lemma CNOT_at_i0_WT :
  forall (n j : nat) (pf_j : 0 < j) (pf_n : j < n),
  Typed_Box (CNOT_at_i0 n j pf_j pf_n).
Proof.
(intros n j pf_j).
gen n.
(induction j as [| [| j']]; intros n pf_n).
*
(absurd False; auto).
(inversion pf_j).
*
(destruct n as [| [| n']]).
{
(absurd False; auto).
(inversion pf_n).
}
{
(absurd False; auto).
(inversion pf_n).
(inversion H0).
}
(simpl).
type_check.
*
(destruct n as [| [| n']]).
{
(absurd False; auto).
(inversion pf_n).
}
{
(absurd False; auto).
(inversion pf_n).
(inversion H0).
}
(set (pf_j' := Nat.lt_0_succ _ : 0 < S j')).
(set (pf_n' := lt_S_n _ _ pf_n : S j' < S n')).
(assert (IH : Typed_Box (CNOT_at_i0 (S n') (S j') pf_j' pf_n'))).
{
(intros).
(apply IHj).
}
clear IHj.
type_check.
Qed.
Lemma CNOT_at_i0_SS :
  forall n j (pfj : 0 < S (S j)) (pfj' : 0 < S j) (pfn : S (S j) < S (S n))
    (pfn' : S j < S n),
  CNOT_at_i0 (S (S n)) (S (S j)) pfj pfn =
  box_ q
  \226\135\146 (let_ (q0, (q1, qs))\226\134\144 q;
     let_ (q0, qs)\226\134\144 CNOT_at_i0 (S n) (S j) pfj' pfn' $ (q0, qs); (q0, (q1, qs))).
Proof.
(intros).
(simpl).
replace (lt_S_n (S j) (S n) pfn) with pfn'.
(simpl).
replace pfj' with Nat.lt_0_succ j.
reflexivity.
*
(apply lt_hprop).
*
(apply lt_hprop).
Qed.
Definition CNOT_at_j0 (n i : nat) (pf_j : 0 < i) (pf_n : i < n) :
  Box (n \226\168\130 Qubit) (n \226\168\130 Qubit).
Proof.
gen n.
(induction i as [| [| i']]; intros n pf_n).
*
omega.
*
(destruct n as [| [| n']]; try omega).
exact
 (box_ q \226\135\146 (let_ (q0, (q1, qs))\226\134\144 q; let_ (q1, q0)\226\134\144 CNOT $ (q1, q0); (q0, (q1, qs)))).
*
(destruct n as [| [| n']]; try omega).
refine
 (box_ q
  \226\135\146 (let_ (q0, (q1, qs))\226\134\144 q;
     let_ (q0, qs)\226\134\144 IHi _ (S n') _ $ (q0, qs); (q0, (q1, qs)))).
+
(apply Nat.lt_0_succ).
+
(apply lt_S_n).
auto.
Defined.
Lemma CNOT_at_j0_WT :
  forall (n i : nat) (pf_i : 0 < i) (pf_n : i < n),
  Typed_Box (CNOT_at_j0 n i pf_i pf_n).
Proof.
(intros n i pf_i).
gen n.
(induction i as [| [| i']]; intros n pf_n).
*
omega.
*
(destruct n as [| [| n']]; try omega).
(simpl).
type_check.
*
(destruct n as [| [| n']]; try omega).
(set (pf_i' := Nat.lt_0_succ _ : 0 < S i')).
(set (pf_n' := lt_S_n _ _ pf_n : S i' < S n')).
specialize (IHi pf_i' _ pf_n').
type_check.
Qed.
Lemma CNOT_at_j0_SS :
  forall n i (pfi : 0 < S (S i)) (pfi' : 0 < S i) (pfn : S (S i) < S (S n))
    (pfn' : S i < S n),
  CNOT_at_j0 (S (S n)) (S (S i)) pfi pfn =
  box_ q
  \226\135\146 (let_ (q0, (q1, qs))\226\134\144 q;
     let_ (q0, qs)\226\134\144 CNOT_at_j0 (S n) (S i) pfi' pfn' $ (q0, qs); (q0, (q1, qs))).
Proof.
(intros).
(simpl).
replace (lt_S_n (S i) (S n) pfn) with pfn'.
(simpl).
replace pfi' with Nat.lt_0_succ i.
reflexivity.
*
(apply lt_hprop).
*
(apply lt_hprop).
Qed.
Definition CNOT_at' (n i j : nat) (pf_i : i < n) (pf_j : j < n) 
  (pf_i_j : i <> j) : Box (n \226\168\130 Qubit) (n \226\168\130 Qubit).
Proof.
dependent induction n.
-
omega.
-
(destruct i as [| i'], j as [| j']).
*
contradiction.
*
refine (CNOT_at_i0 (S n) (S j') _ pf_j).
+
(apply Nat.lt_0_succ).
*
refine (CNOT_at_j0 (S n) (S i') _ pf_i).
+
(apply Nat.lt_0_succ).
*
refine (box_ q \226\135\146 (let_ (q0, qs)\226\134\144 q; let_ qs \226\134\144 IHn i' j' _ _ _ $ qs; (q0, qs))).
+
(apply (lt_S_n _ _ pf_i)).
+
(apply (lt_S_n _ _ pf_j)).
+
(apply Nat.succ_inj_wd_neg).
(apply pf_i_j).
Defined.
Opaque CNOT_at_i0.
Opaque CNOT_at_j0.
Lemma CNOT_at'_WT :
  forall (n i j : nat) (pf_i : i < n) (pf_j : j < n) (pf_i_j : i <> j),
  Typed_Box (CNOT_at' n i j pf_i pf_j pf_i_j).
Proof.
(induction n; intros i j pf_i pf_j pf_i_j).
-
(absurd False; auto).
(inversion pf_i).
-
(destruct i as [| i'], j as [| j']).
*
contradiction.
*
(apply CNOT_at_i0_WT).
*
(apply CNOT_at_j0_WT).
*
(simpl).
(set (H' := Nat.succ_inj_wd_neg i' j')).
(destruct H' eqn:H'').
(set (IH := IHn i' j' (lt_S_n i' n pf_i) (lt_S_n j' n pf_j) (n0 pf_i_j))).
type_check.
Qed.
Definition CNOT_at (n i j : nat) : Box (n \226\168\130 Qubit) (n \226\168\130 Qubit).
(destruct (lt_dec i n) as [H_i_lt_n| H_i_ge_n]; [  | exact id_circ ]).
(destruct (lt_dec j n) as [H_j_lt_n| H_j_ge_n]; [  | exact id_circ ]).
(destruct (eq_nat_dec i j) as [H_i_j| H_i_j]; [ exact id_circ |  ]).
exact (CNOT_at' n i j H_i_lt_n H_j_lt_n H_i_j).
Defined.
Theorem CNOT_at_WT : forall n i j, Typed_Box (CNOT_at n i j).
Proof.
(intros n i j).
(unfold CNOT_at).
(destruct (lt_dec i n) as [H_i_lt_n| H_i_ge_n] eqn:H_i_n; [  | type_check ]).
(destruct (lt_dec j n) as [H_j_lt_n| H_j_ge_n] eqn:H_j_n; [  | type_check ]).
(destruct (eq_nat_dec i j) as [H_i_j| H_i_j] eqn:H_i_j'; [ type_check |  ]).
(apply CNOT_at'_WT).
Qed.
Lemma CNOT_at_0 : forall i j, CNOT_at 0 i j = id_circ.
Proof.
(intros i j).
(destruct i as [| i'], j as [| j']; compute; reflexivity).
Qed.
Lemma CNOT_at_1 : forall i j, CNOT_at 1 i j = id_circ.
Proof.
(intros i j).
(destruct i as [| i'], j as [| j']; compute; reflexivity).
Qed.
Lemma CNOT_at_n_0_SS :
  forall n' j',
  j' < n' ->
  CNOT_at (S (S n')) 0 (S (S j')) =
  box_ q
  \226\135\146 (let_ (q0, (q1, qs))\226\134\144 q;
     let_ (q0, qs)\226\134\144 CNOT_at (S n') 0 (S j') $ (q0, qs); (q0, (q1, qs))).
Proof.
(intros).
(unfold CNOT_at).
(simpl).
(destruct (lt_dec (S (S j')) (S (S n'))); [  | omega ]).
(destruct (lt_dec (S j') (S n')); [  | omega ]).
(erewrite CNOT_at_i0_SS).
reflexivity.
Qed.
Lemma CNOT_at_n_SS_0 :
  forall n' i',
  i' < n' ->
  CNOT_at (S (S n')) (S (S i')) 0 =
  box_ q
  \226\135\146 (let_ (q0, (q1, qs))\226\134\144 q;
     let_ (q0, qs)\226\134\144 CNOT_at (S n') (S i') 0 $ (q0, qs); (q0, (q1, qs))).
Proof.
(intros).
(unfold CNOT_at).
(simpl).
(destruct (lt_dec (S (S i')) (S (S n'))); [  | omega ]).
(destruct (lt_dec (S i') (S n')); [  | omega ]).
(erewrite CNOT_at_j0_SS).
reflexivity.
Qed.
Lemma CNOT_at_at' :
  forall n i j (pfi : i < n) (pfj : j < n) (pf_i_j : i <> j),
  CNOT_at n i j = CNOT_at' n i j pfi pfj pf_i_j.
Proof.
(intros).
(unfold CNOT_at).
(destruct (lt_dec i n); [  | omega ]).
(destruct (lt_dec j n); [  | omega ]).
(destruct (Nat.eq_dec i j); [ omega |  ]).
replace l with pfi by apply lt_hprop.
replace l0 with pfj by apply lt_hprop.
replace n0 with pf_i_j by apply nat_neq_hprop.
reflexivity.
Qed.
Lemma CNOT_at_n_S_S :
  forall n' i' j',
  i' < n' ->
  j' < n' ->
  i' <> j' ->
  CNOT_at (S n') (S i') (S j') =
  box_ q \226\135\146 (let_ (q0, qs)\226\134\144 q; let_ qs \226\134\144 CNOT_at n' i' j' $ qs; (q0, qs)).
Proof.
(intros n' i' j' pf_i pf_j pf_i_j).
(erewrite CNOT_at_at').
(simpl).
(erewrite CNOT_at_at').
reflexivity.
Unshelve.
*
omega.
*
omega.
*
omega.
Qed.
Definition TOF_at_ij01 (n k : nat) (pf_j : 1 < k) (pf_n : k < n) :
  Box (n \226\168\130 Qubit) (n \226\168\130 Qubit).
gen n.
(induction k as [| [| [| k]]]; intros; try omega).
-
(destruct n as [| [| [| n]]]; try omega).
exact
 (box_ q
  \226\135\146 (let_ (q0, (q1, (q2, qs)))\226\134\144 q;
     let_ (q0, (q1, q2))\226\134\144 CCNOT $ (q0, (q1, q2)); (q0, (q1, (q2, qs))))).
-
(destruct n as [| [| [| n]]]; try omega).
(refine
  (box_ q
   \226\135\146 (let_ (q0, (q1, (q2, qs)))\226\134\144 q;
      let_ (q0, (q1, qs))\226\134\144 IHk _ (S (S n)) _ $ (q0, (q1, qs)); (q0, (q1, (q2, qs)))));
  auto with arith).
Defined.
Lemma TOF_at_ij01_WT : forall n k pf_j pf_n, Typed_Box (TOF_at_ij01 n k pf_j pf_n).
Proof.
(intros n k).
gen n.
(induction k as [| [| [| k]]]; intros; destruct n as [| [| [| n]]]; try omega).
type_check.
(set (pf_j' := gt_le_S 1 (S (S k)) (lt_n_S 0 (S k) (Nat.lt_0_succ k)))).
(set (pf_n' := gt_le_S (S (S k)) (S (S n)) (gt_S_le (S (S (S k))) (S (S n)) pf_n))).
specialize (IHk _ pf_j' pf_n').
type_check.
Qed.
Definition TOF_at_ik01 (n j : nat) (pf_j : 1 < j) (pf_n : j < n) :
  Box (n \226\168\130 Qubit) (n \226\168\130 Qubit).
gen n.
(induction j as [| [| [| j]]]; intros; try omega).
-
(destruct n as [| [| [| n]]]; try omega).
exact
 (box_ q
  \226\135\146 (let_ (q0, (q1, (q2, qs)))\226\134\144 q;
     let_ (q0, (q2, q1))\226\134\144 CCNOT $ (q0, (q2, q1)); (q0, (q1, (q2, qs))))).
-
(destruct n as [| [| [| n]]]; try omega).
(refine
  (box_ q
   \226\135\146 (let_ (q0, (q1, (q2, qs)))\226\134\144 q;
      let_ (q0, (q1, qs))\226\134\144 IHj _ (S (S n)) _ $ (q0, (q1, qs)); (q0, (q1, (q2, qs)))));
  auto with arith).
Defined.
Lemma TOF_at_ik01_WT : forall n j pf_j pf_n, Typed_Box (TOF_at_ik01 n j pf_j pf_n).
Proof.
(intros n j).
gen n.
(induction j as [| [| [| j]]]; intros; destruct n as [| [| [| n]]]; try omega).
type_check.
(set (pf_j' := gt_le_S 1 (S (S j)) (lt_n_S 0 (S j) (Nat.lt_0_succ j)))).
(set (pf_n' := gt_le_S (S (S j)) (S (S n)) (gt_S_le (S (S (S j))) (S (S n)) pf_n))).
specialize (IHj _ pf_j' pf_n').
type_check.
Qed.
Definition TOF_at_ki01 (n j : nat) (pf_j : 1 < j) (pf_n : j < n) :
  Box (n \226\168\130 Qubit) (n \226\168\130 Qubit).
gen n.
(induction j as [| [| [| j]]]; intros; try omega).
-
(destruct n as [| [| [| n]]]; try omega).
exact
 (box_ q
  \226\135\146 (let_ (q0, (q1, (q2, qs)))\226\134\144 q;
     let_ (q1, (q2, q0))\226\134\144 CCNOT $ (q1, (q2, q0)); (q0, (q1, (q2, qs))))).
-
(destruct n as [| [| [| n]]]; try omega).
(refine
  (box_ q
   \226\135\146 (let_ (q0, (q1, (q2, qs)))\226\134\144 q;
      let_ (q0, (q1, qs))\226\134\144 IHj _ (S (S n)) _ $ (q0, (q1, qs)); (q0, (q1, (q2, qs)))));
  auto with arith).
Defined.
Lemma TOF_at_ki01_WT : forall n j pf_j pf_n, Typed_Box (TOF_at_ki01 n j pf_j pf_n).
Proof.
(intros n j).
gen n.
(induction j as [| [| [| j]]]; intros; destruct n as [| [| [| n]]]; try omega).
type_check.
(set (pf_j' := gt_le_S 1 (S (S j)) (lt_n_S 0 (S j) (Nat.lt_0_succ j)))).
(set (pf_n' := gt_le_S (S (S j)) (S (S n)) (gt_S_le (S (S (S j))) (S (S n)) pf_n))).
specialize (IHj _ pf_j' pf_n').
type_check.
Qed.
Definition TOF_at_i0 (n j k : nat) (pf_ij : 0 < j) (pf_ik : 0 < k) 
  (pf_jk : j <> k) (pf_jn : j < n) (pf_kn : k < n) : Box (n \226\168\130 Qubit) (n \226\168\130 Qubit).
gen n k.
(induction j as [| [| j]]; intros; try omega).
-
(apply (TOF_at_ij01 n k); omega).
-
gen n.
(destruct k as [| [| k]]; intros; try omega).
+
(apply (TOF_at_ik01 n (S (S j))); omega).
+
(destruct n as [| [| [| n]]]; try omega).
(refine
  (box_ q
   \226\135\146 (let_ (q0, (q1, qs))\226\134\144 q;
      let_ (q0, qs)\226\134\144 IHj _ (S (S n)) _ (S k) _ _ _ $ (q0, qs); (q0, (q1, qs))));
  auto with arith).
Defined.
Lemma TOF_at_i0_WT :
  forall n j k pf_ij pf_ik pf_jk pf_jn pf_kn,
  Typed_Box (TOF_at_i0 n j k pf_ij pf_ik pf_jk pf_jn pf_kn).
Proof.
(intros n j).
gen n.
(induction j as [| [| j]]; intros; try omega).
(apply TOF_at_ij01_WT).
(destruct k as [| [| k]]; intros; try omega).
(apply TOF_at_ik01_WT).
(destruct n as [| [| [| n]]]; try omega).
specialize (IHj (S (S n)) (S k)).
(epose (pf_ij' := _ : 0 < S j)).
(epose (pf_ik' := _ : 0 < S k)).
(epose (pf_jk' := _ : S j <> S k)).
(epose (pf_jn' := _ : S j < S (S n))).
(epose (pf_kn' := _ : S k < S (S n))).
Unshelve.
all: auto with arith.
specialize (IHj pf_ij' pf_ik' pf_jk' pf_jn' pf_kn').
type_check.
Qed.
Definition TOF_at_k0 (n i j : nat) (pf_ij : i < j) (pf_ik : 0 < i) 
  (pf_jk : 0 < j) (pf_in : i < n) (pf_jn : j < n) : Box (n \226\168\130 Qubit) (n \226\168\130 Qubit).
gen n j.
(induction i as [| [| i]]; intros; try omega).
-
(apply (TOF_at_ki01 n j); omega).
-
(destruct j as [| [| j]]; try omega).
(destruct n as [| [| [| n]]]; try omega).
(refine
  (box_ q
   \226\135\146 (let_ (q0, (q1, qs))\226\134\144 q;
      let_ (q0, qs)\226\134\144 IHi _ (S (S n)) _ (S j) _ _ _ $ (q0, qs); (q0, (q1, qs))));
  auto with arith).
Defined.
Lemma TOF_at_k0_WT :
  forall n i j pf_ij pf_ik pf_jk pf_in pf_jn,
  Typed_Box (TOF_at_k0 n i j pf_ij pf_ik pf_jk pf_in pf_jn).
Proof.
(intros n i).
gen n.
(induction i as [| [| i]]; intros; try omega).
(apply TOF_at_ki01_WT).
(destruct j as [| [| j]]; intros; try omega).
(destruct n as [| [| [| n]]]; try omega).
specialize (IHi (S (S n)) (S j)).
(epose (pf_ij' := _ : S i < S j)).
(epose (pf_ik' := _ : 0 < S i)).
(epose (pf_jk' := _ : 0 < S j)).
(epose (pf_in' := _ : S i < S (S n))).
(epose (pf_jn' := _ : S j < S (S n))).
Unshelve.
all: auto with arith.
specialize (IHi pf_ij' pf_ik' pf_jk' pf_in' pf_jn').
type_check.
Qed.
Definition Toffoli_at' (n : nat) (i j k : Var) (pf_i : i < n) 
  (pf_j : j < n) (pf_k : k < n) (pf_i_j : i <> j) (pf_i_k : i <> k)
  (pf_j_k : j <> k) : Box (n \226\168\130 Qubit) (n \226\168\130 Qubit).
gen i j k.
(induction n; intros; try omega).
(destruct i; [  | destruct j; [  | destruct k ] ]; try omega).
-
(apply (TOF_at_i0 (S n) j k); omega).
-
(apply (TOF_at_i0 (S n) (S i) k); omega).
-
(destruct (lt_dec i j)).
+
(apply (TOF_at_k0 (S n) (S i) (S j)); omega).
+
(apply (TOF_at_k0 (S n) (S j) (S i)); omega).
-
(refine
  (box_ q \226\135\146 (let_ (q0, qs)\226\134\144 q; let_ qs \226\134\144 IHn i _ j _ _ k _ _ _ $ qs; (q0, qs)));
  auto with arith).
Defined.
Lemma Toffoli_at'_WT :
  forall n (i j k : Var) (pf_i : i < n) (pf_j : j < n) (pf_k : k < n)
    (pf_i_j : i <> j) (pf_i_k : i <> k) (pf_j_k : j <> k),
  Typed_Box (Toffoli_at' n i j k pf_i pf_j pf_k pf_i_j pf_i_k pf_j_k).
Proof.
(induction n; intros; try omega).
(destruct i; [  | destruct j; [  | destruct k ] ]; try omega).
-
(apply TOF_at_i0_WT).
-
(apply TOF_at_i0_WT).
-
Opaque TOF_at_k0.
(simpl).
(destruct (lt_dec i j)).
+
(apply (TOF_at_k0_WT (S n) (S i) (S j))).
+
(apply (TOF_at_k0_WT (S n) (S j) (S i))).
-
(epose (pf_i' := _ : i < n)).
(epose (pf_j' := _ : j < n)).
(epose (pf_k' := _ : k < n)).
(epose (pf_i_j' := _ : i <> j)).
(epose (pf_i_k' := _ : i <> k)).
(epose (pf_j_k' := _ : j <> k)).
Unshelve.
all: auto with arith.
specialize (IHn i j k pf_i' pf_j' pf_k' pf_i_j' pf_i_k' pf_j_k').
type_check.
Qed.
Definition Toffoli_at n (i j k : Var) : Box (n \226\168\130 Qubit) (n \226\168\130 Qubit).
(destruct (lt_dec i n) as [H_i_lt_n| H_i_ge_n]; [  | exact id_circ ]).
(destruct (lt_dec j n) as [H_j_lt_n| H_j_ge_n]; [  | exact id_circ ]).
(destruct (lt_dec k n) as [H_k_lt_n| H_k_ge_n]; [  | exact id_circ ]).
(destruct (eq_nat_dec i j) as [H_i_j| H_i_j]; [ exact id_circ |  ]).
(destruct (eq_nat_dec i k) as [H_i_k| H_i_k]; [ exact id_circ |  ]).
(destruct (eq_nat_dec j k) as [H_j_k| H_j_k]; [ exact id_circ |  ]).
exact (Toffoli_at' n i j k H_i_lt_n H_j_lt_n H_k_lt_n H_i_j H_i_k H_j_k).
Defined.
Lemma Toffoli_at_WT : forall n (i j k : Var), Typed_Box (Toffoli_at n i j k).
Proof.
(intros n i j k).
(unfold Toffoli_at).
(destruct (lt_dec i n); [  | type_check ]).
(destruct (lt_dec j n); [  | type_check ]).
(destruct (lt_dec k n); [  | type_check ]).
(destruct (eq_nat_dec i j); [ type_check |  ]).
(destruct (eq_nat_dec i k); [ type_check |  ]).
(destruct (eq_nat_dec j k); [ type_check |  ]).
(apply Toffoli_at'_WT).
Qed.
Definition strip_one_l_in {W W' : WType} (c : Box (One \226\138\151 W) W') : 
  Box W W' := box (fun p => c $ ((), p)).
Lemma strip_one_l_in_WT :
  forall W W' (c : Box (One \226\138\151 W) W'), Typed_Box c -> Typed_Box (strip_one_l_in c).
Proof.
type_check.
Qed.
Lemma strip_one_l_in_eq :
  forall W W' (c : Box (One \226\138\151 W) W') (\207\129 : Matrix (2 ^ \226\159\166 W \226\159\167)%nat (2 ^ \226\159\166 W' \226\159\167)%nat),
  denote_box true (strip_one_l_in c) \207\129 = denote_box true c \207\129.
Proof.
(intros).
(unfold strip_one_l_in).
matrix_denote.
(unfold unbox).
(unfold denote_db_box).
(destruct c).
(simpl).
(rewrite add_fresh_split).
reflexivity.
Qed.
Definition strip_one_l_out {W W' : WType} (c : Box W (One \226\138\151 W')) : 
  Box W W' := box_ p \226\135\146 (let_ (_, p')\226\134\144 unbox c p; p').
Lemma strip_one_l_out_WT :
  forall W W' (c : Box W (One \226\138\151 W')), Typed_Box c -> Typed_Box (strip_one_l_out c).
Proof.
type_check.
Qed.
Fact strip_one_l_out_eq :
  forall W W' (c : Box W (One \226\138\151 W')) (\207\129 : Matrix (2 ^ \226\159\166 W \226\159\167)%nat (2 ^ \226\159\166 W' \226\159\167)%nat),
  denote_box true (strip_one_l_out c) \207\129 = denote_box true c \207\129.
Proof.
(intros).
(unfold strip_one_l_out).
matrix_denote.
(unfold unbox).
(unfold denote_db_box).
(destruct c).
(simpl).
(rewrite add_fresh_split).
(simpl).
Admitted.
Definition strip_one_r_in {W W' : WType} (c : Box (W \226\138\151 One) W') : 
  Box W W' := box (fun p => c $ (p, ())).
Lemma strip_one_r_in_WT :
  forall W W' (c : Box (W \226\138\151 One) W'), Typed_Box c -> Typed_Box (strip_one_r_in c).
Proof.
type_check.
Qed.
Lemma strip_one_r_in_eq :
  forall W W' (c : Box (W \226\138\151 One) W') (\207\129 : Matrix (2 ^ \226\159\166 W \226\159\167)%nat (2 ^ \226\159\166 W' \226\159\167)%nat),
  denote_box true (strip_one_r_in c) \207\129 = denote_box true c \207\129.
Proof.
(intros).
(unfold strip_one_r_in).
matrix_denote.
(unfold unbox).
(unfold denote_db_box).
(destruct c).
(simpl).
(rewrite Nat.add_0_r).
(rewrite add_fresh_split).
reflexivity.
Qed.
Definition strip_one_r_out {W W' : WType} (c : Box W (W' \226\138\151 One)) : 
  Box W W' := box_ p \226\135\146 (let_ (p', _)\226\134\144 c $ p; p').
Lemma strip_one_r_out_WT :
  forall W W' (c : Box W (W' \226\138\151 One)), Typed_Box c -> Typed_Box (strip_one_r_out c).
Proof.
type_check.
Qed.
Fact strip_one_r_out_eq :
  forall W W' (c : Box W (W' \226\138\151 One)) (\207\129 : Matrix (2 ^ \226\159\166 W \226\159\167)%nat (2 ^ \226\159\166 W' \226\159\167)%nat),
  denote_box true (strip_one_r_out c) \207\129 = denote_box true c \207\129.
Proof.
(intros).
(unfold strip_one_r_out).
matrix_denote.
(unfold unbox).
(unfold denote_db_box).
(destruct c).
(simpl).
(rewrite add_fresh_split).
Admitted.
Fixpoint assert_at (b : bool) (n i : nat) {struct i} : Box (S n \226\168\130 Qubit) (n \226\168\130 Qubit)
:=
  match i with
  | 0 => strip_one_l_out (assert b \226\136\165 id_circ)
  | S i' =>
      match n with
      | 0 => strip_one_l_out (assert b \226\136\165 id_circ)
      | S n' => id_circ \226\136\165 assert_at b n' i'
      end
  end.
Lemma assert_at_WT : forall b n i, Typed_Box (assert_at b n i).
Proof.
(intros b n i).
gen n.
(induction i).
-
type_check.
-
(destruct n; simpl).
+
type_check.
+
(apply inPar_WT).
type_check.
(apply IHi).
Qed.
Fixpoint init_at (b : bool) (n i : nat) {struct i} : Box (n \226\168\130 Qubit) (S n \226\168\130 Qubit)
:=
  match i with
  | 0 => strip_one_l_in (init b \226\136\165 id_circ)
  | S i' =>
      match n with
      | 0 => strip_one_l_in (init b \226\136\165 id_circ)
      | S n' => id_circ \226\136\165 init_at b n' i'
      end
  end.
Lemma init_at_WT : forall b n i, Typed_Box (init_at b n i).
Proof.
(intros b n i).
gen n.
(induction i).
-
type_check.
-
(destruct n; simpl).
+
type_check.
+
(apply inPar_WT).
type_check.
(apply IHi).
Qed.
Definition in_scope (n t i : nat) := i < n + t.
Definition in_target (n t i : nat) := n <= i.
Definition in_source (n t i : nat) := i < n.
Lemma in_source_in_scope : forall n t i, in_source n t i -> in_scope n t i.
Proof.
(intros).
(apply lt_le_trans with (m := n); auto).
omega.
Qed.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Inductive source_symmetric :
forall n t, Box ((n + t) \226\168\130 Qubit) ((n + t) \226\168\130 Qubit) -> Set :=
  | sym_id : forall n t, source_symmetric n t id_circ
  | sym_gate :
      forall n t k c g,
      gate_acts_on k g -> source_symmetric n t c -> source_symmetric n t (g \194\183 c \194\183 g)
  | target_gate_l :
      forall n t k c g,
      gate_acts_on k g ->
      source_symmetric n t c -> n <= k -> source_symmetric n t (g \194\183 c)
  | target_gate_r :
      forall n t k c g,
      gate_acts_on k g ->
      source_symmetric n t c -> n <= k -> source_symmetric n t (c \194\183 g)
  | sym_ancilla :
      forall n t c b i,
      i < n ->
      source_symmetric (S n) t c ->
      source_symmetric n t (assert_at b (n + t) i \194\183 c \194\183 init_at b (n + t) i).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Lemma symmetric_reverse_symmetric :
  forall n t c (pf_sym : source_symmetric n t c),
  source_symmetric n t (symmetric_reverse n t c pf_sym).
Proof.
(induction pf_sym).
-
(apply sym_id).
-
(eapply sym_gate; eauto).
-
(apply target_gate_r with (k := k); auto).
-
(apply target_gate_l with (k := k); auto).
-
(apply sym_ancilla; auto).
Defined.
Hint Resolve unitary_at1_WT X_at_WT CNOT_at_WT Toffoli_at_WT init_at_WT
  assert_at_WT: typed_db.
Lemma gate_acts_on_WT :
  forall m (g : Box (m \226\168\130 Qubit) (m \226\168\130 Qubit)) k, gate_acts_on k g -> Typed_Box g.
Proof.
(intros m g k pf_g).
(destruct pf_g; type_check).
Qed.
Lemma source_symmetric_WT : forall n t c, source_symmetric n t c -> Typed_Box c.
Proof.
(intros n t c H).
(induction H; try (solve [ type_check ])).
-
(inversion g0; type_check).
-
(inversion g0; type_check).
-
(inversion g0; type_check).
Qed.
Definition noop_on (m i : nat) (c : Square_Box (S m \226\168\130 Qubit)) : Prop :=
  forall b, valid_ancillae_box' (assert_at b m i \194\183 c \194\183 init_at b m i).
Definition noop_source (n t : nat) : Square_Box ((n + t) \226\168\130 Qubit) -> Prop :=
  match n with
  | 0 => fun _ => True
  | S n' => fun c => forall i, i < S n' -> noop_on _ i c
  end.
Fact gate_acts_on_noop_at :
  forall m g k i, @gate_acts_on (S m) k g -> i <> k -> i < S m -> noop_on m i g.
Proof.
(intros m g k i pf_g pf_i_k pf_i).
dependent destruction pf_g.
*
admit.
*
admit.
*
admit.
Admitted.
Lemma fresh_state_ntensor :
  forall n (\206\147 : Ctx),
  add_fresh_state (n \226\168\130 Qubit) \206\147 = \206\147 ++ List.repeat (Some Qubit) n.
Proof.
(induction n).
-
(intros).
(simpl).
(rewrite app_nil_r; reflexivity).
-
(intros).
(simpl).
(unfold add_fresh_state in *).
(simpl).
specialize (IHn (\206\147 ++ [Some Qubit])).
(rewrite add_fresh_split in *).
(simpl in *).
(rewrite IHn).
(rewrite <- app_assoc).
reflexivity.
Qed.
Open Scope matrix_scope.
Fact init_at_spec_strong :
  forall b n i (\207\129 : Square (2 ^ n)) (safe : bool),
  i <= n ->
  denote_box safe (init_at b n i) \207\129 =
  I (2 ^ i) \226\138\151 bool_to_ket b \226\138\151 I (2 ^ (n - i)) \195\151 \207\129
  \195\151 (I (2 ^ i) \226\138\151 (bool_to_ket b) \226\128\160 \226\138\151 I (2 ^ (n - i))).
Proof.
Admitted.
Fact assert_at_spec_safe :
  forall b n i (\207\129 : Square (2 ^ n)),
  i <= n ->
  denote_box true (assert_at b n i) \207\129 =
  I (2 ^ i) \226\138\151 \226\159\1680\226\136\163 \226\138\151 I (2 ^ (n - i)) \195\151 \207\129 \195\151 (I (2 ^ i) \226\138\151 \226\136\1630\226\159\169 \226\138\151 I (2 ^ (n - i)))
  .+ I (2 ^ i) \226\138\151 \226\159\1681\226\136\163 \226\138\151 I (2 ^ (n - i)) \195\151 \207\129 \195\151 (I (2 ^ i) \226\138\151 \226\136\1631\226\159\169 \226\138\151 I (2 ^ (n - i))).
Admitted.
Fact assert_at_spec_unsafe :
  forall b n i (\207\129 : Square (2 ^ n)),
  i <= n ->
  denote_box false (assert_at b n i) \207\129 =
  I (2 ^ i) \226\138\151 (bool_to_ket b) \226\128\160 \226\138\151 I (2 ^ (n - i)) \195\151 \207\129
  \195\151 (I (2 ^ i) \226\138\151 bool_to_ket b \226\138\151 I (2 ^ (n - i))).
Admitted.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqqi4Q9u"
Print Ltac Signatures.
