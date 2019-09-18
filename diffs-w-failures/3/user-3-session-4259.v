Time From stdpp Require Import numbers.
Time Class NatCancel (m n m' n' : nat) :=
         nat_cancel : m' + n = m + n'.
Time Hint Mode NatCancel ! ! - -: typeclass_instances.
Time Module nat_cancel.
Time Class NatCancelL (m n m' n' : nat) :=
         nat_cancel_l : m' + n = m + n'.
Time Hint Mode NatCancelL ! ! - -: typeclass_instances.
Time
Class NatCancelR (m n m' n' : nat) :=
    nat_cancel_r : NatCancelL m n m' n'.
Time Hint Mode NatCancelR ! ! - -: typeclass_instances.
Time Existing Instance nat_cancel_r |100.
Time
Instance nat_cancel_start  m n m' n':
 (TCNoBackTrack (NatCancelL m n m' n') \226\134\146 NatCancel m n m' n').
Time Proof.
Time by intros [?].
Time Qed.
Time Class MakeNatS (n1 n2 m : nat) :=
         make_nat_S : m = n1 + n2.
Time Instance make_nat_S_0_l  n: (MakeNatS 0 n n).
Time Proof.
Time done.
Time Qed.
Time Instance make_nat_S_1  n: (MakeNatS 1 n (S n)).
Time Proof.
Time done.
Time Qed.
Time Class MakeNatPlus (n1 n2 m : nat) :=
         make_nat_plus : m = n1 + n2.
Time Instance make_nat_plus_0_l  n: (MakeNatPlus 0 n n).
Time Proof.
Time done.
Time Qed.
Time Instance make_nat_plus_0_r  n: (MakeNatPlus n 0 n).
Time Proof.
Time (unfold MakeNatPlus).
Time by rewrite Nat.add_0_r.
Time Qed.
Time
Instance make_nat_plus_default  n1 n2: (MakeNatPlus n1 n2 (n1 + n2)) |100.
Time Proof.
Time done.
Time Qed.
Time Instance nat_cancel_leaf_here  m: (NatCancelR m m 0 0) |0.
Time Proof.
Time by unfold NatCancelR, NatCancelL.
Time Qed.
Time Instance nat_cancel_leaf_else  m n: (NatCancelR m n m n) |100.
Time Proof.
Time by unfold NatCancelR.
Time Qed.
Time
Instance nat_cancel_leaf_plus  m m' m'' n1 n2 n1' 
 n2' n1'n2':
 (NatCancelR m n1 m' n1'
  \226\134\146 NatCancelR m' n2 m'' n2'
    \226\134\146 MakeNatPlus n1' n2' n1'n2' \226\134\146 NatCancelR m (n1 + n2) m'' n1'n2') |2.
Time Proof.
Time (unfold NatCancelR, NatCancelL, MakeNatPlus).
Time lia.
Time Qed.
Time
Instance nat_cancel_leaf_S_here  m n m' n':
 (NatCancelR m n m' n' \226\134\146 NatCancelR (S m) (S n) m' n') |3.
Time Proof.
Time (unfold NatCancelR, NatCancelL).
Time lia.
Time Qed.
Time
Instance nat_cancel_leaf_S_else  m n m' n':
 (NatCancelR m n m' n' \226\134\146 NatCancelR m (S n) m' (S n')) |4.
Time Proof.
Time (unfold NatCancelR, NatCancelL).
Time lia.
Time Qed.
Time
Instance nat_cancel_S_both  m n m' n':
 (NatCancelL m n m' n' \226\134\146 NatCancelL (S m) (S n) m' n') |1.
Time Proof.
Time (unfold NatCancelL).
Time lia.
Time Qed.
Time
Instance nat_cancel_plus  m1 m2 m1' m2' m1'm2' n n' 
 n'':
 (NatCancelL m1 n m1' n'
  \226\134\146 NatCancelL m2 n' m2' n''
    \226\134\146 MakeNatPlus m1' m2' m1'm2' \226\134\146 NatCancelL (m1 + m2) n m1'm2' n'') |2.
Time Proof.
Time (unfold NatCancelL, MakeNatPlus).
Time lia.
Time Qed.
Time
Instance nat_cancel_S  m m' m'' Sm' n n' n'':
 (NatCancelL m n m' n'
  \226\134\146 NatCancelR 1 n' m'' n''
    \226\134\146 MakeNatS m'' m' Sm' \226\134\146 NatCancelL (S m) n Sm' n'') |3.
Time Proof.
Time (unfold NatCancelR, NatCancelL, MakeNatS).
Time lia.
Time Qed.
Time End nat_cancel.
