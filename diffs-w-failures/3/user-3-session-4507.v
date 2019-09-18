Time From stdpp Require Import numbers.
Time From stdpp Require Import numbers.
Time Class NatCancel (m n m' n' : nat) :=
         nat_cancel : m' + n = m + n'.
Time Set Default Proof Using "Type".
Time
Notation cast_trichotomy T:=
  match T with
  | inleft (left _) => inleft (left _)
  | inleft (right _) => inleft (right _)
  | inright _ => inright _
  end.
Time
Instance prod_lexico  `{Lexico A} `{Lexico B}: (Lexico (A * B)) :=
 (\206\187 p1 p2, lexico p1.1 p2.1 \226\136\168 p1.1 = p2.1 \226\136\167 lexico p1.2 p2.2).
Time
Instance bool_lexico : (Lexico bool) :=
 (\206\187 b1 b2, match b1, b2 with
           | false, true => True
           | _, _ => False
           end).
Time Instance nat_lexico : (Lexico nat) := (<).
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
Time Instance N_lexico : (Lexico N) := (<)%N.
Time Instance Z_lexico : (Lexico Z) := (<)%Z.
Time Typeclasses Opaque bool_lexico nat_lexico N_lexico Z_lexico.
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
Time
Instance list_lexico  `{Lexico A}: (Lexico (list A)) :=
 (fix go l1 l2 :=
    let _ : Lexico (list A) := @go in
    match l1, l2 with
    | [], _ :: _ => True
    | x1 :: l1, x2 :: l2 => lexico (x1, l1) (x2, l2)
    | _, _ => False
    end).
Time Instance make_nat_plus_0_l  n: (MakeNatPlus 0 n n).
Time Proof.
Time done.
Time Qed.
Time Instance make_nat_plus_0_r  n: (MakeNatPlus n 0 n).
Time Proof.
Time
Instance sig_lexico  `{Lexico A} (P : A \226\134\146 Prop) `{\226\136\128 x, ProofIrrel (P x)}:
 (Lexico (sig P)) := (\206\187 x1 x2, lexico (`x1) (`x2)).
Time
Lemma prod_lexico_irreflexive `{Lexico A} `{Lexico B}
  `{!Irreflexive (@lexico A _)} (x : A) (y : B) :
  complement lexico y y \226\134\146 complement lexico (x, y) (x, y).
Time Proof.
Time (intros ? [?| [? ?]]).
Time by apply (irreflexivity lexico x).
Time done.
Time Qed.
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
Time
Lemma prod_lexico_transitive `{Lexico A} `{Lexico B}
  `{!Transitive (@lexico A _)} (x1 x2 x3 : A) (y1 y2 y3 : B) :
  lexico (x1, y1) (x2, y2)
  \226\134\146 lexico (x2, y2) (x3, y3)
    \226\134\146 (lexico y1 y2 \226\134\146 lexico y2 y3 \226\134\146 lexico y1 y3) \226\134\146 lexico (x1, y1) (x3, y3).
Time Proof.
Time (intros Hx12 Hx23 ?; revert Hx12 Hx23).
Time (unfold lexico, prod_lexico).
Time (intros [| [? ?]] [?| [? ?]]; simplify_eq /=; auto).
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
Time by left; trans x2.
Time Qed.
Time
Instance prod_lexico_po  `{Lexico A} `{Lexico B}
 `{!StrictOrder (@lexico A _)} `{!StrictOrder (@lexico B _)}:
 (StrictOrder (@lexico (A * B) _)).
Time Proof.
Time split.
Time -
Time (intros [x y]).
Time (apply prod_lexico_irreflexive).
Time by apply (irreflexivity lexico y).
Time -
Time (intros [? ?] [? ?] [? ?] ? ?).
Time (eapply prod_lexico_transitive; eauto).
Time (apply transitivity).
Time Qed.
Time
Instance prod_lexico_trichotomyT  `{Lexico A}
 `{tA : !TrichotomyT (@lexico A _)} `{Lexico B}
 `{tB : !TrichotomyT (@lexico B _)}: (TrichotomyT (@lexico (A * B) _)).
Time Proof.
Time
(red; refine
  (\206\187 p1 p2,
     match trichotomyT lexico p1.1 p2.1 with
     | inleft (left _) => inleft (left _)
     | inleft (right _) => cast_trichotomy (trichotomyT lexico p1.2 p2.2)
     | inright _ => inright _
     end); clear tA tB;
  abstract (unfold lexico, prod_lexico; auto using injective_projections)).
Time Defined.
Time Instance bool_lexico_po : (StrictOrder (@lexico bool _)).
Time Proof.
Time split.
Time by intros [] ?.
Time by intros [] [] [] ? ?.
Time Qed.
Time Instance bool_lexico_trichotomy : (TrichotomyT (@lexico bool _)).
Time Proof.
Time
(red; refine
  (\206\187 b1 b2,
     match b1, b2 with
     | false, false => inleft (right _)
     | false, true => inleft (left _)
     | true, false => inright _
     | true, true => inleft (right _)
     end); abstract (unfold strict, lexico, bool_lexico; naive_solver)).
Time Defined.
Time Instance nat_lexico_po : (StrictOrder (@lexico nat _)).
Time Proof.
Time (unfold lexico, nat_lexico).
Time (apply _).
Time Qed.
Time Instance nat_lexico_trichotomy : (TrichotomyT (@lexico nat _)).
Time Proof.
Time
(red; refine
  (\206\187 n1 n2,
     match Nat.compare n1 n2 as c return (Nat.compare n1 n2 = c \226\134\146 _) with
     | Lt => \206\187 H, inleft (left (nat_compare_Lt_lt _ _ H))
     | Eq => \206\187 H, inleft (right (nat_compare_eq _ _ H))
     | Gt => \206\187 H, inright (nat_compare_Gt_gt _ _ H)
     end eq_refl)).
Time Defined.
Time Instance N_lexico_po : (StrictOrder (@lexico N _)).
Time Proof.
Time (unfold lexico, N_lexico).
Time (apply _).
Time Qed.
Time Instance N_lexico_trichotomy : (TrichotomyT (@lexico N _)).
Time Proof.
Time
(red; refine
  (\206\187 n1 n2,
     match N.compare n1 n2 as c return (N.compare n1 n2 = c \226\134\146 _) with
     | Lt => \206\187 H, inleft (left (proj2 (N.compare_lt_iff _ _) H))
     | Eq => \206\187 H, inleft (right (N.compare_eq _ _ H))
     | Gt => \206\187 H, inright (proj1 (N.compare_gt_iff _ _) H)
     end eq_refl)).
Time Defined.
Time Instance Z_lexico_po : (StrictOrder (@lexico Z _)).
Time Proof.
Time (unfold lexico, Z_lexico).
Time (apply _).
Time Qed.
Time Instance Z_lexico_trichotomy : (TrichotomyT (@lexico Z _)).
Time Proof.
Time Qed.
Time
(red; refine
  (\206\187 n1 n2,
     match Z.compare n1 n2 as c return (Z.compare n1 n2 = c \226\134\146 _) with
     | Lt => \206\187 H, inleft (left (proj2 (Z.compare_lt_iff _ _) H))
     | Eq => \206\187 H, inleft (right (Z.compare_eq _ _ H))
     | Gt => \206\187 H, inright (proj1 (Z.compare_gt_iff _ _) H)
     end eq_refl)).
Time Defined.
Time
Instance list_lexico_po  `{Lexico A} `{!StrictOrder (@lexico A _)}:
 (StrictOrder (@lexico (list A) _)).
Time Proof.
Time split.
Time -
Time (intros l).
Time (induction l).
Time by intros ?.
Time by apply prod_lexico_irreflexive.
Time -
Time (intros l1).
Time (induction l1 as [| x1 l1]; intros [| x2 l2] [| x3 l3] ? ?; try done).
Time
Instance nat_cancel_leaf_S_here  m n m' n':
 (NatCancelR m n m' n' \226\134\146 NatCancelR (S m) (S n) m' n') |3.
Time Proof.
Time (unfold NatCancelR, NatCancelL).
Time lia.
Time (eapply prod_lexico_transitive; eauto).
Time Qed.
Time
Instance nat_cancel_leaf_S_else  m n m' n':
 (NatCancelR m n m' n' \226\134\146 NatCancelR m (S n) m' (S n')) |4.
Time Proof.
Time (unfold NatCancelR, NatCancelL).
Time lia.
Time Qed.
Time
Instance list_lexico_trichotomy  `{Lexico A}
 `{tA : !TrichotomyT (@lexico A _)}: (TrichotomyT (@lexico (list A) _)).
Time Proof.
Time
(refine
  (fix go l1 l2 :=
     let go' : TrichotomyT (@lexico (list A) _) := @go in
     match l1, l2 with
     | [], [] => inleft (right _)
     | [], _ :: _ => inleft (left _)
     | _ :: _, [] => inright _
     | x1 :: l1, x2 :: l2 =>
         cast_trichotomy (trichotomyT lexico (x1, l1) (x2, l2))
     end); clear tA go go';
  abstract (repeat done || constructor || congruence || by inversion 1)).
Time Qed.
Time
Instance nat_cancel_S_both  m n m' n':
 (NatCancelL m n m' n' \226\134\146 NatCancelL (S m) (S n) m' n') |1.
Time Proof.
Time (unfold NatCancelL).
Time lia.
Time Defined.
Time
Instance sig_lexico_po  `{Lexico A} `{!StrictOrder (@lexico A _)}
 (P : A \226\134\146 Prop) `{\226\136\128 x, ProofIrrel (P x)}: (StrictOrder (@lexico (sig P) _)).
Time Proof.
Time (unfold lexico, sig_lexico).
Time split.
Time -
Time (intros [x ?] ?).
Time by apply (irreflexivity lexico x).
Time -
Time (intros [x1 ?] [x2 ?] [x3 ?] ? ?).
Time by trans x2.
Time Qed.
Time
Instance sig_lexico_trichotomy  `{Lexico A}
 `{tA : !TrichotomyT (@lexico A _)} (P : A \226\134\146 Prop) 
 `{\226\136\128 x, ProofIrrel (P x)}: (TrichotomyT (@lexico (sig P) _)).
Time Qed.
Time
Instance nat_cancel_plus  m1 m2 m1' m2' m1'm2' n n' 
 n'':
 (NatCancelL m1 n m1' n'
  \226\134\146 NatCancelL m2 n' m2' n''
    \226\134\146 MakeNatPlus m1' m2' m1'm2' \226\134\146 NatCancelL (m1 + m2) n m1'm2' n'') |2.
Time Proof.
Time
(red; refine (\206\187 x1 x2, cast_trichotomy (trichotomyT lexico (`x1) (`x2)));
  abstract (repeat done || constructor || apply (sig_eq_pi P))).
Time Defined.
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
