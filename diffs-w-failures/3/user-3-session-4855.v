Time From Coq Require Export EqdepFacts PArith NArith ZArith NPeano.
Time From Coq Require Import QArith Qcanon.
Time From stdpp Require Export base decidable option.
Time Set Default Proof Using "Type".
Time Open Scope nat_scope.
Time Coercion Z.of_nat : nat >-> Z.
Time Instance comparison_eq_dec : (EqDecision comparison).
Time Proof.
Time solve_decision.
Time Defined.
Time Arguments minus !_ !_ / : assert.
Time Arguments Nat.max : simpl nomatch.
Time Typeclasses Opaque lt.
Time Reserved Notation "x \226\137\164 y \226\137\164 z" (at level 70, y  at next level).
Time Reserved Notation "x \226\137\164 y < z" (at level 70, y  at next level).
Time Reserved Notation "x < y < z" (at level 70, y  at next level).
Time Reserved Notation "x < y \226\137\164 z" (at level 70, y  at next level).
Time Reserved Notation "x \226\137\164 y \226\137\164 z \226\137\164 z'"
(at level 70, y  at next level, z  at next level).
Time Infix "\226\137\164" := le : nat_scope.
Time Notation "x \226\137\164 y \226\137\164 z" := (x \226\137\164 y \226\136\167 y \226\137\164 z)%nat : nat_scope.
Time Notation "x \226\137\164 y < z" := (x \226\137\164 y \226\136\167 y < z)%nat : nat_scope.
Time Notation "x < y \226\137\164 z" := (x < y \226\136\167 y \226\137\164 z)%nat : nat_scope.
Time Notation "x \226\137\164 y \226\137\164 z \226\137\164 z'" := (x \226\137\164 y \226\136\167 y \226\137\164 z \226\136\167 z \226\137\164 z')%nat : nat_scope.
Time Notation "(\226\137\164)" := le (only parsing) : nat_scope.
Time Notation "(<)" := lt (only parsing) : nat_scope.
Time Infix "`div`" := Nat.div (at level 35) : nat_scope.
Time Infix "`mod`" := Nat.modulo (at level 35) : nat_scope.
Time Infix "`max`" := Nat.max (at level 35) : nat_scope.
Time Infix "`min`" := Nat.min (at level 35) : nat_scope.
Time Instance nat_eq_dec : (EqDecision nat) := eq_nat_dec.
Time Instance nat_le_dec : (RelDecision le) := le_dec.
Time Instance nat_lt_dec : (RelDecision lt) := lt_dec.
Time Instance nat_inhabited : (Inhabited nat) := (populate 0%nat).
Time Instance S_inj : (Inj (=) (=) S).
Time Proof.
Time by injection 1.
Time Qed.
Time Instance nat_le_po : (PartialOrder (\226\137\164)).
Time Proof.
Time (repeat split; repeat intro; auto with lia).
Time Qed.
Time Instance nat_le_total : (Total (\226\137\164)).
Time Proof.
Time (repeat intro; lia).
Time Qed.
Time Instance nat_le_pi : (\226\136\128 x y : nat, ProofIrrel (x \226\137\164 y)).
Time Proof.
Time
(assert
  (aux :
   \226\136\128 x y (p : x \226\137\164 y) y' (q : x \226\137\164 y'), y = y' \226\134\146 eq_dep nat (le x) y p y' q)).
Time {
Time fix FIX 3.
Time (intros x ? [| y p] ? [| y' q]).
Time -
Time done.
Time -
Time clear FIX.
Time (intros; exfalso; auto with lia).
Time -
Time clear FIX.
Time (intros; exfalso; auto with lia).
Time -
Time injection 1.
Time (intros Hy).
Time by case (FIX x y p y' q Hy).
Time }
Time (intros x y p q).
Time by apply (Eqdep_dec.eq_dep_eq_dec (\206\187 x y, decide (x = y))), aux.
Time Qed.
Time Instance nat_lt_pi : (\226\136\128 x y : nat, ProofIrrel (x < y)).
Time Proof.
Time (unfold lt).
Time (apply _).
Time Qed.
Time Lemma nat_le_sum (x y : nat) : x \226\137\164 y \226\134\148 (\226\136\131 z, y = x + z).
Time Proof.
Time split.
Time (exists (y - x); lia).
Time (intros [z ->]; lia).
Time Qed.
Time Lemma Nat_lt_succ_succ n : n < S (S n).
Time Proof.
Time auto with arith.
Time Qed.
Time
Lemma Nat_mul_split_l n x1 x2 y1 y2 :
  x2 < n \226\134\146 y2 < n \226\134\146 x1 * n + x2 = y1 * n + y2 \226\134\146 x1 = y1 \226\136\167 x2 = y2.
Time Proof.
Time (intros Hx2 Hy2 E).
Time (cut (x1 = y1); [ intros; subst; lia |  ]).
Time revert y1 E.
Time (induction x1; simpl; intros [| ?]; simpl; auto with lia).
Time Qed.
Time
Lemma Nat_mul_split_r n x1 x2 y1 y2 :
  x1 < n \226\134\146 y1 < n \226\134\146 x1 + x2 * n = y1 + y2 * n \226\134\146 x1 = y1 \226\136\167 x2 = y2.
Time Proof.
Time (intros).
Time (destruct (Nat_mul_split_l n x2 x1 y2 y1); auto with lia).
Time Qed.
Time Notation lcm := Nat.lcm.
Time Notation divide := Nat.divide.
Time Notation "( x | y )" := (divide x y) : nat_scope.
Time Instance Nat_divide_dec : (RelDecision Nat.divide).
Time Proof.
Time
(refine (\206\187 x y, cast_if (decide (lcm x y = y))); by
  rewrite Nat.divide_lcm_iff).
Time Defined.
Time Instance: (PartialOrder divide).
Time Proof.
Time (repeat split; try apply _).
Time (intros ? ?).
Time (apply Nat.divide_antisym_nonneg; lia).
Time Qed.
Time Hint Extern 0 (_ | _) => reflexivity: core.
Time Lemma Nat_divide_ne_0 x y : (x | y) \226\134\146 y \226\137\160 0 \226\134\146 x \226\137\160 0.
Time Proof.
Time (intros Hxy Hy ->).
Time by apply Hy, Nat.divide_0_l.
Time Qed.
Time
Lemma Nat_iter_S {A} n (f : A \226\134\146 A) x :
  Nat.iter (S n) f x = f (Nat.iter n f x).
Time Proof.
Time done.
Time Qed.
Time
Lemma Nat_iter_S_r {A} n (f : A \226\134\146 A) x :
  Nat.iter (S n) f x = Nat.iter n f (f x).
Time Proof.
Time (induction n; by f_equal /=).
Time Qed.
Time
Lemma Nat_iter_add {A} n1 n2 (f : A \226\134\146 A) x :
  Nat.iter (n1 + n2) f x = Nat.iter n1 f (Nat.iter n2 f x).
Time Proof.
Time (induction n1; by f_equal /=).
Time Qed.
Time
Lemma Nat_iter_ind {A} (P : A \226\134\146 Prop) f x k :
  P x \226\134\146 (\226\136\128 y, P y \226\134\146 P (f y)) \226\134\146 P (Nat.iter k f x).
Time Proof.
Time (induction k; simpl; auto).
Time Qed.
Time
Definition sum_list_with {A} (f : A \226\134\146 nat) : list A \226\134\146 nat :=
  fix go l := match l with
              | [] => 0
              | x :: l => f x + go l
              end.
Time Notation sum_list := (sum_list_with id).
Time
Definition max_list_with {A} (f : A \226\134\146 nat) : list A \226\134\146 nat :=
  fix go l := match l with
              | [] => 0
              | x :: l => f x `max` go l
              end.
Time Notation max_list := (max_list_with id).
Time Open Scope positive_scope.
Time Typeclasses Opaque Pos.le.
Time Typeclasses Opaque Pos.lt.
Time Infix "\226\137\164" := Pos.le : positive_scope.
Time Notation "x \226\137\164 y \226\137\164 z" := (x \226\137\164 y \226\136\167 y \226\137\164 z) : positive_scope.
Time Notation "x \226\137\164 y < z" := (x \226\137\164 y \226\136\167 y < z) : positive_scope.
Time Notation "x < y \226\137\164 z" := (x < y \226\136\167 y \226\137\164 z) : positive_scope.
Time Notation "x \226\137\164 y \226\137\164 z \226\137\164 z'" := (x \226\137\164 y \226\136\167 y \226\137\164 z \226\136\167 z \226\137\164 z') : positive_scope.
Time Notation "(\226\137\164)" := Pos.le (only parsing) : positive_scope.
Time Notation "(<)" := Pos.lt (only parsing) : positive_scope.
Time Notation "(~0)" := xO (only parsing) : positive_scope.
Time Notation "(~1)" := xI (only parsing) : positive_scope.
Time Arguments Pos.of_nat : simpl never.
Time Arguments Pmult : simpl never.
Time Instance positive_eq_dec : (EqDecision positive) := Pos.eq_dec.
Time Instance positive_le_dec : (RelDecision Pos.le).
Time Proof.
Time refine (\206\187 x y, decide ((x ?= y) \226\137\160 Gt)).
Time Defined.
Time Instance positive_lt_dec : (RelDecision Pos.lt).
Time Proof.
Time refine (\206\187 x y, decide ((x ?= y) = Lt)).
Time Defined.
Time Instance positive_le_total : (Total Pos.le).
Time Proof.
Time (repeat intro; lia).
Time Qed.
Time Instance positive_inhabited : (Inhabited positive) := (populate 1).
Time
Instance maybe_xO : (Maybe xO) :=
 (\206\187 p, match p with
       | p~0 => Some p
       | _ => None
       end).
Time
Instance maybe_xI : (Maybe xI) :=
 (\206\187 p, match p with
       | p~1 => Some p
       | _ => None
       end).
Time Instance xO_inj : (Inj (=) (=) (~0)).
Time Proof.
Time by injection 1.
Time Qed.
Time Instance xI_inj : (Inj (=) (=) (~1)).
Time Proof.
Time by injection 1.
Time Qed.
Time
Fixpoint Papp (p1 p2 : positive) : positive :=
  match p2 with
  | 1 => p1
  | p2~0 => (Papp p1 p2)~0
  | p2~1 => (Papp p1 p2)~1
  end.
Time Infix "++" := Papp : positive_scope.
Time Notation "(++)" := Papp (only parsing) : positive_scope.
Time Notation "( p ++)" := (Papp p) (only parsing) : positive_scope.
Time Notation "(++ q )" := (\206\187 p, Papp p q) (only parsing) : positive_scope.
Time
Fixpoint Preverse_go (p1 p2 : positive) : positive :=
  match p2 with
  | 1 => p1
  | p2~0 => Preverse_go p1~0 p2
  | p2~1 => Preverse_go p1~1 p2
  end.
Time Definition Preverse : positive \226\134\146 positive := Preverse_go 1.
Time #[global]Instance Papp_1_l : (LeftId (=) 1 (++)).
Time Proof.
Time (intros p).
Time by induction p; intros; f_equal /=.
Time Qed.
Time #[global]Instance Papp_1_r : (RightId (=) 1 (++)).
Time Proof.
Time done.
Time Qed.
Time #[global]Instance Papp_assoc : (Assoc (=) (++)).
Time Proof.
Time (intros ? ? p).
Time by induction p; intros; f_equal /=.
Time Qed.
Time #[global]Instance Papp_inj  p: (Inj (=) (=) (++p)).
Time Proof.
Time (intros ? ? ?).
Time (induction p; simplify_eq; auto).
Time Qed.
Time
Lemma Preverse_go_app p1 p2 p3 :
  Preverse_go p1 (p2 ++ p3) = Preverse_go p1 p3 ++ Preverse_go 1 p2.
Time Proof.
Time revert p3 p1 p2.
Time (cut (\226\136\128 p1 p2 p3, Preverse_go (p2 ++ p3) p1 = p2 ++ Preverse_go p3 p1)).
Time {
Time
by intros go p3; induction p3; intros p1 p2; simpl; auto; rewrite <- ?go.
Time }
Time
(intros p1; induction p1 as [p1 IH| p1 IH| ]; intros p2 p3; simpl; auto).
Time -
Time (apply (IH _ _~1)).
Time -
Time (apply (IH _ _~0)).
Time Qed.
Time
Lemma Preverse_app p1 p2 : Preverse (p1 ++ p2) = Preverse p2 ++ Preverse p1.
Time Proof.
Time (unfold Preverse).
Time by rewrite Preverse_go_app.
Time Qed.
Time Lemma Preverse_xO p : Preverse p~0 = 1~0 ++ Preverse p.
Time Proof Preverse_app p 1~0.
Time Lemma Preverse_xI p : Preverse p~1 = 1~1 ++ Preverse p.
Time Proof Preverse_app p 1~1.
Time Lemma Preverse_involutive p : Preverse (Preverse p) = p.
Time Proof.
Time (induction p as [p IH| p IH| ]; simpl).
Time -
Time by rewrite Preverse_xI, Preverse_app, IH.
Time -
Time by rewrite Preverse_xO, Preverse_app, IH.
Time -
Time reflexivity.
Time Qed.
Time Instance Preverse_inj : (Inj (=) (=) Preverse).
Time Proof.
Time (intros p q eq).
Time (rewrite <- (Preverse_involutive p)).
Time (rewrite <- (Preverse_involutive q)).
Time by rewrite eq.
Time Qed.
Time
Fixpoint Plength (p : positive) : nat :=
  match p with
  | 1 => 0%nat
  | p~0 | p~1 => S (Plength p)
  end.
Time
Lemma Papp_length p1 p2 : Plength (p1 ++ p2) = (Plength p2 + Plength p1)%nat.
Time Proof.
Time by induction p2; f_equal /=.
Time Qed.
Time Lemma Plt_sum (x y : positive) : x < y \226\134\148 (\226\136\131 z, y = x + z).
Time Proof.
Time split.
Time -
Time exists (y - x)%positive.
Time symmetry.
Time (apply Pplus_minus).
Time lia.
Time -
Time (intros [z ->]).
Time lia.
Time Qed.
Time
Fixpoint Pdup (p : positive) : positive :=
  match p with
  | 1 => 1
  | p'~0 => (Pdup p')~0~0
  | p'~1 => (Pdup p')~1~1
  end.
Time Lemma Pdup_app p q : Pdup (p ++ q) = Pdup p ++ Pdup q.
Time Proof.
Time revert p.
Time (induction q as [p IH| p IH| ]; intros q; simpl).
Time -
Time by rewrite IH.
Time -
Time by rewrite IH.
Time -
Time reflexivity.
Time Qed.
Time
Lemma Pdup_suffix_eq p q s1 s2 : s1~1~0 ++ Pdup p = s2~1~0 ++ Pdup q \226\134\146 p = q.
Time Proof.
Time revert q.
Time (induction p as [p IH| p IH| ]; intros [q| q| ] eq; simplify_eq /=).
Time -
Time by rewrite (IH q).
Time -
Time by rewrite (IH q).
Time -
Time reflexivity.
Time Qed.
Time Instance Pdup_inj : (Inj (=) (=) Pdup).
Time Proof.
Time (intros p q eq).
Time (apply (Pdup_suffix_eq _ _ 1 1)).
Time by rewrite eq.
Time Qed.
Time Lemma Preverse_Pdup p : Preverse (Pdup p) = Pdup (Preverse p).
Time Proof.
Time (induction p as [p IH| p IH| ]; simpl).
Time -
Time (rewrite 3!Preverse_xI).
Time (rewrite (assoc_L (++))).
Time (rewrite IH).
Time (rewrite Pdup_app).
Time reflexivity.
Time -
Time (rewrite 3!Preverse_xO).
Time (rewrite (assoc_L (++))).
Time (rewrite IH).
Time (rewrite Pdup_app).
Time reflexivity.
Time -
Time reflexivity.
Time Qed.
Time Close Scope positive_scope.
Time Typeclasses Opaque N.le.
Time Typeclasses Opaque N.lt.
Time Infix "\226\137\164" := N.le : N_scope.
Time Notation "x \226\137\164 y \226\137\164 z" := (x \226\137\164 y \226\136\167 y \226\137\164 z)%N : N_scope.
Time Notation "x \226\137\164 y < z" := (x \226\137\164 y \226\136\167 y < z)%N : N_scope.
Time Notation "x < y \226\137\164 z" := (x < y \226\136\167 y \226\137\164 z)%N : N_scope.
Time Notation "x \226\137\164 y \226\137\164 z \226\137\164 z'" := (x \226\137\164 y \226\136\167 y \226\137\164 z \226\136\167 z \226\137\164 z')%N : N_scope.
Time Notation "(\226\137\164)" := N.le (only parsing) : N_scope.
Time Notation "(<)" := N.lt (only parsing) : N_scope.
Time Infix "`div`" := N.div (at level 35) : N_scope.
Time Infix "`mod`" := N.modulo (at level 35) : N_scope.
Time Infix "`max`" := N.max (at level 35) : N_scope.
Time Infix "`min`" := N.min (at level 35) : N_scope.
Time Arguments N.add : simpl never.
Time Instance Npos_inj : (Inj (=) (=) Npos).
Time Proof.
Time by injection 1.
Time Qed.
Time Instance N_eq_dec : (EqDecision N) := N.eq_dec.
Time #[program]
Instance N_le_dec : (RelDecision N.le) :=
 (\206\187 x y, match N.compare x y with
         | Gt => right _
         | _ => left _
         end).
Time Solve Obligations with naive_solver.
Time #[program]
Instance N_lt_dec : (RelDecision N.lt) :=
 (\206\187 x y, match N.compare x y with
         | Lt => left _
         | _ => right _
         end).
Time Solve Obligations with naive_solver.
Time Instance N_inhabited : (Inhabited N) := (populate 1%N).
Time Instance N_lt_pi  x y: (ProofIrrel (x < y)%N).
Time Proof.
Time (unfold N.lt).
Time (apply _).
Time Qed.
Time Instance N_le_po : (PartialOrder (\226\137\164)%N).
Time Proof.
Time (repeat split; red).
Time (apply N.le_refl).
Time (apply N.le_trans).
Time (apply N.le_antisymm).
Time Qed.
Time Instance N_le_total : (Total (\226\137\164)%N).
Time Proof.
Time (repeat intro; lia).
Time Qed.
Time Hint Extern 0 (_ \226\137\164 _)%N => reflexivity: core.
Time Open Scope Z_scope.
Time Typeclasses Opaque Z.le.
Time Typeclasses Opaque Z.lt.
Time Infix "\226\137\164" := Z.le : Z_scope.
Time Notation "x \226\137\164 y \226\137\164 z" := (x \226\137\164 y \226\136\167 y \226\137\164 z) : Z_scope.
Time Notation "x \226\137\164 y < z" := (x \226\137\164 y \226\136\167 y < z) : Z_scope.
Time Notation "x < y < z" := (x < y \226\136\167 y < z) : Z_scope.
Time Notation "x < y \226\137\164 z" := (x < y \226\136\167 y \226\137\164 z) : Z_scope.
Time Notation "x \226\137\164 y \226\137\164 z \226\137\164 z'" := (x \226\137\164 y \226\136\167 y \226\137\164 z \226\136\167 z \226\137\164 z') : Z_scope.
Time Notation "(\226\137\164)" := Z.le (only parsing) : Z_scope.
Time Notation "(<)" := Z.lt (only parsing) : Z_scope.
Time Infix "`div`" := Z.div (at level 35) : Z_scope.
Time Infix "`mod`" := Z.modulo (at level 35) : Z_scope.
Time Infix "`quot`" := Z.quot (at level 35) : Z_scope.
Time Infix "`rem`" := Z.rem (at level 35) : Z_scope.
Time Infix "\226\137\170" := Z.shiftl (at level 35) : Z_scope.
Time Infix "\226\137\171" := Z.shiftr (at level 35) : Z_scope.
Time Infix "`max`" := Z.max (at level 35) : Z_scope.
Time Infix "`min`" := Z.min (at level 35) : Z_scope.
Time Instance Zpos_inj : (Inj (=) (=) Zpos).
Time Proof.
Time by injection 1.
Time Qed.
Time Instance Zneg_inj : (Inj (=) (=) Zneg).
Time Proof.
Time by injection 1.
Time Qed.
Time Instance Z_of_nat_inj : (Inj (=) (=) Z.of_nat).
Time Proof.
Time (intros n1 n2).
Time (apply Nat2Z.inj).
Time Qed.
Time Instance Z_eq_dec : (EqDecision Z) := Z.eq_dec.
Time Instance Z_le_dec : (RelDecision Z.le) := Z_le_dec.
Time Instance Z_lt_dec : (RelDecision Z.lt) := Z_lt_dec.
Time Instance Z_inhabited : (Inhabited Z) := (populate 1).
Time Instance Z_lt_pi  x y: (ProofIrrel (x < y)).
Time Proof.
Time (unfold Z.lt).
Time (apply _).
Time Qed.
Time Instance Z_le_po : (PartialOrder (\226\137\164)).
Time Proof.
Time (repeat split; red).
Time (apply Z.le_refl).
Time (apply Z.le_trans).
Time (apply Z.le_antisymm).
Time Qed.
Time Instance Z_le_total : (Total Z.le).
Time Proof.
Time (repeat intro; lia).
Time Qed.
Time Lemma Z_pow_pred_r n m : 0 < m \226\134\146 n * n ^ Z.pred m = n ^ m.
Time Proof.
Time (intros).
Time (rewrite <- Z.pow_succ_r, Z.succ_pred).
Time done.
Time by apply Z.lt_le_pred.
Time Qed.
Time
Lemma Z_quot_range_nonneg k x y : 0 \226\137\164 x < k \226\134\146 0 < y \226\134\146 0 \226\137\164 x `quot` y < k.
Time Proof.
Time (intros [? ?] ?).
Time (destruct (decide (y = 1)); subst; [ rewrite Z.quot_1_r; auto |  ]).
Time
(destruct (decide (x = 0)); subst; [ rewrite Z.quot_0_l; auto with lia |  ]).
Time split.
Time (apply Z.quot_pos; lia).
Time (trans x; auto).
Time (apply Z.quot_lt; lia).
Time Qed.
Time Arguments Z.pred : simpl never.
Time Arguments Z.succ : simpl never.
Time Arguments Z.of_nat : simpl never.
Time Arguments Z.to_nat : simpl never.
Time Arguments Z.mul : simpl never.
Time Arguments Z.add : simpl never.
Time Arguments Z.sub : simpl never.
Time Arguments Z.opp : simpl never.
Time Arguments Z.pow : simpl never.
Time Arguments Z.div : simpl never.
Time Arguments Z.modulo : simpl never.
Time Arguments Z.quot : simpl never.
Time Arguments Z.rem : simpl never.
Time Arguments Z.shiftl : simpl never.
Time Arguments Z.shiftr : simpl never.
Time Arguments Z.gcd : simpl never.
Time Arguments Z.lcm : simpl never.
Time Arguments Z.min : simpl never.
Time Arguments Z.max : simpl never.
Time Arguments Z.lor : simpl never.
Time Arguments Z.land : simpl never.
Time Arguments Z.lxor : simpl never.
Time Arguments Z.lnot : simpl never.
Time Arguments Z.square : simpl never.
Time Arguments Z.abs : simpl never.
Time Lemma Z_to_nat_neq_0_pos x : Z.to_nat x \226\137\160 0%nat \226\134\146 0 < x.
Time Proof.
Time by destruct x.
Time Qed.
Time Lemma Z_to_nat_neq_0_nonneg x : Z.to_nat x \226\137\160 0%nat \226\134\146 0 \226\137\164 x.
Time Proof.
Time by destruct x.
Time Qed.
Time Lemma Z_mod_pos x y : 0 < y \226\134\146 0 \226\137\164 x `mod` y.
Time Proof.
Time (apply Z.mod_pos_bound).
Time Qed.
Time Hint Resolve Z.lt_le_incl: zpos.
Time
Hint Resolve Z.add_nonneg_pos Z.add_pos_nonneg Z.add_nonneg_nonneg: zpos.
Time Hint Resolve Z.mul_nonneg_nonneg Z.mul_pos_pos: zpos.
Time Hint Resolve Z.pow_pos_nonneg Z.pow_nonneg: zpos.
Time Hint Resolve Z_mod_pos Z.div_pos: zpos.
Time Hint Extern 1000  => lia: zpos.
Time Lemma Z_to_nat_nonpos x : x \226\137\164 0 \226\134\146 Z.to_nat x = 0%nat.
Time Proof.
Time (destruct x; simpl; auto using Z2Nat.inj_neg).
Time by intros [].
Time Qed.
Time Lemma Z2Nat_inj_pow (x y : nat) : Z.of_nat (x ^ y) = x ^ y.
Time Proof.
Time (induction y as [| y IH]; [ by rewrite Z.pow_0_r, Nat.pow_0_r |  ]).
Time
by
 rewrite Nat.pow_succ_r, Nat2Z.inj_succ, Z.pow_succ_r, Nat2Z.inj_mul, IH by
  auto with zpos.
Time Qed.
Time Lemma Nat2Z_divide n m : (Z.of_nat n | Z.of_nat m) \226\134\148 (n | m)%nat.
Time Proof.
Time split.
Time -
Time (rewrite <- (Nat2Z.id m)  at 2; intros [i ->]; exists (Z.to_nat i)).
Time (destruct (decide (0 \226\137\164 i)%Z)).
Time {
Time by rewrite Z2Nat.inj_mul, Nat2Z.id by lia.
Time }
Time by rewrite !Z_to_nat_nonpos by auto using Z.mul_nonpos_nonneg with lia.
Time -
Time (intros [i ->]).
Time exists (Z.of_nat i).
Time by rewrite Nat2Z.inj_mul.
Time Qed.
Time
Lemma Z2Nat_divide n m :
  0 \226\137\164 n \226\134\146 0 \226\137\164 m \226\134\146 (Z.to_nat n | Z.to_nat m)%nat \226\134\148 (n | m).
Time Proof.
Time (intros).
Time by rewrite <- Nat2Z_divide, !Z2Nat.id by done.
Time Qed.
Time Lemma Z2Nat_inj_div x y : Z.of_nat (x `div` y) = x `div` y.
Time Proof.
Time (destruct (decide (y = 0%nat)); [ by subst; destruct x |  ]).
Time (apply Z.div_unique with (x `mod` y)%nat).
Time {
Time left.
Time (rewrite <- (Nat2Z.inj_le 0), <- Nat2Z.inj_lt).
Time (apply Nat.mod_bound_pos; lia).
Time }
Time by rewrite <- Nat2Z.inj_mul, <- Nat2Z.inj_add, <- Nat.div_mod.
Time Qed.
Time Lemma Z2Nat_inj_mod x y : Z.of_nat (x `mod` y) = x `mod` y.
Time Proof.
Time (destruct (decide (y = 0%nat)); [ by subst; destruct x |  ]).
Time (apply Z.mod_unique with (x `div` y)%nat).
Time {
Time left.
Time (rewrite <- (Nat2Z.inj_le 0), <- Nat2Z.inj_lt).
Time (apply Nat.mod_bound_pos; lia).
Time }
Time by rewrite <- Nat2Z.inj_mul, <- Nat2Z.inj_add, <- Nat.div_mod.
Time Qed.
Time
Lemma Z_succ_pred_induction y (P : Z \226\134\146 Prop) :
  P y
  \226\134\146 (\226\136\128 x, y \226\137\164 x \226\134\146 P x \226\134\146 P (Z.succ x))
    \226\134\146 (\226\136\128 x, x \226\137\164 y \226\134\146 P x \226\134\146 P (Z.pred x)) \226\134\146 \226\136\128 x, P x.
Time Proof.
Time (intros H0 HS HP).
Time by apply (Z.order_induction' _ _ y).
Time Qed.
Time Close Scope Z_scope.
Time Instance N_of_nat_inj : (Inj (=) (=) N.of_nat) := Nat2N.inj.
Time Instance nat_of_N_inj : (Inj (=) (=) N.to_nat) := N2Nat.inj.
Time Instance nat_of_pos_inj : (Inj (=) (=) Pos.to_nat) := Pos2Nat.inj.
Time
Instance pos_of_Snat_inj : (Inj (=) (=) Pos.of_succ_nat) := SuccNat2Pos.inj.
Time Instance Z_of_N_inj : (Inj (=) (=) Z.of_N) := N2Z.inj.
Time Typeclasses Opaque Qcle.
Time Typeclasses Opaque Qclt.
Time Open Scope Qc_scope.
Time Delimit Scope Qc_scope with Qc.
Time Notation "1" := (Q2Qc 1) : Qc_scope.
Time Notation "2" := (1 + 1) : Qc_scope.
Time Notation "- 1" := (Qcopp 1) : Qc_scope.
Time Notation "- 2" := (Qcopp 2) : Qc_scope.
Time Infix "\226\137\164" := Qcle : Qc_scope.
Time Notation "x \226\137\164 y \226\137\164 z" := (x \226\137\164 y \226\136\167 y \226\137\164 z) : Qc_scope.
Time Notation "x \226\137\164 y < z" := (x \226\137\164 y \226\136\167 y < z) : Qc_scope.
Time Notation "x < y < z" := (x < y \226\136\167 y < z) : Qc_scope.
Time Notation "x < y \226\137\164 z" := (x < y \226\136\167 y \226\137\164 z) : Qc_scope.
Time Notation "x \226\137\164 y \226\137\164 z \226\137\164 z'" := (x \226\137\164 y \226\136\167 y \226\137\164 z \226\136\167 z \226\137\164 z') : Qc_scope.
Time Notation "(\226\137\164)" := Qcle (only parsing) : Qc_scope.
Time Notation "(<)" := Qclt (only parsing) : Qc_scope.
Time Hint Extern 1 (_ \226\137\164 _) => (reflexivity || discriminate): core.
Time Arguments Qred : simpl never.
Time Instance Qc_eq_dec : (EqDecision Qc) := Qc_eq_dec.
Time #[program]
Instance Qc_le_dec : (RelDecision Qcle) :=
 (\206\187 x y, if Qclt_le_dec y x then right _ else left _).
Time Next Obligation.
Time (intros x y; apply Qclt_not_le).
Time Qed.
Time Next Obligation.
Time done.
Time Qed.
Time #[program]
Instance Qc_lt_dec : (RelDecision Qclt) :=
 (\206\187 x y, if Qclt_le_dec x y then left _ else right _).
Time Next Obligation.
Time done.
Time Qed.
Time Next Obligation.
Time (intros x y; apply Qcle_not_lt).
Time Qed.
Time Instance Qc_lt_pi  x y: (ProofIrrel (x < y)).
Time Proof.
Time (unfold Qclt).
Time (apply _).
Time Qed.
Time Instance Qc_le_po : (PartialOrder (\226\137\164)).
Time Proof.
Time (repeat split; red).
Time (apply Qcle_refl).
Time (apply Qcle_trans).
Time (apply Qcle_antisym).
Time Qed.
Time Instance Qc_lt_strict : (StrictOrder (<)).
Time Proof.
Time (split; red).
Time (intros x Hx).
Time by destruct (Qclt_not_eq x x).
Time (apply Qclt_trans).
Time Qed.
Time Instance Qc_le_total : (Total Qcle).
Time Proof.
Time (intros x y).
Time (destruct (Qclt_le_dec x y); auto using Qclt_le_weak).
Time Qed.
Time Lemma Qcmult_0_l x : 0 * x = 0.
Time Proof.
Time ring.
Time Qed.
Time Lemma Qcmult_0_r x : x * 0 = 0.
Time Proof.
Time ring.
Time Qed.
Time Lemma Qcplus_diag x : (x + x)%Qc = (2 * x)%Qc.
Time Proof.
Time ring.
Time Qed.
Time Lemma Qcle_ngt (x y : Qc) : x \226\137\164 y \226\134\148 \194\172 y < x.
Time Proof.
Time (split; auto using Qcle_not_lt, Qcnot_lt_le).
Time Qed.
Time Lemma Qclt_nge (x y : Qc) : x < y \226\134\148 \194\172 y \226\137\164 x.
Time Proof.
Time (split; auto using Qclt_not_le, Qcnot_le_lt).
Time Qed.
Time Lemma Qcplus_le_mono_l (x y z : Qc) : x \226\137\164 y \226\134\148 z + x \226\137\164 z + y.
Time Proof.
Time (split; intros).
Time -
Time by apply Qcplus_le_compat.
Time -
Time replace x with 0 - z + (z + x) by ring.
Time replace y with 0 - z + (z + y) by ring.
Time by apply Qcplus_le_compat.
Time Qed.
Time Lemma Qcplus_le_mono_r (x y z : Qc) : x \226\137\164 y \226\134\148 x + z \226\137\164 y + z.
Time Proof.
Time (rewrite !(Qcplus_comm _ z)).
Time (apply Qcplus_le_mono_l).
Time Qed.
Time Lemma Qcplus_lt_mono_l (x y z : Qc) : x < y \226\134\148 z + x < z + y.
Time Proof.
Time by rewrite !Qclt_nge, <- Qcplus_le_mono_l.
Time Qed.
Time Lemma Qcplus_lt_mono_r (x y z : Qc) : x < y \226\134\148 x + z < y + z.
Time Proof.
Time by rewrite !Qclt_nge, <- Qcplus_le_mono_r.
Time Qed.
Time Instance Qcopp_inj : (Inj (=) (=) Qcopp).
Time Proof.
Time (intros x y H).
Time by rewrite <- (Qcopp_involutive x), H, Qcopp_involutive.
Time Qed.
Time Instance Qcplus_inj_r  z: (Inj (=) (=) (Qcplus z)).
Time Proof.
Time (intros x y H).
Time by apply (anti_symm (\226\137\164)); rewrite (Qcplus_le_mono_l _ _ z), H.
Time Qed.
Time Instance Qcplus_inj_l  z: (Inj (=) (=) (\206\187 x, x + z)).
Time Proof.
Time (intros x y H).
Time by apply (anti_symm (\226\137\164)); rewrite (Qcplus_le_mono_r _ _ z), H.
Time Qed.
Time Lemma Qcplus_pos_nonneg (x y : Qc) : 0 < x \226\134\146 0 \226\137\164 y \226\134\146 0 < x + y.
Time Proof.
Time (intros).
Time (apply Qclt_le_trans with (x + 0); [ by rewrite Qcplus_0_r |  ]).
Time by apply Qcplus_le_mono_l.
Time Qed.
Time Lemma Qcplus_nonneg_pos (x y : Qc) : 0 \226\137\164 x \226\134\146 0 < y \226\134\146 0 < x + y.
Time Proof.
Time (rewrite (Qcplus_comm x)).
Time auto using Qcplus_pos_nonneg.
Time Qed.
Time Lemma Qcplus_pos_pos (x y : Qc) : 0 < x \226\134\146 0 < y \226\134\146 0 < x + y.
Time Proof.
Time auto using Qcplus_pos_nonneg, Qclt_le_weak.
Time Qed.
Time Lemma Qcplus_nonneg_nonneg (x y : Qc) : 0 \226\137\164 x \226\134\146 0 \226\137\164 y \226\134\146 0 \226\137\164 x + y.
Time Proof.
Time (intros).
Time (trans x + 0; [ by rewrite Qcplus_0_r |  ]).
Time by apply Qcplus_le_mono_l.
Time Qed.
Time Lemma Qcplus_neg_nonpos (x y : Qc) : x < 0 \226\134\146 y \226\137\164 0 \226\134\146 x + y < 0.
Time Proof.
Time (intros).
Time (apply Qcle_lt_trans with (x + 0); [  | by rewrite Qcplus_0_r ]).
Time by apply Qcplus_le_mono_l.
Time Qed.
Time Lemma Qcplus_nonpos_neg (x y : Qc) : x \226\137\164 0 \226\134\146 y < 0 \226\134\146 x + y < 0.
Time Proof.
Time (rewrite (Qcplus_comm x)).
Time auto using Qcplus_neg_nonpos.
Time Qed.
Time Lemma Qcplus_neg_neg (x y : Qc) : x < 0 \226\134\146 y < 0 \226\134\146 x + y < 0.
Time Proof.
Time auto using Qcplus_nonpos_neg, Qclt_le_weak.
Time Qed.
Time Lemma Qcplus_nonpos_nonpos (x y : Qc) : x \226\137\164 0 \226\134\146 y \226\137\164 0 \226\134\146 x + y \226\137\164 0.
Time Proof.
Time (intros).
Time (trans x + 0; [  | by rewrite Qcplus_0_r ]).
Time by apply Qcplus_le_mono_l.
Time Qed.
Time Lemma Qcmult_le_mono_nonneg_l x y z : 0 \226\137\164 z \226\134\146 x \226\137\164 y \226\134\146 z * x \226\137\164 z * y.
Time Proof.
Time (intros).
Time (rewrite !(Qcmult_comm z)).
Time by apply Qcmult_le_compat_r.
Time Qed.
Time Lemma Qcmult_le_mono_nonneg_r x y z : 0 \226\137\164 z \226\134\146 x \226\137\164 y \226\134\146 x * z \226\137\164 y * z.
Time Proof.
Time (intros).
Time by apply Qcmult_le_compat_r.
Time Qed.
Time Lemma Qcmult_le_mono_pos_l x y z : 0 < z \226\134\146 x \226\137\164 y \226\134\148 z * x \226\137\164 z * y.
Time Proof.
Time (split; auto using Qcmult_le_mono_nonneg_l, Qclt_le_weak).
Time (rewrite !Qcle_ngt, !(Qcmult_comm z)).
Time intuition auto using Qcmult_lt_compat_r.
Time Qed.
Time Lemma Qcmult_le_mono_pos_r x y z : 0 < z \226\134\146 x \226\137\164 y \226\134\148 x * z \226\137\164 y * z.
Time Proof.
Time (rewrite !(Qcmult_comm _ z)).
Time by apply Qcmult_le_mono_pos_l.
Time Qed.
Time Lemma Qcmult_lt_mono_pos_l x y z : 0 < z \226\134\146 x < y \226\134\148 z * x < z * y.
Time Proof.
Time (intros).
Time by rewrite !Qclt_nge, <- Qcmult_le_mono_pos_l.
Time Qed.
Time Lemma Qcmult_lt_mono_pos_r x y z : 0 < z \226\134\146 x < y \226\134\148 x * z < y * z.
Time Proof.
Time (intros).
Time by rewrite !Qclt_nge, <- Qcmult_le_mono_pos_r.
Time Qed.
Time Lemma Qcmult_pos_pos x y : 0 < x \226\134\146 0 < y \226\134\146 0 < x * y.
Time Proof.
Time (intros).
Time (apply Qcle_lt_trans with (0 * y); [ by rewrite Qcmult_0_l |  ]).
Time by apply Qcmult_lt_mono_pos_r.
Time Qed.
Time Lemma Qcmult_nonneg_nonneg x y : 0 \226\137\164 x \226\134\146 0 \226\137\164 y \226\134\146 0 \226\137\164 x * y.
Time Proof.
Time (intros).
Time (trans 0 * y; [ by rewrite Qcmult_0_l |  ]).
Time by apply Qcmult_le_mono_nonneg_r.
Time Qed.
Time Lemma inject_Z_Qred n : Qred (inject_Z n) = inject_Z n.
Time Proof.
Time (apply Qred_identity; auto using Z.gcd_1_r).
Time Qed.
Time Coercion Qc_of_Z (n : Z) : Qc := Qcmake _ (inject_Z_Qred n).
Time Lemma Z2Qc_inj_0 : Qc_of_Z 0 = 0.
Time Proof.
Time by apply Qc_is_canon.
Time Qed.
Time Lemma Z2Qc_inj_1 : Qc_of_Z 1 = 1.
Time Proof.
Time by apply Qc_is_canon.
Time Qed.
Time Lemma Z2Qc_inj_2 : Qc_of_Z 2 = 2.
Time Proof.
Time by apply Qc_is_canon.
Time Qed.
Time Lemma Z2Qc_inj n m : Qc_of_Z n = Qc_of_Z m \226\134\146 n = m.
Time Proof.
Time by injection 1.
Time Qed.
Time Lemma Z2Qc_inj_iff n m : Qc_of_Z n = Qc_of_Z m \226\134\148 n = m.
Time Proof.
Time split.
Time auto using Z2Qc_inj.
Time by intros ->.
Time Qed.
Time Lemma Z2Qc_inj_le n m : (n \226\137\164 m)%Z \226\134\148 Qc_of_Z n \226\137\164 Qc_of_Z m.
Time Proof.
Time by rewrite Zle_Qle.
Time Qed.
Time Lemma Z2Qc_inj_lt n m : (n < m)%Z \226\134\148 Qc_of_Z n < Qc_of_Z m.
Time Proof.
Time by rewrite Zlt_Qlt.
Time Qed.
Time Lemma Z2Qc_inj_add n m : Qc_of_Z (n + m) = Qc_of_Z n + Qc_of_Z m.
Time Proof.
Time (apply Qc_is_canon; simpl).
Time by rewrite Qred_correct, inject_Z_plus.
Time Qed.
Time Lemma Z2Qc_inj_mul n m : Qc_of_Z (n * m) = Qc_of_Z n * Qc_of_Z m.
Time Proof.
Time (apply Qc_is_canon; simpl).
Time by rewrite Qred_correct, inject_Z_mult.
Time Qed.
Time Lemma Z2Qc_inj_opp n : Qc_of_Z (- n) = - Qc_of_Z n.
Time Proof.
Time (apply Qc_is_canon; simpl).
Time by rewrite Qred_correct, inject_Z_opp.
Time Qed.
Time Lemma Z2Qc_inj_sub n m : Qc_of_Z (n - m) = Qc_of_Z n - Qc_of_Z m.
Time Proof.
Time (apply Qc_is_canon; simpl).
Time by rewrite !Qred_correct, <- inject_Z_opp, <- inject_Z_plus.
Time Qed.
Time Close Scope Qc_scope.
Time Record Qp := mk_Qp {Qp_car :> Qc; Qp_prf : (0 < Qp_car)%Qc}.
Time Hint Resolve Qp_prf: core.
Time Delimit Scope Qp_scope with Qp.
Time Bind Scope Qp_scope with Qp.
Time Arguments Qp_car _%Qp : assert.
Time Definition Qp_one : Qp := mk_Qp 1 eq_refl.
Time #[program]Definition Qp_plus (x y : Qp) : Qp := mk_Qp (x + y) _.
Time Next Obligation.
Time by intros x y; apply Qcplus_pos_pos.
Time Qed.
Time
Definition Qp_minus (x y : Qp) : option Qp :=
  let z := (x - y)%Qc in
  match decide (0 < z)%Qc with
  | left Hz => Some (mk_Qp z Hz)
  | _ => None
  end.
Time #[program]Definition Qp_mult (x y : Qp) : Qp := mk_Qp (x * y) _.
Time Next Obligation.
Time (intros x y).
Time (apply Qcmult_pos_pos; apply Qp_prf).
Time Qed.
Time #[program]
Definition Qp_div (x : Qp) (y : positive) : Qp := mk_Qp (x / Zpos y) _.
Time Next Obligation.
Time (intros x y).
Time (unfold Qcdiv).
Time (assert (0 < Zpos y)%Qc).
Time {
Time (apply (Z2Qc_inj_lt 0%Z (Zpos y)), Pos2Z.is_pos).
Time }
Time
by
 rewrite (Qcmult_lt_mono_pos_r _ _ (Zpos y)%Z), Qcmult_0_l, <- Qcmult_assoc,
  Qcmult_inv_l, Qcmult_1_r.
Time Qed.
Time Infix "+" := Qp_plus : Qp_scope.
Time Infix "-" := Qp_minus : Qp_scope.
Time Infix "*" := Qp_mult : Qp_scope.
Time Infix "/" := Qp_div : Qp_scope.
Time Notation "1" := Qp_one : Qp_scope.
Time Notation "2" := (1 + 1)%Qp : Qp_scope.
Time Notation "3" := (1 + 2)%Qp : Qp_scope.
Time Notation "4" := (1 + 3)%Qp : Qp_scope.
Time Lemma Qp_eq x y : x = y \226\134\148 Qp_car x = Qp_car y.
Time Proof.
Time (split; [ by intros -> |  ]).
Time (destruct x, y; intros; simplify_eq /=; f_equal; apply (proof_irrel _)).
Time Qed.
Time Instance Qp_inhabited : (Inhabited Qp) := (populate 1%Qp).
Time Instance Qp_eq_dec : (EqDecision Qp).
Time Proof.
Time
(refine (\206\187 x y, cast_if (decide (Qp_car x = Qp_car y))); by rewrite Qp_eq).
Time Defined.
Time Instance Qp_plus_assoc : (Assoc (=) Qp_plus).
Time Proof.
Time (intros x y z; apply Qp_eq, Qcplus_assoc).
Time Qed.
Time Instance Qp_plus_comm : (Comm (=) Qp_plus).
Time Proof.
Time (intros x y; apply Qp_eq, Qcplus_comm).
Time Qed.
Time Instance Qp_plus_inj_r  p: (Inj (=) (=) (Qp_plus p)).
Time Proof.
Time (intros q1 q2).
Time (rewrite !Qp_eq; simpl).
Time (apply (inj _)).
Time Qed.
Time Instance Qp_plus_inj_l  p: (Inj (=) (=) (\206\187 q, q + p)%Qp).
Time Proof.
Time (intros q1 q2).
Time (rewrite !Qp_eq; simpl).
Time (apply (inj (\206\187 q, q + p)%Qc)).
Time Qed.
Time Lemma Qp_minus_diag x : (x - x)%Qp = None.
Time Proof.
Time (unfold Qp_minus, Qcminus).
Time by rewrite Qcplus_opp_r.
Time Qed.
Time Lemma Qp_op_minus x y : (x + y - x)%Qp = Some y.
Time Proof.
Time (unfold Qp_minus, Qcminus; simpl).
Time (rewrite (Qcplus_comm x), <- Qcplus_assoc, Qcplus_opp_r, Qcplus_0_r).
Time (destruct (decide _) as [| []]; auto).
Time by f_equal; apply Qp_eq.
Time Qed.
Time Instance Qp_mult_assoc : (Assoc (=) Qp_mult).
Time Proof.
Time (intros x y z; apply Qp_eq, Qcmult_assoc).
Time Qed.
Time Instance Qp_mult_comm : (Comm (=) Qp_mult).
Time Proof.
Time (intros x y; apply Qp_eq, Qcmult_comm).
Time Qed.
Time Lemma Qp_mult_plus_distr_r x y z : (x * (y + z) = x * y + x * z)%Qp.
Time Proof.
Time (apply Qp_eq, Qcmult_plus_distr_r).
Time Qed.
Time Lemma Qp_mult_plus_distr_l x y z : ((x + y) * z = x * z + y * z)%Qp.
Time Proof.
Time (apply Qp_eq, Qcmult_plus_distr_l).
Time Qed.
Time Lemma Qp_mult_1_l x : (1 * x)%Qp = x.
Time Proof.
Time (apply Qp_eq, Qcmult_1_l).
Time Qed.
Time Lemma Qp_mult_1_r x : (x * 1)%Qp = x.
Time Proof.
Time (apply Qp_eq, Qcmult_1_r).
Time Qed.
Time Lemma Qp_div_1 x : (x / 1 = x)%Qp.
Time Proof.
Time (apply Qp_eq; simpl).
Time (rewrite <- (Qcmult_div_r x 1)  at 2 by done).
Time by rewrite Qcmult_1_l.
Time Qed.
Time Lemma Qp_div_S x y : (x / (2 * y) + x / (2 * y) = x / y)%Qp.
Time Proof.
Time (apply Qp_eq; simpl).
Time (unfold Qcdiv).
Time
(rewrite <- Qcmult_plus_distr_l, Pos2Z.inj_mul, Z2Qc_inj_mul, Z2Qc_inj_2).
Time (rewrite Qcplus_diag).
Time by field_simplify.
Time Qed.
Time Lemma Qp_div_2 x : (x / 2 + x / 2 = x)%Qp.
Time Proof.
Time (change_no_check 2%positive with (2 * 1)%positive).
Time by rewrite Qp_div_S, Qp_div_1.
Time Qed.
Time Lemma Qp_half_half : (1 / 2 + 1 / 2 = 1)%Qp.
Time Proof.
Time (apply (bool_decide_unpack _); by compute).
Time Qed.
Time Lemma Qp_quarter_three_quarter : (1 / 4 + 3 / 4 = 1)%Qp.
Time Proof.
Time (apply (bool_decide_unpack _); by compute).
Time Qed.
Time Lemma Qp_three_quarter_quarter : (3 / 4 + 1 / 4 = 1)%Qp.
Time Proof.
Time (apply (bool_decide_unpack _); by compute).
Time Qed.
Time Lemma Qp_lt_sum (x y : Qp) : (x < y)%Qc \226\134\148 (\226\136\131 z, y = (x + z)%Qp).
Time Proof.
Time split.
Time -
Time (intros Hlt%Qclt_minus_iff).
Time exists (mk_Qp (y - x) Hlt).
Time (apply Qp_eq; simpl).
Time (unfold Qcminus).
Time by rewrite (Qcplus_comm y), Qcplus_assoc, Qcplus_opp_r, Qcplus_0_l.
Time -
Time (intros [z ->]; simpl).
Time (rewrite <- (Qcplus_0_r x)  at 1).
Time (apply Qcplus_lt_mono_l, Qp_prf).
Time Qed.
Time
Lemma Qp_lower_bound q1 q2 : \226\136\131 q q1' q2', (q1 = q + q1' \226\136\167 q2 = q + q2')%Qp.
Time Proof.
Time revert q1 q2.
Time
(cut
  (\226\136\128 q1 q2 : Qp, (q1 \226\137\164 q2)%Qc \226\134\146 \226\136\131 q q1' q2', (q1 = q + q1' \226\136\167 q2 = q + q2')%Qp)).
Time {
Time (intros help q1 q2).
Time
(destruct (Qc_le_dec q1 q2) as [LE| LE%Qclt_le_weak%Qclt_nge];
  [ by eauto |  ]).
Time (destruct (help q2 q1) as (q, (q1', (q2', (?, ?)))); eauto).
Time }
Time (intros q1 q2 Hq).
Time exists (q1 / 2)%Qp,(q1 / 2)%Qp.
Time (assert (Hq2' : (0 < q2 + - q1 * / 2)%Qc)).
Time {
Time (eapply Qclt_le_trans; [  | by apply Qcplus_le_mono_r, Hq ]).
Time replace (q1 + - q1 * / 2)%Qc with (q1 * (1 + - 1 * / 2))%Qc by ring.
Time replace 0%Qc with (0 * (1 + - 1 * / 2))%Qc by ring.
Time by apply Qcmult_lt_compat_r.
Time }
Time exists (mk_Qp (q2 + - q1 * / 2%Z) Hq2').
Time (split; [ by rewrite Qp_div_2 |  ]).
Time (apply Qp_eq; simpl).
Time (unfold Qcdiv).
Time ring.
Time Qed.
Time
Lemma Qp_cross_split p a b c d :
  (a + b = p
   \226\134\146 c + d = p
     \226\134\146 \226\136\131 ac ad bc bd, ac + ad = a \226\136\167 bc + bd = b \226\136\167 ac + bc = c \226\136\167 ad + bd = d)%Qp.
Time Proof.
Time (intros H <-).
Time revert a b c d H.
Time
(cut
  (\226\136\128 a b c d : Qp,
     (a < c)%Qc
     \226\134\146 a + b = c + d
       \226\134\146 \226\136\131 ac ad bc bd, ac + ad = a \226\136\167 bc + bd = b \226\136\167 ac + bc = c \226\136\167 ad + bd = d)%Qp).
Time {
Time (intros help a b c d ?).
Time (destruct (Qclt_le_dec a c) as [?| [?| ->%Qp_eq]%Qcle_lt_or_eq]).
Time -
Time auto.
Time -
Time (destruct (help c d a b); [ done.. | idtac ]).
Time naive_solver.
Time -
Time (apply (inj _) in H as ->).
Time (destruct (Qp_lower_bound a d) as (q, (a', (d', (->, ->))))).
Time eauto  10 using (comm_L Qp_plus).
Time }
Time (intros a b c d [e ->]%Qp_lt_sum).
Time (rewrite <- (assoc_L _)).
Time (intros ->%(inj _)).
Time (destruct (Qp_lower_bound a d) as (q, (a', (d', (->, ->))))).
Time (eexists a',q,(q + e)%Qp,d'; split_and ?; auto using (comm_L Qp_plus)).
Time -
Time by rewrite (assoc_L _), (comm_L Qp_plus e).
Time -
Time by rewrite (assoc_L _), (comm_L Qp_plus a').
Time Qed.
Time
Lemma Qp_bounded_split (p r : Qp) :
  \226\136\131 q1 q2 : Qp, (q1 \226\137\164 r)%Qc \226\136\167 p = (q1 + q2)%Qp.
Time Proof.
Time (destruct (Qclt_le_dec r p) as [?| ?]).
Time -
Time (assert (Hpos : (0 < p + - r)%Qc)).
Time {
Time (apply (Qcplus_lt_mono_r _ _ r)).
Time (rewrite <- Qcplus_assoc, (Qcplus_comm (- r))).
Time by rewrite Qcplus_opp_r, Qcplus_0_l, Qcplus_0_r.
Time }
Time (exists r,(mk_Qp _ Hpos); simpl; split; [ done |  ]).
Time (apply Qp_eq; simpl).
Time (rewrite Qcplus_comm, <- Qcplus_assoc, (Qcplus_comm (- r))).
Time by rewrite Qcplus_opp_r, Qcplus_0_r.
Time -
Time (exists (p / 2)%Qp,(p / 2)%Qp; split).
Time +
Time (trans p; [  | done ]).
Time (apply Qclt_le_weak, Qp_lt_sum).
Time exists (p / 2)%Qp.
Time by rewrite Qp_div_2.
Time +
Time by rewrite Qp_div_2.
Time Qed.
Time Lemma Qp_not_plus_q_ge_1 (q : Qp) : \194\172 ((1 + q)%Qp \226\137\164 1%Qp)%Qc.
Time Proof.
Time (intros Hle).
Time (apply (Qcplus_le_mono_l q 0 1) in Hle).
Time (apply Qcle_ngt in Hle).
Time (apply Hle, Qp_prf).
Time Qed.
Time Lemma Qp_ge_0 (q : Qp) : (0 \226\137\164 q)%Qc.
Time Proof.
Time (apply Qclt_le_weak, Qp_prf).
Time Qed.
