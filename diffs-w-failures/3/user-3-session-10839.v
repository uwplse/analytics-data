Time From Coq Require Import Wf_nat.
Time From stdpp Require Export tactics base.
Time Set Default Proof Using "Type".
Time Section definitions.
Time Context `(R : relation A).
Time Definition red (x : A) := \226\136\131 y, R x y.
Time Definition nf (x : A) := \194\172 red x.
Time Definition sc : relation A := \206\187 x y, R x y \226\136\168 R y x.
Time
Inductive rtc : relation A :=
  | rtc_refl : forall x, rtc x x
  | rtc_l : forall x y z, R x y \226\134\146 rtc y z \226\134\146 rtc x z.
Time
Inductive rtcS `{Equiv A} : relation A :=
  | rtcS_refl : forall x y, x \226\137\161 y \226\134\146 rtcS x y
  | rtcS_l : forall x y z, R x y \226\134\146 rtcS y z \226\134\146 rtcS x z.
Time
Inductive nsteps : nat \226\134\146 relation A :=
  | nsteps_O : forall x, nsteps 0 x x
  | nsteps_l : forall n x y z, R x y \226\134\146 nsteps n y z \226\134\146 nsteps (S n) x z.
Time
Inductive bsteps : nat \226\134\146 relation A :=
  | bsteps_refl : forall n x, bsteps n x x
  | bsteps_l : forall n x y z, R x y \226\134\146 bsteps n y z \226\134\146 bsteps (S n) x z.
Time
Inductive tc : relation A :=
  | tc_once : forall x y, R x y \226\134\146 tc x y
  | tc_l : forall x y z, R x y \226\134\146 tc y z \226\134\146 tc x z.
Time
CoInductive all_loop : A \226\134\146 Prop :=
    all_loop_do_step :
      forall x, red x \226\134\146 (\226\136\128 y, R x y \226\134\146 all_loop y) \226\134\146 all_loop x.
Time
CoInductive ex_loop : A \226\134\146 Prop :=
    ex_loop_do_step : forall x y, R x y \226\134\146 ex_loop y \226\134\146 ex_loop x.
Time End definitions.
Time Definition rtsc {A} (R : relation A) := rtc (sc R).
Time Notation sn R:= (Acc (flip R)).
Time
Definition diamond {A} (R : relation A) :=
  \226\136\128 x y1 y2, R x y1 \226\134\146 R x y2 \226\134\146 \226\136\131 z, R y1 z \226\136\167 R y2 z.
Time Definition confluent {A} (R : relation A) := diamond (rtc R).
Time
Definition locally_confluent {A} (R : relation A) :=
  \226\136\128 x y1 y2, R x y1 \226\134\146 R x y2 \226\134\146 \226\136\131 z, rtc R y1 z \226\136\167 rtc R y2 z.
Time Hint Unfold nf red: core.
Time Section closure.
Time Context `{R : relation A}.
Time Hint Constructors rtc nsteps bsteps tc: core.
Time Lemma rtc_transitive x y z : rtc R x y \226\134\146 rtc R y z \226\134\146 rtc R x z.
Time Proof.
Time (induction 1; eauto).
Time Qed.
Time #[global]Instance rtc_po : (PreOrder (rtc R)) |10.
Time Proof.
Time split.
Time exact (@rtc_refl A R).
Time exact rtc_transitive.
Time Qed.
Time Lemma rtc_equivalence : Symmetric R \226\134\146 Equivalence (rtc R).
Time Proof.
Time (split; try apply _).
Time (intros x y).
Time (induction 1 as [| x1 x2 x3]; [ done | trans x2; eauto ]).
Time Qed.
Time Lemma rtc_once x y : R x y \226\134\146 rtc R x y.
Time Proof.
Time eauto.
Time Qed.
Time Lemma rtc_r x y z : rtc R x y \226\134\146 R y z \226\134\146 rtc R x z.
Time Proof.
Time (intros).
Time (etrans; eauto).
Time Qed.
Time Lemma rtc_inv x z : rtc R x z \226\134\146 x = z \226\136\168 (\226\136\131 y, R x y \226\136\167 rtc R y z).
Time Proof.
Time (inversion_clear 1; eauto).
Time Qed.
Time
Lemma rtc_ind_l (P : A \226\134\146 Prop) (z : A) (Prefl : P z)
  (Pstep : \226\136\128 x y, R x y \226\134\146 rtc R y z \226\134\146 P y \226\134\146 P x) : 
  \226\136\128 x, rtc R x z \226\134\146 P x.
Time Proof.
Time (induction 1; eauto).
Time Qed.
Time
Lemma rtc_ind_r_weak (P : A \226\134\146 A \226\134\146 Prop) (Prefl : \226\136\128 x, P x x)
  (Pstep : \226\136\128 x y z, rtc R x y \226\134\146 R y z \226\134\146 P x y \226\134\146 P x z) :
  \226\136\128 x z, rtc R x z \226\134\146 P x z.
Time Proof.
Time (cut (\226\136\128 y z, rtc R y z \226\134\146 \226\136\128 x, rtc R x y \226\134\146 P x y \226\134\146 P x z)).
Time {
Time eauto using rtc_refl.
Time }
Time (induction 1; eauto using rtc_r).
Time Qed.
Time
Lemma rtc_ind_r (P : A \226\134\146 Prop) (x : A) (Prefl : P x)
  (Pstep : \226\136\128 y z, rtc R x y \226\134\146 R y z \226\134\146 P y \226\134\146 P z) : 
  \226\136\128 z, rtc R x z \226\134\146 P z.
Time Proof.
Time (intros z p).
Time revert x z p Prefl Pstep.
Time (refine (rtc_ind_r_weak _ _ _); eauto).
Time Qed.
Time Lemma rtc_inv_r x z : rtc R x z \226\134\146 x = z \226\136\168 (\226\136\131 y, rtc R x y \226\136\167 R y z).
Time Proof.
Time revert z.
Time (apply rtc_ind_r; eauto).
Time Qed.
Time Lemma rtc_nf x y : rtc R x y \226\134\146 nf R x \226\134\146 x = y.
Time Proof.
Time (destruct 1 as [x| x y1 y2]).
Time done.
Time (intros []; eauto).
Time Qed.
Time Lemma nsteps_once x y : R x y \226\134\146 nsteps R 1 x y.
Time Proof.
Time eauto.
Time Qed.
Time Lemma nsteps_once_inv x y : nsteps R 1 x y \226\134\146 R x y.
Time Proof.
Time (inversion 1 as [| ? ? ? ? Hhead Htail]; inversion Htail; by subst).
Time Qed.
Time
Lemma nsteps_trans n m x y z :
  nsteps R n x y \226\134\146 nsteps R m y z \226\134\146 nsteps R (n + m) x z.
Time Proof.
Time (induction 1; simpl; eauto).
Time Qed.
Time Lemma nsteps_r n x y z : nsteps R n x y \226\134\146 R y z \226\134\146 nsteps R (S n) x z.
Time Proof.
Time (induction 1; eauto).
Time Qed.
Time Lemma nsteps_rtc n x y : nsteps R n x y \226\134\146 rtc R x y.
Time Proof.
Time (induction 1; eauto).
Time Qed.
Time Lemma rtc_nsteps x y : rtc R x y \226\134\146 \226\136\131 n, nsteps R n x y.
Time Proof.
Time (induction 1; firstorder  eauto).
Time Qed.
Time Lemma bsteps_once n x y : R x y \226\134\146 bsteps R (S n) x y.
Time Proof.
Time eauto.
Time Qed.
Time Lemma bsteps_plus_r n m x y : bsteps R n x y \226\134\146 bsteps R (n + m) x y.
Time Proof.
Time (induction 1; simpl; eauto).
Time Qed.
Time Lemma bsteps_weaken n m x y : n \226\137\164 m \226\134\146 bsteps R n x y \226\134\146 bsteps R m x y.
Time Proof.
Time (intros).
Time (rewrite (Minus.le_plus_minus n m); auto using bsteps_plus_r).
Time Qed.
Time Lemma bsteps_plus_l n m x y : bsteps R n x y \226\134\146 bsteps R (m + n) x y.
Time Proof.
Time (apply bsteps_weaken).
Time auto with arith.
Time Qed.
Time Lemma bsteps_S n x y : bsteps R n x y \226\134\146 bsteps R (S n) x y.
Time Proof.
Time (apply bsteps_weaken).
Time lia.
Time Qed.
Time
Lemma bsteps_trans n m x y z :
  bsteps R n x y \226\134\146 bsteps R m y z \226\134\146 bsteps R (n + m) x z.
Time Proof.
Time (induction 1; simpl; eauto using bsteps_plus_l).
Time Qed.
Time Lemma bsteps_r n x y z : bsteps R n x y \226\134\146 R y z \226\134\146 bsteps R (S n) x z.
Time Proof.
Time (induction 1; eauto).
Time Qed.
Time Lemma bsteps_rtc n x y : bsteps R n x y \226\134\146 rtc R x y.
Time Proof.
Time (induction 1; eauto).
Time Qed.
Time Lemma rtc_bsteps x y : rtc R x y \226\134\146 \226\136\131 n, bsteps R n x y.
Time Proof.
Time (induction 1; [ exists 0; constructor |  ]).
Time naive_solver eauto.
Time Qed.
Time
Lemma bsteps_ind_r (P : nat \226\134\146 A \226\134\146 Prop) (x : A) (Prefl : \226\136\128 n, P n x)
  (Pstep : \226\136\128 n y z, bsteps R n x y \226\134\146 R y z \226\134\146 P n y \226\134\146 P (S n) z) :
  \226\136\128 n z, bsteps R n x z \226\134\146 P n z.
Time Proof.
Time
(cut
  (\226\136\128 m y z,
     bsteps R m y z
     \226\134\146 \226\136\128 n,
         bsteps R n x y \226\134\146 (\226\136\128 m', n \226\137\164 m' \226\136\167 m' \226\137\164 n + m \226\134\146 P m' y) \226\134\146 P (n + m) z)).
Time {
Time (intros help ?).
Time (change_no_check n with (0 + n)).
Time eauto.
Time }
Time (induction 1 as [| m x' y z p2 p3 IH]; [ by eauto with arith |  ]).
Time (intros n p1 H).
Time (rewrite <- plus_n_Sm).
Time (apply (IH (S n)); [ by eauto using bsteps_r |  ]).
Time (intros [| m'] [? ?]; [ lia |  ]).
Time (apply Pstep with x').
Time -
Time (apply bsteps_weaken with n; intuition lia).
Time -
Time done.
Time -
Time (apply H; intuition lia).
Time Qed.
Time Lemma tc_transitive x y z : tc R x y \226\134\146 tc R y z \226\134\146 tc R x z.
Time Proof.
Time (induction 1; eauto).
Time Qed.
Time #[global]Instance tc_transitive' : (Transitive (tc R)).
Time Proof.
Time exact tc_transitive.
Time Qed.
Time Lemma tc_r x y z : tc R x y \226\134\146 R y z \226\134\146 tc R x z.
Time Proof.
Time (intros).
Time (etrans; eauto).
Time Qed.
Time Lemma tc_rtc_l x y z : rtc R x y \226\134\146 tc R y z \226\134\146 tc R x z.
Time Proof.
Time (induction 1; eauto).
Time Qed.
Time Lemma tc_rtc_r x y z : tc R x y \226\134\146 rtc R y z \226\134\146 tc R x z.
Time Proof.
Time (intros Hxy Hyz).
Time revert x Hxy.
Time (induction Hyz; eauto using tc_r).
Time Qed.
Time Lemma tc_rtc x y : tc R x y \226\134\146 rtc R x y.
Time Proof.
Time (induction 1; eauto).
Time Qed.
Time #[global]Instance sc_symmetric : (Symmetric (sc R)).
Time Proof.
Time (unfold Symmetric, sc).
Time naive_solver.
Time Qed.
Time Lemma sc_lr x y : R x y \226\134\146 sc R x y.
Time Proof.
Time by left.
Time Qed.
Time Lemma sc_rl x y : R y x \226\134\146 sc R x y.
Time Proof.
Time by right.
Time Qed.
Time End closure.
Time Section more_closure.
Time Context `{R : relation A}.
Time #[global]Instance rtsc_equivalence : (Equivalence (rtsc R)) |10.
Time Proof.
Time (apply rtc_equivalence, _).
Time Qed.
Time Lemma rtsc_lr x y : R x y \226\134\146 rtsc R x y.
Time Proof.
Time (unfold rtsc).
Time eauto using sc_lr, rtc_once.
Time Qed.
Time Lemma rtsc_rl x y : R y x \226\134\146 rtsc R x y.
Time Proof.
Time (unfold rtsc).
Time eauto using sc_rl, rtc_once.
Time Qed.
Time Lemma rtc_rtsc_rl x y : rtc R x y \226\134\146 rtsc R x y.
Time Proof.
Time (induction 1; econstructor; eauto using sc_lr).
Time Qed.
Time Lemma rtc_rtsc_lr x y : rtc R y x \226\134\146 rtsc R x y.
Time Proof.
Time (intros).
Time symmetry.
Time eauto using rtc_rtsc_rl.
Time Qed.
Time End more_closure.
Time Section properties.
Time Context `{R : relation A}.
Time Hint Constructors rtc nsteps bsteps tc: core.
Time Lemma acc_not_ex_loop x : Acc (flip R) x \226\134\146 \194\172 ex_loop R x.
Time Proof.
Time (unfold not).
Time (induction 1; destruct 1; eauto).
Time Qed.
Time Lemma all_loop_red x : all_loop R x \226\134\146 red R x.
Time Proof.
Time (destruct 1; auto).
Time Qed.
Time Lemma all_loop_step x y : all_loop R x \226\134\146 R x y \226\134\146 all_loop R y.
Time Proof.
Time (destruct 1; auto).
Time Qed.
Time Lemma all_loop_rtc x y : all_loop R x \226\134\146 rtc R x y \226\134\146 all_loop R y.
Time Proof.
Time (induction 2; eauto using all_loop_step).
Time Qed.
Time Lemma all_loop_alt x : all_loop R x \226\134\148 (\226\136\128 y, rtc R x y \226\134\146 red R y).
Time Proof.
Time (split; [ eauto using all_loop_red, all_loop_rtc |  ]).
Time (intros H).
Time (cut (\226\136\128 z, rtc R x z \226\134\146 all_loop R z); [ eauto |  ]).
Time cofix FIX.
Time (constructor; eauto using rtc_r).
Time Qed.
Time
Lemma confluent_alt :
  confluent R \226\134\148 (\226\136\128 x y, rtsc R x y \226\134\146 \226\136\131 z, rtc R x z \226\136\167 rtc R y z).
Time Proof.
Time split.
Time -
Time (intros Hcr).
Time (induction 1 as [x| x y1 y1' [Hy1| Hy1] Hy1' (z, (IH1, IH2))]; eauto).
Time (destruct (Hcr y1 x z) as (z', (?, ?)); eauto using rtc_transitive).
Time -
Time (intros Hcr x y1 y2 Hy1 Hy2).
Time (apply Hcr; trans x; eauto using rtc_rtsc_rl, rtc_rtsc_lr).
Time Qed.
Time
Lemma confluent_nf_r x y : confluent R \226\134\146 rtsc R x y \226\134\146 nf R y \226\134\146 rtc R x y.
Time Proof.
Time (rewrite confluent_alt).
Time (intros Hcr ? ?).
Time (destruct (Hcr x y) as (z, (Hx, Hy)); auto).
Time by apply rtc_nf in Hy as ->.
Time Qed.
Time
Lemma confluent_nf_l x y : confluent R \226\134\146 rtsc R x y \226\134\146 nf R x \226\134\146 rtc R y x.
Time Proof.
Time (intros).
Time by apply (confluent_nf_r y x).
Time Qed.
Time Lemma diamond_confluent : diamond R \226\134\146 confluent R.
Time Proof.
Time (intros Hdiam).
Time
(assert
  (Hstrip : \226\136\128 x y1 y2, rtc R x y1 \226\134\146 R x y2 \226\134\146 \226\136\131 z, rtc R y1 z \226\136\167 rtc R y2 z)).
Time {
Time (intros x y1 y2 Hy1; revert y2).
Time
(induction Hy1 as [x| x y1 y1' Hy1 Hy1' IH]; [ by eauto |  ]; intros y2 Hy2).
Time (destruct (Hdiam x y1 y2) as (z, (Hy1z, Hy2z)); auto).
Time (destruct (IH z) as (z', (?, ?)); eauto).
Time }
Time (intros x y1 y2 Hy1; revert y2).
Time
(induction Hy1 as [x| x y1 y1' Hy1 Hy1' IH]; [ by eauto |  ]; intros y2 Hy2).
Time (destruct (Hstrip x y2 y1) as (z, (?, ?)); eauto).
Time (destruct (IH z) as (z', (?, ?)); eauto using rtc_transitive).
Time Qed.
Time Lemma confluent_locally_confluent : confluent R \226\134\146 locally_confluent R.
Time Proof.
Time (unfold confluent, locally_confluent; eauto).
Time Qed.
Time
Lemma locally_confluent_confluent :
  (\226\136\128 x, sn R x) \226\134\146 locally_confluent R \226\134\146 confluent R.
Time Proof.
Time (intros Hsn Hcr x).
Time (induction (Hsn x) as [x _ IH]).
Time (intros y1 y2 Hy1 Hy2).
Time (destruct Hy1 as [x| x y1 y1' Hy1 Hy1']; [ by eauto |  ]).
Time (destruct Hy2 as [x| x y2 y2' Hy2 Hy2']; [ by eauto |  ]).
Time (destruct (Hcr x y1 y2) as (z, (Hy1z, Hy2z)); auto).
Time (destruct (IH _ Hy1 y1' z) as (z1, (?, ?)); auto).
Time
(destruct (IH _ Hy2 y2' z1) as (z2, (?, ?)); eauto using rtc_transitive).
Time Qed.
Time End properties.
Time Section subrel.
Time Context {A} (R1 R2 : relation A).
Time Notation subrel := (\226\136\128 x y, R1 x y \226\134\146 R2 x y).
Time Lemma red_subrel x : subrel \226\134\146 red R1 x \226\134\146 red R2 x.
Time Proof.
Time (intros ? [y ?]; eauto).
Time Qed.
Time Lemma nf_subrel x : subrel \226\134\146 nf R2 x \226\134\146 nf R1 x.
Time Proof.
Time (intros ? H1 H2; destruct H1; by apply red_subrel).
Time Qed.
Time Lemma rtc_subrel x y : subrel \226\134\146 rtc R1 x y \226\134\146 rtc R2 x y.
Time Proof.
Time (induction 2; [ by apply rtc_refl |  ]).
Time (eapply rtc_l; eauto).
Time Qed.
Time End subrel.
Time
Lemma Acc_impl {A} (R1 R2 : relation A) x :
  Acc R1 x \226\134\146 (\226\136\128 y1 y2, R2 y1 y2 \226\134\146 R1 y1 y2) \226\134\146 Acc R2 x.
Time Proof.
Time (induction 1; constructor; naive_solver).
Time Qed.
Time Notation wf := well_founded.
Time
Definition wf_guard `{R : relation A} (n : nat) (wfR : wf R) : 
  wf R := Acc_intro_generator n wfR.
Time Strategy 100 [wf_guard].
Time
Lemma wf_projected `{R1 : relation A} `(R2 : relation B) 
  (f : A \226\134\146 B) : (\226\136\128 x y, R1 x y \226\134\146 R2 (f x) (f y)) \226\134\146 wf R2 \226\134\146 wf R1.
Time Proof.
Time (intros Hf Hwf).
Time (cut (\226\136\128 y, Acc R2 y \226\134\146 \226\136\128 x, y = f x \226\134\146 Acc R1 x)).
Time {
Time (intros aux x).
Time (apply (aux (f x)); auto).
Time }
Time (induction 1 as [y _ IH]).
Time (intros x ?).
Time subst.
Time constructor.
Time (intros).
Time (apply (IH (f y)); auto).
Time Qed.
Time
Lemma Fix_F_proper `{R : relation A} (B : A \226\134\146 Type) 
  (E : \226\136\128 x, relation (B x)) (F : \226\136\128 x, (\226\136\128 y, R y x \226\134\146 B y) \226\134\146 B x)
  (HF : \226\136\128 (x : A) (f g : \226\136\128 y, R y x \226\134\146 B y),
          (\226\136\128 y Hy Hy', E _ (f y Hy) (g y Hy')) \226\134\146 E _ (F x f) (F x g)) 
  (x : A) (acc1 acc2 : Acc R x) : E _ (Fix_F B F acc1) (Fix_F B F acc2).
Time Proof.
Time revert x acc1 acc2.
Time fix FIX 2.
Time (intros x [acc1] [acc2]; simpl; auto).
Time Qed.
Time
Lemma Fix_unfold_rel `{R : relation A} (wfR : wf R) 
  (B : A \226\134\146 Type) (E : \226\136\128 x, relation (B x))
  (F : \226\136\128 x, (\226\136\128 y, R y x \226\134\146 B y) \226\134\146 B x)
  (HF : \226\136\128 (x : A) (f g : \226\136\128 y, R y x \226\134\146 B y),
          (\226\136\128 y Hy Hy', E _ (f y Hy) (g y Hy')) \226\134\146 E _ (F x f) (F x g)) 
  (x : A) : E _ (Fix wfR B F x) (F x (\206\187 y _, Fix wfR B F y)).
Time Proof.
Time (unfold Fix).
Time (destruct (wfR x); simpl).
Time (apply HF; intros).
Time (apply Fix_F_proper; auto).
Time Qed.
