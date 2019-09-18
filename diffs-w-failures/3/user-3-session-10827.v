Time From stdpp Require Export proof_irrel.
Time Set Default Proof Using "Type*".
Time Lemma dec_stable `{Decision P} : \194\172 \194\172 P \226\134\146 P.
Time Proof.
Time firstorder.
Time Qed.
Time Lemma Is_true_reflect (b : bool) : reflect b b.
Time Proof.
Time (destruct b).
Time (left; constructor).
Time right.
Time (intros []).
Time Qed.
Time Instance: (Inj (=) (\226\134\148) Is_true).
Time Proof.
Time (intros [] []; simpl; intuition).
Time Qed.
Time
Lemma decide_True {A} `{Decision P} (x y : A) :
  P \226\134\146 (if decide P then x else y) = x.
Time Proof.
Time (destruct (decide P); tauto).
Time Qed.
Time
Lemma decide_False {A} `{Decision P} (x y : A) :
  \194\172 P \226\134\146 (if decide P then x else y) = y.
Time Proof.
Time (destruct (decide P); tauto).
Time Qed.
Time
Lemma decide_iff {A} P Q `{Decision P} `{Decision Q} 
  (x y : A) :
  P \226\134\148 Q \226\134\146 (if decide P then x else y) = (if decide Q then x else y).
Time Proof.
Time (intros [? ?]).
Time (destruct (decide P), (decide Q); tauto).
Time Qed.
Time
Lemma decide_left `{Decision P} `{!ProofIrrel P} (HP : P) :
  decide P = left HP.
Time Proof.
Time (destruct (decide P); [  | contradiction ]).
Time f_equal.
Time (apply proof_irrel).
Time Qed.
Time
Lemma decide_right `{Decision P} `{!ProofIrrel (\194\172 P)} 
  (HP : \194\172 P) : decide P = right HP.
Time Proof.
Time (destruct (decide P); [ contradiction |  ]).
Time f_equal.
Time (apply proof_irrel).
Time Qed.
Time
Tactic Notation "destruct_decide" constr(dec) "as" ident(H) :=
 (destruct dec as [H| H];
   try match type of H with
       | \194\172 \194\172 _ => apply dec_stable in H
       end).
Time
Tactic Notation "destruct_decide" constr(dec) :=
 (let H := fresh in
  destruct_decide
  dec
  as
  H).
Time
Tactic Notation "case_decide" "as" ident(Hd) :=
 (match goal with
  | H:context [ @decide ?P ?dec ] |- _ => destruct_decide @decide P dec as Hd
  | H:context [ @decide_rel _ _ ?R ?x ?y ?dec ]
    |- _ => destruct_decide @decide_rel _ _ R x y dec as Hd
  | |- context [ @decide ?P ?dec ] => destruct_decide @decide P dec as Hd
  | |- context [ @decide_rel _ _ ?R ?x ?y ?dec ] => destruct_decide
    @decide_rel _ _ R x y dec as Hd
  end).
Time Tactic Notation "case_decide" := (let H := fresh in
                                       case_decide
                                       as
                                       H).
Time
Ltac
 solve_trivial_decision :=
  match goal with
  | |- Decision ?P => apply _
  | |- sumbool ?P (\194\172 ?P) => change_no_check (Decision P); apply _
  end.
Time
Ltac
 solve_decision :=
  unfold EqDecision; intros; (first
   [ solve_trivial_decision
   | unfold Decision; decide equality; solve_trivial_decision ]).
Time
Notation swap_if S:= match S with
                     | left H => right H
                     | right H => left H
                     end.
Time Notation cast_if S:= (if S then left _ else right _).
Time Notation cast_if_and S1 S2:= (if S1 then cast_if S2 else right _).
Time
Notation cast_if_and3 S1 S2 S3:= (if S1 then cast_if_and S2 S3 else right _).
Time
Notation cast_if_and4 S1 S2 S3 S4:=
  (if S1 then cast_if_and3 S2 S3 S4 else right _).
Time
Notation cast_if_and5 S1 S2 S3 S4 S5:=
  (if S1 then cast_if_and4 S2 S3 S4 S5 else right _).
Time
Notation cast_if_and6 S1 S2 S3 S4 S5 S6:=
  (if S1 then cast_if_and5 S2 S3 S4 S5 S6 else right _).
Time Notation cast_if_or S1 S2:= (if S1 then left _ else cast_if S2).
Time
Notation cast_if_or3 S1 S2 S3:= (if S1 then left _ else cast_if_or S2 S3).
Time Notation cast_if_not_or S1 S2:= (if S1 then cast_if S2 else left _).
Time Notation cast_if_not S:= (if S then right _ else left _).
Time
Definition bool_decide (P : Prop) {dec : Decision P} : bool :=
  if dec then true else false.
Time
Lemma bool_decide_reflect P `{dec : Decision P} : reflect P (bool_decide P).
Time Proof.
Time (unfold bool_decide).
Time (destruct dec; [ left | right ]; assumption).
Time Qed.
Time
Lemma bool_decide_decide P `{!Decision P} :
  bool_decide P = (if decide P then true else false).
Time Proof.
Time reflexivity.
Time Qed.
Time
Lemma decide_bool_decide P {Hdec : Decision P} {X : Type} 
  (x1 x2 : X) :
  (if decide P then x1 else x2) = (if bool_decide P then x1 else x2).
Time Proof.
Time (unfold bool_decide, decide).
Time (destruct Hdec; reflexivity).
Time Qed.
Time
Tactic Notation "case_bool_decide" "as" ident(Hd) :=
 (match goal with
  | H:context [ @bool_decide ?P ?dec ]
    |- _ => destruct_decide @bool_decide_reflect P dec as Hd
  | |- context [ @bool_decide ?P ?dec ] => destruct_decide
    @bool_decide_reflect P dec as Hd
  end).
Time
Tactic Notation "case_bool_decide" :=
 (let H := fresh in
  case_bool_decide
  as
  H).
Time
Lemma bool_decide_spec (P : Prop) {dec : Decision P} : bool_decide P \226\134\148 P.
Time Proof.
Time (unfold bool_decide).
Time (destruct dec; simpl; tauto).
Time Qed.
Time
Lemma bool_decide_unpack (P : Prop) {dec : Decision P} : bool_decide P \226\134\146 P.
Time Proof.
Time (rewrite bool_decide_spec; trivial).
Time Qed.
Time
Lemma bool_decide_pack (P : Prop) {dec : Decision P} : P \226\134\146 bool_decide P.
Time Proof.
Time (rewrite bool_decide_spec; trivial).
Time Qed.
Time Hint Resolve bool_decide_pack: core.
Time
Lemma bool_decide_eq_true (P : Prop) `{Decision P} : bool_decide P = true \226\134\148 P.
Time Proof.
Time (case_bool_decide; intuition discriminate).
Time Qed.
Time
Lemma bool_decide_eq_false (P : Prop) `{Decision P} :
  bool_decide P = false \226\134\148 \194\172 P.
Time Proof.
Time (case_bool_decide; intuition discriminate).
Time Qed.
Time
Lemma bool_decide_iff (P Q : Prop) `{Decision P} `{Decision Q} :
  P \226\134\148 Q \226\134\146 bool_decide P = bool_decide Q.
Time Proof.
Time (repeat case_bool_decide; tauto).
Time Qed.
Time Lemma bool_decide_eq_true_1 P `{!Decision P} : bool_decide P = true \226\134\146 P.
Time Proof.
Time (apply bool_decide_eq_true).
Time Qed.
Time Lemma bool_decide_eq_true_2 P `{!Decision P} : P \226\134\146 bool_decide P = true.
Time Proof.
Time (apply bool_decide_eq_true).
Time Qed.
Time
Lemma bool_decide_eq_false_1 P `{!Decision P} : bool_decide P = false \226\134\146 \194\172 P.
Time Proof.
Time (apply bool_decide_eq_false).
Time Qed.
Time
Lemma bool_decide_eq_false_2 P `{!Decision P} : \194\172 P \226\134\146 bool_decide P = false.
Time Proof.
Time (apply bool_decide_eq_false).
Time Qed.
Time Notation bool_decide_true := bool_decide_eq_true_2.
Time Notation bool_decide_false := bool_decide_eq_false_2.
Time
Definition dsig `(P : A \226\134\146 Prop) `{\226\136\128 x : A, Decision (P x)} :=
  {x | bool_decide (P x)}.
Time
Definition proj2_dsig `{\226\136\128 x : A, Decision (P x)} (x : dsig P) : 
  P (`x) := bool_decide_unpack _ (proj2_sig x).
Time
Definition dexist `{\226\136\128 x : A, Decision (P x)} (x : A) 
  (p : P x) : dsig P := x \226\134\190 bool_decide_pack _ p.
Time
Lemma dsig_eq `(P : A \226\134\146 Prop) `{\226\136\128 x, Decision (P x)} 
  (x y : dsig P) : x = y \226\134\148 `x = `y.
Time Proof.
Time (apply (sig_eq_pi _)).
Time Qed.
Time
Lemma dexists_proj1 `(P : A \226\134\146 Prop) `{\226\136\128 x, Decision (P x)} 
  (x : dsig P) p : dexist (`x) p = x.
Time Proof.
Time (apply dsig_eq; reflexivity).
Time Qed.
Time Instance True_dec : (Decision True) := (left I).
Time Instance False_dec : (Decision False) := (right (False_rect False)).
Time Instance Is_true_dec  b: (Decision (Is_true b)).
Time Proof.
Time (destruct b; simpl; apply _).
Time Defined.
Time Section prop_dec.
Time Context `(P_dec : Decision P) `(Q_dec : Decision Q).
Time #[global]Instance not_dec : (Decision (\194\172 P)).
Time Proof.
Time (refine (cast_if_not P_dec); intuition).
Time Defined.
Time #[global]Instance and_dec : (Decision (P \226\136\167 Q)).
Time Proof.
Time (refine (cast_if_and P_dec Q_dec); intuition).
Time Defined.
Time #[global]Instance or_dec : (Decision (P \226\136\168 Q)).
Time Proof.
Time (refine (cast_if_or P_dec Q_dec); intuition).
Time Defined.
Time #[global]Instance impl_dec : (Decision (P \226\134\146 Q)).
Time Proof.
Time (refine (if P_dec then cast_if Q_dec else left _); intuition).
Time Defined.
Time End prop_dec.
Time
Instance iff_dec  `(P_dec : Decision P) `(Q_dec : Decision Q):
 (Decision (P \226\134\148 Q)) := (and_dec _ _).
Time Instance bool_eq_dec : (EqDecision bool).
Time Proof.
Time solve_decision.
Time Defined.
Time Instance unit_eq_dec : (EqDecision unit).
Time Proof.
Time solve_decision.
Time Defined.
Time Instance Empty_set_eq_dec : (EqDecision Empty_set).
Time Proof.
Time solve_decision.
Time Defined.
Time
Instance prod_eq_dec  `{EqDecision A} `{EqDecision B}: (EqDecision (A * B)).
Time Proof.
Time solve_decision.
Time Defined.
Time
Instance sum_eq_dec  `{EqDecision A} `{EqDecision B}: (EqDecision (A + B)).
Time Proof.
Time solve_decision.
Time Defined.
Time
Instance curry_dec  `(P_dec : \226\136\128 (x : A) (y : B), Decision (P x y)) 
 p: (Decision (curry P p)) :=
 match p as p return (Decision (curry P p)) with
 | (x, y) => P_dec x y
 end.
Time
Instance sig_eq_dec  `(P : A \226\134\146 Prop) `{\226\136\128 x, ProofIrrel (P x)}
 `{EqDecision A}: (EqDecision (sig P)).
Time Proof.
Time
(refine (\206\187 x y, cast_if (decide (`x = `y))); rewrite sig_eq_pi; trivial).
Time Defined.
Time Lemma not_and_l {P Q : Prop} `{Decision P} : \194\172 (P \226\136\167 Q) \226\134\148 \194\172 P \226\136\168 \194\172 Q.
Time Proof.
Time (destruct (decide P); tauto).
Time Qed.
Time Lemma not_and_r {P Q : Prop} `{Decision Q} : \194\172 (P \226\136\167 Q) \226\134\148 \194\172 P \226\136\168 \194\172 Q.
Time Proof.
Time (destruct (decide Q); tauto).
Time Qed.
Time
Lemma not_and_l_alt {P Q : Prop} `{Decision P} : \194\172 (P \226\136\167 Q) \226\134\148 \194\172 P \226\136\168 \194\172 Q \226\136\167 P.
Time Proof.
Time (destruct (decide P); tauto).
Time Qed.
Time
Lemma not_and_r_alt {P Q : Prop} `{Decision Q} : \194\172 (P \226\136\167 Q) \226\134\148 \194\172 P \226\136\167 Q \226\136\168 \194\172 Q.
Time Proof.
Time (destruct (decide Q); tauto).
Time Qed.
Time #[program]
Definition inj_eq_dec `{EqDecision A} {B} (f : B \226\134\146 A) 
  `{!Inj (=) (=) f} : EqDecision B := \206\187 x y, cast_if (decide (f x = f y)).
Time Solve Obligations with firstorder  congruence.
Time
Definition flip_dec {A} (R : relation A) `{!RelDecision R} :
  RelDecision (flip R) := \206\187 x y, decide_rel R y x.
Time
Hint Extern 3 (RelDecision (flip _)) => (apply flip_dec): typeclass_instances.
