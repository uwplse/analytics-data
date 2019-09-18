Time From Coq.QArith Require Import QArith_base Qcanon.
Time From stdpp Require Export list numbers.
Time Set Default Proof Using "Type".
Time #[local]Open Scope positive.
Time
Class Countable A `{EqDecision A} :={encode : A \226\134\146 positive;
                                     decode : positive \226\134\146 option A;
                                     decode_encode :
                                      forall x, decode (encode x) = Some x}.
Time Hint Mode Countable ! -: typeclass_instances.
Time Arguments encode : simpl never.
Time Arguments decode : simpl never.
Time
Definition encode_nat `{Countable A} (x : A) : nat :=
  pred (Pos.to_nat (encode x)).
Time
Definition decode_nat `{Countable A} (i : nat) : option A :=
  decode (Pos.of_nat (S i)).
Time Instance encode_inj  `{Countable A}: (Inj (=) (=) (encode (A:=A))).
Time Proof.
Time (intros x y Hxy; apply (inj Some)).
Time by rewrite <- (decode_encode x), Hxy, decode_encode.
Time Qed.
Time
Instance encode_nat_inj  `{Countable A}: (Inj (=) (=) (encode_nat (A:=A))).
Time Proof.
Time (unfold encode_nat; intros x y Hxy; apply (inj encode); lia).
Time Qed.
Time
Lemma decode_encode_nat `{Countable A} (x : A) :
  decode_nat (encode_nat x) = Some x.
Time Proof.
Time (pose proof (Pos2Nat.is_pos (encode x))).
Time (unfold decode_nat, encode_nat).
Time (rewrite Nat.succ_pred by lia).
Time by rewrite Pos2Nat.id, decode_encode.
Time Qed.
Time Section choice.
Time Context `{Countable A} (P : A \226\134\146 Prop).
Time
Inductive choose_step : relation positive :=
  | choose_step_None :
      forall {p}, decode (A:=A) p = None \226\134\146 choose_step (Pos.succ p) p
  | choose_step_Some :
      forall {p} {x : A},
      decode p = Some x \226\134\146 \194\172 P x \226\134\146 choose_step (Pos.succ p) p.
Time Lemma choose_step_acc : (\226\136\131 x, P x) \226\134\146 Acc choose_step 1%positive.
Time Proof.
Time (intros [x Hx]).
Time (cut (\226\136\128 i p, i \226\137\164 encode x \226\134\146 1 + encode x = p + i \226\134\146 Acc choose_step p)).
Time {
Time (intros help).
Time by apply (help (encode x)).
Time }
Time (induction i as [| i IH] using Pos.peano_ind; intros p ? ?).
Time {
Time constructor.
Time (intros j).
Time (assert (p = encode x) by lia; subst).
Time
(inversion 1 as [? Hd| ? ? Hd]; subst; rewrite decode_encode in Hd;
  congruence).
Time }
Time constructor.
Time (intros j).
Time (inversion 1 as [? Hd| ? y Hd]; subst; auto with lia).
Time Qed.
Time Context `{\226\136\128 x, Decision (P x)}.
Time
Fixpoint choose_go {i} (acc : Acc choose_step i) : A :=
  match Some_dec (decode i) with
  | inleft (x \226\134\190 Hx) =>
      match decide (P x) with
      | left _ => x
      | right H => choose_go (Acc_inv acc (choose_step_Some Hx H))
      end
  | inright H => choose_go (Acc_inv acc (choose_step_None H))
  end.
Time
Fixpoint choose_go_correct {i} (acc : Acc choose_step i) : P (choose_go acc).
Time Proof.
Time (destruct acc; simpl).
Time (repeat case_match; auto).
Time Qed.
Time
Fixpoint choose_go_pi {i} (acc1 acc2 : Acc choose_step i) :
choose_go acc1 = choose_go acc2.
Time Proof.
Time (destruct acc1, acc2; simpl; repeat case_match; auto).
Time Qed.
Time Definition choose (H : \226\136\131 x, P x) : A := choose_go (choose_step_acc H).
Time
Definition choose_correct (H : \226\136\131 x, P x) : P (choose H) :=
  choose_go_correct _.
Time
Definition choose_pi (H1 H2 : \226\136\131 x, P x) : choose H1 = choose H2 :=
  choose_go_pi _ _.
Time Definition choice (HA : \226\136\131 x, P x) : {x | P x} := _ \226\134\190 choose_correct HA.
Time End choice.
Time
Lemma surj_cancel `{Countable A} `{EqDecision B} (f : A \226\134\146 B) 
  `{!Surj (=) f} : {g : B \226\134\146 A & Cancel (=) f g}.
Time Proof.
Time exists (\206\187 y, choose (\206\187 x, f x = y) (surj f y)).
Time (intros y).
Time by rewrite (choose_correct (\206\187 x, f x = y) (surj f y)).
Time Qed.
Time Section inj_countable.
Time Context `{Countable A} `{EqDecision B}.
Time Context (f : B \226\134\146 A) (g : A \226\134\146 option B) (fg : \226\136\128 x, g (f x) = Some x).
Time #[program]
Instance inj_countable : (Countable B) :=
 {| encode := fun y => encode (f y); decode := fun p => x \226\134\144 decode p; g x |}.
Time Next Obligation.
Time (intros y; simpl; rewrite decode_encode; eauto).
Time Qed.
Time End inj_countable.
Time Section inj_countable'.
Time Context `{Countable A} `{EqDecision B}.
Time Context (f : B \226\134\146 A) (g : A \226\134\146 B) (fg : \226\136\128 x, g (f x) = x).
Time #[program]
Instance inj_countable' : (Countable B) := (inj_countable f (Some \226\136\152 g) _).
Time Next Obligation.
Time (intros x).
Time by f_equal /=.
Time Qed.
Time End inj_countable'.
Time #[program]
Instance unit_countable : (Countable unit) :=
 {| encode := fun u => 1; decode := fun p => Some () |}.
Time Next Obligation.
Time by intros [].
Time Qed.
Time #[program]
Instance bool_countable : (Countable bool) :=
 {|
 encode := fun b => if b then 1 else 2;
 decode := fun p =>
           Some match p return bool with
                | 1 => true
                | _ => false
                end |}.
Time Next Obligation.
Time by intros [].
Time Qed.
Time #[program]
Instance option_countable  `{Countable A}: (Countable (option A)) :=
 {|
 encode := fun o =>
           match o with
           | None => 1
           | Some x => Pos.succ (encode x)
           end;
 decode := fun p =>
           if decide (p = 1) then Some None else Some <$> decode (Pos.pred p) |}.
Time Next Obligation.
Time (intros ? ? ? [x| ]; simpl; repeat case_decide; auto with lia).
Time by rewrite Pos.pred_succ, decode_encode.
Time Qed.
Time #[program]
Instance sum_countable  `{Countable A} `{Countable B}:
 (Countable (A + B)%type) :=
 {|
 encode := fun xy =>
           match xy with
           | inl x => (encode x)~0
           | inr y => (encode y)~1
           end;
 decode := fun p =>
           match p with
           | 1 => None
           | p~0 => inl <$> decode p
           | p~1 => inr <$> decode p
           end |}.
Time Next Obligation.
Time by intros ? ? ? ? ? ? [x| y]; simpl; rewrite decode_encode.
Time Qed.
Time
Fixpoint prod_encode_fst (p : positive) : positive :=
  match p with
  | 1 => 1
  | p~0 => (prod_encode_fst p)~0~0
  | p~1 => (prod_encode_fst p)~0~1
  end.
Time
Fixpoint prod_encode_snd (p : positive) : positive :=
  match p with
  | 1 => 1~0
  | p~0 => (prod_encode_snd p)~0~0
  | p~1 => (prod_encode_snd p)~1~0
  end.
Time
Fixpoint prod_encode (p q : positive) : positive :=
  match p, q with
  | 1, 1 => 1~1
  | p~0, 1 => (prod_encode_fst p)~1~0
  | p~1, 1 => (prod_encode_fst p)~1~1
  | 1, q~0 => (prod_encode_snd q)~0~1
  | 1, q~1 => (prod_encode_snd q)~1~1
  | p~0, q~0 => (prod_encode p q)~0~0
  | p~0, q~1 => (prod_encode p q)~1~0
  | p~1, q~0 => (prod_encode p q)~0~1
  | p~1, q~1 => (prod_encode p q)~1~1
  end.
Time
Fixpoint prod_decode_fst (p : positive) : option positive :=
  match p with
  | p~0~0 => (~0) <$> prod_decode_fst p
  | p~0~1 => Some match prod_decode_fst p with
                  | Some q => q~1
                  | _ => 1
                  end
  | p~1~0 => (~0) <$> prod_decode_fst p
  | p~1~1 => Some match prod_decode_fst p with
                  | Some q => q~1
                  | _ => 1
                  end
  | 1~0 => None
  | 1~1 => Some 1
  | 1 => Some 1
  end.
Time
Fixpoint prod_decode_snd (p : positive) : option positive :=
  match p with
  | p~0~0 => (~0) <$> prod_decode_snd p
  | p~0~1 => (~0) <$> prod_decode_snd p
  | p~1~0 => Some match prod_decode_snd p with
                  | Some q => q~1
                  | _ => 1
                  end
  | p~1~1 => Some match prod_decode_snd p with
                  | Some q => q~1
                  | _ => 1
                  end
  | 1~0 => Some 1
  | 1~1 => Some 1
  | 1 => None
  end.
Time
Lemma prod_decode_encode_fst p q : prod_decode_fst (prod_encode p q) = Some p.
Time Proof.
Time (assert (\226\136\128 p, prod_decode_fst (prod_encode_fst p) = Some p)).
Time {
Time (intros p').
Time by induction p'; simplify_option_eq.
Time }
Time (assert (\226\136\128 p, prod_decode_fst (prod_encode_snd p) = None)).
Time {
Time (intros p').
Time by induction p'; simplify_option_eq.
Time }
Time revert q.
Time by induction p; intros [?| ?| ]; simplify_option_eq.
Time Qed.
Time
Lemma prod_decode_encode_snd p q : prod_decode_snd (prod_encode p q) = Some q.
Time Proof.
Time (assert (\226\136\128 p, prod_decode_snd (prod_encode_snd p) = Some p)).
Time {
Time (intros p').
Time by induction p'; simplify_option_eq.
Time }
Time (assert (\226\136\128 p, prod_decode_snd (prod_encode_fst p) = None)).
Time {
Time (intros p').
Time by induction p'; simplify_option_eq.
Time }
Time revert q.
Time by induction p; intros [?| ?| ]; simplify_option_eq.
Time Qed.
Time #[program]
Instance prod_countable  `{Countable A} `{Countable B}:
 (Countable (A * B)%type) :=
 {|
 encode := fun xy => prod_encode (encode xy.1) (encode xy.2);
 decode := fun p =>
           x \226\134\144 prod_decode_fst p \226\137\171= decode;
           y \226\134\144 prod_decode_snd p \226\137\171= decode; Some (x, y) |}.
Time Next Obligation.
Time (intros ? ? ? ? ? ? [x y]; simpl).
Time (rewrite prod_decode_encode_fst, prod_decode_encode_snd; simpl).
Time by rewrite !decode_encode.
Time Qed.
Time #[global, program]
Instance list_countable  `{Countable A}: (Countable (list A)) :=
 {|
 encode := fun xs => positives_flatten (encode <$> xs);
 decode := fun p => positives \226\134\144 positives_unflatten p; mapM decode positives |}.
Time Next Obligation.
Time (intros A EqA CA xs).
Time (simpl).
Time (rewrite positives_unflatten_flatten).
Time (simpl).
Time (apply (mapM_fmap_Some _ _ _ decode_encode)).
Time Qed.
Time
Instance pos_countable : (Countable positive) :=
 {| encode := id; decode := Some; decode_encode := fun x => eq_refl |}.
Time #[program]
Instance N_countable : (Countable N) :=
 {|
 encode := fun x => match x with
                    | N0 => 1
                    | Npos p => Pos.succ p
                    end;
 decode := fun p =>
           if decide (p = 1) then Some 0%N else Some (Npos (Pos.pred p)) |}.
Time Next Obligation.
Time (intros [| p]; simpl; [ done |  ]).
Time by rewrite decide_False, Pos.pred_succ by by destruct p.
Time Qed.
Time #[program]
Instance Z_countable : (Countable Z) :=
 {|
 encode := fun x =>
           match x with
           | Z0 => 1
           | Zpos p => p~0
           | Zneg p => p~1
           end;
 decode := fun p =>
           Some match p with
                | 1 => Z0
                | p~0 => Zpos p
                | p~1 => Zneg p
                end |}.
Time Next Obligation.
Time by intros [| p| p].
Time Qed.
Time #[program]
Instance nat_countable : (Countable nat) :=
 {|
 encode := fun x => encode (N.of_nat x);
 decode := fun p => N.to_nat <$> decode p |}.
Time Next Obligation.
Time by intros x; lazy beta; rewrite decode_encode; csimpl; rewrite Nat2N.id.
Time Qed.
Time #[global, program]
Instance Qc_countable : (Countable Qc) :=
 (inj_countable (\206\187 p : Qc, let 'Qcmake (x # y) _ := p in (x, y))
    (\206\187 q : Z * positive, let '(x, y) := q in Some (Q2Qc (x # y))) _).
Time Next Obligation.
Time (intros [[x y] Hcan]).
Time f_equal.
Time (apply Qc_is_canon).
Time (simpl).
Time by rewrite Hcan.
Time Qed.
Time #[global, program]
Instance Qp_countable : (Countable Qp) :=
 (inj_countable Qp_car (\206\187 p : Qc, guard (0 < p)%Qc as Hp; Some (mk_Qp p Hp))
    _).
Time Next Obligation.
Time (intros [p Hp]).
Time (unfold mguard, option_guard; simpl).
Time (case_match; [  | done ]).
Time f_equal.
Time by apply Qp_eq.
Time Qed.
Time Close Scope positive.
Time
Inductive gen_tree (T : Type) : Type :=
  | GenLeaf : T \226\134\146 gen_tree T
  | GenNode : nat \226\134\146 list (gen_tree T) \226\134\146 gen_tree T.
Time Arguments GenLeaf {_} _ : assert.
Time Arguments GenNode {_} _ _ : assert.
Time Instance gen_tree_dec  `{EqDecision T}: (EqDecision (gen_tree T)).
Time Proof.
Time
(refine
  (fix go t1 t2 :=
     let _ : EqDecision _ := @go in
     match t1, t2 with
     | GenLeaf x1, GenLeaf x2 => cast_if (decide (x1 = x2))
     | GenNode n1 ts1, GenNode n2 ts2 =>
         cast_if_and (decide (n1 = n2)) (decide (ts1 = ts2))
     | _, _ => right _
     end); abstract congruence).
Time Defined.
Time
Fixpoint gen_tree_to_list {T} (t : gen_tree T) : list (nat * nat + T) :=
  match t with
  | GenLeaf x => [inr x]
  | GenNode n ts => (ts \226\137\171= gen_tree_to_list) ++ [inl (length ts, n)]
  end.
Time
Fixpoint gen_tree_of_list {T} (k : list (gen_tree T))
(l : list (nat * nat + T)) : option (gen_tree T) :=
  match l with
  | [] => head k
  | inr x :: l => gen_tree_of_list (GenLeaf x :: k) l
  | inl (len, n) :: l =>
      gen_tree_of_list (GenNode n (reverse (take len k)) :: drop len k) l
  end.
Time
Lemma gen_tree_of_to_list {T} k l (t : gen_tree T) :
  gen_tree_of_list k (gen_tree_to_list t ++ l) = gen_tree_of_list (t :: k) l.
Time Proof.
Time (revert t k l; fix FIX 1; intros [| n ts] k l; simpl; auto).
Time trans gen_tree_of_list (reverse ts ++ k) ([inl (length ts, n)] ++ l).
Time -
Time (rewrite <- (assoc_L _)).
Time revert k.
Time (generalize ([inl (length ts, n)] ++ l)).
Time (induction ts as [| t ts'' IH]; intros k ts'''; csimpl; auto).
Time (rewrite reverse_cons, <- !(assoc_L _), FIX; simpl; auto).
Time -
Time (simpl).
Time
by
 rewrite take_app_alt, drop_app_alt, reverse_involutive by by
  rewrite reverse_length.
Time Qed.
Time #[program]
Instance gen_tree_countable  `{Countable T}: (Countable (gen_tree T)) :=
 (inj_countable gen_tree_to_list (gen_tree_of_list []) _).
Time Next Obligation.
Time (intros T ? ? t).
Time
by rewrite <- (right_id_L [] _ (gen_tree_to_list _)), gen_tree_of_to_list.
Time Qed.
