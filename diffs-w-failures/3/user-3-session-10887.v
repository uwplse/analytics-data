Time From stdpp Require Export fin list.
Time From Coq.QArith Require Import QArith_base Qcanon.
Time From stdpp Require Export orders list.
Time From stdpp Require Export list numbers.
Time Set Default Proof Using "Type".
Time Open Scope vector_scope.
Time Notation vec := Vector.t.
Time Notation vnil := Vector.nil.
Time Arguments vnil {_}.
Time Notation vcons := Vector.cons.
Time Notation vapp := Vector.append.
Time Arguments vcons {_} _ {_} _.
Time Infix ":::" := vcons (at level 60, right associativity) : vector_scope.
Time Notation "(:::)" := vcons (only parsing) : vector_scope.
Time Notation "( x :::)" := (vcons x) (only parsing) : vector_scope.
Time Notation "(::: v )" := (\206\187 x, vcons x v) (only parsing) : vector_scope.
Time Notation "[# ] " := vnil : vector_scope.
Time Notation "[# x ] " := (vcons x vnil) : vector_scope.
Time
Notation "[# x ; .. ; y ] " := (vcons x .. (vcons y vnil) ..) : vector_scope.
Time Infix "+++" := vapp (at level 60, right associativity) : vector_scope.
Time Notation "(+++)" := vapp (only parsing) : vector_scope.
Time Notation "( v +++)" := (vapp v) (only parsing) : vector_scope.
Time Notation "(+++ w )" := (\206\187 v, vapp v w) (only parsing) : vector_scope.
Time Arguments Vector.nth {_} {_} !_ !_%fin /.
Time Infix "!!!" := Vector.nth (at level 20) : vector_scope.
Time Notation vec_rect2 := Vector.rect2.
Time
Ltac
 vec_double_ind v1 v2 :=
  match type of v1 with
  | vec _ ?n =>
      repeat
       match goal with
       | H':context [ n ] |- _ => var_neq v1 H'; var_neq v2 H'; revert H'
       end; revert n v1 v2;
       match goal with
       | |- \226\136\128 n v1 v2, @?P n v1 v2 => apply (vec_rect2 P)
       end
  end.
Time Notation vcons_inj := VectorSpec.cons_inj.
Time
Lemma vcons_inj_1 {A} {n} x y (v w : vec A n) : x ::: v = y ::: w \226\134\146 x = y.
Time Proof.
Time (apply vcons_inj).
Time Qed.
Time
Lemma vcons_inj_2 {A} {n} x y (v w : vec A n) : x ::: v = y ::: w \226\134\146 v = w.
Time Proof.
Time (apply vcons_inj).
Time Qed.
Time Lemma vec_eq {A} {n} (v w : vec A n) : (\226\136\128 i, v !!! i = w !!! i) \226\134\146 v = w.
Time Proof.
Time (vec_double_ind v w; [ done |  ]).
Time (intros n v w IH x y Hi).
Time f_equal.
Time -
Time (apply (Hi 0%fin)).
Time -
Time (apply IH).
Time (intros i).
Time (apply (Hi (FS i))).
Time Qed.
Time Instance vec_dec  {A} {dec : EqDecision A} {n}: (EqDecision (vec A n)).
Time Proof.
Time
(refine
  (vec_rect2 (\206\187 n (v w : vec A n), {v = w} + {v \226\137\160 w}) 
     (left _) (\206\187 _ _ _ H x y, cast_if_and (dec x y) H)); f_equal; eauto
  using vcons_inj_1, vcons_inj_2).
Time Defined.
Time Notation vec_0_inv := Vector.case0.
Time
Definition vec_S_inv {A} {n} (P : vec A (S n) \226\134\146 Type)
  (Hcons : \226\136\128 x v, P (x ::: v)) v : P v.
Time Proof.
Time revert P Hcons.
Time refine match v with
            | [# ] => tt
            | x ::: v => \206\187 P Hcons, Hcons x v
            end.
Time Defined.
Time
Ltac
 inv_vec v :=
  let T := type of v in
  match eval hnf in T with
  | vec _ ?n =>
      match eval hnf in n with
      | 0 =>
          revert dependent v;
           match goal with
           | |- \226\136\128 v, @?P v => apply (vec_0_inv P)
           end
      | S ?n =>
          revert dependent v;
           match goal with
           | |- \226\136\128 v, @?P v => apply (vec_S_inv P)
           end; try (let x := fresh "x" in
                     intros x v; inv_vec v; revert x)
      end
  end.
Time
Ltac
 inv_all_vec_fin :=
  block_goal;
   repeat
    match goal with
    | v:vec _ _ |- _ => inv_vec v; intros
    | i:fin _ |- _ => inv_fin i; intros
    end; unblock_goal.
Time
Fixpoint vec_to_list {A n} (v : vec A n) : list A :=
  match v with
  | [# ] => []
  | x ::: v => x :: vec_to_list v
  end.
Time Coercion vec_to_list : vec >-> list.
Time Notation list_to_vec := Vector.of_list.
Time
Lemma vec_to_list_cons {A} {n} x (v : vec A n) :
  vec_to_list (x ::: v) = x :: vec_to_list v.
Time Proof.
Time done.
Time Qed.
Time
Lemma vec_to_list_app {A} {n} {m} (v : vec A n) (w : vec A m) :
  vec_to_list (v +++ w) = vec_to_list v ++ vec_to_list w.
Time Proof.
Time by induction v; f_equal /=.
Time Qed.
Time
Lemma vec_to_list_of_list {A} (l : list A) : vec_to_list (list_to_vec l) = l.
Time Proof.
Time by induction l; f_equal /=.
Time Qed.
Time
Lemma vec_to_list_length {A} {n} (v : vec A n) : length (vec_to_list v) = n.
Time Proof.
Time (induction v; simpl; by f_equal).
Time Qed.
Time
Lemma vec_to_list_same_length {A} {B} {n} (v : vec A n) 
  (w : vec B n) : length v = length w.
Time Proof.
Time by rewrite !vec_to_list_length.
Time Qed.
Time
Lemma vec_to_list_inj1 {A} {n} {m} (v : vec A n) (w : vec A m) :
  vec_to_list v = vec_to_list w \226\134\146 n = m.
Time Proof.
Time revert m w.
Time (induction v; intros ? [| ? ? ?] ?; simplify_eq /=; f_equal; eauto).
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
Time Qed.
Time by rewrite <- (decode_encode x), Hxy, decode_encode.
Time Qed.
Time
Instance encode_nat_inj  `{Countable A}: (Inj (=) (=) (encode_nat (A:=A))).
Time
Lemma vec_to_list_inj2 {A} {n} (v : vec A n) (w : vec A n) :
  vec_to_list v = vec_to_list w \226\134\146 v = w.
Time Proof.
Time revert w.
Time
(induction v; intros w; inv_vec w; intros; simplify_eq /=; f_equal; eauto).
Time Proof.
Time (unfold encode_nat; intros x y Hxy; apply (inj encode); lia).
Time
Instance set_equiv  `{ElemOf A C}: (Equiv C) |20 :=
 (\206\187 X Y, \226\136\128 x, x \226\136\136 X \226\134\148 x \226\136\136 Y).
Time
Instance set_subseteq  `{ElemOf A C}: (SubsetEq C) |20 :=
 (\206\187 X Y, \226\136\128 x, x \226\136\136 X \226\134\146 x \226\136\136 Y).
Time
Instance set_disjoint  `{ElemOf A C}: (Disjoint C) |20 :=
 (\206\187 X Y, \226\136\128 x, x \226\136\136 X \226\134\146 x \226\136\136 Y \226\134\146 False).
Time Typeclasses Opaque set_equiv set_subseteq set_disjoint.
Time Qed.
Time
Lemma vlookup_middle {A} {n} {m} (v : vec A n) (w : vec A m) 
  x : \226\136\131 i : fin (n + S m), x = (v +++ x ::: w) !!! i.
Time Proof.
Time (induction v; simpl; [ by eexists 0%fin |  ]).
Time (destruct IHv as [i ?]).
Time by exists (FS i).
Time Qed.
Time Section setoids_simple.
Time Context `{SemiSet A C}.
Time #[global]Instance set_equiv_equivalence : (Equivalence (\226\137\161@{C} )).
Time Proof.
Time split.
Time -
Time done.
Time
Lemma vec_to_list_lookup_middle {A} {n} (v : vec A n) 
  (l k : list A) x :
  vec_to_list v = l ++ x :: k
  \226\134\146 \226\136\131 i : fin n, l = take i v \226\136\167 x = v !!! i \226\136\167 k = drop (S i) v.
Time Proof.
Time (intros H).
Time (rewrite <- (vec_to_list_of_list l), <- (vec_to_list_of_list k) in H).
Time -
Time (intros X Y ? x).
Time by symmetry.
Time -
Time (intros X Y Z ? ? x; by trans x \226\136\136 Y).
Time Qed.
Time (rewrite <- vec_to_list_cons, <- vec_to_list_app in H).
Time (pose proof (vec_to_list_inj1 _ _ H); subst).
Time (apply vec_to_list_inj2 in H; subst).
Time #[global]
Instance singleton_proper : (Proper ((=) ==> (\226\137\161@{C} )) singleton).
Time Proof.
Time (apply _).
Time Qed.
Time #[global]
Instance elem_of_proper : (Proper ((=) ==> (\226\137\161) ==> iff) (\226\136\136@{C} )) |5.
Time (induction l).
Time (simpl).
Time -
Time eexists 0%fin.
Time (simpl).
Time by rewrite vec_to_list_of_list.
Time Proof.
Time by intros x ? <- X Y.
Time Qed.
Time #[global]
Instance disjoint_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> iff) (##@{C} )).
Time Proof.
Time (intros X1 X2 HX Y1 Y2 HY; apply forall_proper; intros x).
Time by rewrite HX, HY.
Time -
Time (destruct IHl as [i ?]).
Time exists (FS i).
Time (simpl).
Time intuition congruence.
Time Qed.
Time Qed.
Time Qed.
Time #[global]
Instance union_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161@{C} )) union).
Time Proof.
Time (intros X1 X2 HX Y1 Y2 HY x).
Time (rewrite !elem_of_union).
Time
Lemma vec_to_list_drop_lookup {A} {n} (v : vec A n) 
  (i : fin n) : drop i v = v !!! i :: drop (S i) v.
Time Proof.
Time (induction i; inv_vec v; simpl; intros; [ done | by rewrite IHi ]).
Time
Lemma decode_encode_nat `{Countable A} (x : A) :
  decode_nat (encode_nat x) = Some x.
Time Proof.
Time Qed.
Time (pose proof (Pos2Nat.is_pos (encode x))).
Time (unfold decode_nat, encode_nat).
Time (rewrite Nat.succ_pred by lia).
Time (f_equiv; auto).
Time Qed.
Time #[global]
Instance union_list_proper : (Proper ((\226\137\161) ==> (\226\137\161@{C} )) union_list).
Time Proof.
Time by induction 1; simpl; try apply union_proper.
Time
Lemma vec_to_list_take_drop_lookup {A} {n} (v : vec A n) 
  (i : fin n) : vec_to_list v = take i v ++ v !!! i :: drop (S i) v.
Time Proof.
Time (rewrite <- (take_drop i v)  at 1).
Time by rewrite vec_to_list_drop_lookup.
Time by rewrite Pos2Nat.id, decode_encode.
Time Qed.
Time
Lemma vlookup_lookup {A} {n} (v : vec A n) (i : fin n) 
  x : v !!! i = x \226\134\148 (v : list A) !! (i : nat) = Some x.
Time Qed.
Time Qed.
Time #[global]
Instance subseteq_proper : (Proper ((\226\137\161@{C} ) ==> (\226\137\161@{C} ) ==> iff) (\226\138\134)).
Time Proof.
Time (intros X1 X2 HX Y1 Y2 HY).
Time (apply forall_proper; intros x).
Time by rewrite HX, HY.
Time Proof.
Time (induction v as [| ? ? v IH]; inv_fin i).
Time (simpl; split; congruence).
Time done.
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
Time
Lemma vlookup_lookup' {A} {n} (v : vec A n) (i : nat) 
  x : (\226\136\131 H : i < n, v !!! fin_of_nat H = x) \226\134\148 (v : list A) !! i = Some x.
Time Proof.
Time split.
Time -
Time (intros [Hlt ?]).
Time (rewrite <- (fin_to_of_nat i n Hlt)).
Time (cut (\226\136\128 i p, i \226\137\164 encode x \226\134\146 1 + encode x = p + i \226\134\146 Acc choose_step p)).
Time {
Time (intros help).
Time by apply (help (encode x)).
Time by apply vlookup_lookup.
Time }
Time (induction i as [| i IH] using Pos.peano_ind; intros p ? ?).
Time {
Time constructor.
Time (intros j).
Time (assert (p = encode x) by lia; subst).
Time Qed.
Time End setoids_simple.
Time Section setoids.
Time Context `{Set_ A C}.
Time #[global]
Instance intersection_proper :
 (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161@{C} )) intersection).
Time Proof.
Time (intros X1 X2 HX Y1 Y2 HY x).
Time by rewrite !elem_of_intersection, HX, HY.
Time -
Time (intros Hvix).
Time (pose proof (lookup_lt_Some _ _ _ Hvix) as Hlt).
Time (rewrite vec_to_list_length in Hlt).
Time exists Hlt.
Time (apply vlookup_lookup).
Time by rewrite fin_to_of_nat.
Time Qed.
Time
Lemma elem_of_vlookup {A} {n} (v : vec A n) x :
  x \226\136\136 vec_to_list v \226\134\148 (\226\136\131 i, v !!! i = x).
Time Proof.
Time (rewrite elem_of_list_lookup).
Time setoid_rewrite  <- vlookup_lookup'.
Time
(inversion 1 as [? Hd| ? ? Hd]; subst; rewrite decode_encode in Hd;
  congruence).
Time (split; [ by intros (?, (?, ?)); eauto |  ]).
Time }
Time constructor.
Time (intros j).
Time (inversion 1 as [? Hd| ? y Hd]; subst; auto with lia).
Time (intros [i Hx]).
Time exists i,(fin_to_nat_lt _).
Time by rewrite fin_of_to_nat.
Time Qed.
Time
Lemma Forall_vlookup {A} (P : A \226\134\146 Prop) {n} (v : vec A n) :
  Forall P (vec_to_list v) \226\134\148 (\226\136\128 i, P (v !!! i)).
Time Qed.
Time #[global]
Instance difference_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161@{C} )) difference).
Time Proof.
Time (rewrite Forall_forall).
Time setoid_rewrite elem_of_vlookup.
Time Proof.
Time (intros X1 X2 HX Y1 Y2 HY x).
Time by rewrite !elem_of_difference, HX, HY.
Time naive_solver.
Time Qed.
Time
Lemma Forall_vlookup_1 {A} (P : A \226\134\146 Prop) {n} (v : vec A n) 
  i : Forall P (vec_to_list v) \226\134\146 P (v !!! i).
Time Proof.
Time by rewrite Forall_vlookup.
Time Qed.
Time
Lemma Forall_vlookup_2 {A} (P : A \226\134\146 Prop) {n} (v : vec A n) :
  (\226\136\128 i, P (v !!! i)) \226\134\146 Forall P (vec_to_list v).
Time Proof.
Time by rewrite Forall_vlookup.
Time Qed.
Time End setoids.
Time Section setoids_monad.
Time Qed.
Time
Lemma Exists_vlookup {A} (P : A \226\134\146 Prop) {n} (v : vec A n) :
  Exists P (vec_to_list v) \226\134\148 (\226\136\131 i, P (v !!! i)).
Time Proof.
Time (rewrite Exists_exists).
Time Context `{MonadSet M}.
Time #[global]
Instance set_fmap_proper  {A} {B}:
 (Proper (pointwise_relation _ (=) ==> (\226\137\161) ==> (\226\137\161)) (@fmap M _ A B)).
Time Proof.
Time (intros f1 f2 Hf X1 X2 HX x).
Time (rewrite !elem_of_fmap).
Time setoid_rewrite elem_of_vlookup.
Time naive_solver.
Time (f_equiv; intros z).
Time by rewrite HX, Hf.
Time Qed.
Time
Lemma Forall2_vlookup {A} {B} (P : A \226\134\146 B \226\134\146 Prop) {n} 
  (v1 : vec A n) (v2 : vec B n) :
  Forall2 P (vec_to_list v1) (vec_to_list v2)
  \226\134\148 (\226\136\128 i, P (v1 !!! i) (v2 !!! i)).
Time Proof.
Time split.
Time -
Time (vec_double_ind v1 v2; [ intros _ i; inv_fin i |  ]).
Time (intros n v1 v2 IH a b; simpl).
Time (inversion_clear 1).
Time Qed.
Time (intros i).
Time (inv_fin i; simpl; auto).
Time -
Time (vec_double_ind v1 v2; [ constructor |  ]).
Time #[global]
Instance set_bind_proper  {A} {B}:
 (Proper (pointwise_relation _ (\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) (@mbind M _ A B)).
Time Proof.
Time (intros f1 f2 Hf X1 X2 HX x).
Time (rewrite !elem_of_bind).
Time (intros ? ? ? IH ? ? H).
Time constructor.
Time (apply (H 0%fin)).
Time (apply IH, (\206\187 i, H (FS i))).
Time Qed.
Time Notation vmap := Vector.map.
Time
Lemma vlookup_map `(f : A \226\134\146 B) {n} (v : vec A n) i :
  vmap f v !!! i = f (v !!! i).
Time Proof.
Time by apply Vector.nth_map.
Time Qed.
Time (f_equiv; intros z).
Time by rewrite HX, (Hf z).
Time
Lemma vec_to_list_map `(f : A \226\134\146 B) {n} (v : vec A n) :
  vec_to_list (vmap f v) = f <$> vec_to_list v.
Time Proof.
Time (induction v; simpl).
Time done.
Time by rewrite IHv.
Time Qed.
Time Notation vzip_with := Vector.map2.
Time
Lemma vlookup_zip_with `(f : A \226\134\146 B \226\134\146 C) {n} (v1 : vec A n) 
  (v2 : vec B n) i : vzip_with f v1 v2 !!! i = f (v1 !!! i) (v2 !!! i).
Time Proof.
Time by apply Vector.nth_map2.
Time Qed.
Time
Lemma vec_to_list_zip_with `(f : A \226\134\146 B \226\134\146 C) {n} (v1 : vec A n) 
  (v2 : vec B n) :
  vec_to_list (vzip_with f v1 v2) =
  zip_with f (vec_to_list v1) (vec_to_list v2).
Time Qed.
Time Proof.
Time revert v2.
Time (induction v1; intros v2; inv_vec v2; intros; simpl; [ done |  ]).
Time by rewrite IHv1.
Time Qed.
Time Qed.
Time
Fixpoint vinsert {A n} (i : fin n) (x : A) : vec A n \226\134\146 vec A n :=
  match i with
  | 0%fin => vec_S_inv _ (\206\187 _ v, x ::: v)
  | FS i => vec_S_inv _ (\206\187 y v, y ::: vinsert i x v)
  end.
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
Lemma vec_to_list_insert {A} {n} i x (v : vec A n) :
  vec_to_list (vinsert i x v) = insert (fin_to_nat i) x (vec_to_list v).
Time Proof.
Time (induction v; inv_fin i).
Time done.
Time
Fixpoint choose_go_correct {i} (acc : Acc choose_step i) : P (choose_go acc).
Time Proof.
Time (destruct acc; simpl).
Time (repeat case_match; auto).
Time (simpl).
Time (intros).
Time by rewrite IHv.
Time Qed.
Time Qed.
Time #[global]
Instance set_join_proper  {A}: (Proper ((\226\137\161) ==> (\226\137\161)) (@mjoin M _ A)).
Time Proof.
Time (intros X1 X2 HX x).
Time (rewrite !elem_of_join).
Time
Lemma vlookup_insert {A} {n} i x (v : vec A n) : vinsert i x v !!! i = x.
Time Proof.
Time by induction i; inv_vec v.
Time Qed.
Time
Fixpoint choose_go_pi {i} (acc1 acc2 : Acc choose_step i) :
choose_go acc1 = choose_go acc2.
Time Proof.
Time (destruct acc1, acc2; simpl; repeat case_match; auto).
Time
Lemma vlookup_insert_ne {A} {n} i j x (v : vec A n) :
  i \226\137\160 j \226\134\146 vinsert i x v !!! j = v !!! j.
Time Proof.
Time (induction i; inv_fin j; inv_vec v; simpl; try done).
Time (f_equiv; intros z).
Time by rewrite HX.
Time (intros).
Time (apply IHi).
Time congruence.
Time Qed.
Time Qed.
Time Definition choose (H : \226\136\131 x, P x) : A := choose_go (choose_step_acc H).
Time
Lemma vlookup_insert_self {A} {n} i (v : vec A n) : vinsert i (v !!! i) v = v.
Time Proof.
Time by induction v; inv_fin i; intros; f_equal /=.
Time
Definition choose_correct (H : \226\136\131 x, P x) : P (choose H) :=
  choose_go_correct _.
Time
Definition choose_pi (H1 H2 : \226\136\131 x, P x) : choose H1 = choose H2 :=
  choose_go_pi _ _.
Time Definition choice (HA : \226\136\131 x, P x) : {x | P x} := _ \226\134\190 choose_correct HA.
Time End choice.
Time Qed.
Time End setoids_monad.
Time Qed.
Time
Lemma vmap_insert {A} {B} (f : A \226\134\146 B) (n : nat) i 
  x (v : vec A n) : vmap f (vinsert i x v) = vinsert i (f x) (vmap f v).
Time Proof.
Time Class SetUnfold (P Q : Prop) :={set_unfold : P \226\134\148 Q}.
Time Arguments set_unfold _ _ {_} : assert.
Time Hint Mode SetUnfold + -: typeclass_instances.
Time (induction v; inv_fin i; intros; f_equal /=; auto).
Time
Lemma surj_cancel `{Countable A} `{EqDecision B} (f : A \226\134\146 B) 
  `{!Surj (=) f} : {g : B \226\134\146 A & Cancel (=) f g}.
Time
Class SetUnfoldElemOf `{ElemOf A C} (x : A) (X : C) (Q : Prop) :={
 set_unfold_elem_of : x \226\136\136 X \226\134\148 Q}.
Time Arguments set_unfold_elem_of {_} {_} {_} _ _ _ {_} : assert.
Time Hint Mode SetUnfoldElemOf + + + - + -: typeclass_instances.
Time
Instance set_unfold_elem_of_default  `{ElemOf A C} 
 (x : A) (X : C): (SetUnfoldElemOf x X (x \226\136\136 X)) |1000.
Time Proof.
Time done.
Time Qed.
Time Qed.
Time Proof.
Time exists (\206\187 y, choose (\206\187 x, f x = y) (surj f y)).
Time (intros y).
Time by rewrite (choose_correct (\206\187 x, f x = y) (surj f y)).
Time Qed.
Time
Instance set_unfold_elem_of_set_unfold  `{ElemOf A C} 
 (x : A) (X : C) Q: (SetUnfoldElemOf x X Q \226\134\146 SetUnfold (x \226\136\136 X) Q).
Time Proof.
Time by destruct 1; constructor.
Time Qed.
Time Class SetUnfoldSimpl (P Q : Prop) :={set_unfold_simpl : SetUnfold P Q}.
Time
Hint Extern 0 (SetUnfoldSimpl _ _) => (csimpl; constructor):
  typeclass_instances.
Time Instance set_unfold_default  P: (SetUnfold P P) |1000.
Time
Fixpoint vtake {A n} (i : fin n) : vec A n \226\134\146 vec A i :=
  match i in (fin n) return (vec A n \226\134\146 vec A i) with
  | 0%fin => \206\187 _, [# ]
  | FS i => vec_S_inv _ (\206\187 x v, x ::: vtake i v)
  end.
Time
Fixpoint vdrop {A n} (i : fin n) : vec A n \226\134\146 vec A (n - i) :=
  match i in (fin n) return (vec A n \226\134\146 vec A (n - i)) with
  | 0%fin => id
  | FS i => vec_S_inv _ (\206\187 _, vdrop i)
  end.
Time Section inj_countable.
Time Context `{Countable A} `{EqDecision B}.
Time Context (f : B \226\134\146 A) (g : A \226\134\146 option B) (fg : \226\136\128 x, g (f x) = Some x).
Time #[program]
Instance inj_countable : (Countable B) :=
 {| encode := fun y => encode (f y); decode := fun p => x \226\134\144 decode p; g x |}.
Time done.
Time Qed.
Time
Definition set_unfold_1 `{SetUnfold P Q} : P \226\134\146 Q := proj1 (set_unfold P Q).
Time
Lemma vec_to_list_take {A} {n} i (v : vec A n) :
  vec_to_list (vtake i v) = take (fin_to_nat i) (vec_to_list v).
Time Proof.
Time (induction i; inv_vec v; intros; f_equal /=; auto).
Time Next Obligation.
Time (intros y; simpl; rewrite decode_encode; eauto).
Time
Definition set_unfold_2 `{SetUnfold P Q} : Q \226\134\146 P := proj2 (set_unfold P Q).
Time
Lemma set_unfold_impl P Q P' Q' :
  SetUnfold P P' \226\134\146 SetUnfold Q Q' \226\134\146 SetUnfold (P \226\134\146 Q) (P' \226\134\146 Q').
Time Proof.
Time constructor.
Time Qed.
Time
Lemma vec_to_list_drop {A} {n} i (v : vec A n) :
  vec_to_list (vdrop i v) = drop (fin_to_nat i) (vec_to_list v).
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
Time by rewrite (set_unfold P P'), (set_unfold Q Q').
Time Proof.
Time (induction i; inv_vec v; intros; f_equal /=; auto).
Time Qed.
Time End inj_countable'.
Time #[program]
Instance Empty_set_countable : (Countable Empty_set) :=
 {| encode := fun u => 1; decode := fun p => None |}.
Time Next Obligation.
Time by intros [].
Time Qed.
Time Qed.
Time
Lemma set_unfold_and P Q P' Q' :
  SetUnfold P P' \226\134\146 SetUnfold Q Q' \226\134\146 SetUnfold (P \226\136\167 Q) (P' \226\136\167 Q').
Time Proof.
Time constructor.
Time Qed.
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
Time by rewrite (set_unfold P P'), (set_unfold Q Q').
Time
Fixpoint vreplicate {A} (n : nat) (x : A) : vec A n :=
  match n with
  | 0 => [# ]
  | S n => x ::: vreplicate n x
  end.
Time
Lemma vec_to_list_replicate {A} n (x : A) :
  vec_to_list (vreplicate n x) = replicate n x.
Time Proof.
Time (induction n; by f_equal /=).
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
Time Qed.
Time
Lemma set_unfold_or P Q P' Q' :
  SetUnfold P P' \226\134\146 SetUnfold Q Q' \226\134\146 SetUnfold (P \226\136\168 Q) (P' \226\136\168 Q').
Time Qed.
Time Lemma vlookup_replicate {A} n (x : A) i : vreplicate n x !!! i = x.
Time Proof.
Time (induction i; f_equal /=; auto).
Time Qed.
Time
Lemma vmap_replicate {A} {B} (f : A \226\134\146 B) n (x : A) :
  vmap f (vreplicate n x) = vreplicate n (f x).
Time (intros ? ? ? [x| ]; simpl; repeat case_decide; auto with lia).
Time Proof.
Time constructor.
Time by rewrite (set_unfold P P'), (set_unfold Q Q').
Time Proof.
Time (induction n; f_equal /=; auto).
Time Qed.
Time Qed.
Time
Lemma set_unfold_iff P Q P' Q' :
  SetUnfold P P' \226\134\146 SetUnfold Q Q' \226\134\146 SetUnfold (P \226\134\148 Q) (P' \226\134\148 Q').
Time #[global]
Instance vec_0_inhabited  T: (Inhabited (vec T 0)) := (populate [# ]).
Time #[global]
Instance vec_inhabited  `{Inhabited T} n: (Inhabited (vec T n)) :=
 (populate (vreplicate n inhabitant)).
Time Proof.
Time constructor.
Time by rewrite (set_unfold P P'), (set_unfold Q Q').
Time Qed.
Time Lemma set_unfold_not P P' : SetUnfold P P' \226\134\146 SetUnfold (\194\172 P) (\194\172 P').
Time by rewrite Pos.pred_succ, decode_encode.
Time Proof.
Time constructor.
Time by rewrite (set_unfold P P').
Time Qed.
Time
Lemma set_unfold_forall {A} (P P' : A \226\134\146 Prop) :
  (\226\136\128 x, SetUnfold (P x) (P' x)) \226\134\146 SetUnfold (\226\136\128 x, P x) (\226\136\128 x, P' x).
Time Proof.
Time constructor.
Time naive_solver.
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
Time Qed.
Time
Lemma set_unfold_exist {A} (P P' : A \226\134\146 Prop) :
  (\226\136\128 x, SetUnfold (P x) (P' x)) \226\134\146 SetUnfold (\226\136\131 x, P x) (\226\136\131 x, P' x).
Time Next Obligation.
Time by intros ? ? ? ? ? ? [x| y]; simpl; rewrite decode_encode.
Time Proof.
Time constructor.
Time naive_solver.
Time Qed.
Time Qed.
Time
Hint Extern 0 (SetUnfold (_ \226\134\146 _) _) => (class_apply set_unfold_impl):
  typeclass_instances.
Time
Hint Extern 0 (SetUnfold (_ \226\136\167 _) _) => (class_apply set_unfold_and):
  typeclass_instances.
Time
Hint Extern 0 (SetUnfold (_ \226\136\168 _) _) => (class_apply set_unfold_or):
  typeclass_instances.
Time
Hint Extern 0 (SetUnfold (_ \226\134\148 _) _) => (class_apply set_unfold_iff):
  typeclass_instances.
Time
Hint Extern 0 (SetUnfold (\194\172 _) _) => (class_apply set_unfold_not):
  typeclass_instances.
Time
Hint Extern 1 (SetUnfold (\226\136\128 _, _) _) => (class_apply set_unfold_forall):
  typeclass_instances.
Time
Hint Extern 0 (SetUnfold (\226\136\131 _, _) _) => (class_apply set_unfold_exist):
  typeclass_instances.
Time Section set_unfold_simple.
Time Context `{SemiSet A C}.
Time Implicit Types x y : A.
Time Implicit Types X Y : C.
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
Time #[global]
Instance set_unfold_empty  x: (SetUnfoldElemOf x (\226\136\133 : C) False).
Time Proof.
Time constructor.
Time split.
Time (apply not_elem_of_empty).
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
Time done.
Time Qed.
Time #[global]
Instance set_unfold_singleton  x y: (SetUnfoldElemOf x ({[y]} : C) (x = y)).
Time Proof.
Time (constructor; apply elem_of_singleton).
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
Time Qed.
Time #[global]
Instance set_unfold_union  x X Y P Q:
 (SetUnfoldElemOf x X P
  \226\134\146 SetUnfoldElemOf x Y Q \226\134\146 SetUnfoldElemOf x (X \226\136\170 Y) (P \226\136\168 Q)).
Time Proof.
Time (intros ? ?; constructor).
Time
by
 rewrite elem_of_union, (set_unfold_elem_of x X P),
  (set_unfold_elem_of x Y Q).
Time
Lemma prod_decode_encode_fst p q : prod_decode_fst (prod_encode p q) = Some p.
Time Proof.
Time (assert (\226\136\128 p, prod_decode_fst (prod_encode_fst p) = Some p)).
Time {
Time (intros p').
Time by induction p'; simplify_option_eq.
Time Qed.
Time #[global]Instance set_unfold_equiv_same  X: (SetUnfold (X \226\137\161 X) True) |1.
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance set_unfold_equiv_empty_l  X (P : A \226\134\146 Prop):
 ((\226\136\128 x, SetUnfoldElemOf x X (P x)) \226\134\146 SetUnfold (\226\136\133 \226\137\161 X) (\226\136\128 x, \194\172 P x)) |5.
Time Proof.
Time (intros ?; constructor).
Time (unfold equiv, set_equiv).
Time (pose proof (not_elem_of_empty (C:=C)); naive_solver).
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
Time Qed.
Time (intros p').
Time by induction p'; simplify_option_eq.
Time #[global]
Instance set_unfold_equiv_empty_r  (P : A \226\134\146 Prop) 
 X: ((\226\136\128 x, SetUnfoldElemOf x X (P x)) \226\134\146 SetUnfold (X \226\137\161 \226\136\133) (\226\136\128 x, \194\172 P x)) |5.
Time Proof.
Time (intros ?; constructor).
Time (unfold equiv, set_equiv).
Time (pose proof (not_elem_of_empty (C:=C)); naive_solver).
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
Time Qed.
Time #[global]
Instance set_unfold_equiv  (P Q : A \226\134\146 Prop) X:
 ((\226\136\128 x, SetUnfoldElemOf x X (P x))
  \226\134\146 (\226\136\128 x, SetUnfoldElemOf x Y (Q x)) \226\134\146 SetUnfold (X \226\137\161 Y) (\226\136\128 x, P x \226\134\148 Q x))
 |10.
Time Proof.
Time constructor.
Time #[program]
Instance nat_countable : (Countable nat) :=
 {|
 encode := fun x => encode (N.of_nat x);
 decode := fun p => N.to_nat <$> decode p |}.
Time Next Obligation.
Time by intros x; lazy beta; rewrite decode_encode; csimpl; rewrite Nat2N.id.
Time Qed.
Time (apply forall_proper; naive_solver).
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
Time Qed.
Time #[global]
Instance set_unfold_subseteq  (P Q : A \226\134\146 Prop) X Y:
 ((\226\136\128 x, SetUnfoldElemOf x X (P x))
  \226\134\146 (\226\136\128 x, SetUnfoldElemOf x Y (Q x)) \226\134\146 SetUnfold (X \226\138\134 Y) (\226\136\128 x, P x \226\134\146 Q x)).
Time Proof.
Time constructor.
Time (apply forall_proper; naive_solver).
Time Qed.
Time #[global]
Instance set_unfold_subset  (P Q : A \226\134\146 Prop) X:
 ((\226\136\128 x, SetUnfoldElemOf x X (P x))
  \226\134\146 (\226\136\128 x, SetUnfoldElemOf x Y (Q x))
    \226\134\146 SetUnfold (X \226\138\130 Y) ((\226\136\128 x, P x \226\134\146 Q x) \226\136\167 \194\172 (\226\136\128 x, Q x \226\134\146 P x))).
Time Proof.
Time constructor.
Time (unfold strict).
Time (repeat f_equiv; apply forall_proper; naive_solver).
Time Qed.
Time #[global]
Instance set_unfold_disjoint  (P Q : A \226\134\146 Prop) X Y:
 ((\226\136\128 x, SetUnfoldElemOf x X (P x))
  \226\134\146 (\226\136\128 x, SetUnfoldElemOf x Y (Q x))
    \226\134\146 SetUnfold (X ## Y) (\226\136\128 x, P x \226\134\146 Q x \226\134\146 False)).
Time Proof.
Time constructor.
Time (unfold disjoint, set_disjoint).
Time naive_solver.
Time Qed.
Time Context `{!LeibnizEquiv C}.
Time #[global]
Instance set_unfold_equiv_same_L  X: (SetUnfold (X = X) True) |1.
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance set_unfold_equiv_empty_l_L  X (P : A \226\134\146 Prop):
 ((\226\136\128 x, SetUnfoldElemOf x X (P x)) \226\134\146 SetUnfold (\226\136\133 = X) (\226\136\128 x, \194\172 P x)) |5.
Time Proof.
Time constructor.
Time unfold_leibniz.
Time by apply set_unfold_equiv_empty_l.
Time Qed.
Time #[global]
Instance set_unfold_equiv_empty_r_L  (P : A \226\134\146 Prop) 
 X: ((\226\136\128 x, SetUnfoldElemOf x X (P x)) \226\134\146 SetUnfold (X = \226\136\133) (\226\136\128 x, \194\172 P x)) |5.
Time Proof.
Time constructor.
Time unfold_leibniz.
Time by apply set_unfold_equiv_empty_r.
Time Qed.
Time #[global]
Instance set_unfold_equiv_L  (P Q : A \226\134\146 Prop) X Y:
 ((\226\136\128 x, SetUnfoldElemOf x X (P x))
  \226\134\146 (\226\136\128 x, SetUnfoldElemOf x Y (Q x)) \226\134\146 SetUnfold (X = Y) (\226\136\128 x, P x \226\134\148 Q x))
 |10.
Time Proof.
Time constructor.
Time unfold_leibniz.
Time by apply set_unfold_equiv.
Time Qed.
Time End set_unfold_simple.
Time Section set_unfold.
Time Context `{Set_ A C}.
Time Implicit Types x y : A.
Time Implicit Types X Y : C.
Time #[global]
Instance set_unfold_intersection  x X Y P Q:
 (SetUnfoldElemOf x X P
  \226\134\146 SetUnfoldElemOf x Y Q \226\134\146 SetUnfoldElemOf x (X \226\136\169 Y) (P \226\136\167 Q)).
Time Proof.
Time (intros ? ?; constructor).
Time (rewrite elem_of_intersection).
Time by rewrite (set_unfold_elem_of x X P), (set_unfold_elem_of x Y Q).
Time Qed.
Time #[global]
Instance set_unfold_difference  x X Y P Q:
 (SetUnfoldElemOf x X P
  \226\134\146 SetUnfoldElemOf x Y Q \226\134\146 SetUnfoldElemOf x (X \226\136\150 Y) (P \226\136\167 \194\172 Q)).
Time Proof.
Time (intros ? ?; constructor).
Time (rewrite elem_of_difference).
Time by rewrite (set_unfold_elem_of x X P), (set_unfold_elem_of x Y Q).
Time Qed.
Time End set_unfold.
Time Section set_unfold_monad.
Time Context `{MonadSet M}.
Time #[global]
Instance set_unfold_ret  {A} (x y : A):
 (SetUnfoldElemOf x (mret (M:=M) y) (x = y)).
Time Proof.
Time (constructor; apply elem_of_ret).
Time Qed.
Time #[global]
Instance set_unfold_bind  {A} {B} (f : A \226\134\146 M B) X 
 (P Q : A \226\134\146 Prop):
 ((\226\136\128 y, SetUnfoldElemOf y X (P y))
  \226\134\146 (\226\136\128 y, SetUnfoldElemOf x (f y) (Q y))
    \226\134\146 SetUnfoldElemOf x (X \226\137\171= f) (\226\136\131 y, Q y \226\136\167 P y)).
Time Proof.
Time constructor.
Time (rewrite elem_of_bind; naive_solver).
Time Qed.
Time #[global]
Instance set_unfold_fmap  {A} {B} (f : A \226\134\146 B) (X : M A) 
 (P : A \226\134\146 Prop):
 ((\226\136\128 y, SetUnfoldElemOf y X (P y))
  \226\134\146 SetUnfoldElemOf x (f <$> X) (\226\136\131 y, x = f y \226\136\167 P y)).
Time Proof.
Time constructor.
Time (rewrite elem_of_fmap; naive_solver).
Time Qed.
Time #[global]
Instance set_unfold_join  {A} (X : M (M A)) (P : M A \226\134\146 Prop):
 ((\226\136\128 Y, SetUnfoldElemOf Y X (P Y))
  \226\134\146 SetUnfoldElemOf x (mjoin X) (\226\136\131 Y, x \226\136\136 Y \226\136\167 P Y)).
Time Proof.
Time constructor.
Time (rewrite elem_of_join; naive_solver).
Time Qed.
Time End set_unfold_monad.
Time Section set_unfold_list.
Time Context {A : Type}.
Time Implicit Type x : A.
Time Implicit Type l : list A.
Time #[global]Instance set_unfold_nil  x: (SetUnfoldElemOf x [] False).
Time Proof.
Time (constructor; apply elem_of_nil).
Time Qed.
Time #[global]
Instance set_unfold_cons  x y l P:
 (SetUnfoldElemOf x l P \226\134\146 SetUnfoldElemOf x (y :: l) (x = y \226\136\168 P)).
Time Proof.
Time constructor.
Time by rewrite elem_of_cons, (set_unfold_elem_of x l P).
Time Qed.
Time #[global]
Instance set_unfold_app  x l k P Q:
 (SetUnfoldElemOf x l P
  \226\134\146 SetUnfoldElemOf x k Q \226\134\146 SetUnfoldElemOf x (l ++ k) (P \226\136\168 Q)).
Time Proof.
Time (intros ? ?; constructor).
Time
by
 rewrite elem_of_app, (set_unfold_elem_of x l P), (set_unfold_elem_of x k Q).
Time Qed.
Time #[global]
Instance set_unfold_included  l k (P Q : A \226\134\146 Prop):
 ((\226\136\128 x, SetUnfoldElemOf x l (P x))
  \226\134\146 (\226\136\128 x, SetUnfoldElemOf x k (Q x)) \226\134\146 SetUnfold (l \226\138\134 k) (\226\136\128 x, P x \226\134\146 Q x)).
Time Proof.
Time (constructor; unfold subseteq, list_subseteq).
Time (apply forall_proper; naive_solver).
Time Qed.
Time #[global]
Instance set_unfold_reverse  x l P:
 (SetUnfoldElemOf x l P \226\134\146 SetUnfoldElemOf x (reverse l) P).
Time Proof.
Time constructor.
Time by rewrite elem_of_reverse, (set_unfold_elem_of x l P).
Time Qed.
Time #[global]
Instance set_unfold_list_fmap  {B} (f : A \226\134\146 B) l P:
 ((\226\136\128 y, SetUnfoldElemOf y l (P y))
  \226\134\146 SetUnfoldElemOf x (f <$> l) (\226\136\131 y, x = f y \226\136\167 P y)).
Time Proof.
Time constructor.
Time (rewrite elem_of_list_fmap).
Time (f_equiv; intros y).
Time by rewrite (set_unfold_elem_of y l (P y)).
Time Qed.
Time End set_unfold_list.
Time
Ltac
 set_unfold :=
  let rec unfold_hyps :=
   try
    match goal with
    | H:?P
      |- _ =>
          lazymatch type of P with
          | Prop =>
              apply set_unfold_1 in H; revert H; (first
               [ unfold_hyps; intros H | intros H; fail 1 ])
          | _ => fail
          end
    end
  in
  apply set_unfold_2; unfold_hyps; csimpl in *.
Time
Tactic Notation "set_solver" "by" tactic3(tac) :=
 (try fast_done; intros; setoid_subst; set_unfold; intros; setoid_subst;
   try match goal with
       | |- _ \226\136\136 _ => apply dec_stable
       end; naive_solver tac).
Time
Tactic Notation "set_solver" "-" hyp_list(Hs) "by" tactic3(tac) :=
 (clear Hs; set_solver by tac).
Time
Tactic Notation "set_solver" "+" hyp_list(Hs) "by" tactic3(tac) :=
 (clear - Hs; set_solver by tac).
Time Tactic Notation "set_solver" := set_solver by idtac.
Time Tactic Notation "set_solver" "-" hyp_list(Hs) := (clear Hs; set_solver).
Time
Tactic Notation "set_solver" "+" hyp_list(Hs) := (clear - Hs; set_solver).
Time Hint Extern 1000 (_ \226\136\137 _) => set_solver: set_solver.
Time Hint Extern 1000 (_ \226\136\136 _) => set_solver: set_solver.
Time Hint Extern 1000 (_ \226\138\134 _) => set_solver: set_solver.
Time Section semi_set.
Time Context `{SemiSet A C}.
Time Implicit Types x y : A.
Time Implicit Types X Y : C.
Time Implicit Types Xs Ys : list C.
Time Lemma elem_of_equiv X Y : X \226\137\161 Y \226\134\148 (\226\136\128 x, x \226\136\136 X \226\134\148 x \226\136\136 Y).
Time Proof.
Time set_solver.
Time Qed.
Time Lemma set_equiv_spec X Y : X \226\137\161 Y \226\134\148 X \226\138\134 Y \226\136\167 Y \226\138\134 X.
Time Proof.
Time set_solver.
Time Qed.
Time #[global]Instance set_subseteq_antisymm : (AntiSymm (\226\137\161) (\226\138\134@{C} )).
Time Proof.
Time (intros ? ?).
Time set_solver.
Time Qed.
Time #[global]Instance set_subseteq_preorder : (PreOrder (\226\138\134@{C} )).
Time Proof.
Time split.
Time by intros ? ?.
Time (intros ? ? ?; set_solver).
Time Qed.
Time Lemma subseteq_union X Y : X \226\138\134 Y \226\134\148 X \226\136\170 Y \226\137\161 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma subseteq_union_1 X Y : X \226\138\134 Y \226\134\146 X \226\136\170 Y \226\137\161 Y.
Time Proof.
Time by rewrite subseteq_union.
Time Qed.
Time Lemma subseteq_union_2 X Y : X \226\136\170 Y \226\137\161 Y \226\134\146 X \226\138\134 Y.
Time Proof.
Time by rewrite subseteq_union.
Time Qed.
Time Lemma union_subseteq_l X Y : X \226\138\134 X \226\136\170 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma union_subseteq_r X Y : Y \226\138\134 X \226\136\170 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma union_least X Y Z : X \226\138\134 Z \226\134\146 Y \226\138\134 Z \226\134\146 X \226\136\170 Y \226\138\134 Z.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma elem_of_subseteq X Y : X \226\138\134 Y \226\134\148 (\226\136\128 x, x \226\136\136 X \226\134\146 x \226\136\136 Y).
Time Proof.
Time done.
Time Qed.
Time
Lemma elem_of_subset X Y :
  X \226\138\130 Y \226\134\148 (\226\136\128 x, x \226\136\136 X \226\134\146 x \226\136\136 Y) \226\136\167 \194\172 (\226\136\128 x, x \226\136\136 Y \226\134\146 x \226\136\136 X).
Time Proof.
Time set_solver.
Time Qed.
Time Lemma union_subseteq X Y Z : X \226\136\170 Y \226\138\134 Z \226\134\148 X \226\138\134 Z \226\136\167 Y \226\138\134 Z.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma not_elem_of_union x X Y : x \226\136\137 X \226\136\170 Y \226\134\148 (x \226\136\137 X) \226\136\167 x \226\136\137 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma elem_of_union_l x X Y : x \226\136\136 X \226\134\146 x \226\136\136 X \226\136\170 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma elem_of_union_r x X Y : x \226\136\136 Y \226\134\146 x \226\136\136 X \226\136\170 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma union_mono_l X Y1 Y2 : Y1 \226\138\134 Y2 \226\134\146 X \226\136\170 Y1 \226\138\134 X \226\136\170 Y2.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma union_mono_r X1 X2 Y : X1 \226\138\134 X2 \226\134\146 X1 \226\136\170 Y \226\138\134 X2 \226\136\170 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma union_mono X1 X2 Y1 Y2 : X1 \226\138\134 X2 \226\134\146 Y1 \226\138\134 Y2 \226\134\146 X1 \226\136\170 Y1 \226\138\134 X2 \226\136\170 Y2.
Time Proof.
Time set_solver.
Time Qed.
Time #[global]Instance union_idemp : (IdemP (\226\137\161@{C} ) (\226\136\170)).
Time Proof.
Time (intros X).
Time set_solver.
Time Qed.
Time #[global]Instance union_empty_l : (LeftId (\226\137\161@{C} ) \226\136\133 (\226\136\170)).
Time Proof.
Time (intros X).
Time set_solver.
Time Qed.
Time #[global]Instance union_empty_r : (RightId (\226\137\161@{C} ) \226\136\133 (\226\136\170)).
Time Proof.
Time (intros X).
Time set_solver.
Time Qed.
Time #[global]Instance union_comm : (Comm (\226\137\161@{C} ) (\226\136\170)).
Time Proof.
Time (intros X Y).
Time set_solver.
Time Qed.
Time #[global]Instance union_assoc : (Assoc (\226\137\161@{C} ) (\226\136\170)).
Time Proof.
Time (intros X Y Z).
Time set_solver.
Time Qed.
Time Lemma empty_union X Y : X \226\136\170 Y \226\137\161 \226\136\133 \226\134\148 X \226\137\161 \226\136\133 \226\136\167 Y \226\137\161 \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma union_cancel_l X Y Z : Z ## X \226\134\146 Z ## Y \226\134\146 Z \226\136\170 X \226\137\161 Z \226\136\170 Y \226\134\146 X \226\137\161 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma union_cancel_r X Y Z : X ## Z \226\134\146 Y ## Z \226\134\146 X \226\136\170 Z \226\137\161 Y \226\136\170 Z \226\134\146 X \226\137\161 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma empty_subseteq X : \226\136\133 \226\138\134 X.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma elem_of_equiv_empty X : X \226\137\161 \226\136\133 \226\134\148 (\226\136\128 x, x \226\136\137 X).
Time Proof.
Time set_solver.
Time Qed.
Time Lemma elem_of_empty x : x \226\136\136 (\226\136\133 : C) \226\134\148 False.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma equiv_empty X : X \226\138\134 \226\136\133 \226\134\146 X \226\137\161 \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma union_positive_l X Y : X \226\136\170 Y \226\137\161 \226\136\133 \226\134\146 X \226\137\161 \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma union_positive_l_alt X Y : X \226\137\162 \226\136\133 \226\134\146 X \226\136\170 Y \226\137\162 \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma non_empty_inhabited x X : x \226\136\136 X \226\134\146 X \226\137\162 \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma elem_of_singleton_1 x y : x \226\136\136 ({[y]} : C) \226\134\146 x = y.
Time Proof.
Time by rewrite elem_of_singleton.
Time Qed.
Time Lemma elem_of_singleton_2 x y : x = y \226\134\146 x \226\136\136 ({[y]} : C).
Time Proof.
Time by rewrite elem_of_singleton.
Time Qed.
Time Lemma elem_of_subseteq_singleton x X : x \226\136\136 X \226\134\148 {[x]} \226\138\134 X.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma non_empty_singleton x : ({[x]} : C) \226\137\162 \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma not_elem_of_singleton x y : x \226\136\137 ({[y]} : C) \226\134\148 x \226\137\160 y.
Time Proof.
Time by rewrite elem_of_singleton.
Time Qed.
Time Lemma elem_of_disjoint X Y : X ## Y \226\134\148 (\226\136\128 x, x \226\136\136 X \226\134\146 x \226\136\136 Y \226\134\146 False).
Time Proof.
Time done.
Time Qed.
Time #[global]Instance disjoint_sym : (Symmetric (##@{C} )).
Time Proof.
Time (intros X Y).
Time set_solver.
Time Qed.
Time Lemma disjoint_empty_l Y : \226\136\133 ## Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_empty_r X : X ## \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_singleton_l x Y : {[x]} ## Y \226\134\148 x \226\136\137 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_singleton_r y X : X ## {[y]} \226\134\148 y \226\136\137 X.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_union_l X1 X2 Y : X1 \226\136\170 X2 ## Y \226\134\148 X1 ## Y \226\136\167 X2 ## Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_union_r X Y1 Y2 : X ## Y1 \226\136\170 Y2 \226\134\148 X ## Y1 \226\136\167 X ## Y2.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma elem_of_union_list Xs x : x \226\136\136 \226\139\131 Xs \226\134\148 (\226\136\131 X, X \226\136\136 Xs \226\136\167 x \226\136\136 X).
Time Proof.
Time split.
Time -
Time (induction Xs; simpl; intros HXs; [ by apply elem_of_empty in HXs |  ]).
Time setoid_rewrite elem_of_cons.
Time (apply elem_of_union in HXs).
Time naive_solver.
Time -
Time (intros [X [Hx]]).
Time (induction Hx; simpl; [ by apply elem_of_union_l |  ]).
Time (intros).
Time (apply elem_of_union_r; auto).
Time Qed.
Time Lemma union_list_nil : \226\139\131 @nil C = \226\136\133.
Time Proof.
Time done.
Time Qed.
Time Lemma union_list_cons X Xs : \226\139\131 (X :: Xs) = X \226\136\170 \226\139\131 Xs.
Time Proof.
Time done.
Time Qed.
Time Lemma union_list_singleton X : \226\139\131 [X] \226\137\161 X.
Time Proof.
Time (simpl).
Time by rewrite (right_id \226\136\133 _).
Time Qed.
Time Lemma union_list_app Xs1 Xs2 : \226\139\131 (Xs1 ++ Xs2) \226\137\161 \226\139\131 Xs1 \226\136\170 \226\139\131 Xs2.
Time Proof.
Time (induction Xs1 as [| X Xs1 IH]; simpl; [ by rewrite (left_id \226\136\133 _) |  ]).
Time by rewrite IH, (assoc _).
Time Qed.
Time Lemma union_list_reverse Xs : \226\139\131 reverse Xs \226\137\161 \226\139\131 Xs.
Time Proof.
Time (induction Xs as [| X Xs IH]; simpl; [ done |  ]).
Time
by rewrite reverse_cons, union_list_app, union_list_singleton, (comm _), IH.
Time Qed.
Time Lemma union_list_mono Xs Ys : Xs \226\138\134* Ys \226\134\146 \226\139\131 Xs \226\138\134 \226\139\131 Ys.
Time Proof.
Time (induction 1; simpl; auto using union_mono).
Time Qed.
Time Lemma empty_union_list Xs : \226\139\131 Xs \226\137\161 \226\136\133 \226\134\148 Forall (\226\137\161\226\136\133) Xs.
Time Proof.
Time split.
Time -
Time (induction Xs; simpl; rewrite ?empty_union; intuition).
Time -
Time (induction 1 as [| ? ? E1 ? E2]; simpl).
Time done.
Time by apply empty_union.
Time Qed.
Time Section leibniz.
Time Context `{!LeibnizEquiv C}.
Time Lemma elem_of_equiv_L X Y : X = Y \226\134\148 (\226\136\128 x, x \226\136\136 X \226\134\148 x \226\136\136 Y).
Time Proof.
Time unfold_leibniz.
Time (apply elem_of_equiv).
Time Qed.
Time Lemma set_equiv_spec_L X Y : X = Y \226\134\148 X \226\138\134 Y \226\136\167 Y \226\138\134 X.
Time Proof.
Time unfold_leibniz.
Time (apply set_equiv_spec).
Time Qed.
Time #[global]Instance set_subseteq_partialorder : (PartialOrder (\226\138\134@{C} )).
Time Proof.
Time split.
Time (apply _).
Time (intros ? ?).
Time unfold_leibniz.
Time (apply (anti_symm _)).
Time Qed.
Time Lemma subseteq_union_L X Y : X \226\138\134 Y \226\134\148 X \226\136\170 Y = Y.
Time Proof.
Time unfold_leibniz.
Time (apply subseteq_union).
Time Qed.
Time Lemma subseteq_union_1_L X Y : X \226\138\134 Y \226\134\146 X \226\136\170 Y = Y.
Time Proof.
Time unfold_leibniz.
Time (apply subseteq_union_1).
Time Qed.
Time Lemma subseteq_union_2_L X Y : X \226\136\170 Y = Y \226\134\146 X \226\138\134 Y.
Time Proof.
Time unfold_leibniz.
Time (apply subseteq_union_2).
Time Qed.
Time #[global]Instance union_idemp_L : (IdemP (=@{C} ) (\226\136\170)).
Time Proof.
Time (intros ?).
Time unfold_leibniz.
Time (apply (idemp _)).
Time Qed.
Time #[global]Instance union_empty_l_L : (LeftId (=@{C} ) \226\136\133 (\226\136\170)).
Time Proof.
Time (intros ?).
Time unfold_leibniz.
Time (apply (left_id _ _)).
Time Qed.
Time #[global]Instance union_empty_r_L : (RightId (=@{C} ) \226\136\133 (\226\136\170)).
Time Proof.
Time (intros ?).
Time unfold_leibniz.
Time (apply (right_id _ _)).
Time Qed.
Time #[global]Instance union_comm_L : (Comm (=@{C} ) (\226\136\170)).
Time Proof.
Time (intros ? ?).
Time unfold_leibniz.
Time (apply (comm _)).
Time Qed.
Time #[global]Instance union_assoc_L : (Assoc (=@{C} ) (\226\136\170)).
Time Proof.
Time (intros ? ? ?).
Time unfold_leibniz.
Time (apply (assoc _)).
Time Qed.
Time Lemma empty_union_L X Y : X \226\136\170 Y = \226\136\133 \226\134\148 X = \226\136\133 \226\136\167 Y = \226\136\133.
Time Proof.
Time unfold_leibniz.
Time (apply empty_union).
Time Qed.
Time Lemma union_cancel_l_L X Y Z : Z ## X \226\134\146 Z ## Y \226\134\146 Z \226\136\170 X = Z \226\136\170 Y \226\134\146 X = Y.
Time Proof.
Time unfold_leibniz.
Time (apply union_cancel_l).
Time Qed.
Time Lemma union_cancel_r_L X Y Z : X ## Z \226\134\146 Y ## Z \226\134\146 X \226\136\170 Z = Y \226\136\170 Z \226\134\146 X = Y.
Time Proof.
Time unfold_leibniz.
Time (apply union_cancel_r).
Time Qed.
Time Lemma elem_of_equiv_empty_L X : X = \226\136\133 \226\134\148 (\226\136\128 x, x \226\136\137 X).
Time Proof.
Time unfold_leibniz.
Time (apply elem_of_equiv_empty).
Time Qed.
Time Lemma equiv_empty_L X : X \226\138\134 \226\136\133 \226\134\146 X = \226\136\133.
Time Proof.
Time unfold_leibniz.
Time (apply equiv_empty).
Time Qed.
Time Lemma union_positive_l_L X Y : X \226\136\170 Y = \226\136\133 \226\134\146 X = \226\136\133.
Time Proof.
Time unfold_leibniz.
Time (apply union_positive_l).
Time Qed.
Time Lemma union_positive_l_alt_L X Y : X \226\137\160 \226\136\133 \226\134\146 X \226\136\170 Y \226\137\160 \226\136\133.
Time Proof.
Time unfold_leibniz.
Time (apply union_positive_l_alt).
Time Qed.
Time Lemma non_empty_inhabited_L x X : x \226\136\136 X \226\134\146 X \226\137\160 \226\136\133.
Time Proof.
Time unfold_leibniz.
Time (apply non_empty_inhabited).
Time Qed.
Time Lemma non_empty_singleton_L x : {[x]} \226\137\160 (\226\136\133 : C).
Time Proof.
Time unfold_leibniz.
Time (apply non_empty_singleton).
Time Qed.
Time Lemma union_list_singleton_L X : \226\139\131 [X] = X.
Time Proof.
Time unfold_leibniz.
Time (apply union_list_singleton).
Time Qed.
Time Lemma union_list_app_L Xs1 Xs2 : \226\139\131 (Xs1 ++ Xs2) = \226\139\131 Xs1 \226\136\170 \226\139\131 Xs2.
Time Proof.
Time unfold_leibniz.
Time (apply union_list_app).
Time Qed.
Time Lemma union_list_reverse_L Xs : \226\139\131 reverse Xs = \226\139\131 Xs.
Time Proof.
Time unfold_leibniz.
Time (apply union_list_reverse).
Time Qed.
Time Lemma empty_union_list_L Xs : \226\139\131 Xs = \226\136\133 \226\134\148 Forall (=\226\136\133) Xs.
Time Proof.
Time unfold_leibniz.
Time by rewrite empty_union_list.
Time Qed.
Time End leibniz.
Time Section dec.
Time Context `{!RelDecision (\226\137\161@{C} )}.
Time Lemma set_subseteq_inv X Y : X \226\138\134 Y \226\134\146 X \226\138\130 Y \226\136\168 X \226\137\161 Y.
Time Proof.
Time (destruct (decide (X \226\137\161 Y)); [ by right | left; set_solver ]).
Time Qed.
Time Lemma set_not_subset_inv X Y : X \226\138\132 Y \226\134\146 X \226\138\136 Y \226\136\168 X \226\137\161 Y.
Time Proof.
Time (destruct (decide (X \226\137\161 Y)); [ by right | left; set_solver ]).
Time Qed.
Time Lemma non_empty_union X Y : X \226\136\170 Y \226\137\162 \226\136\133 \226\134\148 X \226\137\162 \226\136\133 \226\136\168 Y \226\137\162 \226\136\133.
Time Proof.
Time (rewrite empty_union).
Time (destruct (decide (X \226\137\161 \226\136\133)); intuition).
Time Qed.
Time Lemma non_empty_union_list Xs : \226\139\131 Xs \226\137\162 \226\136\133 \226\134\146 Exists (\226\137\162\226\136\133) Xs.
Time Proof.
Time (rewrite empty_union_list).
Time (apply (not_Forall_Exists _)).
Time Qed.
Time Context `{!LeibnizEquiv C}.
Time Lemma set_subseteq_inv_L X Y : X \226\138\134 Y \226\134\146 X \226\138\130 Y \226\136\168 X = Y.
Time Proof.
Time unfold_leibniz.
Time (apply set_subseteq_inv).
Time Qed.
Time Lemma set_not_subset_inv_L X Y : X \226\138\132 Y \226\134\146 X \226\138\136 Y \226\136\168 X = Y.
Time Proof.
Time unfold_leibniz.
Time (apply set_not_subset_inv).
Time Qed.
Time Lemma non_empty_union_L X Y : X \226\136\170 Y \226\137\160 \226\136\133 \226\134\148 X \226\137\160 \226\136\133 \226\136\168 Y \226\137\160 \226\136\133.
Time Proof.
Time unfold_leibniz.
Time (apply non_empty_union).
Time Qed.
Time Lemma non_empty_union_list_L Xs : \226\139\131 Xs \226\137\160 \226\136\133 \226\134\146 Exists (\226\137\160\226\136\133) Xs.
Time Proof.
Time unfold_leibniz.
Time (apply non_empty_union_list).
Time Qed.
Time End dec.
Time End semi_set.
Time Section set.
Time Context `{Set_ A C}.
Time Implicit Types x y : A.
Time Implicit Types X Y : C.
Time Lemma subseteq_intersection X Y : X \226\138\134 Y \226\134\148 X \226\136\169 Y \226\137\161 X.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma subseteq_intersection_1 X Y : X \226\138\134 Y \226\134\146 X \226\136\169 Y \226\137\161 X.
Time Proof.
Time (apply subseteq_intersection).
Time Qed.
Time Lemma subseteq_intersection_2 X Y : X \226\136\169 Y \226\137\161 X \226\134\146 X \226\138\134 Y.
Time Proof.
Time (apply subseteq_intersection).
Time Qed.
Time Lemma intersection_subseteq_l X Y : X \226\136\169 Y \226\138\134 X.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma intersection_subseteq_r X Y : X \226\136\169 Y \226\138\134 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma intersection_greatest X Y Z : Z \226\138\134 X \226\134\146 Z \226\138\134 Y \226\134\146 Z \226\138\134 X \226\136\169 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma intersection_mono_l X Y1 Y2 : Y1 \226\138\134 Y2 \226\134\146 X \226\136\169 Y1 \226\138\134 X \226\136\169 Y2.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma intersection_mono_r X1 X2 Y : X1 \226\138\134 X2 \226\134\146 X1 \226\136\169 Y \226\138\134 X2 \226\136\169 Y.
Time Proof.
Time set_solver.
Time Qed.
Time
Lemma intersection_mono X1 X2 Y1 Y2 : X1 \226\138\134 X2 \226\134\146 Y1 \226\138\134 Y2 \226\134\146 X1 \226\136\169 Y1 \226\138\134 X2 \226\136\169 Y2.
Time Proof.
Time set_solver.
Time Qed.
Time #[global]Instance intersection_idemp : (IdemP (\226\137\161@{C} ) (\226\136\169)).
Time Proof.
Time (intros X; set_solver).
Time Qed.
Time #[global]Instance intersection_comm : (Comm (\226\137\161@{C} ) (\226\136\169)).
Time Proof.
Time (intros X Y; set_solver).
Time Qed.
Time #[global]Instance intersection_assoc : (Assoc (\226\137\161@{C} ) (\226\136\169)).
Time Proof.
Time (intros X Y Z; set_solver).
Time Qed.
Time #[global]Instance intersection_empty_l : (LeftAbsorb (\226\137\161@{C} ) \226\136\133 (\226\136\169)).
Time Proof.
Time (intros X; set_solver).
Time Qed.
Time #[global]Instance intersection_empty_r : (RightAbsorb (\226\137\161@{C} ) \226\136\133 (\226\136\169)).
Time Proof.
Time (intros X; set_solver).
Time Qed.
Time Lemma intersection_singletons x : ({[x]} : C) \226\136\169 {[x]} \226\137\161 {[x]}.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma union_intersection_l X Y Z : X \226\136\170 Y \226\136\169 Z \226\137\161 (X \226\136\170 Y) \226\136\169 (X \226\136\170 Z).
Time Proof.
Time set_solver.
Time Qed.
Time Lemma union_intersection_r X Y Z : X \226\136\169 Y \226\136\170 Z \226\137\161 (X \226\136\170 Z) \226\136\169 (Y \226\136\170 Z).
Time Proof.
Time set_solver.
Time Qed.
Time Lemma intersection_union_l X Y Z : X \226\136\169 (Y \226\136\170 Z) \226\137\161 X \226\136\169 Y \226\136\170 X \226\136\169 Z.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma intersection_union_r X Y Z : (X \226\136\170 Y) \226\136\169 Z \226\137\161 X \226\136\169 Z \226\136\170 Y \226\136\169 Z.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma difference_twice X Y : X \226\136\150 Y \226\136\150 Y \226\137\161 X \226\136\150 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma subseteq_empty_difference X Y : X \226\138\134 Y \226\134\146 X \226\136\150 Y \226\137\161 \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma difference_diag X : X \226\136\150 X \226\137\161 \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma difference_empty X : X \226\136\150 \226\136\133 \226\137\161 X.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma difference_union_distr_l X Y Z : (X \226\136\170 Y) \226\136\150 Z \226\137\161 X \226\136\150 Z \226\136\170 Y \226\136\150 Z.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma difference_union_distr_r X Y Z : Z \226\136\150 (X \226\136\170 Y) \226\137\161 (Z \226\136\150 X) \226\136\169 (Z \226\136\150 Y).
Time Proof.
Time set_solver.
Time Qed.
Time
Lemma difference_intersection_distr_l X Y Z : X \226\136\169 Y \226\136\150 Z \226\137\161 (X \226\136\150 Z) \226\136\169 Y \226\136\150 Z.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma difference_disjoint X Y : X ## Y \226\134\146 X \226\136\150 Y \226\137\161 X.
Time Proof.
Time set_solver.
Time Qed.
Time
Lemma subset_difference_elem_of {x : A} {s : C} (inx : x \226\136\136 s) : s \226\136\150 {[x]} \226\138\130 s.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma difference_difference X Y Z : X \226\136\150 Y \226\136\150 Z \226\137\161 X \226\136\150 (Y \226\136\170 Z).
Time Proof.
Time set_solver.
Time Qed.
Time
Lemma difference_mono X1 X2 Y1 Y2 : X1 \226\138\134 X2 \226\134\146 Y2 \226\138\134 Y1 \226\134\146 X1 \226\136\150 Y1 \226\138\134 X2 \226\136\150 Y2.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma difference_mono_l X Y1 Y2 : Y2 \226\138\134 Y1 \226\134\146 X \226\136\150 Y1 \226\138\134 X \226\136\150 Y2.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma difference_mono_r X1 X2 Y : X1 \226\138\134 X2 \226\134\146 X1 \226\136\150 Y \226\138\134 X2 \226\136\150 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma subseteq_difference_r X Y1 Y2 : X ## Y2 \226\134\146 X \226\138\134 Y1 \226\134\146 X \226\138\134 Y1 \226\136\150 Y2.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma subseteq_difference_l X1 X2 Y : X1 \226\138\134 Y \226\134\146 X1 \226\136\150 X2 \226\138\134 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_intersection X Y : X ## Y \226\134\148 X \226\136\169 Y \226\137\161 \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_difference_l1 X1 X2 Y : Y \226\138\134 X2 \226\134\146 X1 \226\136\150 X2 ## Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_difference_l2 X1 X2 Y : X1 ## Y \226\134\146 X1 \226\136\150 X2 ## Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_difference_r1 X Y1 Y2 : X \226\138\134 Y2 \226\134\146 X ## Y1 \226\136\150 Y2.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_difference_r2 X Y1 Y2 : X ## Y1 \226\134\146 X ## Y1 \226\136\150 Y2.
Time Proof.
Time set_solver.
Time Qed.
Time Section leibniz.
Time Context `{!LeibnizEquiv C}.
Time Lemma subseteq_intersection_L X Y : X \226\138\134 Y \226\134\148 X \226\136\169 Y = X.
Time Proof.
Time unfold_leibniz.
Time (apply subseteq_intersection).
Time Qed.
Time Lemma subseteq_intersection_1_L X Y : X \226\138\134 Y \226\134\146 X \226\136\169 Y = X.
Time Proof.
Time unfold_leibniz.
Time (apply subseteq_intersection_1).
Time Qed.
Time Lemma subseteq_intersection_2_L X Y : X \226\136\169 Y = X \226\134\146 X \226\138\134 Y.
Time Proof.
Time unfold_leibniz.
Time (apply subseteq_intersection_2).
Time Qed.
Time #[global]Instance intersection_idemp_L : (IdemP (=@{C} ) (\226\136\169)).
Time Proof.
Time (intros ?).
Time unfold_leibniz.
Time (apply (idemp _)).
Time Qed.
Time #[global]Instance intersection_comm_L : (Comm (=@{C} ) (\226\136\169)).
Time Proof.
Time (intros ? ?).
Time unfold_leibniz.
Time (apply (comm _)).
Time Qed.
Time #[global]Instance intersection_assoc_L : (Assoc (=@{C} ) (\226\136\169)).
Time Proof.
Time (intros ? ? ?).
Time unfold_leibniz.
Time (apply (assoc _)).
Time Qed.
Time #[global]Instance intersection_empty_l_L : (LeftAbsorb (=@{C} ) \226\136\133 (\226\136\169)).
Time Proof.
Time (intros ?).
Time unfold_leibniz.
Time (apply (left_absorb _ _)).
Time Qed.
Time #[global]Instance intersection_empty_r_L : (RightAbsorb (=@{C} ) \226\136\133 (\226\136\169)).
Time Proof.
Time (intros ?).
Time unfold_leibniz.
Time (apply (right_absorb _ _)).
Time Qed.
Time Lemma intersection_singletons_L x : {[x]} \226\136\169 {[x]} = ({[x]} : C).
Time Proof.
Time unfold_leibniz.
Time (apply intersection_singletons).
Time Qed.
Time Lemma union_intersection_l_L X Y Z : X \226\136\170 Y \226\136\169 Z = (X \226\136\170 Y) \226\136\169 (X \226\136\170 Z).
Time Proof.
Time (unfold_leibniz; apply union_intersection_l).
Time Qed.
Time Lemma union_intersection_r_L X Y Z : X \226\136\169 Y \226\136\170 Z = (X \226\136\170 Z) \226\136\169 (Y \226\136\170 Z).
Time Proof.
Time (unfold_leibniz; apply union_intersection_r).
Time Qed.
Time Lemma intersection_union_l_L X Y Z : X \226\136\169 (Y \226\136\170 Z) = X \226\136\169 Y \226\136\170 X \226\136\169 Z.
Time Proof.
Time (unfold_leibniz; apply intersection_union_l).
Time Qed.
Time Lemma intersection_union_r_L X Y Z : (X \226\136\170 Y) \226\136\169 Z = X \226\136\169 Z \226\136\170 Y \226\136\169 Z.
Time Proof.
Time (unfold_leibniz; apply intersection_union_r).
Time Qed.
Time Lemma difference_twice_L X Y : X \226\136\150 Y \226\136\150 Y = X \226\136\150 Y.
Time Proof.
Time unfold_leibniz.
Time (apply difference_twice).
Time Qed.
Time Lemma subseteq_empty_difference_L X Y : X \226\138\134 Y \226\134\146 X \226\136\150 Y = \226\136\133.
Time Proof.
Time unfold_leibniz.
Time (apply subseteq_empty_difference).
Time Qed.
Time Lemma difference_diag_L X : X \226\136\150 X = \226\136\133.
Time Proof.
Time unfold_leibniz.
Time (apply difference_diag).
Time Qed.
Time Lemma difference_empty_L X : X \226\136\150 \226\136\133 = X.
Time Proof.
Time unfold_leibniz.
Time (apply difference_empty).
Time Qed.
Time Lemma difference_union_distr_l_L X Y Z : (X \226\136\170 Y) \226\136\150 Z = X \226\136\150 Z \226\136\170 Y \226\136\150 Z.
Time Proof.
Time unfold_leibniz.
Time (apply difference_union_distr_l).
Time Qed.
Time
Lemma difference_union_distr_r_L X Y Z : Z \226\136\150 (X \226\136\170 Y) = (Z \226\136\150 X) \226\136\169 (Z \226\136\150 Y).
Time Proof.
Time unfold_leibniz.
Time (apply difference_union_distr_r).
Time Qed.
Time
Lemma difference_intersection_distr_l_L X Y Z : X \226\136\169 Y \226\136\150 Z = (X \226\136\150 Z) \226\136\169 Y \226\136\150 Z.
Time Proof.
Time unfold_leibniz.
Time (apply difference_intersection_distr_l).
Time Qed.
Time Lemma difference_disjoint_L X Y : X ## Y \226\134\146 X \226\136\150 Y = X.
Time Proof.
Time unfold_leibniz.
Time (apply difference_disjoint).
Time Qed.
Time Lemma difference_difference_L X Y Z : X \226\136\150 Y \226\136\150 Z = X \226\136\150 (Y \226\136\170 Z).
Time Proof.
Time unfold_leibniz.
Time (apply difference_difference).
Time Qed.
Time Lemma disjoint_intersection_L X Y : X ## Y \226\134\148 X \226\136\169 Y = \226\136\133.
Time Proof.
Time unfold_leibniz.
Time (apply disjoint_intersection).
Time Qed.
Time End leibniz.
Time Section dec.
Time Context `{!RelDecision (\226\136\136@{C} )}.
Time Lemma not_elem_of_intersection x X Y : x \226\136\137 X \226\136\169 Y \226\134\148 x \226\136\137 X \226\136\168 x \226\136\137 Y.
Time Proof.
Time (rewrite elem_of_intersection).
Time (destruct (decide (x \226\136\136 X)); tauto).
Time Qed.
Time Lemma not_elem_of_difference x X Y : x \226\136\137 X \226\136\150 Y \226\134\148 x \226\136\137 X \226\136\168 x \226\136\136 Y.
Time Proof.
Time (rewrite elem_of_difference).
Time (destruct (decide (x \226\136\136 Y)); tauto).
Time Qed.
Time Lemma union_difference X Y : X \226\138\134 Y \226\134\146 Y \226\137\161 X \226\136\170 Y \226\136\150 X.
Time Proof.
Time
(intros ? x; split; rewrite !elem_of_union, elem_of_difference;
  [  | intuition ]).
Time (destruct (decide (x \226\136\136 X)); intuition).
Time Qed.
Time Lemma difference_union X Y : X \226\136\150 Y \226\136\170 Y \226\137\161 X \226\136\170 Y.
Time Proof.
Time (intros x).
Time (rewrite !elem_of_union; rewrite elem_of_difference).
Time (split; [  | destruct (decide (x \226\136\136 Y)) ]; intuition).
Time Qed.
Time Lemma subseteq_disjoint_union X Y : X \226\138\134 Y \226\134\148 (\226\136\131 Z, Y \226\137\161 X \226\136\170 Z \226\136\167 X ## Z).
Time Proof.
Time (split; [  | set_solver ]).
Time (exists (Y \226\136\150 X); split; [ auto using union_difference | set_solver ]).
Time Qed.
Time Lemma non_empty_difference X Y : X \226\138\130 Y \226\134\146 Y \226\136\150 X \226\137\162 \226\136\133.
Time Proof.
Time (intros [HXY1 HXY2] Hdiff).
Time (destruct HXY2).
Time set_solver.
Time Qed.
Time Lemma empty_difference_subseteq X Y : X \226\136\150 Y \226\137\161 \226\136\133 \226\134\146 X \226\138\134 Y.
Time Proof.
Time set_solver.
Time Qed.
Time
Lemma singleton_union_difference X Y x :
  {[x]} \226\136\170 X \226\136\150 Y \226\137\161 ({[x]} \226\136\170 X) \226\136\150 (Y \226\136\150 {[x]}).
Time Proof.
Time (intro y; split; intros Hy; [ set_solver |  ]).
Time (destruct (decide (y \226\136\136 ({[x]} : C))); set_solver).
Time Qed.
Time Context `{!LeibnizEquiv C}.
Time Lemma union_difference_L X Y : X \226\138\134 Y \226\134\146 Y = X \226\136\170 Y \226\136\150 X.
Time Proof.
Time unfold_leibniz.
Time (apply union_difference).
Time Qed.
Time Lemma difference_union_L X Y : X \226\136\150 Y \226\136\170 Y = X \226\136\170 Y.
Time Proof.
Time unfold_leibniz.
Time (apply difference_union).
Time Qed.
Time Lemma non_empty_difference_L X Y : X \226\138\130 Y \226\134\146 Y \226\136\150 X \226\137\160 \226\136\133.
Time Proof.
Time unfold_leibniz.
Time (apply non_empty_difference).
Time Qed.
Time Lemma empty_difference_subseteq_L X Y : X \226\136\150 Y = \226\136\133 \226\134\146 X \226\138\134 Y.
Time Proof.
Time unfold_leibniz.
Time (apply empty_difference_subseteq).
Time Qed.
Time Lemma subseteq_disjoint_union_L X Y : X \226\138\134 Y \226\134\148 (\226\136\131 Z, Y = X \226\136\170 Z \226\136\167 X ## Z).
Time Proof.
Time unfold_leibniz.
Time (apply subseteq_disjoint_union).
Time Qed.
Time
Lemma singleton_union_difference_L X Y x :
  {[x]} \226\136\170 X \226\136\150 Y = ({[x]} \226\136\170 X) \226\136\150 (Y \226\136\150 {[x]}).
Time Proof.
Time unfold_leibniz.
Time (apply singleton_union_difference).
Time Qed.
Time End dec.
Time End set.
Time Section option_and_list_to_set.
Time Context `{SemiSet A C}.
Time Implicit Type l : list A.
Time
Lemma elem_of_option_to_set (x : A) mx :
  x \226\136\136 option_to_set (C:=C) mx \226\134\148 mx = Some x.
Time Proof.
Time (destruct mx; set_solver).
Time Qed.
Time
Lemma not_elem_of_option_to_set (x : A) mx :
  x \226\136\137 option_to_set (C:=C) mx \226\134\148 mx \226\137\160 Some x.
Time Proof.
Time by rewrite elem_of_option_to_set.
Time Qed.
Time Lemma elem_of_list_to_set (x : A) l : x \226\136\136 list_to_set (C:=C) l \226\134\148 x \226\136\136 l.
Time Proof.
Time split.
Time -
Time (induction l; simpl; [ by rewrite elem_of_empty |  ]).
Time
(rewrite elem_of_union, elem_of_singleton; intros [->| ?]; constructor; auto).
Time -
Time (induction 1; simpl; rewrite elem_of_union, elem_of_singleton; auto).
Time Qed.
Time
Lemma not_elem_of_list_to_set (x : A) l : x \226\136\137 list_to_set (C:=C) l \226\134\148 x \226\136\137 l.
Time Proof.
Time by rewrite elem_of_list_to_set.
Time Qed.
Time #[global]
Instance set_unfold_option_to_set  (mx : option A) 
 x: (SetUnfoldElemOf x (option_to_set (C:=C) mx) (mx = Some x)).
Time Proof.
Time (constructor; apply elem_of_option_to_set).
Time Qed.
Time #[global]
Instance set_unfold_list_to_set  (l : list A) x P:
 (SetUnfoldElemOf x l P \226\134\146 SetUnfoldElemOf x (list_to_set (C:=C) l) P).
Time Proof.
Time constructor.
Time by rewrite elem_of_list_to_set, (set_unfold (x \226\136\136 l) P).
Time Qed.
Time Lemma list_to_set_nil : list_to_set [] =@{ C} \226\136\133.
Time Proof.
Time done.
Time Qed.
Time
Lemma list_to_set_cons x l :
  list_to_set (x :: l) =@{ C} {[x]} \226\136\170 list_to_set l.
Time Proof.
Time done.
Time Qed.
Time
Lemma list_to_set_app l1 l2 :
  list_to_set (l1 ++ l2) \226\137\161@{ C} list_to_set l1 \226\136\170 list_to_set l2.
Time Proof.
Time set_solver.
Time Qed.
Time #[global]
Instance list_to_set_perm : (Proper ((\226\137\161\226\130\154) ==> (\226\137\161)) (list_to_set (C:=C))).
Time Proof.
Time (induction 1; set_solver).
Time Qed.
Time Context `{!LeibnizEquiv C}.
Time
Lemma list_to_set_app_L l1 l2 :
  list_to_set (l1 ++ l2) =@{ C} list_to_set l1 \226\136\170 list_to_set l2.
Time Proof.
Time set_solver.
Time Qed.
Time #[global]
Instance list_to_set_perm_L : (Proper ((\226\137\161\226\130\154) ==> (=)) (list_to_set (C:=C))).
Time Proof.
Time (induction 1; set_solver).
Time Qed.
Time End option_and_list_to_set.
Time #[global]
Instance set_guard  `{MonadSet M}: (MGuard M) :=
 (\206\187 P dec A x, match dec with
               | left H => x H
               | _ => \226\136\133
               end).
Time Section set_monad_base.
Time Context `{MonadSet M}.
Time
Lemma elem_of_guard `{Decision P} {A} (x : A) (X : M A) :
  x \226\136\136 guard P; X \226\134\148 P \226\136\167 x \226\136\136 X.
Time Proof.
Time
(unfold mguard, set_guard; simpl; case_match; rewrite ?elem_of_empty;
  naive_solver).
Time Qed.
Time
Lemma elem_of_guard_2 `{Decision P} {A} (x : A) (X : M A) :
  P \226\134\146 x \226\136\136 X \226\134\146 x \226\136\136 guard P; X.
Time Proof.
Time by rewrite elem_of_guard.
Time Qed.
Time
Lemma guard_empty `{Decision P} {A} (X : M A) : guard P; X \226\137\161 \226\136\133 \226\134\148 \194\172 P \226\136\168 X \226\137\161 \226\136\133.
Time Proof.
Time (rewrite !elem_of_equiv_empty; setoid_rewrite elem_of_guard).
Time (destruct (decide P); naive_solver).
Time Qed.
Time #[global]
Instance set_unfold_guard  `{Decision P} {A} (x : A) 
 (X : M A) Q:
 (SetUnfoldElemOf x X Q \226\134\146 SetUnfoldElemOf x (guard P; X) (P \226\136\167 Q)).
Time Proof.
Time constructor.
Time by rewrite elem_of_guard, (set_unfold (x \226\136\136 X) Q).
Time Qed.
Time
Lemma bind_empty {A} {B} (f : A \226\134\146 M B) X :
  X \226\137\171= f \226\137\161 \226\136\133 \226\134\148 X \226\137\161 \226\136\133 \226\136\168 (\226\136\128 x, x \226\136\136 X \226\134\146 f x \226\137\161 \226\136\133).
Time Proof.
Time set_solver.
Time Qed.
Time End set_monad_base.
Time
Definition set_Forall `{ElemOf A C} (P : A \226\134\146 Prop) 
  (X : C) := \226\136\128 x, x \226\136\136 X \226\134\146 P x.
Time
Definition set_Exists `{ElemOf A C} (P : A \226\134\146 Prop) 
  (X : C) := \226\136\131 x, x \226\136\136 X \226\136\167 P x.
Time Section quantifiers.
Time Context `{SemiSet A C} (P : A \226\134\146 Prop).
Time Implicit Types X Y : C.
Time Lemma set_Forall_empty : set_Forall P (\226\136\133 : C).
Time Proof.
Time (unfold set_Forall).
Time set_solver.
Time Qed.
Time Lemma set_Forall_singleton x : set_Forall P ({[x]} : C) \226\134\148 P x.
Time Proof.
Time (unfold set_Forall).
Time set_solver.
Time Qed.
Time
Lemma set_Forall_union X Y :
  set_Forall P X \226\134\146 set_Forall P Y \226\134\146 set_Forall P (X \226\136\170 Y).
Time Proof.
Time (unfold set_Forall).
Time set_solver.
Time Qed.
Time
Lemma set_Forall_union_inv_1 X Y : set_Forall P (X \226\136\170 Y) \226\134\146 set_Forall P X.
Time Proof.
Time (unfold set_Forall).
Time set_solver.
Time Qed.
Time
Lemma set_Forall_union_inv_2 X Y : set_Forall P (X \226\136\170 Y) \226\134\146 set_Forall P Y.
Time Proof.
Time (unfold set_Forall).
Time set_solver.
Time Qed.
Time
Lemma set_Forall_list_to_set l :
  set_Forall P (list_to_set (C:=C) l) \226\134\148 Forall P l.
Time Proof.
Time (rewrite Forall_forall).
Time (unfold set_Forall).
Time set_solver.
Time Qed.
Time Lemma set_Exists_empty : \194\172 set_Exists P (\226\136\133 : C).
Time Proof.
Time (unfold set_Exists).
Time set_solver.
Time Qed.
Time Lemma set_Exists_singleton x : set_Exists P ({[x]} : C) \226\134\148 P x.
Time Proof.
Time (unfold set_Exists).
Time set_solver.
Time Qed.
Time Lemma set_Exists_union_1 X Y : set_Exists P X \226\134\146 set_Exists P (X \226\136\170 Y).
Time Proof.
Time (unfold set_Exists).
Time set_solver.
Time Qed.
Time Lemma set_Exists_union_2 X Y : set_Exists P Y \226\134\146 set_Exists P (X \226\136\170 Y).
Time Proof.
Time (unfold set_Exists).
Time set_solver.
Time Qed.
Time
Lemma set_Exists_union_inv X Y :
  set_Exists P (X \226\136\170 Y) \226\134\146 set_Exists P X \226\136\168 set_Exists P Y.
Time Proof.
Time (unfold set_Exists).
Time set_solver.
Time Qed.
Time
Lemma set_Exists_list_to_set l :
  set_Exists P (list_to_set (C:=C) l) \226\134\148 Exists P l.
Time Proof.
Time (rewrite Exists_exists).
Time (unfold set_Exists).
Time set_solver.
Time Qed.
Time End quantifiers.
Time Section more_quantifiers.
Time Context `{SemiSet A C}.
Time Implicit Type X : C.
Time
Lemma set_Forall_impl (P Q : A \226\134\146 Prop) X :
  set_Forall P X \226\134\146 (\226\136\128 x, P x \226\134\146 Q x) \226\134\146 set_Forall Q X.
Time Proof.
Time (unfold set_Forall).
Time naive_solver.
Time Qed.
Time
Lemma set_Exists_impl (P Q : A \226\134\146 Prop) X :
  set_Exists P X \226\134\146 (\226\136\128 x, P x \226\134\146 Q x) \226\134\146 set_Exists Q X.
Time Proof.
Time (unfold set_Exists).
Time naive_solver.
Time Qed.
Time End more_quantifiers.
Time Section set_monad.
Time Context `{MonadSet M}.
Time #[global]
Instance set_fmap_mono  {A} {B}:
 (Proper (pointwise_relation _ (=) ==> (\226\138\134) ==> (\226\138\134)) (@fmap M _ A B)).
Time Proof.
Time (intros f g ? X Y ?; set_solver by eauto).
Time Qed.
Time #[global]
Instance set_bind_mono  {A} {B}:
 (Proper (pointwise_relation _ (\226\138\134) ==> (\226\138\134) ==> (\226\138\134)) (@mbind M _ A B)).
Time Proof.
Time (unfold respectful, pointwise_relation; intros f g Hfg X Y ?).
Time set_solver.
Time Qed.
Time #[global]
Instance set_join_mono  {A}: (Proper ((\226\138\134) ==> (\226\138\134)) (@mjoin M _ A)).
Time Proof.
Time (intros X Y ?; set_solver).
Time Qed.
Time Lemma set_bind_singleton {A} {B} (f : A \226\134\146 M B) x : {[x]} \226\137\171= f \226\137\161 f x.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma set_guard_True {A} `{Decision P} (X : M A) : P \226\134\146 guard P; X \226\137\161 X.
Time Proof.
Time set_solver.
Time Qed.
Time
Lemma set_fmap_compose {A} {B} {C} (f : A \226\134\146 B) (g : B \226\134\146 C) 
  (X : M A) : g \226\136\152 f <$> X \226\137\161 g <$> (f <$> X).
Time Proof.
Time set_solver.
Time Qed.
Time
Lemma elem_of_fmap_1 {A} {B} (f : A \226\134\146 B) (X : M A) 
  (y : B) : y \226\136\136 f <$> X \226\134\146 \226\136\131 x, y = f x \226\136\167 x \226\136\136 X.
Time Proof.
Time set_solver.
Time Qed.
Time
Lemma elem_of_fmap_2 {A} {B} (f : A \226\134\146 B) (X : M A) 
  (x : A) : x \226\136\136 X \226\134\146 f x \226\136\136 f <$> X.
Time Proof.
Time set_solver.
Time Qed.
Time
Lemma elem_of_fmap_2_alt {A} {B} (f : A \226\134\146 B) (X : M A) 
  (x : A) (y : B) : x \226\136\136 X \226\134\146 y = f x \226\134\146 y \226\136\136 f <$> X.
Time Proof.
Time set_solver.
Time Qed.
Time
Lemma elem_of_mapM {A} {B} (f : A \226\134\146 M B) l k :
  l \226\136\136 mapM f k \226\134\148 Forall2 (\206\187 x y, x \226\136\136 f y) l k.
Time Proof.
Time split.
Time -
Time revert l.
Time (induction k; set_solver by eauto).
Time -
Time (induction 1; set_solver).
Time Qed.
Time
Lemma set_mapM_length {A} {B} (f : A \226\134\146 M B) l k :
  l \226\136\136 mapM f k \226\134\146 length l = length k.
Time Proof.
Time (revert l; induction k; set_solver by eauto).
Time Qed.
Time
Lemma elem_of_mapM_fmap {A} {B} (f : A \226\134\146 B) (g : B \226\134\146 M A) 
  l k : Forall (\206\187 x, \226\136\128 y, y \226\136\136 g x \226\134\146 f y = x) l \226\134\146 k \226\136\136 mapM g l \226\134\146 fmap f k = l.
Time Proof.
Time (intros Hl).
Time revert k.
Time (induction Hl; set_solver).
Time Qed.
Time
Lemma elem_of_mapM_Forall {A} {B} (f : A \226\134\146 M B) (P : B \226\134\146 Prop) 
  l k : l \226\136\136 mapM f k \226\134\146 Forall (\206\187 x, \226\136\128 y, y \226\136\136 f x \226\134\146 P y) k \226\134\146 Forall P l.
Time Proof.
Time (rewrite elem_of_mapM).
Time (apply Forall2_Forall_l).
Time Qed.
Time
Lemma elem_of_mapM_Forall2_l {A} {B} {C} (f : A \226\134\146 M B) 
  (P : B \226\134\146 C \226\134\146 Prop) l1 l2 k :
  l1 \226\136\136 mapM f k
  \226\134\146 Forall2 (\206\187 x y, \226\136\128 z, z \226\136\136 f x \226\134\146 P z y) k l2 \226\134\146 Forall2 P l1 l2.
Time Proof.
Time (rewrite elem_of_mapM).
Time (intros Hl1).
Time revert l2.
Time (induction Hl1; inversion_clear 1; constructor; auto).
Time Qed.
Time End set_monad.
Time
Definition pred_finite {A} (P : A \226\134\146 Prop) := \226\136\131 xs : list A, \226\136\128 x, P x \226\134\146 x \226\136\136 xs.
Time Definition set_finite `{ElemOf A B} (X : B) := pred_finite (\226\136\136X).
Time
Definition pred_infinite {A} (P : A \226\134\146 Prop) :=
  \226\136\128 xs : list A, \226\136\131 x, P x \226\136\167 x \226\136\137 xs.
Time Definition set_infinite `{ElemOf A C} (X : C) := pred_infinite (\226\136\136X).
Time Section pred_finite_infinite.
Time
Lemma pred_finite_impl {A} (P Q : A \226\134\146 Prop) :
  pred_finite P \226\134\146 (\226\136\128 x, Q x \226\134\146 P x) \226\134\146 pred_finite Q.
Time Proof.
Time (unfold pred_finite).
Time set_solver.
Time Qed.
Time
Lemma pred_infinite_impl {A} (P Q : A \226\134\146 Prop) :
  pred_infinite P \226\134\146 (\226\136\128 x, P x \226\134\146 Q x) \226\134\146 pred_infinite Q.
Time Proof.
Time (unfold pred_infinite).
Time set_solver.
Time Qed.
Time
Lemma pred_not_infinite_finite {A} (P : A \226\134\146 Prop) :
  pred_infinite P \226\134\146 pred_finite P \226\134\146 False.
Time Proof.
Time (intros Hinf [xs ?]).
Time (destruct (Hinf xs)).
Time set_solver.
Time Qed.
Time Lemma pred_infinite_True `{Infinite A} : pred_infinite (\206\187 _ : A, True).
Time Proof.
Time (intros xs).
Time exists (fresh xs).
Time (split; [ done |  ]).
Time (apply infinite_is_fresh).
Time Qed.
Time End pred_finite_infinite.
Time Section set_finite_infinite.
Time Context `{SemiSet A C}.
Time Implicit Types X Y : C.
Time Lemma set_not_infinite_finite X : set_infinite X \226\134\146 set_finite X \226\134\146 False.
Time Proof.
Time (apply pred_not_infinite_finite).
Time Qed.
Time #[global]
Instance set_finite_subseteq :
 (Proper (flip (\226\138\134) ==> impl) (@set_finite A C _)).
Time Proof.
Time (intros X Y HX ?).
Time (eapply pred_finite_impl; set_solver).
Time Qed.
Time #[global]
Instance set_finite_proper : (Proper ((\226\137\161) ==> iff) (@set_finite A C _)).
Time Proof.
Time (intros X Y HX; apply exist_proper).
Time by setoid_rewrite HX.
Time Qed.
Time Lemma empty_finite : set_finite (\226\136\133 : C).
Time Proof.
Time by exists []; intros ?; rewrite elem_of_empty.
Time Qed.
Time Lemma singleton_finite (x : A) : set_finite ({[x]} : C).
Time Proof.
Time (exists [x]; intros y ->%elem_of_singleton; left).
Time Qed.
Time
Lemma union_finite X Y : set_finite X \226\134\146 set_finite Y \226\134\146 set_finite (X \226\136\170 Y).
Time Proof.
Time (intros [lX ?] [lY ?]; exists (lX ++ lY); intros x).
Time (rewrite elem_of_union, elem_of_app; naive_solver).
Time Qed.
Time Lemma union_finite_inv_l X Y : set_finite (X \226\136\170 Y) \226\134\146 set_finite X.
Time Proof.
Time (intros [l ?]; exists l; set_solver).
Time Qed.
Time Lemma union_finite_inv_r X Y : set_finite (X \226\136\170 Y) \226\134\146 set_finite Y.
Time Proof.
Time (intros [l ?]; exists l; set_solver).
Time Qed.
Time #[global]
Instance set_infinite_subseteq :
 (Proper ((\226\138\134) ==> impl) (@set_infinite A C _)).
Time Proof.
Time (intros X Y HX ?).
Time (eapply pred_infinite_impl; set_solver).
Time Qed.
Time #[global]
Instance set_infinite_proper : (Proper ((\226\137\161) ==> iff) (@set_infinite A C _)).
Time Proof.
Time (intros X Y HX; apply forall_proper).
Time by setoid_rewrite HX.
Time Qed.
Time Lemma union_infinite_l X Y : set_infinite X \226\134\146 set_infinite (X \226\136\170 Y).
Time Proof.
Time (intros Hinf xs).
Time (destruct (Hinf xs)).
Time set_solver.
Time Qed.
Time Lemma union_infinite_r X Y : set_infinite Y \226\134\146 set_infinite (X \226\136\170 Y).
Time Proof.
Time (intros Hinf xs).
Time (destruct (Hinf xs)).
Time set_solver.
Time Qed.
Time End set_finite_infinite.
Time Section more_finite.
Time Context `{Set_ A C}.
Time Implicit Types X Y : C.
Time Lemma intersection_finite_l X Y : set_finite X \226\134\146 set_finite (X \226\136\169 Y).
Time Proof.
Time (intros [l ?]; exists l; intros x [? ?]%elem_of_intersection; auto).
Time Qed.
Time Lemma intersection_finite_r X Y : set_finite Y \226\134\146 set_finite (X \226\136\169 Y).
Time Proof.
Time (intros [l ?]; exists l; intros x [? ?]%elem_of_intersection; auto).
Time Qed.
Time Lemma difference_finite X Y : set_finite X \226\134\146 set_finite (X \226\136\150 Y).
Time Proof.
Time (intros [l ?]; exists l; intros x [? ?]%elem_of_difference; auto).
Time Qed.
Time
Lemma difference_finite_inv X Y `{\226\136\128 x, Decision (x \226\136\136 Y)} :
  set_finite Y \226\134\146 set_finite (X \226\136\150 Y) \226\134\146 set_finite X.
Time Proof.
Time (intros [l ?] [k ?]; exists (l ++ k)).
Time
(intros x ?; destruct (decide (x \226\136\136 Y)); rewrite elem_of_app; set_solver).
Time Qed.
Time
Lemma difference_infinite X Y :
  set_infinite X \226\134\146 set_finite Y \226\134\146 set_infinite (X \226\136\150 Y).
Time Proof.
Time (intros Hinf [xs ?] xs').
Time (destruct (Hinf (xs ++ xs'))).
Time set_solver.
Time Qed.
Time End more_finite.
Time
Fixpoint set_seq `{Singleton nat C} `{Union C} `{Empty C} 
(start len : nat) : C :=
  match len with
  | O => \226\136\133
  | S len' => {[start]} \226\136\170 set_seq (S start) len'
  end.
Time Section set_seq.
Time Context `{SemiSet nat C}.
Time Implicit Types start len x : nat.
Time
Lemma elem_of_set_seq start len x :
  x \226\136\136 set_seq (C:=C) start len \226\134\148 start \226\137\164 x < start + len.
Time Proof.
Time revert start.
Time (induction len as [| len IH]; intros start; simpl).
Time -
Time (rewrite elem_of_empty).
Time lia.
Time -
Time (rewrite elem_of_union, elem_of_singleton, IH).
Time lia.
Time Qed.
Time #[global]
Instance set_unfold_seq  start len:
 (SetUnfoldElemOf x (set_seq (C:=C) start len) (start \226\137\164 x < start + len)).
Time Proof.
Time (constructor; apply elem_of_set_seq).
Time Qed.
Time
Lemma set_seq_plus_disjoint start len1 len2 :
  set_seq (C:=C) start len1 ## set_seq (start + len1) len2.
Time Proof.
Time set_solver by lia.
Time Qed.
Time
Lemma set_seq_plus start len1 len2 :
  set_seq (C:=C) start (len1 + len2)
  \226\137\161 set_seq start len1 \226\136\170 set_seq (start + len1) len2.
Time Proof.
Time set_solver by lia.
Time Qed.
Time
Lemma set_seq_plus_L `{!LeibnizEquiv C} start len1 
  len2 :
  set_seq (C:=C) start (len1 + len2) =
  set_seq start len1 \226\136\170 set_seq (start + len1) len2.
Time Proof.
Time unfold_leibniz.
Time (apply set_seq_plus).
Time Qed.
Time
Lemma set_seq_S_start_disjoint start len :
  {[start]} ## set_seq (C:=C) (S start) len.
Time Proof.
Time set_solver by lia.
Time Qed.
Time
Lemma set_seq_S_start start len :
  set_seq (C:=C) start (S len) \226\137\161 {[start]} \226\136\170 set_seq (S start) len.
Time Proof.
Time set_solver by lia.
Time Qed.
Time
Lemma set_seq_S_end_disjoint start len :
  {[start + len]} ## set_seq (C:=C) start len.
Time Proof.
Time set_solver by lia.
Time Qed.
Time
Lemma set_seq_S_end_union start len :
  set_seq start (S len) \226\137\161@{ C} {[start + len]} \226\136\170 set_seq start len.
Time Proof.
Time set_solver by lia.
Time Qed.
Time
Lemma set_seq_S_end_union_L `{!LeibnizEquiv C} start 
  len : set_seq start (S len) =@{ C} {[start + len]} \226\136\170 set_seq start len.
Time Proof.
Time unfold_leibniz.
Time (apply set_seq_S_end_union).
Time Qed.
Time
Lemma list_to_set_seq start len :
  list_to_set (seq start len) =@{ C} set_seq start len.
Time Proof.
Time (revert start; induction len; intros; f_equal /=; auto).
Time Qed.
Time Lemma set_seq_finite start len : set_finite (set_seq (C:=C) start len).
Time Proof.
Time (exists (seq start len); intros x).
Time (rewrite <- list_to_set_seq).
Time set_solver.
Time Qed.
Time End set_seq.
Time
Definition minimal `{ElemOf A C} (R : relation A) 
  (x : A) (X : C) : Prop := \226\136\128 y, y \226\136\136 X \226\134\146 R y x \226\134\146 R x y.
Time Instance: (Params (@minimal) 5) := { }.
Time Typeclasses Opaque minimal.
Time Section minimal.
Time Context `{SemiSet A C} {R : relation A}.
Time Implicit Types X Y : C.
Time #[global]
Instance minimal_proper  x: (Proper ((\226\137\161@{C} ) ==> iff) (minimal R x)).
Time Proof.
Time (intros X X' y; unfold minimal; set_solver).
Time Qed.
Time
Lemma minimal_anti_symm_1 `{!AntiSymm (=) R} X x y :
  minimal R x X \226\134\146 y \226\136\136 X \226\134\146 R y x \226\134\146 x = y.
Time Proof.
Time (intros Hmin ? ?).
Time (apply (anti_symm _); auto).
Time Qed.
Time
Lemma minimal_anti_symm `{!AntiSymm (=) R} X x :
  minimal R x X \226\134\148 (\226\136\128 y, y \226\136\136 X \226\134\146 R y x \226\134\146 x = y).
Time Proof.
Time (unfold minimal; naive_solver eauto using minimal_anti_symm_1).
Time Qed.
Time
Lemma minimal_strict_1 `{!StrictOrder R} X x y :
  minimal R x X \226\134\146 y \226\136\136 X \226\134\146 \194\172 R y x.
Time Proof.
Time (intros Hmin ? ?).
Time (destruct (irreflexivity R x); trans y; auto).
Time Qed.
Time
Lemma minimal_strict `{!StrictOrder R} X x :
  minimal R x X \226\134\148 (\226\136\128 y, y \226\136\136 X \226\134\146 \194\172 R y x).
Time Proof.
Time
(unfold minimal; split; [ eauto using minimal_strict_1 | naive_solver ]).
Time Qed.
Time Lemma empty_minimal x : minimal R x (\226\136\133 : C).
Time Proof.
Time (unfold minimal; set_solver).
Time Qed.
Time Lemma singleton_minimal x : minimal R x ({[x]} : C).
Time Proof.
Time (unfold minimal; set_solver).
Time Qed.
Time
Lemma singleton_minimal_not_above y x : \194\172 R y x \226\134\146 minimal R x ({[y]} : C).
Time Proof.
Time (unfold minimal; set_solver).
Time Qed.
Time
Lemma union_minimal X Y x :
  minimal R x X \226\134\146 minimal R x Y \226\134\146 minimal R x (X \226\136\170 Y).
Time Proof.
Time (unfold minimal; set_solver).
Time Qed.
Time Lemma minimal_subseteq X Y x : minimal R x X \226\134\146 Y \226\138\134 X \226\134\146 minimal R x Y.
Time Proof.
Time (unfold minimal; set_solver).
Time Qed.
Time
Lemma minimal_weaken `{!Transitive R} X x x' :
  minimal R x X \226\134\146 R x' x \226\134\146 minimal R x' X.
Time Proof.
Time (intros Hmin ? y ? ?).
Time (trans x; [ done |  ]).
Time by eapply (Hmin y), transitivity.
Time Qed.
Time End minimal.
