Time From stdpp Require Export fin list.
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
Time Qed.
Time
Lemma vec_to_list_inj2 {A} {n} (v : vec A n) (w : vec A n) :
  vec_to_list v = vec_to_list w \226\134\146 v = w.
Time Proof.
Time revert w.
Time
(induction v; intros w; inv_vec w; intros; simplify_eq /=; f_equal; eauto).
Time Qed.
Time
Lemma vlookup_middle {A} {n} {m} (v : vec A n) (w : vec A m) 
  x : \226\136\131 i : fin (n + S m), x = (v +++ x ::: w) !!! i.
Time Proof.
Time (induction v; simpl; [ by eexists 0%fin |  ]).
Time (destruct IHv as [i ?]).
Time by exists (FS i).
Time Qed.
Time
Lemma vec_to_list_lookup_middle {A} {n} (v : vec A n) 
  (l k : list A) x :
  vec_to_list v = l ++ x :: k
  \226\134\146 \226\136\131 i : fin n, l = take i v \226\136\167 x = v !!! i \226\136\167 k = drop (S i) v.
Time Proof.
Time (intros H).
Time (rewrite <- (vec_to_list_of_list l), <- (vec_to_list_of_list k) in H).
Time (rewrite <- vec_to_list_cons, <- vec_to_list_app in H).
Time (pose proof (vec_to_list_inj1 _ _ H); subst).
Time (apply vec_to_list_inj2 in H; subst).
Time (induction l).
Time (simpl).
Time -
Time eexists 0%fin.
Time (simpl).
Time by rewrite vec_to_list_of_list.
Time -
Time (destruct IHl as [i ?]).
Time exists (FS i).
Time (simpl).
Time intuition congruence.
Time Qed.
Time
Lemma vec_to_list_drop_lookup {A} {n} (v : vec A n) 
  (i : fin n) : drop i v = v !!! i :: drop (S i) v.
Time Proof.
Time (induction i; inv_vec v; simpl; intros; [ done | by rewrite IHi ]).
Time Qed.
Time
Lemma vec_to_list_take_drop_lookup {A} {n} (v : vec A n) 
  (i : fin n) : vec_to_list v = take i v ++ v !!! i :: drop (S i) v.
Time Proof.
Time (rewrite <- (take_drop i v)  at 1).
Time by rewrite vec_to_list_drop_lookup.
Time Qed.
Time
Lemma vlookup_lookup {A} {n} (v : vec A n) (i : fin n) 
  x : v !!! i = x \226\134\148 (v : list A) !! (i : nat) = Some x.
Time Proof.
Time (induction v as [| ? ? v IH]; inv_fin i).
Time (simpl; split; congruence).
Time done.
Time Qed.
Time
Lemma vlookup_lookup' {A} {n} (v : vec A n) (i : nat) 
  x : (\226\136\131 H : i < n, v !!! fin_of_nat H = x) \226\134\148 (v : list A) !! i = Some x.
Time Proof.
Time split.
Time -
Time (intros [Hlt ?]).
Time (rewrite <- (fin_to_of_nat i n Hlt)).
Time by apply vlookup_lookup.
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
Time (split; [ by intros (?, (?, ?)); eauto |  ]).
Time (intros [i Hx]).
Time exists i,(fin_to_nat_lt _).
Time by rewrite fin_of_to_nat.
Time Qed.
Time
Lemma Forall_vlookup {A} (P : A \226\134\146 Prop) {n} (v : vec A n) :
  Forall P (vec_to_list v) \226\134\148 (\226\136\128 i, P (v !!! i)).
Time Proof.
Time (rewrite Forall_forall).
Time setoid_rewrite elem_of_vlookup.
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
Time
Lemma Exists_vlookup {A} (P : A \226\134\146 Prop) {n} (v : vec A n) :
  Exists P (vec_to_list v) \226\134\148 (\226\136\131 i, P (v !!! i)).
Time Proof.
Time (rewrite Exists_exists).
Time setoid_rewrite elem_of_vlookup.
Time naive_solver.
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
Time (intros i).
Time (inv_fin i; simpl; auto).
Time -
Time (vec_double_ind v1 v2; [ constructor |  ]).
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
Time Proof.
Time revert v2.
Time (induction v1; intros v2; inv_vec v2; intros; simpl; [ done |  ]).
Time by rewrite IHv1.
Time Qed.
Time
Fixpoint vinsert {A n} (i : fin n) (x : A) : vec A n \226\134\146 vec A n :=
  match i with
  | 0%fin => vec_S_inv _ (\206\187 _ v, x ::: v)
  | FS i => vec_S_inv _ (\206\187 y v, y ::: vinsert i x v)
  end.
Time
Lemma vec_to_list_insert {A} {n} i x (v : vec A n) :
  vec_to_list (vinsert i x v) = insert (fin_to_nat i) x (vec_to_list v).
Time Proof.
Time (induction v; inv_fin i).
Time done.
Time (simpl).
Time (intros).
Time by rewrite IHv.
Time Qed.
Time
Lemma vlookup_insert {A} {n} i x (v : vec A n) : vinsert i x v !!! i = x.
Time Proof.
Time by induction i; inv_vec v.
Time Qed.
Time
Lemma vlookup_insert_ne {A} {n} i j x (v : vec A n) :
  i \226\137\160 j \226\134\146 vinsert i x v !!! j = v !!! j.
Time Proof.
Time (induction i; inv_fin j; inv_vec v; simpl; try done).
Time (intros).
Time (apply IHi).
Time congruence.
Time Qed.
Time
Lemma vlookup_insert_self {A} {n} i (v : vec A n) : vinsert i (v !!! i) v = v.
Time Proof.
Time by induction v; inv_fin i; intros; f_equal /=.
Time Qed.
Time
Fixpoint vreplicate {A} (n : nat) (x : A) : vec A n :=
  match n with
  | 0 => [# ]
  | S n => x ::: vreplicate n x
  end.
Time #[global]
Instance vec_0_inhabited  T: (Inhabited (vec T 0)) := (populate [# ]).
Time #[global]
Instance vec_inhabited  `{Inhabited T} n: (Inhabited (vec T n)) :=
 (populate (vreplicate n inhabitant)).
