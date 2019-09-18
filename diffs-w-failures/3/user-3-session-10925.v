Time From iris.algebra Require Export monoid.
Time From stdpp Require Export functions gmap gmultiset.
Time Set Default Proof Using "Type*".
Time #[local]
Existing Instances
 monoid_ne, monoid_assoc, monoid_comm, monoid_left_id, monoid_right_id, monoid_proper, monoid_homomorphism_rel_po, monoid_homomorphism_rel_proper, monoid_homomorphism_op_proper, monoid_homomorphism_ne, weak_monoid_homomorphism_proper.
Time
Fixpoint big_opL `{Monoid M o} {A} (f : nat \226\134\146 A \226\134\146 M) 
(xs : list A) : M :=
  match xs with
  | [] => monoid_unit
  | x :: xs => o (f 0 x) (big_opL (\206\187 n, f (S n)) xs)
  end.
Time Instance: (Params (@big_opL) 4) := { }.
Time Arguments big_opL {M} o {_} {A} _ !_ /.
Time Typeclasses Opaque big_opL.
Time
Notation "'[^' o 'list]' k \226\134\166 x \226\136\136 l , P" := (big_opL o (\206\187 k x, P) l)
  (at level 200, o  at level 1, l  at level 10, k, x  at level 1,
   right associativity, format "[^ o  list]  k \226\134\166 x  \226\136\136  l ,  P") : stdpp_scope.
Time
Notation "'[^' o 'list]' x \226\136\136 l , P" := (big_opL o (\206\187 _ x, P) l)
  (at level 200, o  at level 1, l  at level 10, x  at level 1,
   right associativity, format "[^ o  list]  x  \226\136\136  l ,  P") : stdpp_scope.
Time
Definition big_opM `{Monoid M o} `{Countable K} {A} 
  (f : K \226\134\146 A \226\134\146 M) (m : gmap K A) : M :=
  big_opL o (\206\187 _, curry f) (map_to_list m).
Time Instance: (Params (@big_opM) 7) := { }.
Time Arguments big_opM {M} o {_} {K} {_} {_} {A} _ _ : simpl never.
Time Typeclasses Opaque big_opM.
Time
Notation "'[^' o 'map]' k \226\134\166 x \226\136\136 m , P" := (big_opM o (\206\187 k x, P) m)
  (at level 200, o  at level 1, m  at level 10, k, x  at level 1,
   right associativity, format "[^  o  map]  k \226\134\166 x  \226\136\136  m ,  P") : stdpp_scope.
Time
Notation "'[^' o 'map]' x \226\136\136 m , P" := (big_opM o (\206\187 _ x, P) m)
  (at level 200, o  at level 1, m  at level 10, x  at level 1,
   right associativity, format "[^ o  map]  x  \226\136\136  m ,  P") : stdpp_scope.
Time
Definition big_opS `{Monoid M o} `{Countable A} (f : A \226\134\146 M) 
  (X : gset A) : M := big_opL o (\206\187 _, f) (elements X).
Time Instance: (Params (@big_opS) 6) := { }.
Time Arguments big_opS {M} o {_} {A} {_} {_} _ _ : simpl never.
Time Typeclasses Opaque big_opS.
Time
Notation "'[^' o 'set]' x \226\136\136 X , P" := (big_opS o (\206\187 x, P) X)
  (at level 200, o  at level 1, X  at level 10, x  at level 1,
   right associativity, format "[^ o  set]  x  \226\136\136  X ,  P") : stdpp_scope.
Time
Definition big_opMS `{Monoid M o} `{Countable A} (f : A \226\134\146 M)
  (X : gmultiset A) : M := big_opL o (\206\187 _, f) (elements X).
Time Instance: (Params (@big_opMS) 7) := { }.
Time Arguments big_opMS {M} o {_} {A} {_} {_} _ _ : simpl never.
Time Typeclasses Opaque big_opMS.
Time
Notation "'[^' o 'mset]' x \226\136\136 X , P" := (big_opMS o (\206\187 x, P) X)
  (at level 200, o  at level 1, X  at level 10, x  at level 1,
   right associativity, format "[^ o  mset]  x  \226\136\136  X ,  P") : stdpp_scope.
Time Section big_op.
Time Context `{Monoid M o}.
Time Implicit Type xs : list M.
Time Infix "`o`" := o (at level 50, left associativity).
Time Section list.
Time Context {A : Type}.
Time Implicit Type l : list A.
Time Implicit Types f g : nat \226\134\146 A \226\134\146 M.
Time Lemma big_opL_nil f : ([^o list] k\226\134\166y \226\136\136 [], f k y) = monoid_unit.
Time Proof.
Time done.
Time Qed.
Time
Lemma big_opL_cons f x l :
  ([^o list] k\226\134\166y \226\136\136 (x :: l), f k y) =
  f 0 x `o` ([^o list] k\226\134\166y \226\136\136 l, f (S k) y).
Time Proof.
Time done.
Time Qed.
Time Lemma big_opL_singleton f x : ([^o list] k\226\134\166y \226\136\136 [x], f k y) \226\137\161 f 0 x.
Time Proof.
Time by rewrite /= right_id.
Time Qed.
Time
Lemma big_opL_app f l1 l2 :
  ([^o list] k\226\134\166y \226\136\136 (l1 ++ l2), f k y)
  \226\137\161 ([^o list] k\226\134\166y \226\136\136 l1, f k y) `o` ([^o list] k\226\134\166y \226\136\136 l2, f (length l1 + k) y).
Time Proof.
Time revert f.
Time
(<ssreflect_plugin::ssrtclseq@0> <ssreflect_plugin::ssrtclintros@0>
 induction l1 as [| x l1 IH] =>f /= ; first  by rewrite left_id).
Time by rewrite IH assoc.
Time Qed.
Time
Lemma big_opL_unit l : ([^o list] k\226\134\166y \226\136\136 l, monoid_unit) \226\137\161 (monoid_unit : M).
Time Proof.
Time (induction l; rewrite /= ?left_id //).
Time Qed.
Time
Lemma big_opL_forall R f g l :
  Reflexive R
  \226\134\146 Proper (R ==> R ==> R) o
    \226\134\146 (\226\136\128 k y, l !! k = Some y \226\134\146 R (f k y) (g k y))
      \226\134\146 R ([^o list] k\226\134\166y \226\136\136 l, f k y) ([^o list] k\226\134\166y \226\136\136 l, g k y).
Time Proof.
Time (intros ? ?).
Time revert f g.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>f g ? //=;
  f_equiv; eauto).
Time Qed.
Time
Lemma big_opL_ext f g l :
  (\226\136\128 k y, l !! k = Some y \226\134\146 f k y = g k y)
  \226\134\146 ([^o list] k\226\134\166y \226\136\136 l, f k y) = ([^o list] k\226\134\166y \226\136\136 l, g k y).
Time Proof.
Time (apply big_opL_forall; apply _).
Time Qed.
Time
Lemma big_opL_proper f g l :
  (\226\136\128 k y, l !! k = Some y \226\134\146 f k y \226\137\161 g k y)
  \226\134\146 ([^o list] k\226\134\166y \226\136\136 l, f k y) \226\137\161 ([^o list] k\226\134\166y \226\136\136 l, g k y).
Time Proof.
Time (apply big_opL_forall; apply _).
Time Qed.
Time
Lemma big_opL_permutation (f : A \226\134\146 M) l1 l2 :
  l1 \226\137\161\226\130\154 l2 \226\134\146 ([^o list] x \226\136\136 l1, f x) \226\137\161 ([^o list] x \226\136\136 l2, f x).
Time Proof.
Time (induction 1 as [| x xs1 xs2 ? IH| x y xs| xs1 xs2 xs3]; simpl; auto).
Time -
Time by rewrite IH.
Time -
Time by rewrite !assoc (comm _ (f x)).
Time -
Time by etrans.
Time Qed.
Time #[global]
Instance big_opL_permutation'  (f : A \226\134\146 M):
 (Proper ((\226\137\161\226\130\154) ==> (\226\137\161)) (big_opL o (\206\187 _, f))).
Time Proof.
Time (intros xs1 xs2).
Time (apply big_opL_permutation).
Time Qed.
Time #[global]
Instance big_opL_ne  n:
 (Proper
    (pointwise_relation _ (pointwise_relation _ (dist n)) ==> eq ==> dist n)
    (big_opL o (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time (apply big_opL_forall; apply _ || intros; apply Hf).
Time Qed.
Time #[global]
Instance big_opL_proper' :
 (Proper (pointwise_relation _ (pointwise_relation _ (\226\137\161)) ==> eq ==> (\226\137\161))
    (big_opL o (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time (apply big_opL_forall; apply _ || intros; apply Hf).
Time Qed.
Time
Lemma big_opL_consZ_l (f : Z \226\134\146 A \226\134\146 M) x l :
  ([^o list] k\226\134\166y \226\136\136 (x :: l), f k y) =
  f 0 x `o` ([^o list] k\226\134\166y \226\136\136 l, f (1 + k)%Z y).
Time Proof.
Time rewrite big_opL_cons.
Time auto using big_opL_ext with f_equal lia.
Time Qed.
Time
Lemma big_opL_consZ_r (f : Z \226\134\146 A \226\134\146 M) x l :
  ([^o list] k\226\134\166y \226\136\136 (x :: l), f k y) =
  f 0 x `o` ([^o list] k\226\134\166y \226\136\136 l, f (k + 1)%Z y).
Time Proof.
Time rewrite big_opL_cons.
Time auto using big_opL_ext with f_equal lia.
Time Qed.
Time
Lemma big_opL_fmap {B} (h : A \226\134\146 B) (f : nat \226\134\146 B \226\134\146 M) 
  l : ([^o list] k\226\134\166y \226\136\136 (h <$> l), f k y) \226\137\161 ([^o list] k\226\134\166y \226\136\136 l, f k (h y)).
Time Proof.
Time revert f.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>f;
  <ssreflect_plugin::ssrtclintros@0> csimpl =>//).
Time by rewrite IH.
Time Qed.
Time
Lemma big_opL_op f g l :
  ([^o list] k\226\134\166x \226\136\136 l, f k x `o` g k x)
  \226\137\161 ([^o list] k\226\134\166x \226\136\136 l, f k x) `o` ([^o list] k\226\134\166x \226\136\136 l, g k x).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 revert f g; <ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>f
  g /= ; first  by rewrite left_id).
Time by rewrite IH -!assoc (assoc _ (g _ _)) [g _ _ `o` _]comm -!assoc.
Time Qed.
Time End list.
Time
Lemma big_opL_bind {A} {B} (h : A \226\134\146 list B) (f : B \226\134\146 M) 
  l :
  ([^o list] y \226\136\136 (l \226\137\171= h), f y) \226\137\161 ([^o list] x \226\136\136 l, [^o list] y \226\136\136 h x, f y).
Time Proof.
Time revert f.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>f;
  <ssreflect_plugin::ssrtclintros@0> csimpl =>//).
Time by rewrite big_opL_app IH.
Time Qed.
Time Section gmap.
Time Context `{Countable K} {A : Type}.
Time Implicit Type m : gmap K A.
Time Implicit Types f g : K \226\134\146 A \226\134\146 M.
Time
Lemma big_opM_forall R f g m :
  Reflexive R
  \226\134\146 Proper (R ==> R ==> R) o
    \226\134\146 (\226\136\128 k x, m !! k = Some x \226\134\146 R (f k x) (g k x))
      \226\134\146 R ([^ o map] k\226\134\166x \226\136\136 m, f k x) ([^ o map] k\226\134\166x \226\136\136 m, g k x).
Time Proof.
Time (intros ? ? Hf).
Time (apply (big_opL_forall R); auto).
Time (intros k [i x] ?%elem_of_list_lookup_2).
Time by apply Hf, elem_of_map_to_list.
Time Qed.
Time
Lemma big_opM_ext f g m :
  (\226\136\128 k x, m !! k = Some x \226\134\146 f k x = g k x)
  \226\134\146 ([^ o map] k\226\134\166x \226\136\136 m, f k x) = ([^ o map] k\226\134\166x \226\136\136 m, g k x).
Time Proof.
Time (apply big_opM_forall; apply _).
Time Qed.
Time
Lemma big_opM_proper f g m :
  (\226\136\128 k x, m !! k = Some x \226\134\146 f k x \226\137\161 g k x)
  \226\134\146 ([^ o map] k\226\134\166x \226\136\136 m, f k x) \226\137\161 ([^ o map] k\226\134\166x \226\136\136 m, g k x).
Time Proof.
Time (apply big_opM_forall; apply _).
Time Qed.
Time #[global]
Instance big_opM_ne  n:
 (Proper
    (pointwise_relation _ (pointwise_relation _ (dist n)) ==> eq ==> dist n)
    (big_opM o (K:=K) (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time (apply big_opM_forall; apply _ || intros; apply Hf).
Time Qed.
Time #[global]
Instance big_opM_proper' :
 (Proper (pointwise_relation _ (pointwise_relation _ (\226\137\161)) ==> eq ==> (\226\137\161))
    (big_opM o (K:=K) (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time (apply big_opM_forall; apply _ || intros; apply Hf).
Time Qed.
Time Lemma big_opM_empty f : ([^ o map] k\226\134\166x \226\136\136 \226\136\133, f k x) = monoid_unit.
Time Proof.
Time by rewrite /big_opM map_to_list_empty.
Time Qed.
Time
Lemma big_opM_insert f m i x :
  m !! i = None
  \226\134\146 ([^ o map] k\226\134\166y \226\136\136 <[i:=x]> m, f k y)
    \226\137\161 f i x `o` ([^ o map] k\226\134\166y \226\136\136 m, f k y).
Time Proof.
Time (intros ?).
Time by rewrite /big_opM map_to_list_insert.
Time Qed.
Time
Lemma big_opM_delete f m i x :
  m !! i = Some x
  \226\134\146 ([^ o map] k\226\134\166y \226\136\136 m, f k y)
    \226\137\161 f i x `o` ([^ o map] k\226\134\166y \226\136\136 delete i m, f k y).
Time Proof.
Time (intros).
Time rewrite -big_opM_insert ?lookup_delete //.
Time by rewrite insert_delete insert_id.
Time Qed.
Time
Lemma big_opM_singleton f i x : ([^ o map] k\226\134\166y \226\136\136 {[i := x]}, f k y) \226\137\161 f i x.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite -insert_empty big_opM_insert /= ;
 last  auto using lookup_empty).
Time by rewrite big_opM_empty right_id.
Time Qed.
Time
Lemma big_opM_unit m : ([^ o map] k\226\134\166y \226\136\136 m, monoid_unit) \226\137\161 (monoid_unit : M).
Time Proof.
Time (induction m using map_ind; rewrite /= ?big_opM_insert ?left_id //).
Time Qed.
Time
Lemma big_opM_fmap {B} (h : A \226\134\146 B) (f : K \226\134\146 B \226\134\146 M) 
  m : ([^ o map] k\226\134\166y \226\136\136 (h <$> m), f k y) \226\137\161 ([^ o map] k\226\134\166y \226\136\136 m, f k (h y)).
Time Proof.
Time rewrite /big_opM map_to_list_fmap big_opL_fmap.
Time by <ssreflect_plugin::ssrtclintros@0> apply big_opL_proper =>? [? ?].
Time Qed.
Time
Lemma big_opM_insert_override (f : K \226\134\146 A \226\134\146 M) m i 
  x x' :
  m !! i = Some x
  \226\134\146 f i x \226\137\161 f i x'
    \226\134\146 ([^ o map] k\226\134\166y \226\136\136 <[i:=x']> m, f k y) \226\137\161 ([^ o map] k\226\134\166y \226\136\136 m, f k y).
Time Proof.
Time (intros ? Hx).
Time rewrite -insert_delete big_opM_insert ?lookup_delete //.
Time by rewrite -Hx -big_opM_delete.
Time Qed.
Time
Lemma big_opM_fn_insert {B} (g : K \226\134\146 A \226\134\146 B \226\134\146 M) (f : K \226\134\146 B) 
  m i (x : A) b :
  m !! i = None
  \226\134\146 ([^ o map] k\226\134\166y \226\136\136 <[i:=x]> m, g k y (<[i:=b]> f k))
    \226\137\161 g i x b `o` ([^ o map] k\226\134\166y \226\136\136 m, g k y (f k)).
Time Proof.
Time (intros).
Time rewrite big_opM_insert // fn_lookup_insert.
Time
(f_equiv; apply big_opM_proper; <ssreflect_plugin::ssrtclintros@0> auto =>k y
  ?).
Time
by <ssreflect_plugin::ssrtclseq@0> rewrite fn_lookup_insert_ne ; last 
 set_solver.
Time Qed.
Time
Lemma big_opM_fn_insert' (f : K \226\134\146 M) m i x P :
  m !! i = None
  \226\134\146 ([^ o map] k\226\134\166y \226\136\136 <[i:=x]> m, <[i:=P]> f k)
    \226\137\161 P `o` ([^ o map] k\226\134\166y \226\136\136 m, f k).
Time Proof.
Time (apply (big_opM_fn_insert (\206\187 _ _, id))).
Time Qed.
Time
Lemma big_opM_union f m1 m2 :
  m1 ##\226\130\152 m2
  \226\134\146 ([^ o map] k\226\134\166y \226\136\136 (m1 \226\136\170 m2), f k y)
    \226\137\161 ([^ o map] k\226\134\166y \226\136\136 m1, f k y) `o` ([^ o map] k\226\134\166y \226\136\136 m2, f k y).
Time Proof.
Time (intros).
Time (induction m1 as [| i x m ? IH] using map_ind).
Time {
Time by rewrite big_opM_empty !left_id.
Time }
Time decompose_map_disjoint.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite -insert_union_l !big_opM_insert // ;
 last  by apply lookup_union_None).
Time rewrite -assoc IH //.
Time Qed.
Time
Lemma big_opM_op f g m :
  ([^ o map] k\226\134\166x \226\136\136 m, f k x `o` g k x)
  \226\137\161 ([^ o map] k\226\134\166x \226\136\136 m, f k x) `o` ([^ o map] k\226\134\166x \226\136\136 m, g k x).
Time Proof.
Time rewrite /big_opM -big_opL_op.
Time by <ssreflect_plugin::ssrtclintros@0> apply big_opL_proper =>? [? ?].
Time Qed.
Time End gmap.
Time Section gset.
Time Context `{Countable A}.
Time Implicit Type X : gset A.
Time Implicit Type f : A \226\134\146 M.
Time
Lemma big_opS_forall R f g X :
  Reflexive R
  \226\134\146 Proper (R ==> R ==> R) o
    \226\134\146 (\226\136\128 x, x \226\136\136 X \226\134\146 R (f x) (g x))
      \226\134\146 R ([^o set] x \226\136\136 X, f x) ([^o set] x \226\136\136 X, g x).
Time Proof.
Time (intros ? ? Hf).
Time (apply (big_opL_forall R); auto).
Time (intros k x ?%elem_of_list_lookup_2).
Time by apply Hf, elem_of_elements.
Time Qed.
Time
Lemma big_opS_ext f g X :
  (\226\136\128 x, x \226\136\136 X \226\134\146 f x = g x) \226\134\146 ([^o set] x \226\136\136 X, f x) = ([^o set] x \226\136\136 X, g x).
Time Proof.
Time (apply big_opS_forall; apply _).
Time Qed.
Time
Lemma big_opS_proper f g X :
  (\226\136\128 x, x \226\136\136 X \226\134\146 f x \226\137\161 g x) \226\134\146 ([^o set] x \226\136\136 X, f x) \226\137\161 ([^o set] x \226\136\136 X, g x).
Time Proof.
Time (apply big_opS_forall; apply _).
Time Qed.
Time #[global]
Instance big_opS_ne  n:
 (Proper (pointwise_relation _ (dist n) ==> eq ==> dist n) (big_opS o (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time (apply big_opS_forall; apply _ || intros; apply Hf).
Time Qed.
Time #[global]
Instance big_opS_proper' :
 (Proper (pointwise_relation _ (\226\137\161) ==> eq ==> (\226\137\161)) (big_opS o (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time (apply big_opS_forall; apply _ || intros; apply Hf).
Time Qed.
Time Lemma big_opS_empty f : ([^o set] x \226\136\136 \226\136\133, f x) = monoid_unit.
Time Proof.
Time by rewrite /big_opS elements_empty.
Time Qed.
Time
Lemma big_opS_insert f X x :
  x \226\136\137 X \226\134\146 ([^o set] y \226\136\136 ({[x]} \226\136\170 X), f y) \226\137\161 f x `o` ([^o set] y \226\136\136 X, f y).
Time Proof.
Time (intros).
Time by rewrite /big_opS elements_union_singleton.
Time Qed.
Time
Lemma big_opS_fn_insert {B} (f : A \226\134\146 B \226\134\146 M) h X x 
  b :
  x \226\136\137 X
  \226\134\146 ([^o set] y \226\136\136 ({[x]} \226\136\170 X), f y (<[x:=b]> h y))
    \226\137\161 f x b `o` ([^o set] y \226\136\136 X, f y (h y)).
Time Proof.
Time (intros).
Time rewrite big_opS_insert // fn_lookup_insert.
Time
(f_equiv; apply big_opS_proper; <ssreflect_plugin::ssrtclintros@0> auto =>y ?).
Time
by <ssreflect_plugin::ssrtclseq@0> rewrite fn_lookup_insert_ne ; last 
 set_solver.
Time Qed.
Time
Lemma big_opS_fn_insert' f X x P :
  x \226\136\137 X
  \226\134\146 ([^o set] y \226\136\136 ({[x]} \226\136\170 X), <[x:=P]> f y) \226\137\161 P `o` ([^o set] y \226\136\136 X, f y).
Time Proof.
Time (apply (big_opS_fn_insert (\206\187 y, id))).
Time Qed.
Time
Lemma big_opS_union f X Y :
  X ## Y
  \226\134\146 ([^o set] y \226\136\136 (X \226\136\170 Y), f y)
    \226\137\161 ([^o set] y \226\136\136 X, f y) `o` ([^o set] y \226\136\136 Y, f y).
Time Proof.
Time (intros).
Time (induction X as [| x X ? IH] using set_ind_L).
Time {
Time by rewrite left_id_L big_opS_empty left_id.
Time }
Time (rewrite -assoc_L !big_opS_insert; [ idtac | set_solver.. ]).
Time by <ssreflect_plugin::ssrtclseq@0> rewrite -assoc IH ; last  set_solver.
Time Qed.
Time
Lemma big_opS_delete f X x :
  x \226\136\136 X \226\134\146 ([^o set] y \226\136\136 X, f y) \226\137\161 f x `o` ([^o set] y \226\136\136 (X \226\136\150 {[x]}), f y).
Time Proof.
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite -big_opS_insert ; last  set_solver).
Time
by <ssreflect_plugin::ssrtclseq@0> rewrite -union_difference_L ; last 
 set_solver.
Time Qed.
Time Lemma big_opS_singleton f x : ([^o set] y \226\136\136 {[x]}, f y) \226\137\161 f x.
Time Proof.
Time (intros).
Time by rewrite /big_opS elements_singleton /= right_id.
Time Qed.
Time
Lemma big_opS_unit X : ([^o set] y \226\136\136 X, monoid_unit) \226\137\161 (monoid_unit : M).
Time Proof.
Time (induction X using set_ind_L; rewrite /= ?big_opS_insert ?left_id //).
Time Qed.
Time
Lemma big_opS_op f g X :
  ([^o set] y \226\136\136 X, f y `o` g y)
  \226\137\161 ([^o set] y \226\136\136 X, f y) `o` ([^o set] y \226\136\136 X, g y).
Time Proof.
Time by rewrite /big_opS -big_opL_op.
Time Qed.
Time End gset.
Time
Lemma big_opM_dom `{Countable K} {A} (f : K \226\134\146 M) (m : gmap K A) :
  ([^ o map] k\226\134\166_ \226\136\136 m, f k) \226\137\161 ([^o set] k \226\136\136 dom _ m, f k).
Time Proof.
Time
(induction m as [| i x ? ? IH] using map_ind; [ by rewrite dom_empty_L |  ]).
Time
by rewrite dom_insert_L big_opM_insert // IH big_opS_insert ?not_elem_of_dom.
Time Qed.
Time Section gmultiset.
Time Context `{Countable A}.
Time Implicit Type X : gmultiset A.
Time Implicit Type f : A \226\134\146 M.
Time
Lemma big_opMS_forall R f g X :
  Reflexive R
  \226\134\146 Proper (R ==> R ==> R) o
    \226\134\146 (\226\136\128 x, x \226\136\136 X \226\134\146 R (f x) (g x))
      \226\134\146 R ([^o mset] x \226\136\136 X, f x) ([^o mset] x \226\136\136 X, g x).
Time Proof.
Time (intros ? ? Hf).
Time (apply (big_opL_forall R); auto).
Time (intros k x ?%elem_of_list_lookup_2).
Time by apply Hf, gmultiset_elem_of_elements.
Time Qed.
Time
Lemma big_opMS_ext f g X :
  (\226\136\128 x, x \226\136\136 X \226\134\146 f x = g x) \226\134\146 ([^o mset] x \226\136\136 X, f x) = ([^o mset] x \226\136\136 X, g x).
Time Proof.
Time (apply big_opMS_forall; apply _).
Time Qed.
Time
Lemma big_opMS_proper f g X :
  (\226\136\128 x, x \226\136\136 X \226\134\146 f x \226\137\161 g x) \226\134\146 ([^o mset] x \226\136\136 X, f x) \226\137\161 ([^o mset] x \226\136\136 X, g x).
Time Proof.
Time (apply big_opMS_forall; apply _).
Time Qed.
Time #[global]
Instance big_opMS_ne  n:
 (Proper (pointwise_relation _ (dist n) ==> eq ==> dist n)
    (big_opMS o (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time (apply big_opMS_forall; apply _ || intros; apply Hf).
Time Qed.
Time #[global]
Instance big_opMS_proper' :
 (Proper (pointwise_relation _ (\226\137\161) ==> eq ==> (\226\137\161)) (big_opMS o (A:=A))).
Time Proof.
Time (intros f g Hf m ? <-).
Time (apply big_opMS_forall; apply _ || intros; apply Hf).
Time Qed.
Time Lemma big_opMS_empty f : ([^o mset] x \226\136\136 \226\136\133, f x) = monoid_unit.
Time Proof.
Time by rewrite /big_opMS gmultiset_elements_empty.
Time Qed.
Time
Lemma big_opMS_disj_union f X Y :
  ([^o mset] y \226\136\136 (X \226\138\142 Y), f y)
  \226\137\161 ([^o mset] y \226\136\136 X, f y) `o` ([^o mset] y \226\136\136 Y, f y).
Time Proof.
Time by rewrite /big_opMS gmultiset_elements_disj_union big_opL_app.
Time Qed.
Time Lemma big_opMS_singleton f x : ([^o mset] y \226\136\136 {[x]}, f y) \226\137\161 f x.
Time Proof.
Time (intros).
Time by rewrite /big_opMS gmultiset_elements_singleton /= right_id.
Time Qed.
Time
Lemma big_opMS_delete f X x :
  x \226\136\136 X \226\134\146 ([^o mset] y \226\136\136 X, f y) \226\137\161 f x `o` ([^o mset] y \226\136\136 (X \226\136\150 {[x]}), f y).
Time Proof.
Time (intros).
Time rewrite -big_opMS_singleton -big_opMS_disj_union.
Time by rewrite -gmultiset_disj_union_difference'.
Time Qed.
Time
Lemma big_opMS_unit X : ([^o mset] y \226\136\136 X, monoid_unit) \226\137\161 (monoid_unit : M).
Time Proof.
Time
(induction X using gmultiset_ind; rewrite /= ?big_opMS_disj_union
  ?big_opMS_singleton ?left_id //).
Time Qed.
Time
Lemma big_opMS_op f g X :
  ([^o mset] y \226\136\136 X, f y `o` g y)
  \226\137\161 ([^o mset] y \226\136\136 X, f y) `o` ([^o mset] y \226\136\136 X, g y).
Time Proof.
Time by rewrite /big_opMS -big_opL_op.
Time Qed.
Time End gmultiset.
Time End big_op.
Time Section homomorphisms.
Time Context `{Monoid M1 o1} `{Monoid M2 o2}.
Time Infix "`o1`" := o1 (at level 50, left associativity).
Time Infix "`o2`" := o2 (at level 50, left associativity).
Time #[local]Instance: (\226\136\128 {A} (R : relation A), RewriteRelation R) := { }.
Time
Lemma big_opL_commute {A} (h : M1 \226\134\146 M2) `{!MonoidHomomorphism o1 o2 R h}
  (f : nat \226\134\146 A \226\134\146 M1) l :
  R (h ([^o1 list] k\226\134\166x \226\136\136 l, f k x)) ([^o2 list] k\226\134\166x \226\136\136 l, h (f k x)).
Time Proof.
Time revert f.
Time (<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>f /=).
Time -
Time (apply monoid_homomorphism_unit).
Time -
Time by rewrite monoid_homomorphism IH.
Time Qed.
Time
Lemma big_opL_commute1 {A} (h : M1 \226\134\146 M2) `{!WeakMonoidHomomorphism o1 o2 R h}
  (f : nat \226\134\146 A \226\134\146 M1) l :
  l \226\137\160 [] \226\134\146 R (h ([^o1 list] k\226\134\166x \226\136\136 l, f k x)) ([^o2 list] k\226\134\166x \226\136\136 l, h (f k x)).
Time Proof.
Time (intros ?).
Time revert f.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x [| x' l'] IH] =>f //).
Time -
Time by rewrite !big_opL_singleton.
Time -
Time by rewrite !(big_opL_cons _ x) monoid_homomorphism IH.
Time Qed.
Time
Lemma big_opM_commute `{Countable K} {A} (h : M1 \226\134\146 M2)
  `{!MonoidHomomorphism o1 o2 R h} (f : K \226\134\146 A \226\134\146 M1) 
  m : R (h ([^ o1 map] k\226\134\166x \226\136\136 m, f k x)) ([^ o2 map] k\226\134\166x \226\136\136 m, h (f k x)).
Time Proof.
Time (intros).
Time (induction m as [| i x m ? IH] using map_ind).
Time -
Time by rewrite !big_opM_empty monoid_homomorphism_unit.
Time -
Time by rewrite !big_opM_insert // monoid_homomorphism -IH.
Time Qed.
Time
Lemma big_opM_commute1 `{Countable K} {A} (h : M1 \226\134\146 M2)
  `{!WeakMonoidHomomorphism o1 o2 R h} (f : K \226\134\146 A \226\134\146 M1) 
  m :
  m \226\137\160 \226\136\133 \226\134\146 R (h ([^ o1 map] k\226\134\166x \226\136\136 m, f k x)) ([^ o2 map] k\226\134\166x \226\136\136 m, h (f k x)).
Time Proof.
Time (intros).
Time (induction m as [| i x m ? IH] using map_ind; [ done |  ]).
Time (destruct (decide (m = \226\136\133)) as [->| ]).
Time -
Time by rewrite !big_opM_insert // !big_opM_empty !right_id.
Time -
Time by rewrite !big_opM_insert // monoid_homomorphism -IH //.
Time Qed.
Time
Lemma big_opS_commute `{Countable A} (h : M1 \226\134\146 M2)
  `{!MonoidHomomorphism o1 o2 R h} (f : A \226\134\146 M1) X :
  R (h ([^o1 set] x \226\136\136 X, f x)) ([^o2 set] x \226\136\136 X, h (f x)).
Time Proof.
Time (intros).
Time (induction X as [| x X ? IH] using set_ind_L).
Time -
Time by rewrite !big_opS_empty monoid_homomorphism_unit.
Time -
Time by rewrite !big_opS_insert // monoid_homomorphism -IH.
Time Qed.
Time
Lemma big_opS_commute1 `{Countable A} (h : M1 \226\134\146 M2)
  `{!WeakMonoidHomomorphism o1 o2 R h} (f : A \226\134\146 M1) 
  X : X \226\137\160 \226\136\133 \226\134\146 R (h ([^o1 set] x \226\136\136 X, f x)) ([^o2 set] x \226\136\136 X, h (f x)).
Time Proof.
Time (intros).
Time (induction X as [| x X ? IH] using set_ind_L; [ done |  ]).
Time (destruct (decide (X = \226\136\133)) as [->| ]).
Time -
Time by rewrite !big_opS_insert // !big_opS_empty !right_id.
Time -
Time by rewrite !big_opS_insert // monoid_homomorphism -IH //.
Time Qed.
Time
Lemma big_opMS_commute `{Countable A} (h : M1 \226\134\146 M2)
  `{!MonoidHomomorphism o1 o2 R h} (f : A \226\134\146 M1) X :
  R (h ([^o1 mset] x \226\136\136 X, f x)) ([^o2 mset] x \226\136\136 X, h (f x)).
Time Proof.
Time (intros).
Time (induction X as [| x X IH] using gmultiset_ind).
Time -
Time by rewrite !big_opMS_empty monoid_homomorphism_unit.
Time -
Time
by rewrite !big_opMS_disj_union !big_opMS_singleton monoid_homomorphism -IH.
Time Qed.
Time
Lemma big_opMS_commute1 `{Countable A} (h : M1 \226\134\146 M2)
  `{!WeakMonoidHomomorphism o1 o2 R h} (f : A \226\134\146 M1) 
  X : X \226\137\160 \226\136\133 \226\134\146 R (h ([^o1 mset] x \226\136\136 X, f x)) ([^o2 mset] x \226\136\136 X, h (f x)).
Time Proof.
Time (intros).
Time (induction X as [| x X IH] using gmultiset_ind; [ done |  ]).
Time (destruct (decide (X = \226\136\133)) as [->| ]).
Time -
Time
by rewrite !big_opMS_disj_union !big_opMS_singleton !big_opMS_empty !right_id.
Time -
Time
by rewrite !big_opMS_disj_union !big_opMS_singleton monoid_homomorphism -IH
 //.
Time Qed.
Time Context `{!LeibnizEquiv M2}.
Time
Lemma big_opL_commute_L {A} (h : M1 \226\134\146 M2) `{!MonoidHomomorphism o1 o2 (\226\137\161) h}
  (f : nat \226\134\146 A \226\134\146 M1) l :
  h ([^o1 list] k\226\134\166x \226\136\136 l, f k x) = ([^o2 list] k\226\134\166x \226\136\136 l, h (f k x)).
Time Proof.
Time unfold_leibniz.
Time by apply big_opL_commute.
Time Qed.
Time
Lemma big_opL_commute1_L {A} (h : M1 \226\134\146 M2)
  `{!WeakMonoidHomomorphism o1 o2 (\226\137\161) h} (f : nat \226\134\146 A \226\134\146 M1) 
  l :
  l \226\137\160 [] \226\134\146 h ([^o1 list] k\226\134\166x \226\136\136 l, f k x) = ([^o2 list] k\226\134\166x \226\136\136 l, h (f k x)).
Time Proof.
Time unfold_leibniz.
Time by apply big_opL_commute1.
Time Qed.
Time
Lemma big_opM_commute_L `{Countable K} {A} (h : M1 \226\134\146 M2)
  `{!MonoidHomomorphism o1 o2 (\226\137\161) h} (f : K \226\134\146 A \226\134\146 M1) 
  m : h ([^ o1 map] k\226\134\166x \226\136\136 m, f k x) = ([^ o2 map] k\226\134\166x \226\136\136 m, h (f k x)).
Time Proof.
Time unfold_leibniz.
Time by apply big_opM_commute.
Time Qed.
Time
Lemma big_opM_commute1_L `{Countable K} {A} (h : M1 \226\134\146 M2)
  `{!WeakMonoidHomomorphism o1 o2 (\226\137\161) h} (f : K \226\134\146 A \226\134\146 M1) 
  m : m \226\137\160 \226\136\133 \226\134\146 h ([^ o1 map] k\226\134\166x \226\136\136 m, f k x) = ([^ o2 map] k\226\134\166x \226\136\136 m, h (f k x)).
Time Proof.
Time unfold_leibniz.
Time by apply big_opM_commute1.
Time Qed.
Time
Lemma big_opS_commute_L `{Countable A} (h : M1 \226\134\146 M2)
  `{!MonoidHomomorphism o1 o2 (\226\137\161) h} (f : A \226\134\146 M1) 
  X : h ([^o1 set] x \226\136\136 X, f x) = ([^o2 set] x \226\136\136 X, h (f x)).
Time Proof.
Time unfold_leibniz.
Time by apply big_opS_commute.
Time Qed.
Time
Lemma big_opS_commute1_L `{Countable A} (h : M1 \226\134\146 M2)
  `{!WeakMonoidHomomorphism o1 o2 (\226\137\161) h} (f : A \226\134\146 M1) 
  X : X \226\137\160 \226\136\133 \226\134\146 h ([^o1 set] x \226\136\136 X, f x) = ([^o2 set] x \226\136\136 X, h (f x)).
Time Proof.
Time (intros).
Time (rewrite <- leibniz_equiv_iff).
Time by apply big_opS_commute1.
Time Qed.
Time
Lemma big_opMS_commute_L `{Countable A} (h : M1 \226\134\146 M2)
  `{!MonoidHomomorphism o1 o2 (\226\137\161) h} (f : A \226\134\146 M1) 
  X : h ([^o1 mset] x \226\136\136 X, f x) = ([^o2 mset] x \226\136\136 X, h (f x)).
Time Proof.
Time unfold_leibniz.
Time by apply big_opMS_commute.
Time Qed.
Time
Lemma big_opMS_commute1_L `{Countable A} (h : M1 \226\134\146 M2)
  `{!WeakMonoidHomomorphism o1 o2 (\226\137\161) h} (f : A \226\134\146 M1) 
  X : X \226\137\160 \226\136\133 \226\134\146 h ([^o1 mset] x \226\136\136 X, f x) = ([^o2 mset] x \226\136\136 X, h (f x)).
Time Proof.
Time (intros).
Time (rewrite <- leibniz_equiv_iff).
Time by apply big_opMS_commute1.
Time Qed.
Time End homomorphisms.
