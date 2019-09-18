Time
From stdpp Require Export base tactics orders option vector numbers relations
  sets fin_sets listset list lexico.
Time From Coq Require Import Permutation.
Time From stdpp Require Export relations orders vector fin_sets.
Time Class FinMapToList K A M :=
         map_to_list : M \226\134\146 list (K * A).
Time Hint Mode FinMapToList ! - -: typeclass_instances.
Time Hint Mode FinMapToList - - !: typeclass_instances.
Time
Class FinMap K M `{FMap M} `{\226\136\128 A, Lookup K A (M A)} 
`{\226\136\128 A, Empty (M A)} `{\226\136\128 A, PartialAlter K A (M A)} 
`{OMap M} `{Merge M} `{\226\136\128 A, FinMapToList K A (M A)} 
`{EqDecision K} :={map_eq :
                    forall {A} (m1 m2 : M A),
                    (\226\136\128 i, m1 !! i = m2 !! i) \226\134\146 m1 = m2;
                   lookup_empty : forall {A} i, (\226\136\133 : M A) !! i = None;
                   lookup_partial_alter :
                    forall {A} f (m : M A) i,
                    partial_alter f i m !! i = f (m !! i);
                   lookup_partial_alter_ne :
                    forall {A} f (m : M A) i j,
                    i \226\137\160 j \226\134\146 partial_alter f i m !! j = m !! j;
                   lookup_fmap :
                    forall {A} {B} (f : A \226\134\146 B) (m : M A) i,
                    (f <$> m) !! i = f <$> m !! i;
                   NoDup_map_to_list :
                    forall {A} (m : M A), NoDup (map_to_list m);
                   elem_of_map_to_list :
                    forall {A} (m : M A) i x,
                    (i, x) \226\136\136 map_to_list m \226\134\148 m !! i = Some x;
                   lookup_omap :
                    forall {A} {B} (f : A \226\134\146 option B) (m : M A) i,
                    omap f m !! i = m !! i \226\137\171= f;
                   lookup_merge :
                    forall {A} {B} {C} (f : option A \226\134\146 option B \226\134\146 option C)
                      `{!DiagNone f} (m1 : M A) (m2 : M B) 
                      i, merge f m1 m2 !! i = f (m1 !! i) (m2 !! i)}.
Time
Instance map_insert  `{PartialAlter K A M}: (Insert K A M) :=
 (\206\187 i x, partial_alter (\206\187 _, Some x) i).
Time
Instance map_alter  `{PartialAlter K A M}: (Alter K A M) :=
 (\206\187 f, partial_alter (fmap f)).
Time
Instance map_delete  `{PartialAlter K A M}: (Delete K M) :=
 (partial_alter (\206\187 _, None)).
Time
Instance map_singleton  `{PartialAlter K A M} `{Empty M}: 
 (SingletonM K A M) := (\206\187 i x, <[i:=x]> \226\136\133).
Time
Definition list_to_map `{Insert K A M} `{Empty M} : 
  list (K * A) \226\134\146 M := fold_right (\206\187 p, <[p.1:=p.2]>) \226\136\133.
Time
Instance map_size  `{FinMapToList K A M}: (Size M) :=
 (\206\187 m, length (map_to_list m)).
Time
Definition map_to_set `{FinMapToList K A M} `{Singleton B C} 
  `{Empty C} `{Union C} (f : K \226\134\146 A \226\134\146 B) (m : M) : C :=
  list_to_set (curry f <$> map_to_list m).
Time
Definition set_to_map `{Elements B C} `{Insert K A M} 
  `{Empty M} (f : B \226\134\146 K * A) (X : C) : M := list_to_map (f <$> elements X).
Time
Instance map_union_with  `{Merge M} {A}: (UnionWith A (M A)) :=
 (\206\187 f, merge (union_with f)).
Time
Instance map_intersection_with  `{Merge M} {A}: (IntersectionWith A (M A)) :=
 (\206\187 f, merge (intersection_with f)).
Time
Instance map_difference_with  `{Merge M} {A}: (DifferenceWith A (M A)) :=
 (\206\187 f, merge (difference_with f)).
Time
Instance map_equiv  `{\226\136\128 A, Lookup K A (M A)} `{Equiv A}: 
 (Equiv (M A)) |20 := (\206\187 m1 m2, \226\136\128 i, m1 !! i \226\137\161 m2 !! i).
Time
Definition map_Forall `{Lookup K A M} (P : K \226\134\146 A \226\134\146 Prop) : 
  M \226\134\146 Prop := \206\187 m, \226\136\128 i x, m !! i = Some x \226\134\146 P i x.
Time
Definition map_relation `{\226\136\128 A, Lookup K A (M A)} {A} 
  {B} (R : A \226\134\146 B \226\134\146 Prop) (P : A \226\134\146 Prop) (Q : B \226\134\146 Prop) 
  (m1 : M A) (m2 : M B) : Prop :=
  \226\136\128 i, option_relation R P Q (m1 !! i) (m2 !! i).
Time
Definition map_included `{\226\136\128 A, Lookup K A (M A)} {A} 
  (R : relation A) : relation (M A) :=
  map_relation R (\206\187 _, False) (\206\187 _, True).
Time
Definition map_disjoint `{\226\136\128 A, Lookup K A (M A)} {A} : 
  relation (M A) := map_relation (\206\187 _ _, False) (\206\187 _, True) (\206\187 _, True).
Time Infix "##\226\130\152" := map_disjoint (at level 70) : stdpp_scope.
Time Hint Extern 0 (_ ##\226\130\152 _) => (symmetry; eassumption): core.
Time Notation "( m ##\226\130\152.)" := (map_disjoint m) (only parsing) : stdpp_scope.
Time Notation "(.##\226\130\152 m )" := (\206\187 m2, m2 ##\226\130\152 m) (only parsing) : stdpp_scope.
Time
Instance map_subseteq  `{\226\136\128 A, Lookup K A (M A)} {A}: 
 (SubsetEq (M A)) := (map_included (=)).
Time
Instance map_union  `{Merge M} {A}: (Union (M A)) :=
 (union_with (\206\187 x _, Some x)).
Time
Instance map_intersection  `{Merge M} {A}: (Intersection (M A)) :=
 (intersection_with (\206\187 x _, Some x)).
Time
Instance map_difference  `{Merge M} {A}: (Difference (M A)) :=
 (difference_with (\206\187 _ _, None)).
Time
Definition map_imap `{\226\136\128 A, Insert K A (M A)} `{\226\136\128 A, Empty (M A)}
  `{\226\136\128 A, FinMapToList K A (M A)} {A} {B} (f : K \226\134\146 A \226\134\146 option B) 
  (m : M A) : M B :=
  list_to_map (omap (\206\187 ix, (fst ix,) <$> curry f ix) (map_to_list m)).
Time
Definition map_zip_with `{Merge M} {A} {B} {C} (f : A \226\134\146 B \226\134\146 C) :
  M A \226\134\146 M B \226\134\146 M C :=
  merge
    (\206\187 mx my,
       match mx, my with
       | Some x, Some y => Some (f x y)
       | _, _ => None
       end).
Time Notation map_zip := (map_zip_with pair).
Time
Definition map_fold `{FinMapToList K A M} {B} (f : K \226\134\146 A \226\134\146 B \226\134\146 B) 
  (b : B) : M \226\134\146 B := foldr (curry f) b \226\136\152 map_to_list.
Time
Instance map_filter  `{FinMapToList K A M} `{Insert K A M} 
 `{Empty M}: (Filter (K * A) M) :=
 (\206\187 P _, map_fold (\206\187 k v m, if decide (P (k, v)) then <[k:=v]> m else m) \226\136\133).
Time
Fixpoint map_seq `{Insert nat A M} `{Empty M} (start : nat) 
(xs : list A) : M :=
  match xs with
  | [] => \226\136\133
  | x :: xs => <[start:=x]> (map_seq (S start) xs)
  end.
Time Section theorems.
Time Context `{FinMap K M}.
Time Section setoid.
Time Context `{Equiv A}.
Time
Lemma map_equiv_lookup_l (m1 m2 : M A) i x :
  m1 \226\137\161 m2 \226\134\146 m1 !! i = Some x \226\134\146 \226\136\131 y, m2 !! i = Some y \226\136\167 x \226\137\161 y.
Time Proof.
Time (generalize (equiv_Some_inv_l (m1 !! i) (m2 !! i) x); naive_solver).
Time Qed.
Time #[global]
Instance map_equivalence : (Equivalence (\226\137\161@{A} ) \226\134\146 Equivalence (\226\137\161@{M A} )).
Time Proof.
Time split.
Time -
Time by intros m i.
Time -
Time by intros m1 m2 ? i.
Time -
Time by intros m1 m2 m3 ? ? i; trans m2 !! i.
Time Qed.
Time #[global]
Instance lookup_proper  (i : K): (Proper ((\226\137\161@{M A} ) ==> (\226\137\161)) (lookup i)).
Time Proof.
Time by intros m1 m2 Hm.
Time Qed.
Time #[global]
Instance partial_alter_proper :
 (Proper (((\226\137\161) ==> (\226\137\161)) ==> (=) ==> (\226\137\161) ==> (\226\137\161@{M A} )) partial_alter).
Time Proof.
Time
by
 intros f1 f2 Hf i ? <- m1 m2 Hm j; destruct (decide (i = j)) as [->| ];
  rewrite ?lookup_partial_alter, ?lookup_partial_alter_ne by done;
  try apply Hf; apply lookup_proper.
Time Qed.
Time #[global]
Instance insert_proper  (i : K):
 (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161@{M A} )) (insert i)).
Time Proof.
Time by intros ? ? ?; apply partial_alter_proper; [ constructor |  ].
Time Qed.
Time #[global]
Instance singleton_proper  k: (Proper ((\226\137\161) ==> (\226\137\161@{M A} )) (singletonM k)).
Time Proof.
Time (intros ? ? ?; apply insert_proper; [ done |  ]).
Time (intros ?).
Time (rewrite lookup_empty; constructor).
Time Qed.
Time #[global]
Instance delete_proper  (i : K): (Proper ((\226\137\161) ==> (\226\137\161@{M A} )) (delete i)).
Time Proof.
Time by apply partial_alter_proper; [ constructor |  ].
Time Qed.
Time #[global]
Instance alter_proper :
 (Proper (((\226\137\161) ==> (\226\137\161)) ==> (=) ==> (\226\137\161) ==> (\226\137\161@{M A} )) alter).
Time Proof.
Time (intros ? ? Hf; apply partial_alter_proper).
Time by destruct 1; constructor; apply Hf.
Time Qed.
Time
Lemma merge_ext `{Equiv B} `{Equiv C} (f g : option A \226\134\146 option B \226\134\146 option C)
  `{!DiagNone f} `{!DiagNone g} :
  ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161))%signature f g
  \226\134\146 ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161@{M _} ))%signature (merge f) (merge g).
Time Proof.
Time by intros Hf ? ? Hm1 ? ? Hm2 i; rewrite !lookup_merge by done; apply Hf.
Time Qed.
Time #[global]
Instance union_with_proper :
 (Proper (((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) ==> (\226\137\161) ==> (\226\137\161) ==> (\226\137\161@{M A} )) union_with).
Time Proof.
Time (intros ? ? Hf ? ? Hm1 ? ? Hm2 i; apply (merge_ext _ _); auto).
Time by do 2 destruct 1; (first [ apply Hf | constructor ]).
Time Qed.
Time #[global]Instance map_leibniz  `{!LeibnizEquiv A}: (LeibnizEquiv (M A)).
Time Proof.
Time (intros m1 m2 Hm; apply map_eq; intros i).
Time (apply leibniz_equiv, Hm).
Time Qed.
Time Lemma map_equiv_empty (m : M A) : m \226\137\161 \226\136\133 \226\134\148 m = \226\136\133.
Time Proof.
Time (split; [ intros Hm; apply map_eq; intros i | intros -> ]).
Time -
Time (generalize (Hm i)).
Time by rewrite lookup_empty, equiv_None.
Time -
Time (intros ?).
Time (rewrite lookup_empty; constructor).
Time Qed.
Time #[global]
Instance map_fmap_proper  `{Equiv B} (f : A \226\134\146 B):
 (Proper ((\226\137\161) ==> (\226\137\161)) f \226\134\146 Proper ((\226\137\161) ==> (\226\137\161@{M _} )) (fmap f)).
Time Proof.
Time (intros ? m m' ? k; rewrite !lookup_fmap).
Time by apply option_fmap_proper.
Time Qed.
Time End setoid.
Time Lemma map_eq_iff {A} (m1 m2 : M A) : m1 = m2 \226\134\148 (\226\136\128 i, m1 !! i = m2 !! i).
Time Proof.
Time split.
Time by intros ->.
Time (apply map_eq).
Time Qed.
Time
Lemma map_subseteq_spec {A} (m1 m2 : M A) :
  m1 \226\138\134 m2 \226\134\148 (\226\136\128 i x, m1 !! i = Some x \226\134\146 m2 !! i = Some x).
Time Proof.
Time (unfold subseteq, map_subseteq, map_relation).
Time
(split; intros Hm i; specialize (Hm i); destruct (m1 !! i), (m2 !! i);
  naive_solver).
Time Qed.
Time #[global]
Instance map_included_preorder  {A} (R : relation A):
 (PreOrder R \226\134\146 PreOrder (map_included R : relation (M A))).
Time Proof.
Time (split; [ intros m i; by destruct (m !! i); simpl |  ]).
Time (intros m1 m2 m3 Hm12 Hm23 i; specialize (Hm12 i); specialize (Hm23 i)).
Time
(destruct (m1 !! i), (m2 !! i), (m3 !! i); simplify_eq /=; done || etrans;
  eauto).
Time Qed.
Time #[global]Instance map_subseteq_po : (PartialOrder (\226\138\134@{M A} )).
Time Proof.
Time (split; [ apply _ |  ]).
Time (intros m1 m2; rewrite !map_subseteq_spec).
Time (intros; apply map_eq; intros i; apply option_eq; naive_solver).
Time Qed.
Time
Lemma lookup_weaken {A} (m1 m2 : M A) i x :
  m1 !! i = Some x \226\134\146 m1 \226\138\134 m2 \226\134\146 m2 !! i = Some x.
Time Proof.
Time (rewrite !map_subseteq_spec).
Time auto.
Time Qed.
Time
Lemma lookup_weaken_is_Some {A} (m1 m2 : M A) i :
  is_Some (m1 !! i) \226\134\146 m1 \226\138\134 m2 \226\134\146 is_Some (m2 !! i).
Time Proof.
Time (inversion 1).
Time eauto using lookup_weaken.
Time Qed.
Time
Lemma lookup_weaken_None {A} (m1 m2 : M A) i :
  m2 !! i = None \226\134\146 m1 \226\138\134 m2 \226\134\146 m1 !! i = None.
Time Proof.
Time (rewrite map_subseteq_spec, !eq_None_not_Some).
Time (intros Hm2 Hm [? ?]; destruct Hm2; eauto).
Time Qed.
Time
Lemma lookup_weaken_inv {A} (m1 m2 : M A) i x y :
  m1 !! i = Some x \226\134\146 m1 \226\138\134 m2 \226\134\146 m2 !! i = Some y \226\134\146 x = y.
Time Proof.
Time (intros Hm1 ? Hm2).
Time (eapply lookup_weaken in Hm1; eauto).
Time congruence.
Time Qed.
Time Lemma lookup_ne {A} (m : M A) i j : m !! i \226\137\160 m !! j \226\134\146 i \226\137\160 j.
Time Proof.
Time congruence.
Time Qed.
Time Lemma map_empty {A} (m : M A) : (\226\136\128 i, m !! i = None) \226\134\146 m = \226\136\133.
Time Proof.
Time (intros Hm).
Time (apply map_eq).
Time (intros).
Time by rewrite Hm, lookup_empty.
Time Qed.
Time Lemma lookup_empty_is_Some {A} i : \194\172 is_Some ((\226\136\133 : M A) !! i).
Time Proof.
Time (rewrite lookup_empty).
Time by inversion 1.
Time Qed.
Time Lemma lookup_empty_Some {A} i (x : A) : \194\172 (\226\136\133 : M A) !! i = Some x.
Time Proof.
Time by rewrite lookup_empty.
Time Qed.
Time Lemma map_subset_empty {A} (m : M A) : m \226\138\132 \226\136\133.
Time Proof.
Time (intros [_ []]).
Time (rewrite map_subseteq_spec).
Time (intros ? ?).
Time by rewrite lookup_empty.
Time Qed.
Time Lemma map_fmap_empty {A} {B} (f : A \226\134\146 B) : f <$> (\226\136\133 : M A) = \226\136\133.
Time Proof.
Time by apply map_eq; intros i; rewrite lookup_fmap, !lookup_empty.
Time Qed.
Time Lemma map_fmap_empty_inv {A} {B} (f : A \226\134\146 B) m : f <$> m = \226\136\133 \226\134\146 m = \226\136\133.
Time Proof.
Time (intros Hm).
Time (apply map_eq; intros i).
Time (generalize (f_equal (lookup i) Hm)).
Time by rewrite lookup_fmap, !lookup_empty, fmap_None.
Time Qed.
Time
Lemma map_subset_alt {A} (m1 m2 : M A) :
  m1 \226\138\130 m2 \226\134\148 m1 \226\138\134 m2 \226\136\167 (\226\136\131 i, m1 !! i = None \226\136\167 is_Some (m2 !! i)).
Time Proof.
Time (rewrite strict_spec_alt).
Time split.
Time -
Time (intros [? Heq]; split; [ done |  ]).
Time
(destruct (decide (Exists (\206\187 ix, m1 !! ix.1 = None) (map_to_list m2)))
  as
   [[[i x] [?%elem_of_map_to_list ?]]%Exists_exists| Hm%(not_Exists_Forall _)];
  [ eauto |  ]).
Time
(destruct Heq; apply (anti_symm _), map_subseteq_spec;
  [ done | intros i x Hi ]).
Time (assert (is_Some (m1 !! i)) as [x' ?]).
Time {
Time
by
 apply not_eq_None_Some, (proj1 (Forall_forall _ _) Hm (i, x)),
  elem_of_map_to_list.
Time }
Time by rewrite <- (lookup_weaken_inv m1 m2 i x' x).
Time -
Time (intros [? (i, (?, (x, ?)))]; split; [ done |  ]).
Time congruence.
Time Qed.
Time
Lemma partial_alter_ext {A} (f g : option A \226\134\146 option A) 
  (m : M A) i :
  (\226\136\128 x, m !! i = x \226\134\146 f x = g x) \226\134\146 partial_alter f i m = partial_alter g i m.
Time Proof.
Time (intros).
Time (apply map_eq; intros j).
Time
by
 destruct (decide (i = j)) as [->| ?];
  rewrite ?lookup_partial_alter, ?lookup_partial_alter_ne; auto.
Time Qed.
Time
Lemma partial_alter_compose {A} f g (m : M A) i :
  partial_alter (f \226\136\152 g) i m = partial_alter f i (partial_alter g i m).
Time Proof.
Time (intros).
Time (apply map_eq).
Time (intros ii).
Time
by
 destruct (decide (i = ii)) as [->| ?];
  rewrite ?lookup_partial_alter, ?lookup_partial_alter_ne.
Time Qed.
Time
Lemma partial_alter_commute {A} f g (m : M A) i j :
  i \226\137\160 j
  \226\134\146 partial_alter f i (partial_alter g j m) =
    partial_alter g j (partial_alter f i m).
Time Proof.
Time (intros).
Time (apply map_eq; intros jj).
Time (destruct (decide (jj = j)) as [->| ?]).
Time {
Time
by
 rewrite lookup_partial_alter_ne, !lookup_partial_alter,
  lookup_partial_alter_ne.
Time }
Time (destruct (decide (jj = i)) as [->| ?]).
Time -
Time
by
 rewrite lookup_partial_alter, !lookup_partial_alter_ne, lookup_partial_alter
  by congruence.
Time -
Time by rewrite !lookup_partial_alter_ne by congruence.
Time Qed.
Time
Lemma partial_alter_self_alt {A} (m : M A) i x :
  x = m !! i \226\134\146 partial_alter (\206\187 _, x) i m = m.
Time Proof.
Time (intros).
Time (apply map_eq).
Time (intros ii).
Time
by
 destruct (decide (i = ii)) as [->| ];
  rewrite ?lookup_partial_alter, ?lookup_partial_alter_ne.
Time Qed.
Time
Lemma partial_alter_self {A} (m : M A) i :
  partial_alter (\206\187 _, m !! i) i m = m.
Time Proof.
Time by apply partial_alter_self_alt.
Time Qed.
Time
Lemma partial_alter_subseteq {A} f (m : M A) i :
  m !! i = None \226\134\146 m \226\138\134 partial_alter f i m.
Time Proof.
Time (rewrite map_subseteq_spec).
Time (intros Hi j x Hj).
Time (rewrite lookup_partial_alter_ne; congruence).
Time Qed.
Time
Lemma partial_alter_subset {A} f (m : M A) i :
  m !! i = None \226\134\146 is_Some (f (m !! i)) \226\134\146 m \226\138\130 partial_alter f i m.
Time Proof.
Time (intros Hi Hfi).
Time (apply map_subset_alt; split; [ by apply partial_alter_subseteq |  ]).
Time exists i.
Time by rewrite lookup_partial_alter.
Time Qed.
Time
Lemma lookup_alter {A} (f : A \226\134\146 A) (m : M A) i :
  alter f i m !! i = f <$> m !! i.
Time Proof.
Time (unfold alter).
Time (apply lookup_partial_alter).
Time Qed.
Time
Lemma lookup_alter_ne {A} (f : A \226\134\146 A) (m : M A) i 
  j : i \226\137\160 j \226\134\146 alter f i m !! j = m !! j.
Time Proof.
Time (unfold alter).
Time (apply lookup_partial_alter_ne).
Time Qed.
Time
Lemma alter_ext {A} (f g : A \226\134\146 A) (m : M A) i :
  (\226\136\128 x, m !! i = Some x \226\134\146 f x = g x) \226\134\146 alter f i m = alter g i m.
Time Proof.
Time intro.
Time (apply partial_alter_ext).
Time (intros [x| ] ?; f_equal /=; auto).
Time Qed.
Time
Lemma alter_compose {A} (f g : A \226\134\146 A) (m : M A) i :
  alter (f \226\136\152 g) i m = alter f i (alter g i m).
Time Proof.
Time (unfold alter, map_alter).
Time (rewrite <- partial_alter_compose).
Time (apply partial_alter_ext).
Time by intros [?| ].
Time Qed.
Time
Lemma alter_commute {A} (f g : A \226\134\146 A) (m : M A) i 
  j : i \226\137\160 j \226\134\146 alter f i (alter g j m) = alter g j (alter f i m).
Time Proof.
Time (apply partial_alter_commute).
Time Qed.
Time
Lemma lookup_alter_Some {A} (f : A \226\134\146 A) (m : M A) 
  i j y :
  alter f i m !! j = Some y
  \226\134\148 i = j \226\136\167 (\226\136\131 x, m !! j = Some x \226\136\167 y = f x) \226\136\168 i \226\137\160 j \226\136\167 m !! j = Some y.
Time Proof.
Time (destruct (decide (i = j)) as [->| ?]).
Time -
Time (rewrite lookup_alter).
Time naive_solver simplify_option_eq; eauto.
Time -
Time (rewrite lookup_alter_ne by done).
Time naive_solver.
Time Qed.
Time
Lemma lookup_alter_None {A} (f : A \226\134\146 A) (m : M A) 
  i j : alter f i m !! j = None \226\134\148 m !! j = None.
Time Proof.
Time
by
 destruct (decide (i = j)) as [->| ?];
  rewrite ?lookup_alter, ?fmap_None, ?lookup_alter_ne.
Time Qed.
Time
Lemma lookup_alter_is_Some {A} (f : A \226\134\146 A) (m : M A) 
  i j : is_Some (alter f i m !! j) \226\134\148 is_Some (m !! j).
Time Proof.
Time by rewrite <- !not_eq_None_Some, lookup_alter_None.
Time Qed.
Time
Lemma alter_id {A} (f : A \226\134\146 A) (m : M A) i :
  (\226\136\128 x, m !! i = Some x \226\134\146 f x = x) \226\134\146 alter f i m = m.
Time Proof.
Time
(intros Hi; apply map_eq; intros j; destruct (decide (i = j)) as [->| ?]).
Time {
Time (rewrite lookup_alter; destruct (m !! j); f_equal /=; auto).
Time }
Time by rewrite lookup_alter_ne by done.
Time Qed.
Time
Lemma alter_mono {A} f (m1 m2 : M A) i :
  m1 \226\138\134 m2 \226\134\146 alter f i m1 \226\138\134 alter f i m2.
Time Proof.
Time (rewrite !map_subseteq_spec).
Time (intros ? j x).
Time (rewrite !lookup_alter_Some).
Time naive_solver.
Time Qed.
Time
Lemma alter_strict_mono {A} f (m1 m2 : M A) i :
  m1 \226\138\130 m2 \226\134\146 alter f i m1 \226\138\130 alter f i m2.
Time Proof.
Time (rewrite !map_subset_alt).
Time (intros [? (j, (?, ?))]; split; auto using alter_mono).
Time exists j.
Time by rewrite lookup_alter_None, lookup_alter_is_Some.
Time Qed.
Time Lemma lookup_delete {A} (m : M A) i : delete i m !! i = None.
Time Proof.
Time (apply lookup_partial_alter).
Time Qed.
Time
Lemma lookup_delete_ne {A} (m : M A) i j : i \226\137\160 j \226\134\146 delete i m !! j = m !! j.
Time Proof.
Time (apply lookup_partial_alter_ne).
Time Qed.
Time
Lemma lookup_delete_Some {A} (m : M A) i j y :
  delete i m !! j = Some y \226\134\148 i \226\137\160 j \226\136\167 m !! j = Some y.
Time Proof.
Time split.
Time -
Time
(destruct (decide (i = j)) as [->| ?];
  rewrite ?lookup_delete, ?lookup_delete_ne; intuition congruence).
Time -
Time (intros [? ?]).
Time by rewrite lookup_delete_ne.
Time Qed.
Time
Lemma lookup_delete_is_Some {A} (m : M A) i j :
  is_Some (delete i m !! j) \226\134\148 i \226\137\160 j \226\136\167 is_Some (m !! j).
Time Proof.
Time (unfold is_Some; setoid_rewrite lookup_delete_Some; naive_solver).
Time Qed.
Time
Lemma lookup_delete_None {A} (m : M A) i j :
  delete i m !! j = None \226\134\148 i = j \226\136\168 m !! j = None.
Time Proof.
Time
(destruct (decide (i = j)) as [->| ?];
  rewrite ?lookup_delete, ?lookup_delete_ne; tauto).
Time Qed.
Time Lemma delete_empty {A} i : delete i (\226\136\133 : M A) = \226\136\133.
Time Proof.
Time (rewrite <- (partial_alter_self \226\136\133)  at 2).
Time by rewrite lookup_empty.
Time Qed.
Time
Lemma delete_commute {A} (m : M A) i j :
  delete i (delete j m) = delete j (delete i m).
Time Proof.
Time (destruct (decide (i = j))).
Time by subst.
Time by apply partial_alter_commute.
Time Qed.
Time
Lemma delete_insert_ne {A} (m : M A) i j x :
  i \226\137\160 j \226\134\146 delete i (<[j:=x]> m) = <[j:=x]> (delete i m).
Time Proof.
Time intro.
Time by apply partial_alter_commute.
Time Qed.
Time Lemma delete_notin {A} (m : M A) i : m !! i = None \226\134\146 delete i m = m.
Time Proof.
Time (intros).
Time (apply map_eq).
Time (intros j).
Time
by
 destruct (decide (i = j)) as [->| ?];
  rewrite ?lookup_delete, ?lookup_delete_ne.
Time Qed.
Time Lemma delete_idemp {A} (m : M A) i : delete i (delete i m) = delete i m.
Time Proof.
Time by setoid_rewrite  <- partial_alter_compose.
Time Qed.
Time
Lemma delete_partial_alter {A} (m : M A) i f :
  m !! i = None \226\134\146 delete i (partial_alter f i m) = m.
Time Proof.
Time (intros).
Time (unfold delete, map_delete).
Time (rewrite <- partial_alter_compose).
Time (unfold compose).
Time by apply partial_alter_self_alt.
Time Qed.
Time
Lemma delete_insert {A} (m : M A) i x :
  m !! i = None \226\134\146 delete i (<[i:=x]> m) = m.
Time Proof.
Time (apply delete_partial_alter).
Time Qed.
Time
Lemma delete_insert_delete {A} (m : M A) i x :
  delete i (<[i:=x]> m) = delete i m.
Time Proof.
Time by setoid_rewrite  <- partial_alter_compose.
Time Qed.
Time
Lemma insert_delete {A} (m : M A) i x : <[i:=x]> (delete i m) = <[i:=x]> m.
Time Proof.
Time (symmetry; apply (partial_alter_compose (\206\187 _, Some x))).
Time Qed.
Time Lemma delete_subseteq {A} (m : M A) i : delete i m \226\138\134 m.
Time Proof.
Time (rewrite !map_subseteq_spec).
Time (intros j x).
Time (rewrite lookup_delete_Some).
Time tauto.
Time Qed.
Time Lemma delete_subset {A} (m : M A) i : is_Some (m !! i) \226\134\146 delete i m \226\138\130 m.
Time Proof.
Time
(intros [x ?]; apply map_subset_alt; split; [ apply delete_subseteq |  ]).
Time exists i.
Time (rewrite lookup_delete; eauto).
Time Qed.
Time
Lemma delete_mono {A} (m1 m2 : M A) i : m1 \226\138\134 m2 \226\134\146 delete i m1 \226\138\134 delete i m2.
Time Proof.
Time (rewrite !map_subseteq_spec).
Time (intros ? j x).
Time (rewrite !lookup_delete_Some).
Time intuition eauto.
Time Qed.
Time Lemma lookup_insert {A} (m : M A) i x : <[i:=x]> m !! i = Some x.
Time Proof.
Time (unfold insert).
Time (apply lookup_partial_alter).
Time Qed.
Time
Lemma lookup_insert_rev {A} (m : M A) i x y :
  <[i:=x]> m !! i = Some y \226\134\146 x = y.
Time Proof.
Time (rewrite lookup_insert).
Time congruence.
Time Qed.
Time
Lemma lookup_insert_ne {A} (m : M A) i j x : i \226\137\160 j \226\134\146 <[i:=x]> m !! j = m !! j.
Time Proof.
Time (unfold insert).
Time (apply lookup_partial_alter_ne).
Time Qed.
Time
Lemma insert_insert {A} (m : M A) i x y : <[i:=x]> (<[i:=y]> m) = <[i:=x]> m.
Time Proof.
Time (unfold insert, map_insert).
Time by rewrite <- partial_alter_compose.
Time Qed.
Time
Lemma insert_commute {A} (m : M A) i j x y :
  i \226\137\160 j \226\134\146 <[i:=x]> (<[j:=y]> m) = <[j:=y]> (<[i:=x]> m).
Time Proof.
Time (apply partial_alter_commute).
Time Qed.
Time
Lemma lookup_insert_Some {A} (m : M A) i j x y :
  <[i:=x]> m !! j = Some y \226\134\148 i = j \226\136\167 x = y \226\136\168 i \226\137\160 j \226\136\167 m !! j = Some y.
Time Proof.
Time split.
Time -
Time
(destruct (decide (i = j)) as [->| ?];
  rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence).
Time -
Time (intros [[-> ->]| [? ?]]; [ apply lookup_insert |  ]).
Time by rewrite lookup_insert_ne.
Time Qed.
Time
Lemma lookup_insert_is_Some {A} (m : M A) i j x :
  is_Some (<[i:=x]> m !! j) \226\134\148 i = j \226\136\168 i \226\137\160 j \226\136\167 is_Some (m !! j).
Time Proof.
Time (unfold is_Some; setoid_rewrite lookup_insert_Some; naive_solver).
Time Qed.
Time
Lemma lookup_insert_is_Some' {A} (m : M A) i j x :
  is_Some (<[i:=x]> m !! j) \226\134\148 i = j \226\136\168 is_Some (m !! j).
Time Proof.
Time (rewrite lookup_insert_is_Some).
Time (destruct (decide (i = j)); naive_solver).
Time Qed.
Time
Lemma lookup_insert_None {A} (m : M A) i j x :
  <[i:=x]> m !! j = None \226\134\148 m !! j = None \226\136\167 i \226\137\160 j.
Time Proof.
Time (split; [  | by intros [? ?]; rewrite lookup_insert_ne ]).
Time
(destruct (decide (i = j)) as [->| ];
  rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence).
Time Qed.
Time Lemma insert_id {A} (m : M A) i x : m !! i = Some x \226\134\146 <[i:=x]> m = m.
Time Proof.
Time
(intros; apply map_eq; intros j; destruct (decide (i = j)) as [->| ]; by
  rewrite ?lookup_insert, ?lookup_insert_ne by done).
Time Qed.
Time
Lemma insert_included {A} R `{!Reflexive R} (m : M A) 
  i x : (\226\136\128 y, m !! i = Some y \226\134\146 R y x) \226\134\146 map_included R m (<[i:=x]> m).
Time Proof.
Time (intros ? j; destruct (decide (i = j)) as [->| ]).
Time -
Time (rewrite lookup_insert).
Time (destruct (m !! j); simpl; eauto).
Time -
Time (rewrite lookup_insert_ne by done).
Time by destruct (m !! j); simpl.
Time Qed.
Time Lemma insert_empty {A} i (x : A) : <[i:=x]> (\226\136\133 : M A) = {[i := x]}.
Time Proof.
Time done.
Time Qed.
Time Lemma insert_non_empty {A} (m : M A) i x : <[i:=x]> m \226\137\160 \226\136\133.
Time Proof.
Time (intros Hi%(f_equal (!!i))).
Time by rewrite lookup_insert, lookup_empty in Hi.
Time Qed.
Time
Lemma insert_subseteq {A} (m : M A) i x : m !! i = None \226\134\146 m \226\138\134 <[i:=x]> m.
Time Proof.
Time (apply partial_alter_subseteq).
Time Qed.
Time Lemma insert_subset {A} (m : M A) i x : m !! i = None \226\134\146 m \226\138\130 <[i:=x]> m.
Time Proof.
Time intro.
Time (apply partial_alter_subset; eauto).
Time Qed.
Time
Lemma insert_mono {A} (m1 m2 : M A) i x : m1 \226\138\134 m2 \226\134\146 <[i:=x]> m1 \226\138\134 <[i:=x]> m2.
Time Proof.
Time (rewrite !map_subseteq_spec).
Time (intros Hm j y).
Time (rewrite !lookup_insert_Some).
Time naive_solver.
Time Qed.
Time
Lemma insert_subseteq_r {A} (m1 m2 : M A) i x :
  m1 !! i = None \226\134\146 m1 \226\138\134 m2 \226\134\146 m1 \226\138\134 <[i:=x]> m2.
Time Proof.
Time (intros).
Time (trans <[i:=x]> m1; eauto using insert_subseteq, insert_mono).
Time Qed.
Time
Lemma insert_delete_subseteq {A} (m1 m2 : M A) i x :
  m1 !! i = None \226\134\146 <[i:=x]> m1 \226\138\134 m2 \226\134\146 m1 \226\138\134 delete i m2.
Time Proof.
Time (rewrite !map_subseteq_spec).
Time (intros Hi Hix j y Hj).
Time (destruct (decide (i = j)) as [->| ]; [ congruence |  ]).
Time (rewrite lookup_delete_ne by done).
Time (apply Hix; by rewrite lookup_insert_ne by done).
Time Qed.
Time
Lemma delete_insert_subseteq {A} (m1 m2 : M A) i x :
  m1 !! i = Some x \226\134\146 delete i m1 \226\138\134 m2 \226\134\146 m1 \226\138\134 <[i:=x]> m2.
Time Proof.
Time (rewrite !map_subseteq_spec).
Time (intros Hix Hi j y Hj).
Time (destruct (decide (i = j)) as [->| ?]).
Time -
Time (rewrite lookup_insert).
Time congruence.
Time -
Time (rewrite lookup_insert_ne by done).
Time (apply Hi).
Time by rewrite lookup_delete_ne.
Time Qed.
Time
Lemma insert_delete_subset {A} (m1 m2 : M A) i x :
  m1 !! i = None \226\134\146 <[i:=x]> m1 \226\138\130 m2 \226\134\146 m1 \226\138\130 delete i m2.
Time Proof.
Time
(intros ? [Hm12 Hm21]; split; [ eauto using insert_delete_subseteq |  ]).
Time (contradict Hm21).
Time (apply delete_insert_subseteq; auto).
Time (eapply lookup_weaken, Hm12).
Time by rewrite lookup_insert.
Time Qed.
Time
Lemma insert_subset_inv {A} (m1 m2 : M A) i x :
  m1 !! i = None
  \226\134\146 <[i:=x]> m1 \226\138\130 m2 \226\134\146 \226\136\131 m2', m2 = <[i:=x]> m2' \226\136\167 m1 \226\138\130 m2' \226\136\167 m2' !! i = None.
Time Proof.
Time (intros Hi Hm1m2).
Time exists (delete i m2).
Time split_and ?.
Time -
Time (rewrite insert_delete, insert_id).
Time done.
Time (eapply lookup_weaken, strict_include; eauto).
Time by rewrite lookup_insert.
Time -
Time eauto using insert_delete_subset.
Time -
Time by rewrite lookup_delete.
Time Qed.
Time
Lemma lookup_singleton_Some {A} i j (x y : A) :
  ({[i := x]} : M A) !! j = Some y \226\134\148 i = j \226\136\167 x = y.
Time Proof.
Time
(rewrite <- insert_empty, lookup_insert_Some, lookup_empty; intuition
  congruence).
Time Qed.
Time
Lemma lookup_singleton_None {A} i j (x : A) :
  ({[i := x]} : M A) !! j = None \226\134\148 i \226\137\160 j.
Time Proof.
Time (rewrite <- insert_empty, lookup_insert_None, lookup_empty; tauto).
Time Qed.
Time Lemma lookup_singleton {A} i (x : A) : ({[i := x]} : M A) !! i = Some x.
Time Proof.
Time by rewrite lookup_singleton_Some.
Time Qed.
Time
Lemma lookup_singleton_ne {A} i j (x : A) :
  i \226\137\160 j \226\134\146 ({[i := x]} : M A) !! j = None.
Time Proof.
Time by rewrite lookup_singleton_None.
Time Qed.
Time Lemma map_non_empty_singleton {A} i (x : A) : {[i := x]} \226\137\160 (\226\136\133 : M A).
Time Proof.
Time (intros Hix).
Time (apply (f_equal (!!i)) in Hix).
Time by rewrite lookup_empty, lookup_singleton in Hix.
Time Qed.
Time
Lemma insert_singleton {A} i (x y : A) :
  <[i:=y]> ({[i := x]} : M A) = {[i := y]}.
Time Proof.
Time (unfold singletonM, map_singleton, insert, map_insert).
Time by rewrite <- partial_alter_compose.
Time Qed.
Time
Lemma alter_singleton {A} (f : A \226\134\146 A) i x :
  alter f i ({[i := x]} : M A) = {[i := f x]}.
Time Proof.
Time (intros).
Time (apply map_eq).
Time (intros i').
Time (destruct (decide (i = i')) as [->| ?]).
Time -
Time by rewrite lookup_alter, !lookup_singleton.
Time -
Time by rewrite lookup_alter_ne, !lookup_singleton_ne.
Time Qed.
Time
Lemma alter_singleton_ne {A} (f : A \226\134\146 A) i j x :
  i \226\137\160 j \226\134\146 alter f i ({[j := x]} : M A) = {[j := x]}.
Time Proof.
Time (intros).
Time (apply map_eq; intros i').
Time
by
 destruct (decide (i = i')) as [->| ?];
  rewrite ?lookup_alter, ?lookup_singleton_ne, ?lookup_alter_ne by done.
Time Qed.
Time Lemma singleton_non_empty {A} i (x : A) : {[i := x]} \226\137\160 (\226\136\133 : M A).
Time Proof.
Time (apply insert_non_empty).
Time Qed.
Time Lemma delete_singleton {A} i (x : A) : delete i {[i := x]} = (\226\136\133 : M A).
Time Proof.
Time setoid_rewrite  <- partial_alter_compose.
Time (apply delete_empty).
Time Qed.
Time
Lemma delete_singleton_ne {A} i j (x : A) :
  i \226\137\160 j \226\134\146 delete i ({[j := x]} : M A) = {[j := x]}.
Time Proof.
Time intro.
Time (apply delete_notin).
Time by apply lookup_singleton_ne.
Time Qed.
Time Lemma fmap_empty {A} {B} (f : A \226\134\146 B) : f <$> \226\136\133 = \226\136\133.
Time Proof.
Time (apply map_empty; intros i).
Time by rewrite lookup_fmap, lookup_empty.
Time Qed.
Time Lemma omap_empty {A} {B} (f : A \226\134\146 option B) : omap f \226\136\133 = \226\136\133.
Time Proof.
Time (apply map_empty; intros i).
Time by rewrite lookup_omap, lookup_empty.
Time Qed.
Time
Lemma fmap_insert {A} {B} (f : A \226\134\146 B) m i x :
  f <$> <[i:=x]> m = <[i:=f x]> (f <$> m).
Time Proof.
Time (apply map_eq; intros i'; destruct (decide (i' = i)) as [->| ]).
Time -
Time by rewrite lookup_fmap, !lookup_insert.
Time -
Time by rewrite lookup_fmap, !lookup_insert_ne, lookup_fmap by done.
Time Qed.
Time
Lemma fmap_delete {A} {B} (f : A \226\134\146 B) m i :
  f <$> delete i m = delete i (f <$> m).
Time Proof.
Time (apply map_eq; intros i'; destruct (decide (i' = i)) as [->| ]).
Time -
Time by rewrite lookup_fmap, !lookup_delete.
Time -
Time by rewrite lookup_fmap, !lookup_delete_ne, lookup_fmap by done.
Time Qed.
Time
Lemma omap_insert {A} {B} (f : A \226\134\146 option B) m i x 
  y : f x = Some y \226\134\146 omap f (<[i:=x]> m) = <[i:=y]> (omap f m).
Time Proof.
Time (intros; apply map_eq; intros i'; destruct (decide (i' = i)) as [->| ]).
Time -
Time by rewrite lookup_omap, !lookup_insert.
Time -
Time by rewrite lookup_omap, !lookup_insert_ne, lookup_omap by done.
Time Qed.
Time
Lemma map_fmap_singleton {A} {B} (f : A \226\134\146 B) i x :
  f <$> {[i := x]} = {[i := f x]}.
Time Proof.
Time
by unfold singletonM, map_singleton; rewrite fmap_insert, map_fmap_empty.
Time Qed.
Time
Lemma omap_singleton {A} {B} (f : A \226\134\146 option B) i 
  x y : f x = Some y \226\134\146 omap f {[i := x]} = {[i := y]}.
Time Proof.
Time (intros).
Time (unfold singletonM, map_singleton).
Time by erewrite omap_insert, omap_empty by eauto.
Time Qed.
Time Lemma map_fmap_id {A} (m : M A) : id <$> m = m.
Time Proof.
Time (apply map_eq; intros i; by rewrite lookup_fmap, option_fmap_id).
Time Qed.
Time
Lemma map_fmap_compose {A} {B} {C} (f : A \226\134\146 B) (g : B \226\134\146 C) 
  (m : M A) : g \226\136\152 f <$> m = g <$> (f <$> m).
Time Proof.
Time (apply map_eq; intros i; by rewrite !lookup_fmap, option_fmap_compose).
Time Qed.
Time
Lemma map_fmap_equiv_ext `{Equiv A} `{Equiv B} (f1 f2 : A \226\134\146 B) 
  (m : M A) : (\226\136\128 i x, m !! i = Some x \226\134\146 f1 x \226\137\161 f2 x) \226\134\146 f1 <$> m \226\137\161 f2 <$> m.
Time Proof.
Time (intros Hi i; rewrite !lookup_fmap).
Time (destruct (m !! i) eqn:?; constructor; eauto).
Time Qed.
Time
Lemma map_fmap_ext {A} {B} (f1 f2 : A \226\134\146 B) (m : M A) :
  (\226\136\128 i x, m !! i = Some x \226\134\146 f1 x = f2 x) \226\134\146 f1 <$> m = f2 <$> m.
Time Proof.
Time (intros Hi; apply map_eq; intros i; rewrite !lookup_fmap).
Time by destruct (m !! i) eqn:?; simpl; erewrite ?Hi by eauto.
Time Qed.
Time
Lemma omap_ext {A} {B} (f1 f2 : A \226\134\146 option B) (m : M A) :
  (\226\136\128 i x, m !! i = Some x \226\134\146 f1 x = f2 x) \226\134\146 omap f1 m = omap f2 m.
Time Proof.
Time (intros Hi; apply map_eq; intros i; rewrite !lookup_omap).
Time by destruct (m !! i) eqn:?; simpl; erewrite ?Hi by eauto.
Time Qed.
Time
Lemma map_fmap_mono {A} {B} (f : A \226\134\146 B) (m1 m2 : M A) :
  m1 \226\138\134 m2 \226\134\146 f <$> m1 \226\138\134 f <$> m2.
Time Proof.
Time (rewrite !map_subseteq_spec; intros Hm i x).
Time (rewrite !lookup_fmap, !fmap_Some).
Time naive_solver.
Time Qed.
Time
Lemma map_fmap_strict_mono {A} {B} (f : A \226\134\146 B) (m1 m2 : M A) :
  m1 \226\138\130 m2 \226\134\146 f <$> m1 \226\138\130 f <$> m2.
Time Proof.
Time (rewrite !map_subset_alt).
Time (intros [? (j, (?, ?))]; split; auto using map_fmap_mono).
Time exists j.
Time by rewrite !lookup_fmap, fmap_None, fmap_is_Some.
Time Qed.
Time
Lemma map_omap_mono {A} {B} (f : A \226\134\146 option B) (m1 m2 : M A) :
  m1 \226\138\134 m2 \226\134\146 omap f m1 \226\138\134 omap f m2.
Time Proof.
Time (rewrite !map_subseteq_spec; intros Hm i x).
Time (rewrite !lookup_omap, !bind_Some).
Time naive_solver.
Time Qed.
Time
Lemma elem_of_map_to_list' {A} (m : M A) ix :
  ix \226\136\136 map_to_list m \226\134\148 m !! ix.1 = Some ix.2.
Time Proof.
Time (destruct ix as [i x]).
Time (apply elem_of_map_to_list).
Time Qed.
Time
Lemma map_to_list_unique {A} (m : M A) i x y :
  (i, x) \226\136\136 map_to_list m \226\134\146 (i, y) \226\136\136 map_to_list m \226\134\146 x = y.
Time Proof.
Time (rewrite !elem_of_map_to_list).
Time congruence.
Time Qed.
Time Lemma NoDup_fst_map_to_list {A} (m : M A) : NoDup (map_to_list m).*1.
Time Proof.
Time eauto using NoDup_fmap_fst, map_to_list_unique, NoDup_map_to_list.
Time Qed.
Time
Lemma elem_of_list_to_map_1' {A} (l : list (K * A)) 
  i x :
  (\226\136\128 y, (i, y) \226\136\136 l \226\134\146 x = y)
  \226\134\146 (i, x) \226\136\136 l \226\134\146 (list_to_map l : M A) !! i = Some x.
Time Proof.
Time (induction l as [| [j y] l IH]; csimpl; [ by rewrite elem_of_nil |  ]).
Time setoid_rewrite elem_of_cons.
Time (intros Hdup [?| ?]; simplify_eq; [ by rewrite lookup_insert |  ]).
Time (destruct (decide (i = j)) as [->| ]).
Time -
Time (rewrite lookup_insert; f_equal; eauto using eq_sym).
Time -
Time (rewrite lookup_insert_ne by done; eauto).
Time Qed.
Time
Lemma elem_of_list_to_map_1 {A} (l : list (K * A)) 
  i x : NoDup l.*1 \226\134\146 (i, x) \226\136\136 l \226\134\146 (list_to_map l : M A) !! i = Some x.
Time Proof.
Time (intros ? Hx; apply elem_of_list_to_map_1'; eauto using NoDup_fmap_fst).
Time (intros y; revert Hx).
Time (rewrite !elem_of_list_lookup; intros [i' Hi'] [j' Hj']).
Time (cut (i' = j'); [ naive_solver |  ]).
Time
(apply NoDup_lookup with l.*1 i; by rewrite ?list_lookup_fmap, ?Hi', ?Hj').
Time Qed.
Time
Lemma elem_of_list_to_map_2 {A} (l : list (K * A)) 
  i x : (list_to_map l : M A) !! i = Some x \226\134\146 (i, x) \226\136\136 l.
Time Proof.
Time (induction l as [| [j y] l IH]; simpl; [ by rewrite lookup_empty |  ]).
Time (rewrite elem_of_cons).
Time
(destruct (decide (i = j)) as [->| ];
  rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence).
Time Qed.
Time
Lemma elem_of_list_to_map' {A} (l : list (K * A)) 
  i x :
  (\226\136\128 x', (i, x) \226\136\136 l \226\134\146 (i, x') \226\136\136 l \226\134\146 x = x')
  \226\134\146 (i, x) \226\136\136 l \226\134\148 (list_to_map l : M A) !! i = Some x.
Time Proof.
Time (split; auto using elem_of_list_to_map_1', elem_of_list_to_map_2).
Time Qed.
Time
Lemma elem_of_list_to_map {A} (l : list (K * A)) i 
  x : NoDup l.*1 \226\134\146 (i, x) \226\136\136 l \226\134\148 (list_to_map l : M A) !! i = Some x.
Time Proof.
Time (split; auto using elem_of_list_to_map_1, elem_of_list_to_map_2).
Time Qed.
Time
Lemma not_elem_of_list_to_map_1 {A} (l : list (K * A)) 
  i : i \226\136\137 l.*1 \226\134\146 (list_to_map l : M A) !! i = None.
Time Proof.
Time (rewrite elem_of_list_fmap, eq_None_not_Some).
Time (intros Hi [x ?]; destruct Hi).
Time (exists (i, x); simpl; auto using elem_of_list_to_map_2).
Time Qed.
Time
Lemma not_elem_of_list_to_map_2 {A} (l : list (K * A)) 
  i : (list_to_map l : M A) !! i = None \226\134\146 i \226\136\137 l.*1.
Time Proof.
Time
(induction l as [| [j y] l IH]; csimpl; [ rewrite elem_of_nil; tauto |  ]).
Time (rewrite elem_of_cons).
Time (destruct (decide (i = j)); simplify_eq).
Time -
Time by rewrite lookup_insert.
Time -
Time by rewrite lookup_insert_ne; intuition.
Time Qed.
Time
Lemma not_elem_of_list_to_map {A} (l : list (K * A)) 
  i : i \226\136\137 l.*1 \226\134\148 (list_to_map l : M A) !! i = None.
Time Proof.
Time (red; auto using not_elem_of_list_to_map_1, not_elem_of_list_to_map_2).
Time Qed.
Time
Lemma list_to_map_proper {A} (l1 l2 : list (K * A)) :
  NoDup l1.*1 \226\134\146 l1 \226\137\161\226\130\154 l2 \226\134\146 (list_to_map l1 : M A) = list_to_map l2.
Time Proof.
Time (intros ? Hperm).
Time (apply map_eq).
Time (intros i).
Time (apply option_eq).
Time (intros x).
Time by rewrite <- !elem_of_list_to_map; rewrite <- ?Hperm.
Time Qed.
Time
Lemma list_to_map_inj {A} (l1 l2 : list (K * A)) :
  NoDup l1.*1
  \226\134\146 NoDup l2.*1 \226\134\146 (list_to_map l1 : M A) = list_to_map l2 \226\134\146 l1 \226\137\161\226\130\154 l2.
Time Proof.
Time (intros ? ? Hl1l2).
Time (apply NoDup_Permutation; auto using (NoDup_fmap_1 fst)).
Time (intros [i x]).
Time by rewrite !elem_of_list_to_map, Hl1l2.
Time Qed.
Time
Lemma list_to_map_to_list {A} (m : M A) : list_to_map (map_to_list m) = m.
Time Proof.
Time (apply map_eq).
Time (intros i).
Time (apply option_eq).
Time (intros x).
Time
by
 rewrite <- elem_of_list_to_map, elem_of_map_to_list by auto
  using NoDup_fst_map_to_list.
Time Qed.
Time
Lemma map_to_list_to_map {A} (l : list (K * A)) :
  NoDup l.*1 \226\134\146 map_to_list (list_to_map l) \226\137\161\226\130\154 l.
Time Proof.
Time auto using list_to_map_inj, NoDup_fst_map_to_list, list_to_map_to_list.
Time Qed.
Time
Lemma map_to_list_inj {A} (m1 m2 : M A) :
  map_to_list m1 \226\137\161\226\130\154 map_to_list m2 \226\134\146 m1 = m2.
Time Proof.
Time (intros).
Time (rewrite <- (list_to_map_to_list m1), <- (list_to_map_to_list m2)).
Time auto using list_to_map_proper, NoDup_fst_map_to_list.
Time Qed.
Time
Lemma list_to_map_flip {A} (m1 : M A) l2 :
  map_to_list m1 \226\137\161\226\130\154 l2 \226\134\146 m1 = list_to_map l2.
Time Proof.
Time (intros).
Time (rewrite <- (list_to_map_to_list m1)).
Time auto using list_to_map_proper, NoDup_fst_map_to_list.
Time Qed.
Time Lemma list_to_map_nil {A} : list_to_map [] = (\226\136\133 : M A).
Time Proof.
Time done.
Time Qed.
Time
Lemma list_to_map_cons {A} (l : list (K * A)) i x :
  list_to_map ((i, x) :: l) = <[i:=x]> (list_to_map l : M A).
Time Proof.
Time done.
Time Qed.
Time
Lemma list_to_map_fmap {A} {B} (f : A \226\134\146 B) l :
  list_to_map (prod_map id f <$> l) = f <$> (list_to_map l : M A).
Time Proof.
Time (induction l as [| [i x] l IH]; csimpl; rewrite ?fmap_empty; auto).
Time (rewrite <- list_to_map_cons; simpl).
Time by rewrite IH, <- fmap_insert.
Time Qed.
Time Lemma map_to_list_empty {A} : map_to_list \226\136\133 = @nil (K * A).
Time Proof.
Time (apply elem_of_nil_inv).
Time (intros [i x]).
Time (rewrite elem_of_map_to_list).
Time (apply lookup_empty_Some).
Time Qed.
Time
Lemma map_to_list_insert {A} (m : M A) i x :
  m !! i = None \226\134\146 map_to_list (<[i:=x]> m) \226\137\161\226\130\154 (i, x) :: map_to_list m.
Time Proof.
Time (intros).
Time (apply list_to_map_inj; csimpl).
Time -
Time (apply NoDup_fst_map_to_list).
Time -
Time (constructor; auto using NoDup_fst_map_to_list).
Time (rewrite elem_of_list_fmap).
Time (intros [[? ?] [? Hlookup]]; subst; simpl in *).
Time (rewrite elem_of_map_to_list in Hlookup).
Time congruence.
Time -
Time by rewrite !list_to_map_to_list.
Time Qed.
Time
Lemma map_to_list_singleton {A} i (x : A) :
  map_to_list ({[i := x]} : M A) = [(i, x)].
Time Proof.
Time (apply Permutation_singleton).
Time (unfold singletonM, map_singleton).
Time
by rewrite map_to_list_insert, map_to_list_empty by auto using lookup_empty.
Time Qed.
Time
Lemma map_to_list_submseteq {A} (m1 m2 : M A) :
  m1 \226\138\134 m2 \226\134\146 map_to_list m1 \226\138\134+ map_to_list m2.
Time Proof.
Time (intros; apply NoDup_submseteq; auto using NoDup_map_to_list).
Time (intros [i x]).
Time (rewrite !elem_of_map_to_list; eauto using lookup_weaken).
Time Qed.
Time
Lemma map_to_list_fmap {A} {B} (f : A \226\134\146 B) (m : M A) :
  map_to_list (f <$> m) \226\137\161\226\130\154 prod_map id f <$> map_to_list m.
Time Proof.
Time (assert (NoDup (prod_map id f <$> map_to_list m).*1)).
Time {
Time (erewrite <- list_fmap_compose, (list_fmap_ext _ fst) by done).
Time (apply NoDup_fst_map_to_list).
Time }
Time (rewrite <- (list_to_map_to_list m)  at 1).
Time by rewrite <- list_to_map_fmap, map_to_list_to_map.
Time Qed.
Time
Lemma map_to_list_empty_inv_alt {A} (m : M A) : map_to_list m \226\137\161\226\130\154 [] \226\134\146 m = \226\136\133.
Time Proof.
Time (rewrite <- map_to_list_empty).
Time (apply map_to_list_inj).
Time Qed.
Time Lemma map_to_list_empty_inv {A} (m : M A) : map_to_list m = [] \226\134\146 m = \226\136\133.
Time Proof.
Time (intros Hm).
Time (apply map_to_list_empty_inv_alt).
Time by rewrite Hm.
Time Qed.
Time Lemma map_to_list_empty' {A} (m : M A) : map_to_list m = [] \226\134\148 m = \226\136\133.
Time Proof.
Time split.
Time (apply map_to_list_empty_inv).
Time (intros ->).
Time (apply map_to_list_empty).
Time Qed.
Time
Lemma map_to_list_insert_inv {A} (m : M A) l i x :
  map_to_list m \226\137\161\226\130\154 (i, x) :: l \226\134\146 m = <[i:=x]> (list_to_map l).
Time Proof.
Time (intros Hperm).
Time (apply map_to_list_inj).
Time (assert ((i \226\136\137 l.*1) \226\136\167 NoDup l.*1) as []).
Time {
Time (rewrite <- NoDup_cons).
Time (change_no_check (NoDup ((i, x) :: l).*1)).
Time (rewrite <- Hperm).
Time auto using NoDup_fst_map_to_list.
Time }
Time
(rewrite Hperm, map_to_list_insert, map_to_list_to_map; auto
  using not_elem_of_list_to_map_1).
Time Qed.
Time Lemma map_choose {A} (m : M A) : m \226\137\160 \226\136\133 \226\134\146 \226\136\131 i x, m !! i = Some x.
Time Proof.
Time (intros Hemp).
Time (destruct (map_to_list m) as [| [i x] l] eqn:Hm).
Time {
Time (destruct Hemp; eauto using map_to_list_empty_inv).
Time }
Time exists i,x.
Time (rewrite <- elem_of_map_to_list, Hm).
Time by left.
Time Qed.
Time #[global]
Instance map_eq_dec_empty  {A} (m : M A): (Decision (m = \226\136\133)) |20.
Time Proof.
Time
(refine (cast_if (decide (elements m = [])));
  [ apply _ | by rewrite <- ?map_to_list_empty'.. ]).
Time Defined.
Time
Lemma map_lookup_imap {A} {B} (f : K \226\134\146 A \226\134\146 option B) 
  (m : M A) i : map_imap f m !! i = m !! i \226\137\171= f i.
Time Proof.
Time (unfold map_imap; destruct (m !! i \226\137\171= f i) as [y| ] eqn:Hi; simpl).
Time -
Time (destruct (m !! i) as [x| ] eqn:?; simplify_eq /=).
Time (apply elem_of_list_to_map_1').
Time {
Time (intros y'; rewrite elem_of_list_omap; intros ([i' x'], (Hi', ?))).
Time by rewrite elem_of_map_to_list in Hi'; simplify_option_eq.
Time }
Time
(apply elem_of_list_omap; exists (i, x); split;
  [ by apply elem_of_map_to_list | by simplify_option_eq ]).
Time -
Time (apply not_elem_of_list_to_map; rewrite elem_of_list_fmap).
Time (intros ([i' x], (->, Hi')); simplify_eq /=).
Time (rewrite elem_of_list_omap in Hi'; destruct Hi' as ([j y], (Hj, ?))).
Time (rewrite elem_of_map_to_list in Hj; simplify_option_eq).
Time Qed.
Time Lemma map_imap_Some {A} (m : M A) : map_imap (\206\187 _, Some) m = m.
Time Proof.
Time (apply map_eq).
Time (intros i).
Time (rewrite map_lookup_imap).
Time by destruct (m !! i).
Time Qed.
Time
Lemma map_imap_insert {A} {B} (f : K \226\134\146 A \226\134\146 option B) 
  (i : K) (v : A) (m : M A) :
  map_imap f (<[i:=v]> m) =
  match f i v with
  | None => delete i (map_imap f m)
  | Some w => <[i:=w]> (map_imap f m)
  end.
Time Proof.
Time (destruct (f i v) as [w| ] eqn:Hw).
Time -
Time (apply map_eq).
Time (intros k).
Time (rewrite map_lookup_imap).
Time (destruct (decide (k = i)) as [->| Hk_not_i]).
Time +
Time by rewrite lookup_insert, lookup_insert.
Time +
Time (rewrite !lookup_insert_ne by done).
Time by rewrite map_lookup_imap.
Time -
Time (apply map_eq).
Time (intros k).
Time (rewrite map_lookup_imap).
Time (destruct (decide (k = i)) as [->| Hk_not_i]).
Time +
Time by rewrite lookup_insert, lookup_delete.
Time +
Time (rewrite lookup_insert_ne, lookup_delete_ne by done).
Time by rewrite map_lookup_imap.
Time Qed.
Time
Lemma map_imap_ext {A1} {A2} {B} (f1 : K \226\134\146 A1 \226\134\146 option B)
  (f2 : K \226\134\146 A2 \226\134\146 option B) (m1 : M A1) (m2 : M A2) :
  (\226\136\128 k, f1 k <$> m1 !! k = f2 k <$> m2 !! k)
  \226\134\146 map_imap f1 m1 = map_imap f2 m2.
Time Proof.
Time (intros HExt).
Time (apply map_eq).
Time (intros i).
Time (rewrite !map_lookup_imap).
Time specialize (HExt i).
Time (destruct (m1 !! i), (m2 !! i); naive_solver).
Time Qed.
Time Lemma map_size_empty {A} : size (\226\136\133 : M A) = 0.
Time Proof.
Time (unfold size, map_size).
Time by rewrite map_to_list_empty.
Time Qed.
Time Lemma map_size_empty_inv {A} (m : M A) : size m = 0 \226\134\146 m = \226\136\133.
Time Proof.
Time (unfold size, map_size).
Time by rewrite length_zero_iff_nil, map_to_list_empty'.
Time Qed.
Time Lemma map_size_empty_iff {A} (m : M A) : size m = 0 \226\134\148 m = \226\136\133.
Time Proof.
Time split.
Time (apply map_size_empty_inv).
Time by intros ->; rewrite map_size_empty.
Time Qed.
Time Lemma map_size_non_empty_iff {A} (m : M A) : size m \226\137\160 0 \226\134\148 m \226\137\160 \226\136\133.
Time Proof.
Time by rewrite map_size_empty_iff.
Time Qed.
Time Lemma map_size_singleton {A} i (x : A) : size ({[i := x]} : M A) = 1.
Time Proof.
Time (unfold size, map_size).
Time by rewrite map_to_list_singleton.
Time Qed.
Time
Lemma map_size_insert {A} i x (m : M A) :
  m !! i = None \226\134\146 size (<[i:=x]> m) = S (size m).
Time Proof.
Time (intros).
Time (unfold size, map_size).
Time by rewrite map_to_list_insert.
Time Qed.
Time
Lemma map_size_fmap {A} {B} (f : A -> B) (m : M A) : size (f <$> m) = size m.
Time Proof.
Time (intros).
Time (unfold size, map_size).
Time by rewrite map_to_list_fmap, fmap_length.
Time Qed.
Time Section set_to_map.
Time Context {A : Type} `{FinSet B C}.
Time
Lemma lookup_set_to_map (f : B \226\134\146 K * A) (Y : C) i 
  x :
  (\226\136\128 y y', y \226\136\136 Y \226\134\146 y' \226\136\136 Y \226\134\146 (f y).1 = (f y').1 \226\134\146 y = y')
  \226\134\146 (set_to_map f Y : M A) !! i = Some x \226\134\148 (\226\136\131 y, y \226\136\136 Y \226\136\167 f y = (i, x)).
Time Proof.
Time (intros Hinj).
Time
(assert
  (\226\136\128 x', (i, x) \226\136\136 f <$> elements Y \226\134\146 (i, x') \226\136\136 f <$> elements Y \226\134\146 x = x')).
Time {
Time (intros x').
Time
(intros (y, (Hx, Hy))%elem_of_list_fmap (y', (Hx', Hy'))%elem_of_list_fmap).
Time (rewrite elem_of_elements in Hy, Hy').
Time (cut (y = y'); [ congruence |  ]).
Time (apply Hinj; auto).
Time by rewrite <- Hx, <- Hx'.
Time }
Time (unfold set_to_map; rewrite <- elem_of_list_to_map' by done).
Time (rewrite elem_of_list_fmap).
Time (setoid_rewrite elem_of_elements; naive_solver).
Time Qed.
Time
Lemma elem_of_map_to_set (f : K \226\134\146 A \226\134\146 B) (m : M A) 
  (y : B) : y \226\136\136 map_to_set (C:=C) f m \226\134\148 (\226\136\131 i x, m !! i = Some x \226\136\167 f i x = y).
Time Proof.
Time (unfold map_to_set; simpl).
Time (rewrite elem_of_list_to_set, elem_of_list_fmap).
Time split.
Time -
Time (intros ([i x], (?, ?%elem_of_map_to_list)); eauto).
Time -
Time (intros (i, (x, (?, ?)))).
Time exists (i, x).
Time by rewrite elem_of_map_to_list.
Time Qed.
Time
Lemma map_to_set_empty (f : K \226\134\146 A \226\134\146 B) : map_to_set f (\226\136\133 : M A) = (\226\136\133 : C).
Time Proof.
Time (unfold map_to_set; simpl).
Time by rewrite map_to_list_empty.
Time Qed.
Time
Lemma map_to_set_insert (f : K \226\134\146 A \226\134\146 B) (m : M A) 
  i x :
  m !! i = None \226\134\146 map_to_set f (<[i:=x]> m) \226\137\161@{ C} {[f i x]} \226\136\170 map_to_set f m.
Time Proof.
Time (intros).
Time (unfold map_to_set; simpl).
Time by rewrite map_to_list_insert.
Time Qed.
Time
Lemma map_to_set_insert_L `{!LeibnizEquiv C} (f : K \226\134\146 A \226\134\146 B) 
  (m : M A) i x :
  m !! i = None \226\134\146 map_to_set f (<[i:=x]> m) =@{ C} {[f i x]} \226\136\170 map_to_set f m.
Time Proof.
Time unfold_leibniz.
Time (apply map_to_set_insert).
Time Qed.
Time End set_to_map.
Time
Lemma lookup_set_to_map_id `{FinSet (K * A) C} (X : C) 
  i x :
  (\226\136\128 i y y', (i, y) \226\136\136 X \226\134\146 (i, y') \226\136\136 X \226\134\146 y = y')
  \226\134\146 (set_to_map id X : M A) !! i = Some x \226\134\148 (i, x) \226\136\136 X.
Time Proof.
Time (intros).
Time (etrans; [ apply lookup_set_to_map | naive_solver ]).
Time (intros [] [] ? ? ?; simplify_eq /=; eauto with f_equal).
Time Qed.
Time
Lemma elem_of_map_to_set_pair `{FinSet (K * A) C} 
  (m : M A) i x : (i, x) \226\136\136@{ C} map_to_set pair m \226\134\148 m !! i = Some x.
Time Proof.
Time (rewrite elem_of_map_to_set).
Time naive_solver.
Time Qed.
Time
Lemma map_ind {A} (P : M A \226\134\146 Prop) :
  P \226\136\133 \226\134\146 (\226\136\128 i x m, m !! i = None \226\134\146 P m \226\134\146 P (<[i:=x]> m)) \226\134\146 \226\136\128 m, P m.
Time Proof.
Time (intros ? Hins).
Time (cut (\226\136\128 l, NoDup l.*1 \226\134\146 \226\136\128 m, map_to_list m \226\137\161\226\130\154 l \226\134\146 P m)).
Time {
Time (intros help m).
Time (apply (help (map_to_list m)); auto using NoDup_fst_map_to_list).
Time }
Time (induction l as [| [i x] l IH]; intros Hnodup m Hml).
Time {
Time (apply map_to_list_empty_inv_alt in Hml).
Time by subst.
Time }
Time (inversion_clear Hnodup).
Time (apply map_to_list_insert_inv in Hml; subst m).
Time (apply Hins).
Time -
Time by apply not_elem_of_list_to_map_1.
Time -
Time (apply IH; auto using map_to_list_to_map).
Time Qed.
Time
Lemma map_to_list_length {A} (m1 m2 : M A) :
  m1 \226\138\130 m2 \226\134\146 length (map_to_list m1) < length (map_to_list m2).
Time Proof.
Time revert m2.
Time (induction m1 as [| i x m ? IH] using map_ind).
Time {
Time (intros m2 Hm2).
Time (rewrite map_to_list_empty).
Time (simpl).
Time (apply neq_0_lt).
Time (intros Hlen).
Time symmetry in Hlen.
Time (apply nil_length_inv, map_to_list_empty_inv in Hlen).
Time (rewrite Hlen in Hm2).
Time (destruct (irreflexivity (\226\138\130) \226\136\133 Hm2)).
Time }
Time (intros m2 Hm2).
Time
(destruct (insert_subset_inv m m2 i x) as (m2', (?, (?, ?))); auto; subst).
Time (rewrite !map_to_list_insert; simpl; auto with arith).
Time Qed.
Time Lemma map_wf {A} : wf (\226\138\130@{M A} ).
Time Proof.
Time (apply (wf_projected (<) (length \226\136\152 map_to_list))).
Time -
Time by apply map_to_list_length.
Time -
Time by apply lt_wf.
Time Qed.
Time
Lemma map_fold_empty {A} {B} (f : K \226\134\146 A \226\134\146 B \226\134\146 B) (b : B) : map_fold f b \226\136\133 = b.
Time Proof.
Time (unfold map_fold; simpl).
Time by rewrite map_to_list_empty.
Time Qed.
Time
Lemma map_fold_insert {A} {B} (R : relation B) `{!PreOrder R}
  (f : K \226\134\146 A \226\134\146 B \226\134\146 B) (b : B) (i : K) (x : A) (m : M A) :
  (\226\136\128 j z, Proper (R ==> R) (f j z))
  \226\134\146 (\226\136\128 j1 j2 z1 z2 y,
       j1 \226\137\160 j2
       \226\134\146 <[i:=x]> m !! j1 = Some z1
         \226\134\146 <[i:=x]> m !! j2 = Some z2
           \226\134\146 R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y)))
    \226\134\146 m !! i = None \226\134\146 R (map_fold f b (<[i:=x]> m)) (f i x (map_fold f b m)).
Time Proof.
Time (intros Hf_proper Hf Hi).
Time (unfold map_fold; simpl).
Time (assert (\226\136\128 kz, Proper (R ==> R) (curry f kz)) by (intros []; apply _)).
Time (trans foldr (curry f) b ((i, x) :: map_to_list m); [  | done ]).
Time (eapply (foldr_permutation R (curry f) b), map_to_list_insert; auto).
Time (intros j1 [k1 y1] j2 [k2 y2] c Hj Hj1 Hj2).
Time (apply Hf).
Time -
Time (intros ->).
Time
(eapply Hj, NoDup_lookup;
  [ apply (NoDup_fst_map_to_list (<[i:=x]> m)) |  |  ]).
Time +
Time by rewrite list_lookup_fmap, Hj1.
Time +
Time by rewrite list_lookup_fmap, Hj2.
Time -
Time by eapply elem_of_map_to_list, elem_of_list_lookup_2.
Time -
Time by eapply elem_of_map_to_list, elem_of_list_lookup_2.
Time Qed.
Time
Lemma map_fold_insert_L {A} {B} (f : K \226\134\146 A \226\134\146 B \226\134\146 B) 
  (b : B) (i : K) (x : A) (m : M A) :
  (\226\136\128 j1 j2 z1 z2 y,
     j1 \226\137\160 j2
     \226\134\146 <[i:=x]> m !! j1 = Some z1
       \226\134\146 <[i:=x]> m !! j2 = Some z2
         \226\134\146 f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y))
  \226\134\146 m !! i = None \226\134\146 map_fold f b (<[i:=x]> m) = f i x (map_fold f b m).
Time Proof.
Time (apply map_fold_insert; apply _).
Time Qed.
Time
Lemma map_fold_ind {A} {B} (P : B \226\134\146 M A \226\134\146 Prop) (f : K \226\134\146 A \226\134\146 B \226\134\146 B) 
  (b : B) :
  P b \226\136\133
  \226\134\146 (\226\136\128 i x m r, m !! i = None \226\134\146 P r m \226\134\146 P (f i x r) (<[i:=x]> m))
    \226\134\146 \226\136\128 m, P (map_fold f b m) m.
Time Proof.
Time (intros Hemp Hinsert).
Time
(cut
  (\226\136\128 l,
     NoDup l
     \226\134\146 \226\136\128 m, (\226\136\128 i x, m !! i = Some x \226\134\148 (i, x) \226\136\136 l) \226\134\146 P (foldr (curry f) b l) m)).
Time {
Time (intros help ?).
Time (apply help; [ apply NoDup_map_to_list |  ]).
Time (intros i x).
Time by rewrite elem_of_map_to_list.
Time }
Time (induction 1 as [| [i x] l ? ? IH]; simpl).
Time {
Time (intros m Hm).
Time (cut (m = \226\136\133); [ by intros -> |  ]).
Time (apply map_empty; intros i).
Time (apply eq_None_not_Some; intros [x []%elem_of_nil%Hm]).
Time }
Time (intros m Hm).
Time (assert (m !! i = Some x) by (apply Hm; by left)).
Time (rewrite <- (insert_id m i x), <- insert_delete by done).
Time (apply Hinsert; auto using lookup_delete).
Time (apply IH).
Time (intros j y).
Time (rewrite lookup_delete_Some, Hm).
Time split.
Time -
Time by intros [? [[=? ?]| ?]%elem_of_cons].
Time -
Time (intros ?; split; [ intros -> | by right ]).
Time (assert (m !! j = Some y) by (apply Hm; by right)).
Time naive_solver.
Time Qed.
Time Section map_filter.
Time Context {A} (P : K * A \226\134\146 Prop) `{!\226\136\128 x, Decision (P x)}.
Time Implicit Type m : M A.
Time
Lemma map_filter_lookup_Some m i x :
  filter P m !! i = Some x \226\134\148 m !! i = Some x \226\136\167 P (i, x).
Time Proof.
Time revert m i x.
Time
(apply
  (map_fold_ind (\206\187 m1 m2, \226\136\128 i x, m1 !! i = Some x \226\134\148 m2 !! i = Some x \226\136\167 P _));
  intros i x).
Time -
Time (rewrite lookup_empty).
Time naive_solver.
Time -
Time (intros m m' Hm Eq j y).
Time (case_decide; destruct (decide (j = i)) as [->| ?]).
Time +
Time (rewrite 2!lookup_insert).
Time naive_solver.
Time +
Time (rewrite !lookup_insert_ne by done).
Time by apply Eq.
Time +
Time (rewrite Eq, Hm, lookup_insert).
Time naive_solver.
Time +
Time by rewrite lookup_insert_ne.
Time Qed.
Time
Lemma map_filter_lookup_None m i :
  filter P m !! i = None
  \226\134\148 m !! i = None \226\136\168 (\226\136\128 x, m !! i = Some x \226\134\146 \194\172 P (i, x)).
Time Proof.
Time (rewrite eq_None_not_Some).
Time (unfold is_Some).
Time setoid_rewrite map_filter_lookup_Some.
Time naive_solver.
Time Qed.
Time
Lemma map_filter_lookup_eq m1 m2 :
  (\226\136\128 k x, P (k, x) \226\134\146 m1 !! k = Some x \226\134\148 m2 !! k = Some x)
  \226\134\146 filter P m1 = filter P m2.
Time Proof.
Time (intros HP).
Time (apply map_eq).
Time (intros i).
Time (apply option_eq; intros x).
Time (rewrite !map_filter_lookup_Some).
Time naive_solver.
Time Qed.
Time
Lemma map_filter_insert m i x :
  P (i, x) \226\134\146 filter P (<[i:=x]> m) = <[i:=x]> (filter P m).
Time Proof.
Time (intros HP).
Time (apply map_eq).
Time (intros j).
Time (apply option_eq; intros y).
Time (destruct (decide (j = i)) as [->| ?]).
Time -
Time (rewrite map_filter_lookup_Some, !lookup_insert).
Time naive_solver.
Time -
Time
(rewrite lookup_insert_ne, !map_filter_lookup_Some, lookup_insert_ne by done).
Time naive_solver.
Time Qed.
Time
Lemma map_filter_insert_not' m i x :
  \194\172 P (i, x)
  \226\134\146 (\226\136\128 y, m !! i = Some y \226\134\146 \194\172 P (i, y)) \226\134\146 filter P (<[i:=x]> m) = filter P m.
Time Proof.
Time (intros Hx HP).
Time (apply map_filter_lookup_eq).
Time (intros j y Hy).
Time (rewrite lookup_insert_Some).
Time naive_solver.
Time Qed.
Time
Lemma map_filter_insert_not m i x :
  (\226\136\128 y, \194\172 P (i, y)) \226\134\146 filter P (<[i:=x]> m) = filter P m.
Time Proof.
Time (intros HP).
Time by apply map_filter_insert_not'.
Time Qed.
Time
Lemma map_filter_delete m i : filter P (delete i m) = delete i (filter P m).
Time Proof.
Time (apply map_eq).
Time (intros j).
Time (apply option_eq; intros y).
Time (destruct (decide (j = i)) as [->| ?]).
Time -
Time (rewrite map_filter_lookup_Some, !lookup_delete).
Time naive_solver.
Time -
Time
(rewrite lookup_delete_ne, !map_filter_lookup_Some, lookup_delete_ne by done).
Time naive_solver.
Time Qed.
Time
Lemma map_filter_delete_not m i :
  (\226\136\128 y, \194\172 P (i, y)) \226\134\146 filter P (delete i m) = filter P m.
Time Proof.
Time (intros HP).
Time (apply map_filter_lookup_eq; intros j y Hy).
Time by rewrite lookup_delete_ne by naive_solver.
Time Qed.
Time Lemma map_filter_empty : filter P (\226\136\133 : M A) = \226\136\133.
Time Proof.
Time (apply map_fold_empty).
Time Qed.
Time
Lemma map_filter_alt m : filter P m = list_to_map (filter P (map_to_list m)).
Time Proof.
Time (apply list_to_map_flip).
Time (induction m as [| k x m ? IH] using map_ind).
Time {
Time by rewrite map_to_list_empty, map_filter_empty, map_to_list_empty.
Time }
Time (rewrite map_to_list_insert, filter_cons by done).
Time (destruct (decide (P _))).
Time -
Time (rewrite map_filter_insert by done).
Time
by rewrite map_to_list_insert, IH by (rewrite map_filter_lookup_None; auto).
Time -
Time by rewrite map_filter_insert_not' by naive_solver.
Time Qed.
Time End map_filter.
Time Section map_Forall.
Time Context {A} (P : K \226\134\146 A \226\134\146 Prop).
Time Implicit Type m : M A.
Time
Lemma map_Forall_to_list m :
  map_Forall P m \226\134\148 Forall (curry P) (map_to_list m).
Time Proof.
Time (rewrite Forall_forall).
Time split.
Time -
Time (intros Hforall [i x]).
Time (rewrite elem_of_map_to_list).
Time by apply (Hforall i x).
Time -
Time (intros Hforall i x).
Time (rewrite <- elem_of_map_to_list).
Time by apply (Hforall (i, x)).
Time Qed.
Time Lemma map_Forall_empty : map_Forall P (\226\136\133 : M A).
Time Proof.
Time (intros i x).
Time by rewrite lookup_empty.
Time Qed.
Time
Lemma map_Forall_impl (Q : K \226\134\146 A \226\134\146 Prop) m :
  map_Forall P m \226\134\146 (\226\136\128 i x, P i x \226\134\146 Q i x) \226\134\146 map_Forall Q m.
Time Proof.
Time (unfold map_Forall; naive_solver).
Time Qed.
Time Lemma map_Forall_insert_11 m i x : map_Forall P (<[i:=x]> m) \226\134\146 P i x.
Time Proof.
Time (intros Hm).
Time by apply Hm; rewrite lookup_insert.
Time Qed.
Time
Lemma map_Forall_insert_12 m i x :
  m !! i = None \226\134\146 map_Forall P (<[i:=x]> m) \226\134\146 map_Forall P m.
Time Proof.
Time (intros ? Hm j y ?; apply Hm).
Time by rewrite lookup_insert_ne by congruence.
Time Qed.
Time
Lemma map_Forall_insert_2 m i x :
  P i x \226\134\146 map_Forall P m \226\134\146 map_Forall P (<[i:=x]> m).
Time Proof.
Time (intros ? ? j y; rewrite lookup_insert_Some; naive_solver).
Time Qed.
Time
Lemma map_Forall_insert m i x :
  m !! i = None \226\134\146 map_Forall P (<[i:=x]> m) \226\134\148 P i x \226\136\167 map_Forall P m.
Time Proof.
Time
naive_solver eauto
 using map_Forall_insert_11, map_Forall_insert_12, map_Forall_insert_2.
Time Qed.
Time
Lemma map_Forall_delete m i : map_Forall P m \226\134\146 map_Forall P (delete i m).
Time Proof.
Time (intros Hm j x; rewrite lookup_delete_Some).
Time naive_solver.
Time Qed.
Time
Lemma map_Forall_foldr_delete m is :
  map_Forall P m \226\134\146 map_Forall P (foldr delete m is).
Time Proof.
Time (induction is; eauto using map_Forall_delete).
Time Qed.
Time
Lemma map_Forall_ind (Q : M A \226\134\146 Prop) :
  Q \226\136\133
  \226\134\146 (\226\136\128 m i x, m !! i = None \226\134\146 P i x \226\134\146 map_Forall P m \226\134\146 Q m \226\134\146 Q (<[i:=x]> m))
    \226\134\146 \226\136\128 m, map_Forall P m \226\134\146 Q m.
Time Proof.
Time (intros Hnil Hinsert m).
Time (induction m using map_ind; auto).
Time (rewrite map_Forall_insert by done; intros [? ?]; eauto).
Time Qed.
Time Context `{\226\136\128 i x, Decision (P i x)}.
Time #[global]Instance map_Forall_dec  m: (Decision (map_Forall P m)).
Time Proof.
Time
(refine (cast_if (decide (Forall (curry P) (map_to_list m)))); by
  rewrite map_Forall_to_list).
Time Defined.
Time
Lemma map_not_Forall (m : M A) :
  \194\172 map_Forall P m \226\134\148 (\226\136\131 i x, m !! i = Some x \226\136\167 \194\172 P i x).
Time Proof.
Time (split; [  | intros (i, (x, (?, ?))) Hm; specialize (Hm i x); tauto ]).
Time (rewrite map_Forall_to_list).
Time (intros Hm).
Time (apply (not_Forall_Exists _), Exists_exists in Hm).
Time (destruct Hm as ([i x], (?, ?))).
Time exists i,x.
Time by rewrite <- elem_of_map_to_list.
Time Qed.
Time End map_Forall.
Time Section merge.
Time Context {A} (f : option A \226\134\146 option A \226\134\146 option A) `{!DiagNone f}.
Time Implicit Type m : M A.
Time #[global]Instance: (LeftId (=) None f \226\134\146 LeftId (=) (\226\136\133 : M A) (merge f)).
Time Proof.
Time (intros ? ?).
Time (apply map_eq).
Time (intros).
Time by rewrite !(lookup_merge f), lookup_empty, (left_id_L None f).
Time Qed.
Time #[global]
Instance: (RightId (=) None f \226\134\146 RightId (=) (\226\136\133 : M A) (merge f)).
Time Proof.
Time (intros ? ?).
Time (apply map_eq).
Time (intros).
Time by rewrite !(lookup_merge f), lookup_empty, (right_id_L None f).
Time Qed.
Time #[global]
Instance: (LeftAbsorb (=) None f \226\134\146 LeftAbsorb (=) (\226\136\133 : M A) (merge f)).
Time Proof.
Time (intros ? ?).
Time (apply map_eq).
Time (intros).
Time by rewrite !(lookup_merge f), lookup_empty, (left_absorb_L None f).
Time Qed.
Time #[global]
Instance: (RightAbsorb (=) None f \226\134\146 RightAbsorb (=) (\226\136\133 : M A) (merge f)).
Time Proof.
Time (intros ? ?).
Time (apply map_eq).
Time (intros).
Time by rewrite !(lookup_merge f), lookup_empty, (right_absorb_L None f).
Time Qed.
Time
Lemma merge_comm m1 m2 :
  (\226\136\128 i, f (m1 !! i) (m2 !! i) = f (m2 !! i) (m1 !! i))
  \226\134\146 merge f m1 m2 = merge f m2 m1.
Time Proof.
Time (intros).
Time (apply map_eq).
Time (intros).
Time by rewrite !(lookup_merge f).
Time Qed.
Time #[global]
Instance merge_comm' : (Comm (=) f \226\134\146 Comm (=@{M _} ) (merge f)).
Time Proof.
Time (intros ? ? ?).
Time (apply merge_comm).
Time (intros).
Time by apply (comm f).
Time Qed.
Time
Lemma merge_assoc m1 m2 m3 :
  (\226\136\128 i,
     f (m1 !! i) (f (m2 !! i) (m3 !! i)) =
     f (f (m1 !! i) (m2 !! i)) (m3 !! i))
  \226\134\146 merge f m1 (merge f m2 m3) = merge f (merge f m1 m2) m3.
Time Proof.
Time (intros).
Time (apply map_eq).
Time (intros).
Time by rewrite !(lookup_merge f).
Time Qed.
Time #[global]
Instance merge_assoc' : (Assoc (=) f \226\134\146 Assoc (=@{M _} ) (merge f)).
Time Proof.
Time (intros ? ? ? ?).
Time (apply merge_assoc).
Time (intros).
Time by apply (assoc_L f).
Time Qed.
Time
Lemma merge_idemp m1 :
  (\226\136\128 i, f (m1 !! i) (m1 !! i) = m1 !! i) \226\134\146 merge f m1 m1 = m1.
Time Proof.
Time (intros).
Time (apply map_eq).
Time (intros).
Time by rewrite !(lookup_merge f).
Time Qed.
Time #[global]
Instance merge_idemp' : (IdemP (=) f \226\134\146 IdemP (=@{M _} ) (merge f)).
Time Proof.
Time (intros ? ?).
Time (apply merge_idemp).
Time (intros).
Time by apply (idemp f).
Time Qed.
Time End merge.
Time Section more_merge.
Time Context {A} {B} {C} (f : option A \226\134\146 option B \226\134\146 option C) `{!DiagNone f}.
Time
Lemma merge_Some (m1 : M A) (m2 : M B) (m : M C) :
  (\226\136\128 i, m !! i = f (m1 !! i) (m2 !! i)) \226\134\148 merge f m1 m2 = m.
Time Proof.
Time (split; [  | intros <-; apply (lookup_merge _) ]).
Time (intros Hlookup).
Time (apply map_eq; intros).
Time (rewrite Hlookup).
Time (apply (lookup_merge _)).
Time Qed.
Time Lemma merge_empty : merge f (\226\136\133 : M A) (\226\136\133 : M B) = \226\136\133.
Time Proof.
Time (apply map_eq).
Time (intros).
Time by rewrite !(lookup_merge f), !lookup_empty.
Time Qed.
Time
Lemma partial_alter_merge g g1 g2 (m1 : M A) (m2 : M B) 
  i :
  g (f (m1 !! i) (m2 !! i)) = f (g1 (m1 !! i)) (g2 (m2 !! i))
  \226\134\146 partial_alter g i (merge f m1 m2) =
    merge f (partial_alter g1 i m1) (partial_alter g2 i m2).
Time Proof.
Time intro.
Time (apply map_eq).
Time (intros j).
Time (destruct (decide (i = j)); subst).
Time -
Time by rewrite (lookup_merge _), !lookup_partial_alter, !(lookup_merge _).
Time -
Time by rewrite (lookup_merge _), !lookup_partial_alter_ne, (lookup_merge _).
Time Qed.
Time
Lemma partial_alter_merge_l g g1 (m1 : M A) (m2 : M B) 
  i :
  g (f (m1 !! i) (m2 !! i)) = f (g1 (m1 !! i)) (m2 !! i)
  \226\134\146 partial_alter g i (merge f m1 m2) = merge f (partial_alter g1 i m1) m2.
Time Proof.
Time intro.
Time (apply map_eq).
Time (intros j).
Time (destruct (decide (i = j)); subst).
Time -
Time by rewrite (lookup_merge _), !lookup_partial_alter, !(lookup_merge _).
Time -
Time by rewrite (lookup_merge _), !lookup_partial_alter_ne, (lookup_merge _).
Time Qed.
Time
Lemma partial_alter_merge_r g g2 (m1 : M A) (m2 : M B) 
  i :
  g (f (m1 !! i) (m2 !! i)) = f (m1 !! i) (g2 (m2 !! i))
  \226\134\146 partial_alter g i (merge f m1 m2) = merge f m1 (partial_alter g2 i m2).
Time Proof.
Time intro.
Time (apply map_eq).
Time (intros j).
Time (destruct (decide (i = j)); subst).
Time -
Time by rewrite (lookup_merge _), !lookup_partial_alter, !(lookup_merge _).
Time -
Time by rewrite (lookup_merge _), !lookup_partial_alter_ne, (lookup_merge _).
Time Qed.
Time
Lemma insert_merge (m1 : M A) (m2 : M B) i x y z :
  f (Some y) (Some z) = Some x
  \226\134\146 <[i:=x]> (merge f m1 m2) = merge f (<[i:=y]> m1) (<[i:=z]> m2).
Time Proof.
Time by intros; apply partial_alter_merge.
Time Qed.
Time
Lemma delete_merge (m1 : M A) (m2 : M B) i :
  delete i (merge f m1 m2) = merge f (delete i m1) (delete i m2).
Time Proof.
Time by intros; apply partial_alter_merge.
Time Qed.
Time
Lemma merge_singleton i x y z :
  f (Some y) (Some z) = Some x
  \226\134\146 merge f ({[i := y]} : M A) ({[i := z]} : M B) = {[i := x]}.
Time Proof.
Time (intros).
Time by erewrite <- !insert_empty, <- insert_merge, merge_empty by eauto.
Time Qed.
Time
Lemma insert_merge_l (m1 : M A) (m2 : M B) i x y :
  f (Some y) (m2 !! i) = Some x
  \226\134\146 <[i:=x]> (merge f m1 m2) = merge f (<[i:=y]> m1) m2.
Time Proof.
Time by intros; apply partial_alter_merge_l.
Time Qed.
Time
Lemma insert_merge_r (m1 : M A) (m2 : M B) i x z :
  f (m1 !! i) (Some z) = Some x
  \226\134\146 <[i:=x]> (merge f m1 m2) = merge f m1 (<[i:=z]> m2).
Time Proof.
Time by intros; apply partial_alter_merge_r.
Time Qed.
Time End more_merge.
Time
Lemma map_lookup_zip_with {A} {B} {C} (f : A \226\134\146 B \226\134\146 C) 
  (m1 : M A) (m2 : M B) i :
  map_zip_with f m1 m2 !! i = x \226\134\144 m1 !! i; y \226\134\144 m2 !! i; Some (f x y).
Time Proof.
Time (unfold map_zip_with).
Time (rewrite lookup_merge by done).
Time by destruct (m1 !! i), (m2 !! i).
Time Qed.
Time
Lemma map_zip_with_empty {A} {B} {C} (f : A \226\134\146 B \226\134\146 C) :
  map_zip_with f (\226\136\133 : M A) (\226\136\133 : M B) = \226\136\133.
Time Proof.
Time (unfold map_zip_with).
Time by rewrite merge_empty by done.
Time Qed.
Time
Lemma map_insert_zip_with {A} {B} {C} (f : A \226\134\146 B \226\134\146 C) 
  (m1 : M A) (m2 : M B) i y z :
  <[i:=f y z]> (map_zip_with f m1 m2) =
  map_zip_with f (<[i:=y]> m1) (<[i:=z]> m2).
Time Proof.
Time (unfold map_zip_with).
Time by erewrite insert_merge by done.
Time Qed.
Time
Lemma map_delete_zip_with {A} {B} {C} (f : A \226\134\146 B \226\134\146 C) 
  (m1 : M A) (m2 : M B) i :
  delete i (map_zip_with f m1 m2) =
  map_zip_with f (delete i m1) (delete i m2).
Time Proof.
Time (unfold map_zip_with).
Time by rewrite delete_merge.
Time Qed.
Time
Lemma map_zip_with_singleton {A} {B} {C} (f : A \226\134\146 B \226\134\146 C) 
  i x y :
  map_zip_with f ({[i := x]} : M A) ({[i := y]} : M B) = {[i := f x y]}.
Time Proof.
Time (unfold map_zip_with).
Time by erewrite merge_singleton.
Time Qed.
Time
Lemma map_zip_with_fmap {A'} {A} {B'} {B} {C} (f : A \226\134\146 B \226\134\146 C) 
  (g1 : A' \226\134\146 A) (g2 : B' \226\134\146 B) (m1 : M A') (m2 : M B') :
  map_zip_with f (g1 <$> m1) (g2 <$> m2) =
  map_zip_with (\206\187 x y, f (g1 x) (g2 y)) m1 m2.
Time Proof.
Time (apply map_eq; intro i).
Time (rewrite !map_lookup_zip_with, !lookup_fmap).
Time by destruct (m1 !! i), (m2 !! i).
Time Qed.
Time
Lemma map_zip_with_fmap_1 {A'} {A} {B} {C} (f : A \226\134\146 B \226\134\146 C) 
  (g : A' \226\134\146 A) (m1 : M A') (m2 : M B) :
  map_zip_with f (g <$> m1) m2 = map_zip_with (\206\187 x y, f (g x) y) m1 m2.
Time Proof.
Time (rewrite <- (map_fmap_id m2)  at 1).
Time by rewrite map_zip_with_fmap.
Time Qed.
Time
Lemma map_zip_with_fmap_2 {A} {B'} {B} {C} (f : A \226\134\146 B \226\134\146 C) 
  (g : B' \226\134\146 B) (m1 : M A) (m2 : M B') :
  map_zip_with f m1 (g <$> m2) = map_zip_with (\206\187 x y, f x (g y)) m1 m2.
Time Proof.
Time (rewrite <- (map_fmap_id m1)  at 1).
Time by rewrite map_zip_with_fmap.
Time Qed.
Time
Lemma map_fmap_zip_with {A} {B} {C} {D} (f : A \226\134\146 B \226\134\146 C) 
  (g : C \226\134\146 D) m1 m2 :
  g <$> map_zip_with f m1 m2 = map_zip_with (\206\187 x y, g (f x y)) m1 m2.
Time Proof.
Time (apply map_eq; intro i).
Time (rewrite lookup_fmap, !map_lookup_zip_with).
Time by destruct (m1 !! i), (m2 !! i).
Time Qed.
Time
Lemma map_zip_with_flip {A} {B} {C} (f : A \226\134\146 B \226\134\146 C) 
  (m1 : M A) (m2 : M B) : map_zip_with (flip f) m2 m1 = map_zip_with f m1 m2.
Time Proof.
Time (apply map_eq; intro i).
Time (rewrite !map_lookup_zip_with).
Time by destruct (m1 !! i), (m2 !! i).
Time Qed.
Time
Lemma map_zip_with_map_zip {A} {B} {C} (f : A \226\134\146 B \226\134\146 C) 
  (m1 : M A) (m2 : M B) : map_zip_with f m1 m2 = curry f <$> map_zip m1 m2.
Time Proof.
Time (apply map_eq; intro i).
Time (rewrite lookup_fmap, !map_lookup_zip_with).
Time by destruct (m1 !! i), (m2 !! i).
Time Qed.
Time
Lemma map_fmap_zip {A'} {A} {B'} {B} (g1 : A' \226\134\146 A) 
  (g2 : B' \226\134\146 B) (m1 : M A') (m2 : M B') :
  map_zip (fmap g1 m1) (fmap g2 m2) = prod_map g1 g2 <$> map_zip m1 m2.
Time Proof.
Time (rewrite map_zip_with_fmap, map_zip_with_map_zip).
Time (generalize (map_zip m1 m2); intro m).
Time (apply map_eq; intro i).
Time by rewrite !lookup_fmap; destruct (m !! i) as [[x1 x2]| ].
Time Qed.
Time Section Forall2.
Time Context {A} {B} (R : A \226\134\146 B \226\134\146 Prop) (P : A \226\134\146 Prop) (Q : B \226\134\146 Prop).
Time
Context `{\226\136\128 x y, Decision (R x y)} `{\226\136\128 x, Decision (P x)}
 `{\226\136\128 y, Decision (Q y)}.
Time
Let f (mx : option A) (my : option B) : option bool :=
  match mx, my with
  | Some x, Some y => Some (bool_decide (R x y))
  | Some x, None => Some (bool_decide (P x))
  | None, Some y => Some (bool_decide (Q y))
  | None, None => None
  end.
Time
Lemma map_relation_alt (m1 : M A) (m2 : M B) :
  map_relation R P Q m1 m2 \226\134\148 map_Forall (\206\187 _, Is_true) (merge f m1 m2).
Time Proof.
Time split.
Time -
Time (intros Hm i P'; rewrite lookup_merge by done; intros).
Time specialize (Hm i).
Time
(destruct (m1 !! i), (m2 !! i); simplify_eq /=; auto using bool_decide_pack).
Time -
Time (intros Hm i).
Time specialize (Hm i).
Time (rewrite lookup_merge in Hm by done).
Time
(destruct (m1 !! i), (m2 !! i); simplify_eq /=; auto; by
  eapply bool_decide_unpack, Hm).
Time Qed.
Time #[global]
Instance map_relation_dec : (RelDecision (map_relation (M:=M) R P Q)).
Time Proof.
Time
(refine
  (\206\187 m1 m2, cast_if (decide (map_Forall (\206\187 _, Is_true) (merge f m1 m2))));
  abstract by rewrite map_relation_alt).
Time Defined.
Time
Lemma map_not_Forall2 (m1 : M A) (m2 : M B) :
  \194\172 map_relation R P Q m1 m2
  \226\134\148 (\226\136\131 i,
       (\226\136\131 x y, m1 !! i = Some x \226\136\167 m2 !! i = Some y \226\136\167 \194\172 R x y)
       \226\136\168 (\226\136\131 x, m1 !! i = Some x \226\136\167 m2 !! i = None \226\136\167 \194\172 P x)
         \226\136\168 (\226\136\131 y, m1 !! i = None \226\136\167 m2 !! i = Some y \226\136\167 \194\172 Q y)).
Time Proof.
Time split.
Time -
Time (rewrite map_relation_alt, (map_not_Forall _)).
Time (intros (i, (?, (Hm, ?))); exists i).
Time (rewrite lookup_merge in Hm by done).
Time
(destruct (m1 !! i), (m2 !! i); naive_solver auto  2 using bool_decide_pack).
Time -
Time (unfold map_relation, option_relation).
Time
by
 intros [i [(x, (y, (?, (?, ?))))| [(x, (?, (?, ?)))| (y, (?, (?, ?)))]]] Hm;
  specialize (Hm i); simplify_option_eq.
Time Qed.
Time End Forall2.
Time
Lemma map_disjoint_spec {A} (m1 m2 : M A) :
  m1 ##\226\130\152 m2 \226\134\148 (\226\136\128 i x y, m1 !! i = Some x \226\134\146 m2 !! i = Some y \226\134\146 False).
Time Proof.
Time
(split; intros Hm i; specialize (Hm i); destruct (m1 !! i), (m2 !! i);
  naive_solver).
Time Qed.
Time
Lemma map_disjoint_alt {A} (m1 m2 : M A) :
  m1 ##\226\130\152 m2 \226\134\148 (\226\136\128 i, m1 !! i = None \226\136\168 m2 !! i = None).
Time Proof.
Time
(split; intros Hm1m2 i; specialize (Hm1m2 i); destruct (m1 !! i), (m2 !! i);
  naive_solver).
Time Qed.
Time
Lemma map_not_disjoint {A} (m1 m2 : M A) :
  \194\172 m1 ##\226\130\152 m2 \226\134\148 (\226\136\131 i x1 x2, m1 !! i = Some x1 \226\136\167 m2 !! i = Some x2).
Time Proof.
Time (unfold disjoint, map_disjoint).
Time (rewrite map_not_Forall2 by solve_decision).
Time (split; [  | naive_solver ]).
Time
(intros [i [(x, (y, (?, (?, ?))))| [(x, (?, (?, [])))| (y, (?, (?, [])))]]];
  naive_solver).
Time Qed.
Time #[global]
Instance map_disjoint_sym : (Symmetric (map_disjoint : relation (M A))).
Time Proof.
Time (intros A m1 m2).
Time (rewrite !map_disjoint_spec).
Time naive_solver.
Time Qed.
Time Lemma map_disjoint_empty_l {A} (m : M A) : \226\136\133 ##\226\130\152 m.
Time Proof.
Time (rewrite !map_disjoint_spec).
Time (intros i x y).
Time by rewrite lookup_empty.
Time Qed.
Time Lemma map_disjoint_empty_r {A} (m : M A) : m ##\226\130\152 \226\136\133.
Time Proof.
Time (rewrite !map_disjoint_spec).
Time (intros i x y).
Time by rewrite lookup_empty.
Time Qed.
Time
Lemma map_disjoint_weaken {A} (m1 m1' m2 m2' : M A) :
  m1' ##\226\130\152 m2' \226\134\146 m1 \226\138\134 m1' \226\134\146 m2 \226\138\134 m2' \226\134\146 m1 ##\226\130\152 m2.
Time Proof.
Time (rewrite !map_subseteq_spec, !map_disjoint_spec).
Time eauto.
Time Qed.
Time
Lemma map_disjoint_weaken_l {A} (m1 m1' m2 : M A) :
  m1' ##\226\130\152 m2 \226\134\146 m1 \226\138\134 m1' \226\134\146 m1 ##\226\130\152 m2.
Time Proof.
Time eauto using map_disjoint_weaken.
Time Qed.
Time
Lemma map_disjoint_weaken_r {A} (m1 m2 m2' : M A) :
  m1 ##\226\130\152 m2' \226\134\146 m2 \226\138\134 m2' \226\134\146 m1 ##\226\130\152 m2.
Time Proof.
Time eauto using map_disjoint_weaken.
Time Qed.
Time
Lemma map_disjoint_Some_l {A} (m1 m2 : M A) i x :
  m1 ##\226\130\152 m2 \226\134\146 m1 !! i = Some x \226\134\146 m2 !! i = None.
Time Proof.
Time (rewrite map_disjoint_spec, eq_None_not_Some).
Time (intros ? ? [? ?]; eauto).
Time Qed.
Time
Lemma map_disjoint_Some_r {A} (m1 m2 : M A) i x :
  m1 ##\226\130\152 m2 \226\134\146 m2 !! i = Some x \226\134\146 m1 !! i = None.
Time Proof.
Time (rewrite (symmetry_iff map_disjoint)).
Time (apply map_disjoint_Some_l).
Time Qed.
Time
Lemma map_disjoint_singleton_l {A} (m : M A) i x :
  {[i := x]} ##\226\130\152 m \226\134\148 m !! i = None.
Time Proof.
Time (split; [  | rewrite !map_disjoint_spec ]).
Time -
Time intro.
Time
(apply (map_disjoint_Some_l {[i := x]} _ _ x); auto using lookup_singleton).
Time -
Time (intros ? j y1 y2).
Time (destruct (decide (i = j)) as [->| ]).
Time +
Time (rewrite lookup_singleton).
Time intuition congruence.
Time +
Time by rewrite lookup_singleton_ne.
Time Qed.
Time
Lemma map_disjoint_singleton_r {A} (m : M A) i x :
  m ##\226\130\152 {[i := x]} \226\134\148 m !! i = None.
Time Proof.
Time by rewrite (symmetry_iff map_disjoint), map_disjoint_singleton_l.
Time Qed.
Time
Lemma map_disjoint_singleton_l_2 {A} (m : M A) i x :
  m !! i = None \226\134\146 {[i := x]} ##\226\130\152 m.
Time Proof.
Time by rewrite map_disjoint_singleton_l.
Time Qed.
Time
Lemma map_disjoint_singleton_r_2 {A} (m : M A) i x :
  m !! i = None \226\134\146 m ##\226\130\152 {[i := x]}.
Time Proof.
Time by rewrite map_disjoint_singleton_r.
Time Qed.
Time
Lemma map_disjoint_delete_l {A} (m1 m2 : M A) i :
  m1 ##\226\130\152 m2 \226\134\146 delete i m1 ##\226\130\152 m2.
Time Proof.
Time (rewrite !map_disjoint_alt).
Time (intros Hdisjoint j).
Time (destruct (Hdisjoint j); auto).
Time (rewrite lookup_delete_None).
Time tauto.
Time Qed.
Time
Lemma map_disjoint_delete_r {A} (m1 m2 : M A) i :
  m1 ##\226\130\152 m2 \226\134\146 m1 ##\226\130\152 delete i m2.
Time Proof.
Time symmetry.
Time by apply map_disjoint_delete_l.
Time Qed.
Time Section union_with.
Time Context {A} (f : A \226\134\146 A \226\134\146 option A).
Time Implicit Type m : M A.
Time
Lemma lookup_union_with m1 m2 i :
  union_with f m1 m2 !! i = union_with f (m1 !! i) (m2 !! i).
Time Proof.
Time by rewrite <- (lookup_merge _).
Time Qed.
Time
Lemma lookup_union_with_Some m1 m2 i z :
  union_with f m1 m2 !! i = Some z
  \226\134\148 m1 !! i = Some z \226\136\167 m2 !! i = None
    \226\136\168 m1 !! i = None \226\136\167 m2 !! i = Some z
      \226\136\168 (\226\136\131 x y, m1 !! i = Some x \226\136\167 m2 !! i = Some y \226\136\167 f x y = Some z).
Time Proof.
Time (rewrite lookup_union_with).
Time (destruct (m1 !! i), (m2 !! i); compute; naive_solver).
Time Qed.
Time #[global]Instance: (LeftId (=@{M A} ) \226\136\133 (union_with f)).
Time Proof.
Time (unfold union_with, map_union_with).
Time (apply _).
Time Qed.
Time #[global]Instance: (RightId (=@{M A} ) \226\136\133 (union_with f)).
Time Proof.
Time (unfold union_with, map_union_with).
Time (apply _).
Time Qed.
Time
Lemma union_with_comm m1 m2 :
  (\226\136\128 i x y, m1 !! i = Some x \226\134\146 m2 !! i = Some y \226\134\146 f x y = f y x)
  \226\134\146 union_with f m1 m2 = union_with f m2 m1.
Time Proof.
Time (intros).
Time (apply (merge_comm _)).
Time (intros i).
Time (destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto).
Time Qed.
Time #[global]Instance: (Comm (=) f \226\134\146 Comm (=@{M A} ) (union_with f)).
Time Proof.
Time (intros ? ? ?).
Time (apply union_with_comm).
Time eauto.
Time Qed.
Time
Lemma union_with_idemp m :
  (\226\136\128 i x, m !! i = Some x \226\134\146 f x x = Some x) \226\134\146 union_with f m m = m.
Time Proof.
Time (intros).
Time (apply (merge_idemp _)).
Time (intros i).
Time (destruct (m !! i) eqn:?; simpl; eauto).
Time Qed.
Time
Lemma alter_union_with (g : A \226\134\146 A) m1 m2 i :
  (\226\136\128 x y, m1 !! i = Some x \226\134\146 m2 !! i = Some y \226\134\146 g <$> f x y = f (g x) (g y))
  \226\134\146 alter g i (union_with f m1 m2) =
    union_with f (alter g i m1) (alter g i m2).
Time Proof.
Time (intros).
Time (apply (partial_alter_merge _)).
Time (destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto).
Time Qed.
Time
Lemma alter_union_with_l (g : A \226\134\146 A) m1 m2 i :
  (\226\136\128 x y, m1 !! i = Some x \226\134\146 m2 !! i = Some y \226\134\146 g <$> f x y = f (g x) y)
  \226\134\146 (\226\136\128 y, m1 !! i = None \226\134\146 m2 !! i = Some y \226\134\146 g y = y)
    \226\134\146 alter g i (union_with f m1 m2) = union_with f (alter g i m1) m2.
Time Proof.
Time (intros).
Time (apply (partial_alter_merge_l _)).
Time (destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; f_equal /=; auto).
Time Qed.
Time
Lemma alter_union_with_r (g : A \226\134\146 A) m1 m2 i :
  (\226\136\128 x y, m1 !! i = Some x \226\134\146 m2 !! i = Some y \226\134\146 g <$> f x y = f x (g y))
  \226\134\146 (\226\136\128 x, m1 !! i = Some x \226\134\146 m2 !! i = None \226\134\146 g x = x)
    \226\134\146 alter g i (union_with f m1 m2) = union_with f m1 (alter g i m2).
Time Proof.
Time (intros).
Time (apply (partial_alter_merge_r _)).
Time (destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; f_equal /=; auto).
Time Qed.
Time
Lemma delete_union_with m1 m2 i :
  delete i (union_with f m1 m2) = union_with f (delete i m1) (delete i m2).
Time Proof.
Time by apply (partial_alter_merge _).
Time Qed.
Time
Lemma foldr_delete_union_with (m1 m2 : M A) is :
  foldr delete (union_with f m1 m2) is =
  union_with f (foldr delete m1 is) (foldr delete m2 is).
Time Proof.
Time (induction is; simpl).
Time done.
Time by rewrite IHis, delete_union_with.
Time Qed.
Time
Lemma insert_union_with m1 m2 i x y z :
  f x y = Some z
  \226\134\146 <[i:=z]> (union_with f m1 m2) = union_with f (<[i:=x]> m1) (<[i:=y]> m2).
Time Proof.
Time by intros; apply (partial_alter_merge _).
Time Qed.
Time
Lemma insert_union_with_l m1 m2 i x :
  m2 !! i = None
  \226\134\146 <[i:=x]> (union_with f m1 m2) = union_with f (<[i:=x]> m1) m2.
Time Proof.
Time (intros Hm2).
Time (unfold union_with, map_union_with).
Time by erewrite (insert_merge_l _) by by rewrite Hm2.
Time Qed.
Time
Lemma insert_union_with_r m1 m2 i x :
  m1 !! i = None
  \226\134\146 <[i:=x]> (union_with f m1 m2) = union_with f m1 (<[i:=x]> m2).
Time Proof.
Time (intros Hm1).
Time (unfold union_with, map_union_with).
Time by erewrite (insert_merge_r _) by by rewrite Hm1.
Time Qed.
Time End union_with.
Time #[global]Instance: (LeftId (=@{M A} ) \226\136\133 (\226\136\170)) := _.
Time #[global]Instance: (RightId (=@{M A} ) \226\136\133 (\226\136\170)) := _.
Time #[global]Instance: (Assoc (=@{M A} ) (\226\136\170)).
Time Proof.
Time (intros A m1 m2 m3).
Time (unfold union, map_union, union_with, map_union_with).
Time (apply (merge_assoc _)).
Time (intros i).
Time by destruct (m1 !! i), (m2 !! i), (m3 !! i).
Time Qed.
Time #[global]Instance: (IdemP (=@{M A} ) (\226\136\170)).
Time Proof.
Time (intros A ?).
Time by apply union_with_idemp.
Time Qed.
Time
Lemma lookup_union {A} (m1 m2 : M A) i :
  (m1 \226\136\170 m2) !! i = union_with (\206\187 x _, Some x) (m1 !! i) (m2 !! i).
Time Proof.
Time (apply lookup_union_with).
Time Qed.
Time
Lemma lookup_union_r {A} (m1 m2 : M A) i :
  m1 !! i = None \226\134\146 (m1 \226\136\170 m2) !! i = m2 !! i.
Time Proof.
Time (intros Hi).
Time by rewrite lookup_union, Hi, (left_id_L _ _).
Time Qed.
Time
Lemma lookup_union_Some_raw {A} (m1 m2 : M A) i x :
  (m1 \226\136\170 m2) !! i = Some x
  \226\134\148 m1 !! i = Some x \226\136\168 m1 !! i = None \226\136\167 m2 !! i = Some x.
Time Proof.
Time (rewrite lookup_union).
Time (destruct (m1 !! i), (m2 !! i); naive_solver).
Time Qed.
Time
Lemma lookup_union_None {A} (m1 m2 : M A) i :
  (m1 \226\136\170 m2) !! i = None \226\134\148 m1 !! i = None \226\136\167 m2 !! i = None.
Time Proof.
Time (rewrite lookup_union).
Time (destruct (m1 !! i), (m2 !! i); naive_solver).
Time Qed.
Time Lemma map_positive_l {A} (m1 m2 : M A) : m1 \226\136\170 m2 = \226\136\133 \226\134\146 m1 = \226\136\133.
Time Proof.
Time (intros Hm).
Time (apply map_empty).
Time (intros i).
Time (apply (f_equal (!!i)) in Hm).
Time (rewrite lookup_empty, lookup_union_None in Hm; tauto).
Time Qed.
Time Lemma map_positive_l_alt {A} (m1 m2 : M A) : m1 \226\137\160 \226\136\133 \226\134\146 m1 \226\136\170 m2 \226\137\160 \226\136\133.
Time Proof.
Time eauto using map_positive_l.
Time Qed.
Time
Lemma lookup_union_Some {A} (m1 m2 : M A) i x :
  m1 ##\226\130\152 m2 \226\134\146 (m1 \226\136\170 m2) !! i = Some x \226\134\148 m1 !! i = Some x \226\136\168 m2 !! i = Some x.
Time Proof.
Time (intros Hdisjoint).
Time (rewrite lookup_union_Some_raw).
Time intuition eauto using map_disjoint_Some_r.
Time Qed.
Time
Lemma lookup_union_Some_l {A} (m1 m2 : M A) i x :
  m1 !! i = Some x \226\134\146 (m1 \226\136\170 m2) !! i = Some x.
Time Proof.
Time intro.
Time (rewrite lookup_union_Some_raw; intuition).
Time Qed.
Time
Lemma lookup_union_Some_r {A} (m1 m2 : M A) i x :
  m1 ##\226\130\152 m2 \226\134\146 m2 !! i = Some x \226\134\146 (m1 \226\136\170 m2) !! i = Some x.
Time Proof.
Time intro.
Time (rewrite lookup_union_Some; intuition).
Time Qed.
Time Lemma map_union_comm {A} (m1 m2 : M A) : m1 ##\226\130\152 m2 \226\134\146 m1 \226\136\170 m2 = m2 \226\136\170 m1.
Time Proof.
Time (intros Hdisjoint).
Time (apply (merge_comm (union_with (\206\187 x _, Some x)))).
Time (intros i).
Time specialize (Hdisjoint i).
Time (destruct (m1 !! i), (m2 !! i); compute; naive_solver).
Time Qed.
Time Lemma map_subseteq_union {A} (m1 m2 : M A) : m1 \226\138\134 m2 \226\134\146 m1 \226\136\170 m2 = m2.
Time Proof.
Time (rewrite map_subseteq_spec).
Time (intros Hm1m2).
Time (apply map_eq).
Time (intros i).
Time (apply option_eq).
Time (intros x).
Time (rewrite lookup_union_Some_raw).
Time (split; [ by intuition |  ]).
Time (intros Hm2).
Time specialize (Hm1m2 i).
Time (destruct (m1 !! i) as [y| ]; [  | by auto ]).
Time (rewrite (Hm1m2 y eq_refl) in Hm2).
Time intuition congruence.
Time Qed.
Time Lemma map_union_subseteq_l {A} (m1 m2 : M A) : m1 \226\138\134 m1 \226\136\170 m2.
Time Proof.
Time (rewrite map_subseteq_spec).
Time (intros ? i x).
Time (rewrite lookup_union_Some_raw).
Time tauto.
Time Qed.
Time Lemma map_union_subseteq_r {A} (m1 m2 : M A) : m1 ##\226\130\152 m2 \226\134\146 m2 \226\138\134 m1 \226\136\170 m2.
Time Proof.
Time (intros).
Time (rewrite map_union_comm by done).
Time by apply map_union_subseteq_l.
Time Qed.
Time
Lemma map_union_subseteq_l_alt {A} (m1 m2 m3 : M A) : m1 \226\138\134 m2 \226\134\146 m1 \226\138\134 m2 \226\136\170 m3.
Time Proof.
Time (intros).
Time (trans m2; auto using map_union_subseteq_l).
Time Qed.
Time
Lemma map_union_subseteq_r_alt {A} (m1 m2 m3 : M A) :
  m2 ##\226\130\152 m3 \226\134\146 m1 \226\138\134 m3 \226\134\146 m1 \226\138\134 m2 \226\136\170 m3.
Time Proof.
Time (intros).
Time (trans m3; auto using map_union_subseteq_r).
Time Qed.
Time
Lemma map_union_mono_l {A} (m1 m2 m3 : M A) : m1 \226\138\134 m2 \226\134\146 m3 \226\136\170 m1 \226\138\134 m3 \226\136\170 m2.
Time Proof.
Time (rewrite !map_subseteq_spec).
Time (intros ? ? ?).
Time (rewrite !lookup_union_Some_raw).
Time naive_solver.
Time Qed.
Time
Lemma map_union_mono_r {A} (m1 m2 m3 : M A) :
  m2 ##\226\130\152 m3 \226\134\146 m1 \226\138\134 m2 \226\134\146 m1 \226\136\170 m3 \226\138\134 m2 \226\136\170 m3.
Time Proof.
Time (intros).
Time (rewrite !(map_union_comm _ m3) by eauto using map_disjoint_weaken_l).
Time by apply map_union_mono_l.
Time Qed.
Time
Lemma map_union_reflecting_l {A} (m1 m2 m3 : M A) :
  m3 ##\226\130\152 m1 \226\134\146 m3 ##\226\130\152 m2 \226\134\146 m3 \226\136\170 m1 \226\138\134 m3 \226\136\170 m2 \226\134\146 m1 \226\138\134 m2.
Time Proof.
Time (rewrite !map_subseteq_spec).
Time (intros Hm31 Hm32 Hm i x ?).
Time specialize (Hm i x).
Time (rewrite !lookup_union_Some in Hm by done).
Time (destruct Hm; auto).
Time by rewrite map_disjoint_spec in Hm31; destruct (Hm31 i x x).
Time Qed.
Time
Lemma map_union_reflecting_r {A} (m1 m2 m3 : M A) :
  m1 ##\226\130\152 m3 \226\134\146 m2 ##\226\130\152 m3 \226\134\146 m1 \226\136\170 m3 \226\138\134 m2 \226\136\170 m3 \226\134\146 m1 \226\138\134 m2.
Time Proof.
Time (intros ? ?).
Time (rewrite !(map_union_comm _ m3) by done).
Time by apply map_union_reflecting_l.
Time Qed.
Time
Lemma map_union_cancel_l {A} (m1 m2 m3 : M A) :
  m1 ##\226\130\152 m3 \226\134\146 m2 ##\226\130\152 m3 \226\134\146 m3 \226\136\170 m1 = m3 \226\136\170 m2 \226\134\146 m1 = m2.
Time Proof.
Time (intros).
Time
(apply (anti_symm (\226\138\134)); apply map_union_reflecting_l with m3; auto
  using (reflexive_eq (R:=(\226\138\134@{M A} )))).
Time Qed.
Time
Lemma map_union_cancel_r {A} (m1 m2 m3 : M A) :
  m1 ##\226\130\152 m3 \226\134\146 m2 ##\226\130\152 m3 \226\134\146 m1 \226\136\170 m3 = m2 \226\136\170 m3 \226\134\146 m1 = m2.
Time Proof.
Time (intros).
Time
(apply (anti_symm (\226\138\134)); apply map_union_reflecting_r with m3; auto
  using (reflexive_eq (R:=(\226\138\134@{M A} )))).
Time Qed.
Time
Lemma map_disjoint_union_l {A} (m1 m2 m3 : M A) :
  m1 \226\136\170 m2 ##\226\130\152 m3 \226\134\148 m1 ##\226\130\152 m3 \226\136\167 m2 ##\226\130\152 m3.
Time Proof.
Time (rewrite !map_disjoint_alt).
Time setoid_rewrite lookup_union_None.
Time naive_solver.
Time Qed.
Time
Lemma map_disjoint_union_r {A} (m1 m2 m3 : M A) :
  m1 ##\226\130\152 m2 \226\136\170 m3 \226\134\148 m1 ##\226\130\152 m2 \226\136\167 m1 ##\226\130\152 m3.
Time Proof.
Time (rewrite !map_disjoint_alt).
Time setoid_rewrite lookup_union_None.
Time naive_solver.
Time Qed.
Time
Lemma map_disjoint_union_l_2 {A} (m1 m2 m3 : M A) :
  m1 ##\226\130\152 m3 \226\134\146 m2 ##\226\130\152 m3 \226\134\146 m1 \226\136\170 m2 ##\226\130\152 m3.
Time Proof.
Time by rewrite map_disjoint_union_l.
Time Qed.
Time
Lemma map_disjoint_union_r_2 {A} (m1 m2 m3 : M A) :
  m1 ##\226\130\152 m2 \226\134\146 m1 ##\226\130\152 m3 \226\134\146 m1 ##\226\130\152 m2 \226\136\170 m3.
Time Proof.
Time by rewrite map_disjoint_union_r.
Time Qed.
Time
Lemma insert_union_singleton_l {A} (m : M A) i x :
  <[i:=x]> m = {[i := x]} \226\136\170 m.
Time Proof.
Time (apply map_eq).
Time (intros j).
Time (apply option_eq).
Time (intros y).
Time (rewrite lookup_union_Some_raw).
Time (destruct (decide (i = j)); subst).
Time -
Time (rewrite !lookup_singleton, lookup_insert).
Time intuition congruence.
Time -
Time (rewrite !lookup_singleton_ne, lookup_insert_ne; intuition congruence).
Time Qed.
Time
Lemma insert_union_singleton_r {A} (m : M A) i x :
  m !! i = None \226\134\146 <[i:=x]> m = m \226\136\170 {[i := x]}.
Time Proof.
Time intro.
Time (rewrite insert_union_singleton_l, map_union_comm; [ done |  ]).
Time by apply map_disjoint_singleton_l.
Time Qed.
Time
Lemma map_disjoint_insert_l {A} (m1 m2 : M A) i x :
  <[i:=x]> m1 ##\226\130\152 m2 \226\134\148 m2 !! i = None \226\136\167 m1 ##\226\130\152 m2.
Time Proof.
Time (rewrite insert_union_singleton_l).
Time by rewrite map_disjoint_union_l, map_disjoint_singleton_l.
Time Qed.
Time
Lemma map_disjoint_insert_r {A} (m1 m2 : M A) i x :
  m1 ##\226\130\152 <[i:=x]> m2 \226\134\148 m1 !! i = None \226\136\167 m1 ##\226\130\152 m2.
Time Proof.
Time (rewrite insert_union_singleton_l).
Time by rewrite map_disjoint_union_r, map_disjoint_singleton_r.
Time Qed.
Time
Lemma map_disjoint_insert_l_2 {A} (m1 m2 : M A) i 
  x : m2 !! i = None \226\134\146 m1 ##\226\130\152 m2 \226\134\146 <[i:=x]> m1 ##\226\130\152 m2.
Time Proof.
Time by rewrite map_disjoint_insert_l.
Time Qed.
Time
Lemma map_disjoint_insert_r_2 {A} (m1 m2 : M A) i 
  x : m1 !! i = None \226\134\146 m1 ##\226\130\152 m2 \226\134\146 m1 ##\226\130\152 <[i:=x]> m2.
Time Proof.
Time by rewrite map_disjoint_insert_r.
Time Qed.
Time
Lemma insert_union_l {A} (m1 m2 : M A) i x :
  <[i:=x]> (m1 \226\136\170 m2) = <[i:=x]> m1 \226\136\170 m2.
Time Proof.
Time by rewrite !insert_union_singleton_l, (assoc_L (\226\136\170)).
Time Qed.
Time
Lemma insert_union_r {A} (m1 m2 : M A) i x :
  m1 !! i = None \226\134\146 <[i:=x]> (m1 \226\136\170 m2) = m1 \226\136\170 <[i:=x]> m2.
Time Proof.
Time intro.
Time (rewrite !insert_union_singleton_l, !(assoc_L (\226\136\170))).
Time (rewrite (map_union_comm m1); [ done |  ]).
Time by apply map_disjoint_singleton_r.
Time Qed.
Time
Lemma foldr_insert_union {A} (m : M A) l :
  foldr (\206\187 p, <[p.1:=p.2]>) m l = list_to_map l \226\136\170 m.
Time Proof.
Time (induction l as [| i l IH]; simpl; [ by rewrite (left_id_L _ _) |  ]).
Time by rewrite IH, insert_union_l.
Time Qed.
Time
Lemma delete_union {A} (m1 m2 : M A) i :
  delete i (m1 \226\136\170 m2) = delete i m1 \226\136\170 delete i m2.
Time Proof.
Time (apply delete_union_with).
Time Qed.
Time
Lemma map_Forall_union_11 {A} (m1 m2 : M A) P :
  map_Forall P (m1 \226\136\170 m2) \226\134\146 map_Forall P m1.
Time Proof.
Time (intros HP i x ?).
Time (apply HP, lookup_union_Some_raw; auto).
Time Qed.
Time
Lemma map_Forall_union_12 {A} (m1 m2 : M A) P :
  m1 ##\226\130\152 m2 \226\134\146 map_Forall P (m1 \226\136\170 m2) \226\134\146 map_Forall P m2.
Time Proof.
Time (intros ? HP i x ?).
Time (apply HP, lookup_union_Some; auto).
Time Qed.
Time
Lemma map_Forall_union_2 {A} (m1 m2 : M A) P :
  map_Forall P m1 \226\134\146 map_Forall P m2 \226\134\146 map_Forall P (m1 \226\136\170 m2).
Time Proof.
Time (intros ? ? ? ? [| []]%lookup_union_Some_raw; eauto).
Time Qed.
Time
Lemma map_Forall_union {A} (m1 m2 : M A) P :
  m1 ##\226\130\152 m2 \226\134\146 map_Forall P (m1 \226\136\170 m2) \226\134\148 map_Forall P m1 \226\136\167 map_Forall P m2.
Time Proof.
Time
naive_solver eauto
 using map_Forall_union_11, map_Forall_union_12, map_Forall_union_2.
Time Qed.
Time
Lemma map_disjoint_union_list_l {A} (ms : list (M A)) 
  (m : M A) : \226\139\131 ms ##\226\130\152 m \226\134\148 Forall (.##\226\130\152m) ms.
Time Proof.
Time split.
Time -
Time (induction ms; simpl; rewrite ?map_disjoint_union_l; intuition).
Time -
Time (induction 1; simpl; [ apply map_disjoint_empty_l |  ]).
Time by rewrite map_disjoint_union_l.
Time Qed.
Time
Lemma map_disjoint_union_list_r {A} (ms : list (M A)) 
  (m : M A) : m ##\226\130\152 \226\139\131 ms \226\134\148 Forall (.##\226\130\152m) ms.
Time Proof.
Time by rewrite (symmetry_iff map_disjoint), map_disjoint_union_list_l.
Time Qed.
Time
Lemma map_disjoint_union_list_l_2 {A} (ms : list (M A)) 
  (m : M A) : Forall (.##\226\130\152m) ms \226\134\146 \226\139\131 ms ##\226\130\152 m.
Time Proof.
Time by rewrite map_disjoint_union_list_l.
Time Qed.
Time
Lemma map_disjoint_union_list_r_2 {A} (ms : list (M A)) 
  (m : M A) : Forall (.##\226\130\152m) ms \226\134\146 m ##\226\130\152 \226\139\131 ms.
Time Proof.
Time by rewrite map_disjoint_union_list_r.
Time Qed.
Time
Lemma lookup_foldr_delete {A} (m : M A) is j :
  j \226\136\136 is \226\134\146 foldr delete m is !! j = None.
Time Proof.
Time (induction 1 as [| i j is]; simpl; [ by rewrite lookup_delete |  ]).
Time
by
 destruct (decide (i = j)) as [->| ?];
  rewrite ?lookup_delete, ?lookup_delete_ne by done.
Time Qed.
Time
Lemma lookup_foldr_delete_not_elem_of {A} (m : M A) 
  is j : j \226\136\137 is \226\134\146 foldr delete m is !! j = m !! j.
Time Proof.
Time (induction is; simpl; [ done |  ]).
Time (rewrite elem_of_cons; intros).
Time (rewrite lookup_delete_ne; intuition).
Time Qed.
Time
Lemma lookup_foldr_delete_Some {A} (m : M A) is j 
  y : foldr delete m is !! j = Some y \226\134\148 (j \226\136\137 is) \226\136\167 m !! j = Some y.
Time Proof.
Time (induction is; simpl; rewrite ?lookup_delete_Some; set_solver).
Time Qed.
Time
Lemma foldr_delete_notin {A} (m : M A) is :
  Forall (\206\187 i, m !! i = None) is \226\134\146 foldr delete m is = m.
Time Proof.
Time (induction 1; simpl; [ done |  ]).
Time (rewrite delete_notin; congruence).
Time Qed.
Time
Lemma foldr_delete_commute {A} (m : M A) is j :
  delete j (foldr delete m is) = foldr delete (delete j m) is.
Time Proof.
Time (induction is as [| ? ? IH]; [ done |  ]).
Time (simpl).
Time by rewrite delete_commute, IH.
Time Qed.
Time
Lemma foldr_delete_insert {A} (m : M A) is j x :
  j \226\136\136 is \226\134\146 foldr delete (<[j:=x]> m) is = foldr delete m is.
Time Proof.
Time (induction 1 as [i is| j i is ? IH]; simpl; [  | by rewrite IH ]).
Time by rewrite !foldr_delete_commute, delete_insert_delete.
Time Qed.
Time
Lemma foldr_delete_insert_ne {A} (m : M A) is j x :
  j \226\136\137 is \226\134\146 foldr delete (<[j:=x]> m) is = <[j:=x]> (foldr delete m is).
Time Proof.
Time (induction is; simpl; [ done |  ]).
Time (rewrite elem_of_cons).
Time (intros).
Time (rewrite IHis, delete_insert_ne; intuition).
Time Qed.
Time
Lemma map_disjoint_foldr_delete_l {A} (m1 m2 : M A) 
  is : m1 ##\226\130\152 m2 \226\134\146 foldr delete m1 is ##\226\130\152 m2.
Time Proof.
Time (induction is; simpl; auto using map_disjoint_delete_l).
Time Qed.
Time
Lemma map_disjoint_foldr_delete_r {A} (m1 m2 : M A) 
  is : m1 ##\226\130\152 m2 \226\134\146 m1 ##\226\130\152 foldr delete m2 is.
Time Proof.
Time (induction is; simpl; auto using map_disjoint_delete_r).
Time Qed.
Time
Lemma foldr_delete_union {A} (m1 m2 : M A) is :
  foldr delete (m1 \226\136\170 m2) is = foldr delete m1 is \226\136\170 foldr delete m2 is.
Time Proof.
Time (apply foldr_delete_union_with).
Time Qed.
Time
Lemma map_disjoint_list_to_map_l {A} (m : M A) ixs :
  list_to_map ixs ##\226\130\152 m \226\134\148 Forall (\206\187 ix, m !! ix.1 = None) ixs.
Time Proof.
Time split.
Time -
Time (induction ixs; simpl; rewrite ?map_disjoint_insert_l in *; intuition).
Time -
Time (induction 1; simpl; [ apply map_disjoint_empty_l |  ]).
Time (rewrite map_disjoint_insert_l).
Time auto.
Time Qed.
Time
Lemma map_disjoint_list_to_map_r {A} (m : M A) ixs :
  m ##\226\130\152 list_to_map ixs \226\134\148 Forall (\206\187 ix, m !! ix.1 = None) ixs.
Time Proof.
Time by rewrite (symmetry_iff map_disjoint), map_disjoint_list_to_map_l.
Time Qed.
Time
Lemma map_disjoint_list_to_map_zip_l {A} (m : M A) 
  is xs :
  length is = length xs
  \226\134\146 list_to_map (zip is xs) ##\226\130\152 m \226\134\148 Forall (\206\187 i, m !! i = None) is.
Time Proof.
Time intro.
Time (rewrite map_disjoint_list_to_map_l).
Time (rewrite <- (fst_zip is xs)  at 2 by lia).
Time by rewrite Forall_fmap.
Time Qed.
Time
Lemma map_disjoint_list_to_map_zip_r {A} (m : M A) 
  is xs :
  length is = length xs
  \226\134\146 m ##\226\130\152 list_to_map (zip is xs) \226\134\148 Forall (\206\187 i, m !! i = None) is.
Time Proof.
Time intro.
Time by rewrite (symmetry_iff map_disjoint), map_disjoint_list_to_map_zip_l.
Time Qed.
Time
Lemma map_disjoint_list_to_map_zip_l_2 {A} (m : M A) 
  is xs :
  length is = length xs
  \226\134\146 Forall (\206\187 i, m !! i = None) is \226\134\146 list_to_map (zip is xs) ##\226\130\152 m.
Time Proof.
Time intro.
Time by rewrite map_disjoint_list_to_map_zip_l.
Time Qed.
Time
Lemma map_disjoint_list_to_map_zip_r_2 {A} (m : M A) 
  is xs :
  length is = length xs
  \226\134\146 Forall (\206\187 i, m !! i = None) is \226\134\146 m ##\226\130\152 list_to_map (zip is xs).
Time Proof.
Time intro.
Time by rewrite map_disjoint_list_to_map_zip_r.
Time Qed.
Time Section intersection_with.
Time Context {A} (f : A \226\134\146 A \226\134\146 option A).
Time Implicit Type m : M A.
Time #[global]Instance: (LeftAbsorb (=@{M A} ) \226\136\133 (intersection_with f)).
Time Proof.
Time (unfold intersection_with, map_intersection_with).
Time (apply _).
Time Qed.
Time #[global]Instance: (RightAbsorb (=@{M A} ) \226\136\133 (intersection_with f)).
Time Proof.
Time (unfold intersection_with, map_intersection_with).
Time (apply _).
Time Qed.
Time
Lemma lookup_intersection_with m1 m2 i :
  intersection_with f m1 m2 !! i = intersection_with f (m1 !! i) (m2 !! i).
Time Proof.
Time by rewrite <- (lookup_merge _).
Time Qed.
Time
Lemma lookup_intersection_with_Some m1 m2 i z :
  intersection_with f m1 m2 !! i = Some z
  \226\134\148 (\226\136\131 x y, m1 !! i = Some x \226\136\167 m2 !! i = Some y \226\136\167 f x y = Some z).
Time Proof.
Time (rewrite lookup_intersection_with).
Time (destruct (m1 !! i), (m2 !! i); compute; naive_solver).
Time Qed.
Time
Lemma intersection_with_comm m1 m2 :
  (\226\136\128 i x y, m1 !! i = Some x \226\134\146 m2 !! i = Some y \226\134\146 f x y = f y x)
  \226\134\146 intersection_with f m1 m2 = intersection_with f m2 m1.
Time Proof.
Time (intros).
Time (apply (merge_comm _)).
Time (intros i).
Time (destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto).
Time Qed.
Time #[global]Instance: (Comm (=) f \226\134\146 Comm (=@{M A} ) (intersection_with f)).
Time Proof.
Time (intros ? ? ?).
Time (apply intersection_with_comm).
Time eauto.
Time Qed.
Time
Lemma intersection_with_idemp m :
  (\226\136\128 i x, m !! i = Some x \226\134\146 f x x = Some x) \226\134\146 intersection_with f m m = m.
Time Proof.
Time (intros).
Time (apply (merge_idemp _)).
Time (intros i).
Time (destruct (m !! i) eqn:?; simpl; eauto).
Time Qed.
Time
Lemma alter_intersection_with (g : A \226\134\146 A) m1 m2 i :
  (\226\136\128 x y, m1 !! i = Some x \226\134\146 m2 !! i = Some y \226\134\146 g <$> f x y = f (g x) (g y))
  \226\134\146 alter g i (intersection_with f m1 m2) =
    intersection_with f (alter g i m1) (alter g i m2).
Time Proof.
Time (intros).
Time (apply (partial_alter_merge _)).
Time (destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto).
Time Qed.
Time
Lemma delete_intersection_with m1 m2 i :
  delete i (intersection_with f m1 m2) =
  intersection_with f (delete i m1) (delete i m2).
Time Proof.
Time by apply (partial_alter_merge _).
Time Qed.
Time
Lemma foldr_delete_intersection_with (m1 m2 : M A) 
  is :
  foldr delete (intersection_with f m1 m2) is =
  intersection_with f (foldr delete m1 is) (foldr delete m2 is).
Time Proof.
Time (induction is; simpl).
Time done.
Time by rewrite IHis, delete_intersection_with.
Time Qed.
Time
Lemma insert_intersection_with m1 m2 i x y z :
  f x y = Some z
  \226\134\146 <[i:=z]> (intersection_with f m1 m2) =
    intersection_with f (<[i:=x]> m1) (<[i:=y]> m2).
Time Proof.
Time by intros; apply (partial_alter_merge _).
Time Qed.
Time End intersection_with.
Time #[global]Instance: (LeftAbsorb (=@{M A} ) \226\136\133 (\226\136\169)) := _.
Time #[global]Instance: (RightAbsorb (=@{M A} ) \226\136\133 (\226\136\169)) := _.
Time #[global]Instance: (Assoc (=@{M A} ) (\226\136\169)).
Time Proof.
Time (intros A m1 m2 m3).
Time
(unfold intersection, map_intersection, intersection_with,
  map_intersection_with).
Time (apply (merge_assoc _)).
Time (intros i).
Time by destruct (m1 !! i), (m2 !! i), (m3 !! i).
Time Qed.
Time #[global]Instance: (IdemP (=@{M A} ) (\226\136\169)).
Time Proof.
Time (intros A ?).
Time by apply intersection_with_idemp.
Time Qed.
Time
Lemma lookup_intersection_Some {A} (m1 m2 : M A) i 
  x : (m1 \226\136\169 m2) !! i = Some x \226\134\148 m1 !! i = Some x \226\136\167 is_Some (m2 !! i).
Time Proof.
Time (unfold intersection, map_intersection).
Time (rewrite lookup_intersection_with).
Time (destruct (m1 !! i), (m2 !! i); compute; naive_solver).
Time Qed.
Time
Lemma lookup_intersection_None {A} (m1 m2 : M A) i :
  (m1 \226\136\169 m2) !! i = None \226\134\148 m1 !! i = None \226\136\168 m2 !! i = None.
Time Proof.
Time (unfold intersection, map_intersection).
Time (rewrite lookup_intersection_with).
Time (destruct (m1 !! i), (m2 !! i); compute; naive_solver).
Time Qed.
Time
Lemma lookup_difference_with {A} (f : A \226\134\146 A \226\134\146 option A) 
  (m1 m2 : M A) i :
  difference_with f m1 m2 !! i = difference_with f (m1 !! i) (m2 !! i).
Time Proof.
Time by rewrite <- lookup_merge by done.
Time Qed.
Time
Lemma lookup_difference_with_Some {A} (f : A \226\134\146 A \226\134\146 option A) 
  (m1 m2 : M A) i z :
  difference_with f m1 m2 !! i = Some z
  \226\134\148 m1 !! i = Some z \226\136\167 m2 !! i = None
    \226\136\168 (\226\136\131 x y, m1 !! i = Some x \226\136\167 m2 !! i = Some y \226\136\167 f x y = Some z).
Time Proof.
Time (rewrite lookup_difference_with).
Time (destruct (m1 !! i), (m2 !! i); compute; naive_solver).
Time Qed.
Time
Lemma lookup_difference_Some {A} (m1 m2 : M A) i x :
  (m1 \226\136\150 m2) !! i = Some x \226\134\148 m1 !! i = Some x \226\136\167 m2 !! i = None.
Time Proof.
Time (unfold difference, map_difference; rewrite lookup_difference_with).
Time (destruct (m1 !! i), (m2 !! i); compute; intuition congruence).
Time Qed.
Time
Lemma lookup_difference_None {A} (m1 m2 : M A) i :
  (m1 \226\136\150 m2) !! i = None \226\134\148 m1 !! i = None \226\136\168 is_Some (m2 !! i).
Time Proof.
Time (unfold difference, map_difference; rewrite lookup_difference_with).
Time (destruct (m1 !! i), (m2 !! i); compute; naive_solver).
Time Qed.
Time
Lemma map_disjoint_difference_l {A} (m1 m2 : M A) : m1 \226\138\134 m2 \226\134\146 m2 \226\136\150 m1 ##\226\130\152 m1.
Time Proof.
Time (intros Hm i; specialize (Hm i)).
Time (unfold difference, map_difference; rewrite lookup_difference_with).
Time by destruct (m1 !! i), (m2 !! i).
Time Qed.
Time
Lemma map_disjoint_difference_r {A} (m1 m2 : M A) : m1 \226\138\134 m2 \226\134\146 m1 ##\226\130\152 m2 \226\136\150 m1.
Time Proof.
Time (intros).
Time symmetry.
Time by apply map_disjoint_difference_l.
Time Qed.
Time
Lemma map_difference_union {A} (m1 m2 : M A) : m1 \226\138\134 m2 \226\134\146 m1 \226\136\170 m2 \226\136\150 m1 = m2.
Time Proof.
Time (rewrite map_subseteq_spec).
Time intro Hm1m2.
Time (apply map_eq).
Time (intros i).
Time (apply option_eq).
Time (intros v).
Time specialize (Hm1m2 i).
Time
(unfold difference, map_difference, difference_with, map_difference_with).
Time (rewrite lookup_union_Some_raw, (lookup_merge _)).
Time
(destruct (m1 !! i) as [x'| ], (m2 !! i); try specialize (Hm1m2 x'); compute;
  intuition congruence).
Time Qed.
Time Lemma map_difference_diag {A} (m : M A) : m \226\136\150 m = \226\136\133.
Time Proof.
Time (apply map_empty; intros i).
Time (rewrite lookup_difference_None).
Time (destruct (m !! i); eauto).
Time Qed.
Time End theorems.
Time Section map_seq.
Time Context `{FinMap nat M} {A : Type}.
Time Implicit Type x : A.
Time Implicit Type xs : list A.
Time
Lemma lookup_map_seq_Some_inv start xs i x :
  xs !! i = Some x \226\134\148 map_seq (M:=M A) start xs !! (start + i) = Some x.
Time Proof.
Time revert start i.
Time (induction xs as [| x' xs IH]; intros start i; simpl).
Time {
Time by rewrite lookup_empty, lookup_nil.
Time }
Time (destruct i as [| i]; simpl).
Time {
Time by rewrite Nat.add_0_r, lookup_insert.
Time }
Time (rewrite lookup_insert_ne by lia).
Time by rewrite (IH (S start)), Nat.add_succ_r.
Time Qed.
Time
Lemma lookup_map_seq_Some start xs i x :
  map_seq (M:=M A) start xs !! i = Some x
  \226\134\148 start \226\137\164 i \226\136\167 xs !! (i - start) = Some x.
Time Proof.
Time (destruct (decide (start \226\137\164 i)) as [| Hsi]).
Time {
Time (rewrite (lookup_map_seq_Some_inv start)).
Time replace (start + (i - start)) with i by lia.
Time naive_solver.
Time }
Time (split; [  | naive_solver ]).
Time (intros Hi; destruct Hsi).
Time revert start i Hi.
Time (induction xs as [| x' xs IH]; intros start i; simpl).
Time {
Time by rewrite lookup_empty.
Time }
Time (rewrite lookup_insert_Some; intros [[-> ->]| [? ?%IH]]; lia).
Time Qed.
Time
Lemma lookup_map_seq_None start xs i :
  map_seq (M:=M A) start xs !! i = None \226\134\148 i < start \226\136\168 start + length xs \226\137\164 i.
Time Proof.
Time trans \194\172 start \226\137\164 i \226\136\168 \194\172 is_Some (xs !! (i - start)).
Time -
Time (rewrite eq_None_not_Some, <- not_and_l).
Time (unfold is_Some).
Time setoid_rewrite lookup_map_seq_Some.
Time naive_solver.
Time -
Time (rewrite lookup_lt_is_Some).
Time lia.
Time Qed.
Time Lemma lookup_map_seq_0 xs i : map_seq (M:=M A) 0 xs !! i = xs !! i.
Time Proof.
Time (apply option_eq; intros x).
Time by rewrite (lookup_map_seq_Some_inv 0).
Time Qed.
Time
Lemma map_seq_singleton start x : map_seq (M:=M A) start [x] = {[start := x]}.
Time Proof.
Time done.
Time Qed.
Time
Lemma map_seq_app_disjoint start xs1 xs2 :
  map_seq (M:=M A) start xs1 ##\226\130\152 map_seq (start + length xs1) xs2.
Time Proof.
Time (apply map_disjoint_spec; intros i x1 x2).
Time (rewrite !lookup_map_seq_Some).
Time (intros [? ?%lookup_lt_Some] [? ?%lookup_lt_Some]; lia).
Time Qed.
Time
Lemma map_seq_app start xs1 xs2 :
  map_seq start (xs1 ++ xs2) =@{
  M A} map_seq start xs1 \226\136\170 map_seq (start + length xs1) xs2.
Time Proof.
Time revert start.
Time (induction xs1 as [| x1 xs1 IH]; intros start; simpl).
Time -
Time by rewrite (left_id_L _ _), Nat.add_0_r.
Time -
Time by rewrite IH, Nat.add_succ_r, !insert_union_singleton_l, (assoc_L _).
Time Qed.
Time
Lemma map_seq_cons_disjoint start xs :
  map_seq (M:=M A) (S start) xs !! start = None.
Time Proof.
Time (rewrite lookup_map_seq_None).
Time lia.
Time Qed.
Time
Lemma map_seq_cons start xs x :
  map_seq start (x :: xs) =@{ M A} <[start:=x]> (map_seq (S start) xs).
Time Proof.
Time done.
Time Qed.
Time
Lemma map_seq_snoc_disjoint start xs :
  map_seq (M:=M A) start xs !! (start + length xs) = None.
Time Proof.
Time (rewrite lookup_map_seq_None).
Time lia.
Time Qed.
Time
Lemma map_seq_snoc start xs x :
  map_seq start (xs ++ [x]) =@{
  M A} <[start + length xs:=x]> (map_seq start xs).
Time Proof.
Time (rewrite map_seq_app, map_seq_singleton).
Time by rewrite insert_union_singleton_r by by rewrite map_seq_snoc_disjoint.
Time Qed.
Time End map_seq.
Time
Ltac
 decompose_map_disjoint :=
  repeat
   match goal with
   | H:_ \226\136\170 _ ##\226\130\152 _ |- _ => apply map_disjoint_union_l in H; destruct H
   | H:_ ##\226\130\152 _ \226\136\170 _ |- _ => apply map_disjoint_union_r in H; destruct H
   | H:{[_ := _]} ##\226\130\152 _ |- _ => apply map_disjoint_singleton_l in H
   | H:_ ##\226\130\152 {[_ := _]} |- _ => apply map_disjoint_singleton_r in H
   | H:<[_:=_]> _ ##\226\130\152 _ |- _ => apply map_disjoint_insert_l in H; destruct H
   | H:_ ##\226\130\152 <[_:=_]> _ |- _ => apply map_disjoint_insert_r in H; destruct H
   | H:\226\139\131 _ ##\226\130\152 _ |- _ => apply map_disjoint_union_list_l in H
   | H:_ ##\226\130\152 \226\139\131 _ |- _ => apply map_disjoint_union_list_r in H
   | H:\226\136\133 ##\226\130\152 _ |- _ => clear H
   | H:_ ##\226\130\152 \226\136\133 |- _ => clear H
   | H:Forall (.##\226\130\152_) _ |- _ => rewrite Forall_vlookup in H
   | H:Forall (.##\226\130\152_) [] |- _ => clear H
   | H:Forall (.##\226\130\152_) (_ :: _) |- _ => rewrite Forall_cons in H; destruct H
   | H:Forall (.##\226\130\152_) (_ :: _) |- _ => rewrite Forall_app in H; destruct H
   end.
Time Create HintDb map_disjoint.
Time
Ltac
 solve_map_disjoint := solve
 [ decompose_map_disjoint; auto with map_disjoint ].
Time Hint Extern 1 (_ ##\226\130\152 _) => done: map_disjoint.
Time Hint Extern 2 (\226\136\133 ##\226\130\152 _) => (apply map_disjoint_empty_l): map_disjoint.
Time Hint Extern 2 (_ ##\226\130\152 \226\136\133) => (apply map_disjoint_empty_r): map_disjoint.
Time
Hint Extern 2 ({[_ := _]} ##\226\130\152 _) => (apply map_disjoint_singleton_l_2):
  map_disjoint.
Time
Hint Extern 2 (_ ##\226\130\152 {[_ := _]}) => (apply map_disjoint_singleton_r_2):
  map_disjoint.
Time
Hint Extern 2 (_ \226\136\170 _ ##\226\130\152 _) => (apply map_disjoint_union_l_2): map_disjoint.
Time
Hint Extern 2 (_ ##\226\130\152 _ \226\136\170 _) => (apply map_disjoint_union_r_2): map_disjoint.
Time
Hint Extern 2 ({[_ := _]} ##\226\130\152 _) => (apply map_disjoint_singleton_l):
  map_disjoint.
Time
Hint Extern 2 (_ ##\226\130\152 {[_ := _]}) => (apply map_disjoint_singleton_r):
  map_disjoint.
Time
Hint Extern 2 (<[_:=_]> _ ##\226\130\152 _) => (apply map_disjoint_insert_l_2):
  map_disjoint.
Time
Hint Extern 2 (_ ##\226\130\152 <[_:=_]> _) => (apply map_disjoint_insert_r_2):
  map_disjoint.
Time
Hint Extern 2 (delete _ _ ##\226\130\152 _) => (apply map_disjoint_delete_l):
  map_disjoint.
Time
Hint Extern 2 (_ ##\226\130\152 delete _ _) => (apply map_disjoint_delete_r):
  map_disjoint.
Time
Hint Extern 2 (list_to_map _ ##\226\130\152 _) =>
  (apply map_disjoint_list_to_map_zip_l_2): mem_disjoint.
Time
Hint Extern 2 (_ ##\226\130\152 list_to_map _) =>
  (apply map_disjoint_list_to_map_zip_r_2): mem_disjoint.
Time
Hint Extern 2 (\226\139\131 _ ##\226\130\152 _) => (apply map_disjoint_union_list_l_2):
  mem_disjoint.
Time
Hint Extern 2 (_ ##\226\130\152 \226\139\131 _) => (apply map_disjoint_union_list_r_2):
  mem_disjoint.
Time
Hint Extern 2 (foldr delete _ _ ##\226\130\152 _) =>
  (apply map_disjoint_foldr_delete_l): map_disjoint.
Time
Hint Extern 2 (_ ##\226\130\152 foldr delete _ _) =>
  (apply map_disjoint_foldr_delete_r): map_disjoint.
Time
Tactic Notation "simpl_map" "by" tactic3(tac) :=
 (repeat
   match goal with
   | H:context [ \226\136\133 !! _ ] |- _ => rewrite lookup_empty in H
   | H:context [ <[_:=_]> _ !! _ ]
     |- _ =>
         rewrite lookup_insert in H || rewrite lookup_insert_ne in H by tac
   | H:context [ alter _ _ _ !! _ ]
     |- _ => rewrite lookup_alter in H || rewrite lookup_alter_ne in H by tac
   | H:context [ delete _ _ !! _ ]
     |- _ =>
         rewrite lookup_delete in H || rewrite lookup_delete_ne in H by tac
   | H:context [ {[_ := _]} !! _ ]
     |- _ =>
         rewrite lookup_singleton in H ||
           rewrite lookup_singleton_ne in H by tac
   | H:context [ (_ <$> _) !! _ ] |- _ => rewrite lookup_fmap in H
   | H:context [ omap _ _ !! _ ] |- _ => rewrite lookup_omap in H
   | H:context [ lookup (A:=?A) ?i (?m1 \226\136\170 ?m2) ]
     |- _ =>
         let x := fresh in
         evar ( x : A );
          (let x' := eval unfold x in x in
           clear x;
            (let E := fresh in
             assert (E : (m1 \226\136\170 m2) !! i = Some x') by (clear H; by tac);
              rewrite E in H; clear E))
   | |- context [ \226\136\133 !! _ ] => rewrite lookup_empty
   | |- context [ <[_:=_]> _ !! _ ] =>
         rewrite lookup_insert || rewrite lookup_insert_ne by tac
   | |- context [ alter _ _ _ !! _ ] =>
         rewrite lookup_alter || rewrite lookup_alter_ne by tac
   | |- context [ delete _ _ !! _ ] =>
         rewrite lookup_delete || rewrite lookup_delete_ne by tac
   | |- context [ {[_ := _]} !! _ ] =>
         rewrite lookup_singleton || rewrite lookup_singleton_ne by tac
   | |- context [ (_ <$> _) !! _ ] => rewrite lookup_fmap
   | |- context [ omap _ _ !! _ ] => rewrite lookup_omap
   | |- context [ lookup (A:=?A) ?i ?m ] =>
         let x := fresh in
         evar ( x : A );
          (let x' := eval unfold x in x in
           clear x;
            (let E := fresh in
             assert (E : m !! i = Some x') by tac; rewrite E; clear E))
   end).
Time Create HintDb simpl_map.
Time
Tactic Notation "simpl_map" := simpl_map by eauto with simpl_map map_disjoint.
Time
Hint Extern 80 ((_ \226\136\170 _) !! _ = Some _) => (apply lookup_union_Some_l):
  simpl_map.
Time
Hint Extern 81 ((_ \226\136\170 _) !! _ = Some _) => (apply lookup_union_Some_r):
  simpl_map.
Time
Hint Extern 80 ({[_ := _]} !! _ = Some _) => (apply lookup_singleton):
  simpl_map.
Time
Hint Extern 80 (<[_:=_]> _ !! _ = Some _) => (apply lookup_insert): simpl_map.
Time
Tactic Notation "simplify_map_eq" "by" tactic3(tac) :=
 (decompose_map_disjoint;
   repeat
    match goal with
    | _ => progress simpl_map by tac
    | _ => progress simplify_eq /=
    | _ =>
        progress simpl_option by tac
    | H:{[_ := _]} !! _ = None |- _ => rewrite lookup_singleton_None in H
    | H:{[_ := _]} !! _ = Some _
      |- _ => rewrite lookup_singleton_Some in H; destruct H
    | H1:?m1 !! ?i = Some ?x, H2:?m2 !! ?i = Some ?y
      |- _ =>
          let H3 := fresh in
          feed pose proof lookup_weaken_inv m1 m2 i x y as H3;
           [ done | by tac | done |  ]; clear H2; symmetry in H3
    | H1:?m1 !! ?i = Some ?x, H2:?m2 !! ?i = None
      |- _ =>
          let H3 := fresh in
          apply (lookup_weaken _ m2) in H1; [ congruence | by tac ]
    | H:?m \226\136\170 _ = ?m \226\136\170 _
      |- _ => apply map_union_cancel_l in H; [  | by tac | by tac ]
    | H:_ \226\136\170 ?m = _ \226\136\170 ?m
      |- _ => apply map_union_cancel_r in H; [  | by tac | by tac ]
    | H:{[?i := ?x]} = \226\136\133 |- _ => by destruct (map_non_empty_singleton i x)
    | H:\226\136\133 = {[?i := ?x]} |- _ => by destruct (map_non_empty_singleton i x)
    | H:?m !! ?i = Some _, H2:?m !! ?j = None
      |- _ =>
          unless i \226\137\160 j by done; assert (i \226\137\160 j) by by intros ?; simplify_eq
    end).
Time
Tactic Notation "simplify_map_eq" "/=" "by" tactic3(tac) :=
 (repeat progress csimpl in * || simplify_map_eq by tac).
Time
Tactic Notation "simplify_map_eq" := simplify_map_eq by eauto
 with simpl_map map_disjoint.
Time
Tactic Notation "simplify_map_eq" "/=" := simplify_map_eq /= by eauto
 with simpl_map map_disjoint.
