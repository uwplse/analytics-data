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
