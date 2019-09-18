Time From stdpp Require Export countable infinite fin_maps fin_map_dom.
Time From stdpp Require Import pmap mapset propset.
Time
Definition gmap_wf K `{Countable K} {A} : Pmap A \226\134\146 Prop :=
  map_Forall (\206\187 p _, encode (A:=K) <$> decode p = Some p).
Time
Record gmap K `{Countable K} A :=
 GMap {gmap_car : Pmap A; gmap_prf : bool_decide (gmap_wf K gmap_car)}.
Time Arguments GMap {_} {_} {_} {_} _ _ : assert.
Time Arguments gmap_car {_} {_} {_} {_} _ : assert.
Time
Lemma gmap_eq `{Countable K} {A} (m1 m2 : gmap K A) :
  m1 = m2 \226\134\148 gmap_car m1 = gmap_car m2.
Time Proof.
Time (split; [ by intros -> | intros ]).
Time (destruct m1, m2; simplify_eq /=).
Time (f_equal; apply proof_irrel).
Time Qed.
Time
Instance gmap_eq_eq  `{Countable K} `{EqDecision A}: (EqDecision (gmap K A)).
Time Proof.
Time
(refine (\206\187 m1 m2, cast_if (decide (gmap_car m1 = gmap_car m2))); abstract by
  rewrite gmap_eq).
Time Defined.
Time
Instance gmap_lookup  `{Countable K} {A}: (Lookup K A (gmap K A)) :=
 (\206\187 i m, let (m, _) := m in m !! encode i).
Time
Instance gmap_empty  `{Countable K} {A}: (Empty (gmap K A)) := (GMap \226\136\133 I).
Time #[global]Opaque gmap_empty.
Time
Lemma gmap_partial_alter_wf `{Countable K} {A} (f : option A \226\134\146 option A) 
  m i : gmap_wf K m \226\134\146 gmap_wf K (partial_alter f (encode (A:=K) i) m).
Time Proof.
Time (intros Hm p x).
Time (destruct (decide (encode i = p)) as [<-| ?]).
Time -
Time (rewrite decode_encode; eauto).
Time -
Time (rewrite lookup_partial_alter_ne by done).
Time by apply Hm.
Time Qed.
Time
Instance gmap_partial_alter  `{Countable K} {A}:
 (PartialAlter K A (gmap K A)) :=
 (\206\187 f i m,
    let (m, Hm) := m in
    GMap (partial_alter f (encode i) m)
      (bool_decide_pack _
         (gmap_partial_alter_wf f m i (bool_decide_unpack _ Hm)))).
Time
Lemma gmap_fmap_wf `{Countable K} {A} {B} (f : A \226\134\146 B) 
  m : gmap_wf K m \226\134\146 gmap_wf K (f <$> m).
Time Proof.
Time (intros ? p x).
Time (rewrite lookup_fmap, fmap_Some; intros (?, (?, ?)); eauto).
Time Qed.
Time
Instance gmap_fmap  `{Countable K}: (FMap (gmap K)) :=
 (\206\187 A B f m,
    let (m, Hm) := m in
    GMap (f <$> m)
      (bool_decide_pack _ (gmap_fmap_wf f m (bool_decide_unpack _ Hm)))).
Time
Lemma gmap_omap_wf `{Countable K} {A} {B} (f : A \226\134\146 option B) 
  m : gmap_wf K m \226\134\146 gmap_wf K (omap f m).
Time Proof.
Time
(intros ? p x; rewrite lookup_omap, bind_Some; intros (?, (?, ?)); eauto).
Time Qed.
Time
Instance gmap_omap  `{Countable K}: (OMap (gmap K)) :=
 (\206\187 A B f m,
    let (m, Hm) := m in
    GMap (omap f m)
      (bool_decide_pack _ (gmap_omap_wf f m (bool_decide_unpack _ Hm)))).
Time
Lemma gmap_merge_wf `{Countable K} {A} {B} {C}
  (f : option A \226\134\146 option B \226\134\146 option C) m1 m2 :
  let f' :=
    fun o1 o2 => match o1, o2 with
                 | None, None => None
                 | _, _ => f o1 o2
                 end in
  gmap_wf K m1 \226\134\146 gmap_wf K m2 \226\134\146 gmap_wf K (merge f' m1 m2).
Time Proof.
Time (intros f' Hm1 Hm2 p z; rewrite lookup_merge by done; intros).
Time (destruct (m1 !! _) eqn:?, (m2 !! _) eqn:?; naive_solver).
Time Qed.
Time
Instance gmap_merge  `{Countable K}: (Merge (gmap K)) :=
 (\206\187 A B C f m1 m2,
    let (m1, Hm1) := m1 in
    let (m2, Hm2) := m2 in
    let f' :=
      fun o1 o2 =>
      match o1, o2 with
      | None, None => None
      | _, _ => f o1 o2
      end in
    GMap (merge f' m1 m2)
      (bool_decide_pack _
         (gmap_merge_wf f _ _ (bool_decide_unpack _ Hm1)
            (bool_decide_unpack _ Hm2)))).
Time
Instance gmap_to_list  `{Countable K} {A}: (FinMapToList K A (gmap K A)) :=
 (\206\187 m,
    let (m, _) := m in
    omap (\206\187 ix : positive * A, let (i, x) := ix in (,x) <$> decode i)
      (map_to_list m)).
Time Instance gmap_finmap  `{Countable K}: (FinMap K (gmap K)).
Time Proof.
Time split.
Time -
Time (unfold lookup; intros A [m1 Hm1] [m2 Hm2] Hm).
Time (apply gmap_eq, map_eq; intros i; simpl in *).
Time (apply bool_decide_unpack in Hm1; apply bool_decide_unpack in Hm2).
Time (apply option_eq; intros x; split; intros Hi).
Time +
Time (pose proof (Hm1 i x Hi); simpl in *).
Time by destruct (decode i); simplify_eq /=; rewrite <- Hm.
Time +
Time (pose proof (Hm2 i x Hi); simpl in *).
Time by destruct (decode i); simplify_eq /=; rewrite Hm.
Time -
Time done.
Time -
Time (intros A f [m Hm] i; apply (lookup_partial_alter f m)).
Time -
Time (intros A f [m Hm] i j Hs; apply (lookup_partial_alter_ne f m)).
Time by contradict Hs; apply (inj encode).
Time -
Time (intros A B f [m Hm] i; apply (lookup_fmap f m)).
Time -
Time (intros A [m Hm]; unfold map_to_list; simpl).
Time (apply bool_decide_unpack, map_Forall_to_list in Hm; revert Hm).
Time
(induction (NoDup_map_to_list m) as [| [p x] l Hpx];
  inversion 1 as [| ? ? ? Hm']; simplify_eq /=; [ by constructor |  ]).
Time
(destruct (decode p) as [i| ] eqn:?; simplify_eq /=; constructor; eauto).
Time (rewrite elem_of_list_omap; intros ([p' x'], (?, ?)); simplify_eq /=).
Time
(feed pose proof proj1 (Forall_forall _ _) Hm' (p', x'); simpl in *; auto).
Time by destruct (decode p') as [i'| ]; simplify_eq /=.
Time -
Time (intros A [m Hm] i x; unfold map_to_list, lookup; simpl).
Time (apply bool_decide_unpack in Hm; rewrite elem_of_list_omap; split).
Time +
Time (intros ([p' x'], (Hp', ?)); apply elem_of_map_to_list in Hp').
Time (feed pose proof Hm p' x'; simpl in *; auto).
Time by destruct (decode p') as [i'| ] eqn:?; simplify_eq /=.
Time +
Time (intros; exists (encode i, x); simpl).
Time by rewrite elem_of_map_to_list, decode_encode.
Time -
Time (intros A B f [m Hm] i; apply (lookup_omap f m)).
Time -
Time (intros A B C f ? [m1 Hm1] [m2 Hm2] i; unfold merge, lookup; simpl).
Time
(set
  (f' :=
   fun o1 =>
   fun o2 => match o1, o2 with
             | None, None => None
             | _, _ => f o1 o2
             end)).
Time by rewrite lookup_merge by done; destruct (m1 !! _), (m2 !! _).
Time Qed.
Time #[program]
Instance gmap_countable  `{Countable K} `{Countable A}:
 (Countable (gmap K A)) := {
 encode :=fun m => encode (map_to_list m : list (K * A));
 decode :=fun p => list_to_map <$> decode p}.
Time Next Obligation.
Time (intros K ? ? A ? ? m; simpl).
Time (rewrite decode_encode; simpl).
Time by rewrite list_to_map_to_list.
Time Qed.
Time
Definition gmap_curry `{Countable K1} `{Countable K2} 
  {A} : gmap K1 (gmap K2 A) \226\134\146 gmap (K1 * K2) A :=
  map_fold (\206\187 i1 m' macc, map_fold (\206\187 i2 x, <[(i1, i2):=x]>) macc m') \226\136\133.
Time
Definition gmap_uncurry `{Countable K1} `{Countable K2} 
  {A} : gmap (K1 * K2) A \226\134\146 gmap K1 (gmap K2 A) :=
  map_fold
    (\206\187 ii x,
       let '(i1, i2) := ii in partial_alter (Some \226\136\152 <[i2:=x]> \226\136\152 default \226\136\133) i1)
    \226\136\133.
Time Section curry_uncurry.
Time Context `{Countable K1} `{Countable K2} {A : Type}.
Time
Lemma lookup_gmap_curry (m : gmap K1 (gmap K2 A)) 
  i j : gmap_curry m !! (i, j) = (m !! i : option (gmap K2 A)) \226\137\171= (!!j).
Time Proof.
Time (apply (map_fold_ind (\206\187 mr m, mr !! (i, j) = m !! i \226\137\171= (!!j)))).
Time {
Time by rewrite !lookup_empty.
Time }
Time (clear m; intros i' m2 m m12 Hi' IH).
Time
(apply (map_fold_ind (\206\187 m2r m2, m2r !! (i, j) = <[i':=m2]> m !! i \226\137\171= (!!j)))).
Time {
Time (rewrite IH).
Time (destruct (decide (i' = i)) as [->| ]).
Time -
Time (rewrite lookup_insert, Hi'; simpl; by rewrite lookup_empty).
Time -
Time by rewrite lookup_insert_ne by done.
Time }
Time (intros j' y m2' m12' Hj' IH').
Time (destruct (decide (i = i')) as [->| ]).
Time -
Time (rewrite lookup_insert; simpl).
Time (destruct (decide (j = j')) as [->| ]).
Time +
Time by rewrite !lookup_insert.
Time +
Time by rewrite !lookup_insert_ne, IH', lookup_insert by congruence.
Time -
Time by rewrite !lookup_insert_ne, IH', lookup_insert_ne by congruence.
Time Qed.
Time
Lemma lookup_gmap_uncurry (m : gmap (K1 * K2) A) i 
  j : (gmap_uncurry m !! i : option (gmap K2 A)) \226\137\171= (!!j) = m !! (i, j).
Time Proof.
Time (apply (map_fold_ind (\206\187 mr m, mr !! i \226\137\171= (!!j) = m !! (i, j)))).
Time {
Time by rewrite !lookup_empty.
Time }
Time (clear m; intros [i' j'] x m12 mr Hij' IH).
Time (destruct (decide (i = i')) as [->| ]).
Time -
Time (rewrite lookup_partial_alter).
Time (destruct (decide (j = j')) as [->| ]).
Time +
Time (destruct (mr !! i'); simpl; by rewrite !lookup_insert).
Time +
Time
(destruct (mr !! i'); simpl; by rewrite !lookup_insert_ne by congruence).
Time -
Time by rewrite lookup_partial_alter_ne, lookup_insert_ne by congruence.
Time Qed.
Time
Lemma lookup_gmap_uncurry_None (m : gmap (K1 * K2) A) 
  i : gmap_uncurry m !! i = None \226\134\148 (\226\136\128 j, m !! (i, j) = None).
Time Proof.
Time
(apply (map_fold_ind (\206\187 mr m, mr !! i = None \226\134\148 (\226\136\128 j, m !! (i, j) = None)));
  [ done |  ]).
Time (clear m; intros [i' j'] x m12 mr Hij' IH).
Time (destruct (decide (i = i')) as [->| ]).
Time -
Time (split; [ by rewrite lookup_partial_alter |  ]).
Time (intros Hi).
Time specialize (Hi j').
Time by rewrite lookup_insert in Hi.
Time -
Time (rewrite lookup_partial_alter_ne, IH; [  | done ]).
Time (apply forall_proper).
Time (intros j).
Time (rewrite lookup_insert_ne; [ done | congruence ]).
Time Qed.
Time
Lemma gmap_curry_uncurry (m : gmap (K1 * K2) A) :
  gmap_curry (gmap_uncurry m) = m.
Time Proof.
Time (apply map_eq; intros [i j]).
Time by rewrite lookup_gmap_curry, lookup_gmap_uncurry.
Time Qed.
Time
Lemma gmap_uncurry_non_empty (m : gmap (K1 * K2) A) 
  i x : gmap_uncurry m !! i = Some x \226\134\146 x \226\137\160 \226\136\133.
Time Proof.
Time (intros Hm ->).
Time (eapply eq_None_not_Some; [  | by eexists ]).
Time (eapply lookup_gmap_uncurry_None; intros j).
Time by rewrite <- lookup_gmap_uncurry, Hm.
Time Qed.
Time
Lemma gmap_uncurry_curry_non_empty (m : gmap K1 (gmap K2 A)) :
  (\226\136\128 i x, m !! i = Some x \226\134\146 x \226\137\160 \226\136\133) \226\134\146 gmap_uncurry (gmap_curry m) = m.
Time Proof.
Time (intros Hne).
Time (apply map_eq; intros i).
Time (destruct (m !! i) as [m2| ] eqn:Hm).
Time -
Time (destruct (gmap_uncurry (gmap_curry m) !! i) as [m2'| ] eqn:Hcurry).
Time +
Time f_equal.
Time (apply map_eq).
Time (intros j).
Time trans (gmap_uncurry (gmap_curry m) !! i : option (gmap _ _)) \226\137\171= (!!j).
Time {
Time by rewrite Hcurry.
Time }
Time by rewrite lookup_gmap_uncurry, lookup_gmap_curry, Hm.
Time +
Time (rewrite lookup_gmap_uncurry_None in Hcurry).
Time (exfalso; apply (Hne i m2), map_eq; [ done | intros j ]).
Time by rewrite lookup_empty, <- (Hcurry j), lookup_gmap_curry, Hm.
Time -
Time (apply lookup_gmap_uncurry_None; intros j).
Time by rewrite lookup_gmap_curry, Hm.
Time Qed.
Time End curry_uncurry.
Time Definition gset K `{Countable K} := mapset (gmap K).
Time Section gset.
Time Context `{Countable K}.
Time #[global]Instance gset_elem_of : (ElemOf K (gset K)) := _.
Time #[global]Instance gset_empty : (Empty (gset K)) := _.
Time #[global]Instance gset_singleton : (Singleton K (gset K)) := _.
Time #[global]Instance gset_union : (Union (gset K)) := _.
Time #[global]Instance gset_intersection : (Intersection (gset K)) := _.
Time #[global]Instance gset_difference : (Difference (gset K)) := _.
Time #[global]Instance gset_elements : (Elements K (gset K)) := _.
Time #[global]Instance gset_leibniz : (LeibnizEquiv (gset K)) := _.
Time #[global]Instance gset_semi_set : (SemiSet K (gset K)) |1 := _.
Time #[global]Instance gset_set : (Set_ K (gset K)) |1 := _.
Time #[global]Instance gset_fin_set : (FinSet K (gset K)) := _.
Time #[global]Instance gset_eq_dec : (EqDecision (gset K)) := _.
Time #[global]Instance gset_countable : (Countable (gset K)) := _.
Time #[global]Instance gset_equiv_dec : (RelDecision (\226\137\161@{gset K} )) |1 := _.
Time #[global]
Instance gset_elem_of_dec : (RelDecision (\226\136\136@{gset K} )) |1 := _.
Time #[global]Instance gset_disjoint_dec : (RelDecision (##@{gset K} )) := _.
Time #[global]Instance gset_subseteq_dec : (RelDecision (\226\138\134@{gset K} )) := _.
Time #[global]
Instance gset_dom  {A}: (Dom (gmap K A) (gset K)) := mapset_dom.
Time #[global]
Instance gset_dom_spec : (FinMapDom K (gmap K) (gset K)) := mapset_dom_spec.
Time
Definition gset_to_gmap {A} (x : A) (X : gset K) : 
  gmap K A := (\206\187 _, x) <$> mapset_car X.
Time
Lemma lookup_gset_to_gmap {A} (x : A) (X : gset K) 
  i : gset_to_gmap x X !! i = guard i \226\136\136 X; Some x.
Time Proof.
Time (destruct X as [X]).
Time (unfold gset_to_gmap, gset_elem_of, elem_of, mapset_elem_of; simpl).
Time (rewrite lookup_fmap).
Time (case_option_guard; destruct (X !! i) as [[]| ]; naive_solver).
Time Qed.
Time
Lemma lookup_gset_to_gmap_Some {A} (x : A) (X : gset K) 
  i y : gset_to_gmap x X !! i = Some y \226\134\148 i \226\136\136 X \226\136\167 x = y.
Time Proof.
Time (rewrite lookup_gset_to_gmap).
Time (simplify_option_eq; naive_solver).
Time Qed.
Time
Lemma lookup_gset_to_gmap_None {A} (x : A) (X : gset K) 
  i : gset_to_gmap x X !! i = None \226\134\148 i \226\136\137 X.
Time Proof.
Time (rewrite lookup_gset_to_gmap).
Time (simplify_option_eq; naive_solver).
Time Qed.
Time Lemma gset_to_gmap_empty {A} (x : A) : gset_to_gmap x \226\136\133 = \226\136\133.
Time Proof.
Time (apply fmap_empty).
Time Qed.
Time
Lemma gset_to_gmap_union_singleton {A} (x : A) i Y :
  gset_to_gmap x ({[i]} \226\136\170 Y) = <[i:=x]> (gset_to_gmap x Y).
Time Proof.
Time (apply map_eq; intros j; apply option_eq; intros y).
Time
(rewrite lookup_insert_Some, !lookup_gset_to_gmap_Some, elem_of_union,
  elem_of_singleton; destruct (decide (i = j)); intuition).
Time Qed.
Time
Lemma fmap_gset_to_gmap {A} {B} (f : A \226\134\146 B) (X : gset K) 
  (x : A) : f <$> gset_to_gmap x X = gset_to_gmap (f x) X.
Time Proof.
Time (apply map_eq; intros j).
Time (rewrite lookup_fmap, !lookup_gset_to_gmap).
Time by simplify_option_eq.
Time Qed.
Time
Lemma gset_to_gmap_dom {A} {B} (m : gmap K A) (y : B) :
  gset_to_gmap y (dom _ m) = const y <$> m.
Time Proof.
Time (apply map_eq; intros j).
Time (rewrite lookup_fmap, lookup_gset_to_gmap).
Time (destruct (m !! j) as [x| ] eqn:?).
Time -
Time by rewrite option_guard_True by (rewrite elem_of_dom; eauto).
Time -
Time by rewrite option_guard_False by (rewrite not_elem_of_dom; eauto).
Time Qed.
Time
Lemma dom_gset_to_gmap {A} (X : gset K) (x : A) :
  dom _ (gset_to_gmap x X) = X.
Time Proof.
Time (induction X as [| y X not_in IH] using set_ind_L).
Time -
Time (rewrite gset_to_gmap_empty, dom_empty_L; done).
Time -
Time (rewrite gset_to_gmap_union_singleton, dom_insert_L, IH; done).
Time Qed.
Time End gset.
Time Typeclasses Opaque gset.
