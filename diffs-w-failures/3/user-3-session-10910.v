Time From stdpp Require Export countable fin_map_dom.
Time
Record mapset (M : Type \226\134\146 Type) : Type :=
 Mapset {mapset_car : M (unit : Type)}.
Time Arguments Mapset {_} _ : assert.
Time Arguments mapset_car {_} _ : assert.
Time Section mapset.
Time Context `{FinMap K M}.
Time #[global]
Instance mapset_elem_of : (ElemOf K (mapset M)) :=
 (\206\187 x X, mapset_car X !! x = Some ()).
Time #[global]Instance mapset_empty : (Empty (mapset M)) := (Mapset \226\136\133).
Time #[global]
Instance mapset_singleton : (Singleton K (mapset M)) :=
 (\206\187 x, Mapset {[x := ()]}).
Time #[global]
Instance mapset_union : (Union (mapset M)) :=
 (\206\187 X1 X2, let (m1) := X1 in let (m2) := X2 in Mapset (m1 \226\136\170 m2)).
Time #[global]
Instance mapset_intersection : (Intersection (mapset M)) :=
 (\206\187 X1 X2, let (m1) := X1 in let (m2) := X2 in Mapset (m1 \226\136\169 m2)).
Time #[global]
Instance mapset_difference : (Difference (mapset M)) :=
 (\206\187 X1 X2, let (m1) := X1 in let (m2) := X2 in Mapset (m1 \226\136\150 m2)).
Time #[global]
Instance mapset_elements : (Elements K (mapset M)) :=
 (\206\187 X, let (m) := X in (map_to_list m).*1).
Time Lemma mapset_eq (X1 X2 : mapset M) : X1 = X2 \226\134\148 (\226\136\128 x, x \226\136\136 X1 \226\134\148 x \226\136\136 X2).
Time Proof.
Time (split; [ by intros -> |  ]).
Time (destruct X1 as [m1], X2 as [m2]).
Time (simpl).
Time (intros E).
Time f_equal.
Time (apply map_eq).
Time (intros i).
Time (apply option_eq).
Time (intros []).
Time by apply E.
Time Qed.
Time Instance mapset_set : (Set_ K (mapset M)).
Time Proof.
Time (split; [ split |  |  ]).
Time -
Time (unfold empty, elem_of, mapset_empty, mapset_elem_of).
Time (simpl).
Time (intros).
Time by simpl_map.
Time -
Time (unfold singleton, elem_of, mapset_singleton, mapset_elem_of).
Time (simpl).
Time by split; intros; simplify_map_eq.
Time -
Time (unfold union, elem_of, mapset_union, mapset_elem_of).
Time (intros [m1] [m2] ?).
Time (simpl).
Time (rewrite lookup_union_Some_raw).
Time (destruct (m1 !! x) as [[]| ]; tauto).
Time -
Time (unfold intersection, elem_of, mapset_intersection, mapset_elem_of).
Time (intros [m1] [m2] ?).
Time (simpl).
Time (rewrite lookup_intersection_Some).
Time (assert (is_Some (m2 !! x) \226\134\148 m2 !! x = Some ())).
Time {
Time (split; eauto).
Time by intros [[] ?].
Time }
Time naive_solver.
Time -
Time (unfold difference, elem_of, mapset_difference, mapset_elem_of).
Time (intros [m1] [m2] ?).
Time (simpl).
Time (rewrite lookup_difference_Some).
Time (destruct (m2 !! x) as [[]| ]; intuition congruence).
Time Qed.
Time #[global]Instance mapset_leibniz : (LeibnizEquiv (mapset M)).
Time Proof.
Time (intros ? ?).
Time (apply mapset_eq).
Time Qed.
Time #[global]Instance mapset_fin_set : (FinSet K (mapset M)).
Time Proof.
Time split.
Time -
Time (apply _).
Time -
Time (unfold elements, elem_of at 2, mapset_elements, mapset_elem_of).
Time (intros [m] x).
Time (simpl).
Time (rewrite elem_of_list_fmap).
Time split.
Time +
Time (intros ([y []], (?, Hy))).
Time subst.
Time by rewrite <- elem_of_map_to_list.
Time +
Time (intros).
Time exists (x, ()).
Time by rewrite elem_of_map_to_list.
Time -
Time (unfold elements, mapset_elements).
Time (intros [m]).
Time (simpl).
Time (apply NoDup_fst_map_to_list).
Time Qed.
Time Section deciders.
Time Context `{EqDecision (M unit)}.
Time #[global]Instance mapset_eq_dec : (EqDecision (mapset M)) |1.
Time Proof.
Time
(refine
  (\206\187 X1 X2,
     match X1, X2 with
     | Mapset m1, Mapset m2 => cast_if (decide (m1 = m2))
     end); abstract congruence).
Time Defined.
Time #[global, program]
Instance mapset_countable  `{Countable (M ())}: (Countable (mapset M)) :=
 (inj_countable mapset_car (Some \226\136\152 Mapset) _).
Time Next Obligation.
Time by intros ? ? [].
Time Qed.
Time #[global]Instance mapset_equiv_dec : (RelDecision (\226\137\161@{mapset M} )) |1.
Time Proof.
Time
(refine (\206\187 X1 X2, cast_if (decide (X1 = X2))); abstract by fold_leibniz).
Time Defined.
Time #[global]Instance mapset_elem_of_dec : (RelDecision (\226\136\136@{mapset M} )) |1.
Time Proof.
Time (refine (\206\187 x X, cast_if (decide (mapset_car X !! x = Some ()))); done).
Time Defined.
Time #[global]Instance mapset_disjoint_dec : (RelDecision (##@{mapset M} )).
Time Proof.
Time
(refine (\206\187 X1 X2, cast_if (decide (X1 \226\136\169 X2 = \226\136\133))); abstract by
  rewrite disjoint_intersection_L).
Time Defined.
Time #[global]Instance mapset_subseteq_dec : (RelDecision (\226\138\134@{mapset M} )).
Time Proof.
Time
(refine (\206\187 X1 X2, cast_if (decide (X1 \226\136\170 X2 = X2))); abstract by
  rewrite subseteq_union_L).
Time Defined.
Time End deciders.
Time
Definition mapset_map_with {A} {B} (f : bool \226\134\146 A \226\134\146 option B) 
  (X : mapset M) : M A \226\134\146 M B :=
  let (mX) := X in
  merge
    (\206\187 x y,
       match x, y with
       | Some _, Some a => f true a
       | None, Some a => f false a
       | _, None => None
       end) mX.
Time
Definition mapset_dom_with {A} (f : A \226\134\146 bool) (m : M A) : 
  mapset M :=
  Mapset $
  merge
    (\206\187 x _,
       match x with
       | Some a => if f a then Some () else None
       | None => None
       end) m (@empty (M A) _).
Time
Lemma lookup_mapset_map_with {A} {B} (f : bool \226\134\146 A \226\134\146 option B) 
  X m i : mapset_map_with f X m !! i = m !! i \226\137\171= f (bool_decide (i \226\136\136 X)).
Time Proof.
Time (destruct X as [mX]).
Time (unfold mapset_map_with, elem_of, mapset_elem_of).
Time (rewrite lookup_merge by done).
Time (simpl).
Time by case_bool_decide; destruct (mX !! i) as [[]| ], (m !! i).
Time Qed.
Time
Lemma elem_of_mapset_dom_with {A} (f : A \226\134\146 bool) m 
  i : i \226\136\136 mapset_dom_with f m \226\134\148 (\226\136\131 x, m !! i = Some x \226\136\167 f x).
Time Proof.
Time (unfold mapset_dom_with, elem_of, mapset_elem_of).
Time (simpl).
Time (rewrite lookup_merge by done).
Time (destruct (m !! i) as [a| ]).
Time -
Time (destruct (Is_true_reflect (f a)); naive_solver).
Time -
Time naive_solver.
Time Qed.
Time
Instance mapset_dom  {A}: (Dom (M A) (mapset M)) :=
 (mapset_dom_with (\206\187 _, true)).
Time Instance mapset_dom_spec : (FinMapDom K M (mapset M)).
Time Proof.
Time (split; try apply _).
Time (intros).
Time (unfold dom, mapset_dom, is_Some).
Time (rewrite elem_of_mapset_dom_with; naive_solver).
Time Qed.
Time End mapset.
Time Opaque mapset_elem_of.
Time Arguments mapset_eq_dec : simpl never.
