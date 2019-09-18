Time From stdpp Require Export sets fin_maps.
Time Set Default Proof Using "Type*".
Time
Class FinMapDom K M D `{\226\136\128 A, Dom (M A) D} `{FMap M} 
`{\226\136\128 A, Lookup K A (M A)} `{\226\136\128 A, Empty (M A)} `{\226\136\128 A, PartialAlter K A (M A)}
`{OMap M} `{Merge M} `{\226\136\128 A, FinMapToList K A (M A)} 
`{EqDecision K} `{ElemOf K D} `{Empty D} `{Singleton K D} 
`{Union D} `{Intersection D} `{Difference D} :={finmap_dom_map :>> FinMap K M;
                                                finmap_dom_set :>> Set_ K D;
                                                elem_of_dom :
                                                 forall {A} (m : M A) i,
                                                 i \226\136\136 dom D m
                                                 \226\134\148 
                                                 is_Some (m !! i)}.
Time Section fin_map_dom.
Time Context `{FinMapDom K M D}.
Time
Lemma dom_map_filter {A} (P : K * A \226\134\146 Prop) `{!\226\136\128 x, Decision (P x)} 
  (m : M A) : dom D (filter P m) \226\138\134 dom D m.
Time Proof.
Time (intros ?).
Time (rewrite 2!elem_of_dom).
Time (destruct 1 as [? [Eq _]%map_filter_lookup_Some]).
Time by eexists.
Time Qed.
Time Lemma elem_of_dom_2 {A} (m : M A) i x : m !! i = Some x \226\134\146 i \226\136\136 dom D m.
Time Proof.
Time (rewrite elem_of_dom; eauto).
Time Qed.
Time Lemma not_elem_of_dom {A} (m : M A) i : i \226\136\137 dom D m \226\134\148 m !! i = None.
Time Proof.
Time by rewrite elem_of_dom, eq_None_not_Some.
Time Qed.
Time Lemma subseteq_dom {A} (m1 m2 : M A) : m1 \226\138\134 m2 \226\134\146 dom D m1 \226\138\134 dom D m2.
Time Proof.
Time (rewrite map_subseteq_spec).
Time (intros ? ?).
Time (rewrite !elem_of_dom).
Time (inversion 1; eauto).
Time Qed.
Time Lemma subset_dom {A} (m1 m2 : M A) : m1 \226\138\130 m2 \226\134\146 dom D m1 \226\138\130 dom D m2.
Time Proof.
Time (intros [Hss1 Hss2]; split; [ by apply subseteq_dom |  ]).
Time (contradict Hss2).
Time (rewrite map_subseteq_spec).
Time (intros i x Hi).
Time specialize (Hss2 i).
Time (rewrite !elem_of_dom in Hss2).
Time (destruct Hss2; eauto).
Time by simplify_map_eq.
Time Qed.
Time Lemma dom_empty {A} : dom D (@empty (M A) _) \226\137\161 \226\136\133.
Time Proof.
Time (intros x).
Time (rewrite elem_of_dom, lookup_empty, <- not_eq_None_Some).
Time set_solver.
Time Qed.
Time Lemma dom_empty_inv {A} (m : M A) : dom D m \226\137\161 \226\136\133 \226\134\146 m = \226\136\133.
Time Proof.
Time (intros E).
Time (apply map_empty).
Time (intros).
Time (apply not_elem_of_dom).
Time (rewrite E).
Time set_solver.
Time Qed.
Time Lemma dom_alter {A} f (m : M A) i : dom D (alter f i m) \226\137\161 dom D m.
Time Proof.
Time (apply elem_of_equiv; intros j; rewrite !elem_of_dom; unfold is_Some).
Time (destruct (decide (i = j)); simplify_map_eq /=; eauto).
Time (destruct (m !! j); naive_solver).
Time Qed.
Time
Lemma dom_insert {A} (m : M A) i x : dom D (<[i:=x]> m) \226\137\161 {[i]} \226\136\170 dom D m.
Time Proof.
Time (apply elem_of_equiv).
Time (intros j).
Time (rewrite elem_of_union, !elem_of_dom).
Time (unfold is_Some).
Time setoid_rewrite lookup_insert_Some.
Time (destruct (decide (i = j)); set_solver).
Time Qed.
Time
Lemma dom_insert_subseteq {A} (m : M A) i x : dom D m \226\138\134 dom D (<[i:=x]> m).
Time Proof.
Time (rewrite (dom_insert _)).
Time set_solver.
Time Qed.
Time
Lemma dom_insert_subseteq_compat_l {A} (m : M A) i 
  x X : X \226\138\134 dom D m \226\134\146 X \226\138\134 dom D (<[i:=x]> m).
Time Proof.
Time (intros).
Time (trans dom D m; eauto using dom_insert_subseteq).
Time Qed.
Time
Lemma dom_singleton {A} (i : K) (x : A) : dom D ({[i := x]} : M A) \226\137\161 {[i]}.
Time Proof.
Time (rewrite <- insert_empty, dom_insert, dom_empty; set_solver).
Time Qed.
Time Lemma dom_delete {A} (m : M A) i : dom D (delete i m) \226\137\161 dom D m \226\136\150 {[i]}.
Time Proof.
Time (apply elem_of_equiv).
Time (intros j).
Time (rewrite elem_of_difference, !elem_of_dom).
Time (unfold is_Some).
Time setoid_rewrite lookup_delete_Some.
Time set_solver.
Time Qed.
Time
Lemma delete_partial_alter_dom {A} (m : M A) i f :
  i \226\136\137 dom D m \226\134\146 delete i (partial_alter f i m) = m.
Time Proof.
Time (rewrite not_elem_of_dom).
Time (apply delete_partial_alter).
Time Qed.
Time
Lemma delete_insert_dom {A} (m : M A) i x :
  i \226\136\137 dom D m \226\134\146 delete i (<[i:=x]> m) = m.
Time Proof.
Time (rewrite not_elem_of_dom).
Time (apply delete_insert).
Time Qed.
Time
Lemma map_disjoint_dom {A} (m1 m2 : M A) : m1 ##\226\130\152 m2 \226\134\148 dom D m1 ## dom D m2.
Time Proof.
Time (rewrite map_disjoint_spec, elem_of_disjoint).
Time setoid_rewrite elem_of_dom.
Time (unfold is_Some).
Time naive_solver.
Time Qed.
Time
Lemma map_disjoint_dom_1 {A} (m1 m2 : M A) : m1 ##\226\130\152 m2 \226\134\146 dom D m1 ## dom D m2.
Time Proof.
Time (apply map_disjoint_dom).
Time Qed.
Time
Lemma map_disjoint_dom_2 {A} (m1 m2 : M A) : dom D m1 ## dom D m2 \226\134\146 m1 ##\226\130\152 m2.
Time Proof.
Time (apply map_disjoint_dom).
Time Qed.
Time
Lemma dom_union {A} (m1 m2 : M A) : dom D (m1 \226\136\170 m2) \226\137\161 dom D m1 \226\136\170 dom D m2.
Time Proof.
Time (apply elem_of_equiv).
Time (intros i).
Time (rewrite elem_of_union, !elem_of_dom).
Time (unfold is_Some).
Time setoid_rewrite lookup_union_Some_raw.
Time (destruct (m1 !! i); naive_solver).
Time Qed.
Time
Lemma dom_intersection {A} (m1 m2 : M A) :
  dom D (m1 \226\136\169 m2) \226\137\161 dom D m1 \226\136\169 dom D m2.
Time Proof.
Time (apply elem_of_equiv).
Time (intros i).
Time (rewrite elem_of_intersection, !elem_of_dom).
Time (unfold is_Some).
Time setoid_rewrite lookup_intersection_Some.
Time naive_solver.
Time Qed.
Time
Lemma dom_difference {A} (m1 m2 : M A) :
  dom D (m1 \226\136\150 m2) \226\137\161 dom D m1 \226\136\150 dom D m2.
Time Proof.
Time (apply elem_of_equiv).
Time (intros i).
Time (rewrite elem_of_difference, !elem_of_dom).
Time (unfold is_Some).
Time setoid_rewrite lookup_difference_Some.
Time (destruct (m2 !! i); naive_solver).
Time Qed.
Time
Lemma dom_fmap {A} {B} (f : A \226\134\146 B) (m : M A) : dom D (f <$> m) \226\137\161 dom D m.
Time Proof.
Time (apply elem_of_equiv).
Time (intros i).
Time (rewrite !elem_of_dom, lookup_fmap, <- !not_eq_None_Some).
Time (destruct (m !! i); naive_solver).
Time Qed.
Time Lemma dom_finite {A} (m : M A) : set_finite (dom D m).
Time Proof.
Time
(induction m using map_ind; rewrite ?dom_empty, ?dom_insert; eauto
  using (empty_finite (C:=D)), (union_finite (C:=D)),
    (singleton_finite (C:=D))).
Time Qed.
Time #[global]
Instance dom_proper  `{!Equiv A}: (Proper ((\226\137\161@{M A} ) ==> (\226\137\161)) (dom D)).
Time Proof.
Time (intros m1 m2 EQm).
Time (apply elem_of_equiv).
Time (intros i).
Time (rewrite !elem_of_dom, EQm).
Time done.
Time Qed.
Time #[global]
Instance dom_proper_L  `{!Equiv A} `{!LeibnizEquiv D}:
 (Proper ((\226\137\161@{M A} ) ==> (=)) (dom D)) |0.
Time Proof.
Time (intros ? ? ?).
Time unfold_leibniz.
Time by apply dom_proper.
Time Qed.
Time Context `{!LeibnizEquiv D}.
Time Lemma dom_empty_L {A} : dom D (@empty (M A) _) = \226\136\133.
Time Proof.
Time (unfold_leibniz; apply dom_empty).
Time Qed.
Time Lemma dom_empty_inv_L {A} (m : M A) : dom D m = \226\136\133 \226\134\146 m = \226\136\133.
Time Proof.
Time by intros; apply dom_empty_inv; unfold_leibniz.
Time Qed.
Time Lemma dom_alter_L {A} f (m : M A) i : dom D (alter f i m) = dom D m.
Time Proof.
Time (unfold_leibniz; apply dom_alter).
Time Qed.
Time
Lemma dom_insert_L {A} (m : M A) i x : dom D (<[i:=x]> m) = {[i]} \226\136\170 dom D m.
Time Proof.
Time (unfold_leibniz; apply dom_insert).
Time Qed.
Time
Lemma dom_singleton_L {A} (i : K) (x : A) : dom D ({[i := x]} : M A) = {[i]}.
Time Proof.
Time (unfold_leibniz; apply dom_singleton).
Time Qed.
Time
Lemma dom_delete_L {A} (m : M A) i : dom D (delete i m) = dom D m \226\136\150 {[i]}.
Time Proof.
Time (unfold_leibniz; apply dom_delete).
Time Qed.
Time
Lemma dom_union_L {A} (m1 m2 : M A) : dom D (m1 \226\136\170 m2) = dom D m1 \226\136\170 dom D m2.
Time Proof.
Time (unfold_leibniz; apply dom_union).
Time Qed.
Time
Lemma dom_intersection_L {A} (m1 m2 : M A) :
  dom D (m1 \226\136\169 m2) = dom D m1 \226\136\169 dom D m2.
Time Proof.
Time (unfold_leibniz; apply dom_intersection).
Time Qed.
Time
Lemma dom_difference_L {A} (m1 m2 : M A) :
  dom D (m1 \226\136\150 m2) = dom D m1 \226\136\150 dom D m2.
Time Proof.
Time (unfold_leibniz; apply dom_difference).
Time Qed.
Time
Lemma dom_fmap_L {A} {B} (f : A \226\134\146 B) (m : M A) : dom D (f <$> m) = dom D m.
Time Proof.
Time (unfold_leibniz; apply dom_fmap).
Time Qed.
Time End fin_map_dom.
Time
Lemma dom_seq `{FinMapDom nat M D} {A} start (xs : list A) :
  dom D (map_seq start (M:=M A) xs) \226\137\161 set_seq start (length xs).
Time Proof.
Time revert start.
Time (induction xs as [| x xs IH]; intros start; simpl).
Time -
Time by rewrite dom_empty.
Time -
Time by rewrite dom_insert, IH.
Time Qed.
Time
Lemma dom_seq_L `{FinMapDom nat M D} `{!LeibnizEquiv D} 
  {A} start (xs : list A) :
  dom D (map_seq (M:=M A) start xs) = set_seq start (length xs).
Time Proof.
Time unfold_leibniz.
Time (apply dom_seq).
Time Qed.
