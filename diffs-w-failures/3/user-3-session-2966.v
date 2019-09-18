Time From stdpp Require Export sets.
Time From stdpp Require Export sets list.
Time Set Default Proof Using "Type".
Time Record propset (A : Type) : Type := PropSet {propset_car : A \226\134\146 Prop}.
Time Add Printing Constructor propset.
Time Arguments PropSet {_} _ : assert.
Time Arguments propset_car {_} _ _ : assert.
Time
Notation "{[ x | P ]}" := (PropSet (\206\187 x, P))
  (at level 1, format "{[  x  |  P  ]}") : stdpp_scope.
Time
Instance propset_elem_of  {A}: (ElemOf A (propset A)) :=
 (\206\187 x X, propset_car X x).
Time Instance propset_top  {A}: (Top (propset A)) := {[ _ | True ]}.
Time Instance propset_empty  {A}: (Empty (propset A)) := {[ _ | False ]}.
Time
Instance propset_singleton  {A}: (Singleton A (propset A)) :=
 (\206\187 y, {[ x | y = x ]}).
Time
Instance propset_union  {A}: (Union (propset A)) :=
 (\206\187 X1 X2, {[ x | x \226\136\136 X1 \226\136\168 x \226\136\136 X2 ]}).
Time
Instance propset_intersection  {A}: (Intersection (propset A)) :=
 (\206\187 X1 X2, {[ x | x \226\136\136 X1 \226\136\167 x \226\136\136 X2 ]}).
Time Set Default Proof Using "Type".
Time Record listset A := Listset {listset_car : list A}.
Time Arguments listset_car {_} _ : assert.
Time Arguments Listset {_} _ : assert.
Time Section listset.
Time Context {A : Type}.
Time #[global]
Instance listset_elem_of : (ElemOf A (listset A)) :=
 (\206\187 x l, x \226\136\136 listset_car l).
Time #[global]Instance listset_empty : (Empty (listset A)) := (Listset []).
Time #[global]
Instance listset_singleton : (Singleton A (listset A)) := (\206\187 x, Listset [x]).
Time #[global]
Instance listset_union : (Union (listset A)) :=
 (\206\187 l k, let (l') := l in let (k') := k in Listset (l' ++ k')).
Time #[global]Opaque listset_singleton listset_empty.
Time #[global]Instance listset_simple_set : (SemiSet A (listset A)).
Time Proof.
Time split.
Time -
Time by apply not_elem_of_nil.
Time -
Time by apply elem_of_list_singleton.
Time -
Time (intros [?] [?]).
Time (apply elem_of_app).
Time Qed.
Time
Instance propset_difference  {A}: (Difference (propset A)) :=
 (\206\187 X1 X2, {[ x | x \226\136\136 X1 \226\136\167 x \226\136\137 X2 ]}).
Time Instance propset_set : (Set_ A (propset A)).
Time Proof.
Time (split; [ split |  |  ]; by repeat intro).
Time Qed.
Time Lemma elem_of_top {A} (x : A) : x \226\136\136 (\226\138\164 : propset A) \226\134\148 True.
Time Lemma listset_empty_alt X : X \226\137\161 \226\136\133 \226\134\148 listset_car X = [].
Time Proof.
Time (destruct X as [l]; split; [  | by intros; simplify_eq /= ]).
Time (rewrite elem_of_equiv_empty; intros Hl).
Time Proof.
Time done.
Time Qed.
Time Lemma elem_of_PropSet {A} (P : A \226\134\146 Prop) x : x \226\136\136 {[ x | P x ]} \226\134\148 P x.
Time Proof.
Time done.
Time Qed.
Time
Lemma not_elem_of_PropSet {A} (P : A \226\134\146 Prop) x : x \226\136\137 {[ x | P x ]} \226\134\148 \194\172 P x.
Time Proof.
Time done.
Time Qed.
Time Lemma top_subseteq {A} (X : propset A) : X \226\138\134 \226\138\164.
Time Proof.
Time done.
Time (destruct l as [| x l]; [ done |  ]).
Time feed inversion Hl x.
Time left.
Time Qed.
Time #[global]
Instance listset_empty_dec  (X : listset A): (Decision (X \226\137\161 \226\136\133)).
Time Proof.
Time
(refine (cast_if (decide (listset_car X = []))); abstract by
  rewrite listset_empty_alt).
Time Defined.
Time Qed.
Time Hint Resolve top_subseteq: core.
Time
Definition set_to_propset `{ElemOf A C} (X : C) : 
  propset A := {[ x | x \226\136\136 X ]}.
Time
Lemma elem_of_set_to_propset `{SemiSet A C} x (X : C) :
  x \226\136\136 set_to_propset X \226\134\148 x \226\136\136 X.
Time Proof.
Time done.
Time Qed.
Time Context `{Aeq : !EqDecision A}.
Time #[global]Instance listset_elem_of_dec : (RelDecision (\226\136\136@{listset A} )).
Time Proof  using (Aeq).
Time (refine (\206\187 x X, cast_if (decide (x \226\136\136 listset_car X))); done).
Time Defined.
Time #[global]
Instance listset_intersection : (Intersection (listset A)) :=
 (\206\187 l k, let (l') := l in let (k') := k in Listset (list_intersection l' k')).
Time #[global]
Instance listset_difference : (Difference (listset A)) :=
 (\206\187 l k, let (l') := l in let (k') := k in Listset (list_difference l' k')).
Time Instance listset_set : (Set_ A (listset A)).
Time Proof.
Time split.
Time -
Time (apply _).
Time -
Time (intros [?] [?]).
Time (apply elem_of_list_intersection).
Time -
Time (intros [?] [?]).
Time Instance propset_ret : (MRet propset) := (\206\187 A (x : A), {[x]}).
Time
Instance propset_bind : (MBind propset) :=
 (\206\187 A B (f : A \226\134\146 propset B) (X : propset A),
    PropSet (\206\187 b, \226\136\131 a, b \226\136\136 f a \226\136\167 a \226\136\136 X)).
Time
Instance propset_fmap : (FMap propset) :=
 (\206\187 A B (f : A \226\134\146 B) (X : propset A), {[ b | \226\136\131 a, b = f a \226\136\167 a \226\136\136 X ]}).
Time
Instance propset_join : (MJoin propset) :=
 (\206\187 A (XX : propset (propset A)), {[ a | \226\136\131 X : propset A, a \226\136\136 X \226\136\167 X \226\136\136 XX ]}).
Time Instance propset_monad_set : (MonadSet propset).
Time Proof.
Time by split; try apply _.
Time (apply elem_of_list_difference).
Time Qed.
Time #[global]
Instance listset_elements : (Elements A (listset A)) :=
 (remove_dups \226\136\152 listset_car).
Time #[global]Instance listset_fin_set : (FinSet A (listset A)).
Time Proof.
Time split.
Time -
Time (apply _).
Time -
Time (intros).
Time (apply elem_of_remove_dups).
Time -
Time (intros).
Time (apply NoDup_remove_dups).
Time Qed.
Time End listset.
Time Qed.
Time
Instance set_unfold_propset_top  {A} (x : A):
 (SetUnfoldElemOf x (\226\138\164 : propset A) True).
Time Proof.
Time by constructor.
Time Qed.
Time
Instance set_unfold_PropSet  {A} (P : A \226\134\146 Prop) x 
 Q: (SetUnfoldSimpl (P x) Q \226\134\146 SetUnfoldElemOf x (PropSet P) Q).
Time Proof.
Time (intros HPQ).
Time constructor.
Time (apply HPQ).
Time Qed.
Time Instance listset_ret : (MRet listset) := (\206\187 A x, {[x]}).
Time
Instance listset_fmap : (FMap listset) :=
 (\206\187 A B f l, let (l') := l in Listset (f <$> l')).
Time
Instance listset_bind : (MBind listset) :=
 (\206\187 A B f l, let (l') := l in Listset (mbind (listset_car \226\136\152 f) l')).
Time Instance listset_join : (MJoin listset) := (\206\187 A, mbind id).
Time Instance listset_set_monad : (MonadSet listset).
Time #[global]
Opaque propset_elem_of propset_top propset_empty propset_singleton.
Time #[global]Opaque propset_union propset_intersection propset_difference.
Time #[global]Opaque propset_ret propset_bind propset_fmap propset_join.
Time Proof.
Time split.
Time -
Time (intros).
Time (apply _).
Time -
Time (intros ? ? ? [?] ?).
Time (apply elem_of_list_bind).
Time -
Time (intros).
Time (apply elem_of_list_ret).
Time -
Time (intros ? ? ? [?]).
Time (apply elem_of_list_fmap).
Time -
Time (intros ? [?] ?).
Time (unfold mjoin, listset_join, elem_of, listset_elem_of).
Time (simpl).
Time by rewrite elem_of_list_bind.
Time Qed.
