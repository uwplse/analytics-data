Time From stdpp Require Export sets list.
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
Time Lemma listset_empty_alt X : X \226\137\161 \226\136\133 \226\134\148 listset_car X = [].
Time Proof.
Time (destruct X as [l]; split; [  | by intros; simplify_eq /= ]).
Time (rewrite elem_of_equiv_empty; intros Hl).
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
Time Instance listset_ret : (MRet listset) := (\206\187 A x, {[x]}).
Time
Instance listset_fmap : (FMap listset) :=
 (\206\187 A B f l, let (l') := l in Listset (f <$> l')).
Time
Instance listset_bind : (MBind listset) :=
 (\206\187 A B f l, let (l') := l in Listset (mbind (listset_car \226\136\152 f) l')).
Time Instance listset_join : (MJoin listset) := (\206\187 A, mbind id).
Time Instance listset_set_monad : (MonadSet listset).
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
