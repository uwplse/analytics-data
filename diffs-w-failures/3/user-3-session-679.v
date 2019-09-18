Time From stdpp Require Export orders list.
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
Time Section setoids_simple.
Time Context `{SemiSet A C}.
Time #[global]Instance set_equiv_equivalence : (Equivalence (\226\137\161@{C} )).
Time Proof.
Time split.
Time -
Time done.
Time -
Time (intros X Y ? x).
Time by symmetry.
Time -
Time (intros X Y Z ? ? x; by trans x \226\136\136 Y).
Time Qed.
Time #[global]
Instance singleton_proper : (Proper ((=) ==> (\226\137\161@{C} )) singleton).
Time Proof.
Time (apply _).
Time Qed.
Time #[global]
Instance elem_of_proper : (Proper ((=) ==> (\226\137\161) ==> iff) (\226\136\136@{C} )) |5.
Time Proof.
Time by intros x ? <- X Y.
Time Qed.
Time #[global]
Instance disjoint_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> iff) (##@{C} )).
Time Proof.
Time (intros X1 X2 HX Y1 Y2 HY; apply forall_proper; intros x).
Time by rewrite HX, HY.
Time Qed.
Time #[global]
Instance union_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161@{C} )) union).
Time Proof.
Time (intros X1 X2 HX Y1 Y2 HY x).
Time (rewrite !elem_of_union).
Time (f_equiv; auto).
Time Qed.
Time #[global]
Instance union_list_proper : (Proper ((\226\137\161) ==> (\226\137\161@{C} )) union_list).
Time Proof.
Time by induction 1; simpl; try apply union_proper.
Time Qed.
Time #[global]
Instance subseteq_proper : (Proper ((\226\137\161@{C} ) ==> (\226\137\161@{C} ) ==> iff) (\226\138\134)).
Time Proof.
Time (intros X1 X2 HX Y1 Y2 HY).
Time (apply forall_proper; intros x).
Time by rewrite HX, HY.
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
Time Qed.
Time #[global]
Instance difference_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161@{C} )) difference).
Time Proof.
Time (intros X1 X2 HX Y1 Y2 HY x).
Time by rewrite !elem_of_difference, HX, HY.
Time Qed.
Time End setoids.
Time Section setoids_monad.
Time Context `{MonadSet M}.
Time #[global]
Instance set_fmap_proper  {A} {B}:
 (Proper (pointwise_relation _ (=) ==> (\226\137\161) ==> (\226\137\161)) (@fmap M _ A B)).
Time Proof.
Time (intros f1 f2 Hf X1 X2 HX x).
Time (rewrite !elem_of_fmap).
Time (f_equiv; intros z).
Time by rewrite HX, Hf.
Time Qed.
Time #[global]
Instance set_bind_proper  {A} {B}:
 (Proper (pointwise_relation _ (\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) (@mbind M _ A B)).
Time Proof.
Time (intros f1 f2 Hf X1 X2 HX x).
Time (rewrite !elem_of_bind).
Time (f_equiv; intros z).
Time by rewrite HX, (Hf z).
Time Qed.
Time #[global]
Instance set_join_proper  {A}: (Proper ((\226\137\161) ==> (\226\137\161)) (@mjoin M _ A)).
Time Proof.
Time (intros X1 X2 HX x).
Time (rewrite !elem_of_join).
Time (f_equiv; intros z).
Time by rewrite HX.
Time Qed.
Time End setoids_monad.
Time Class SetUnfold (P Q : Prop) :={set_unfold : P \226\134\148 Q}.
Time Arguments set_unfold _ _ {_} : assert.
Time Hint Mode SetUnfold + -: typeclass_instances.
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
Time done.
Time Qed.
Time
Definition set_unfold_1 `{SetUnfold P Q} : P \226\134\146 Q := proj1 (set_unfold P Q).
Time
Definition set_unfold_2 `{SetUnfold P Q} : Q \226\134\146 P := proj2 (set_unfold P Q).
Time
Lemma set_unfold_impl P Q P' Q' :
  SetUnfold P P' \226\134\146 SetUnfold Q Q' \226\134\146 SetUnfold (P \226\134\146 Q) (P' \226\134\146 Q').
Time Proof.
Time constructor.
Time by rewrite (set_unfold P P'), (set_unfold Q Q').
Time Qed.
Time
Lemma set_unfold_and P Q P' Q' :
  SetUnfold P P' \226\134\146 SetUnfold Q Q' \226\134\146 SetUnfold (P \226\136\167 Q) (P' \226\136\167 Q').
Time Proof.
Time constructor.
Time by rewrite (set_unfold P P'), (set_unfold Q Q').
Time Qed.
Time
Lemma set_unfold_or P Q P' Q' :
  SetUnfold P P' \226\134\146 SetUnfold Q Q' \226\134\146 SetUnfold (P \226\136\168 Q) (P' \226\136\168 Q').
Time Proof.
Time constructor.
Time by rewrite (set_unfold P P'), (set_unfold Q Q').
Time Qed.
Time
Lemma set_unfold_iff P Q P' Q' :
  SetUnfold P P' \226\134\146 SetUnfold Q Q' \226\134\146 SetUnfold (P \226\134\148 Q) (P' \226\134\148 Q').
Time Proof.
Time constructor.
Time by rewrite (set_unfold P P'), (set_unfold Q Q').
Time Qed.
Time Lemma set_unfold_not P P' : SetUnfold P P' \226\134\146 SetUnfold (\194\172 P) (\194\172 P').
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
Time
Lemma set_unfold_exist {A} (P P' : A \226\134\146 Prop) :
  (\226\136\128 x, SetUnfold (P x) (P' x)) \226\134\146 SetUnfold (\226\136\131 x, P x) (\226\136\131 x, P' x).
Time Proof.
Time constructor.
Time naive_solver.
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
Time #[global]
Instance set_unfold_empty  x: (SetUnfoldElemOf x (\226\136\133 : C) False).
Time Proof.
Time constructor.
Time split.
Time (apply not_elem_of_empty).
Time done.
Time Qed.
Time #[global]
Instance set_unfold_singleton  x y: (SetUnfoldElemOf x ({[y]} : C) (x = y)).
Time Proof.
Time (constructor; apply elem_of_singleton).
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
Time Qed.
Time #[global]
Instance set_unfold_equiv_empty_r  (P : A \226\134\146 Prop) 
 X: ((\226\136\128 x, SetUnfoldElemOf x X (P x)) \226\134\146 SetUnfold (X \226\137\161 \226\136\133) (\226\136\128 x, \194\172 P x)) |5.
Time Proof.
Time (intros ?; constructor).
Time (unfold equiv, set_equiv).
Time (pose proof (not_elem_of_empty (C:=C)); naive_solver).
Time Qed.
Time #[global]
Instance set_unfold_equiv  (P Q : A \226\134\146 Prop) X:
 ((\226\136\128 x, SetUnfoldElemOf x X (P x))
  \226\134\146 (\226\136\128 x, SetUnfoldElemOf x Y (Q x)) \226\134\146 SetUnfold (X \226\137\161 Y) (\226\136\128 x, P x \226\134\148 Q x))
 |10.
Time Proof.
Time constructor.
Time (apply forall_proper; naive_solver).
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
Time Lemma disjoint_intersection X Y : X ## Y \226\134\148 X \226\136\169 Y \226\137\161 \226\136\133.
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
