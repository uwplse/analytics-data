Time From Classes Require Import EqualDec.
Time From stdpp Require Export orders list.
Time From stdpp Require Import base.
Time From Transitions Require Import Relations.
Time From Perennial Require Import Spec.Proc.
Time Set Implicit Arguments.
Time Arguments existT {A} {P} _ _.
Time Import EqNotations.
Time Import RelationNotations.
Time
Inductive NonAtomicArgs T :=
  | FinishArgs : forall args : T, _
  | Begin : _.
Time Arguments Begin {T}.
Time
Definition retT T (args : NonAtomicArgs T) T' : Type :=
  if args then T' else unit.
Time
Definition nonAtomicOp {Op} {ArgT} {T}
  (op : forall args : NonAtomicArgs ArgT, Op (retT args T)) :
  ArgT -> proc Op T :=
  fun args => Bind (Call (op Begin)) (fun _ => Call (op (FinishArgs args))).
Time
Inductive NonAtomicState Obj\206\163 : Type :=
  | Clean : forall s : Obj\206\163, _
  | Dirty : forall s : Obj\206\163, _.
Time
Definition readClean {State} Obj\206\163 (s : NonAtomicState Obj\206\163) :
  relation State State Obj\206\163 :=
  match s with
  | Clean s => pure s
  | Dirty _ => error
  end.
Time
Definition readDirty {State} Obj\206\163 (s : NonAtomicState Obj\206\163) :
  relation State State Obj\206\163 :=
  match s with
  | Clean _ => error
  | Dirty s => pure s
  end.
Time
Definition nonAtomicStep {ArgT} (args : NonAtomicArgs ArgT) 
  {T} {Obj\206\163} (obj_s : NonAtomicState Obj\206\163) {State}
  (mkDirty : Obj\206\163 -> relation State State unit)
  (opStep : Obj\206\163 -> ArgT -> relation State State T) :
  relation State State (retT args T) :=
  match args with
  | Begin => s <- readClean obj_s; mkDirty s
  | FinishArgs x => s <- readDirty obj_s; opStep s x
  end.
Time
Record DynMap A (Ref : A -> Type) (Model : A -> Type) :={
 dynMap : sigT Ref -> option (sigT Model);
 dynMap_wf :
  forall T v,
  match dynMap (existT T v) with
  | Some (existT T' _) => T' = T
  | None => True
  end;
 dynMap_dom : list (sigT Ref);
 dynMap_dom_spec : forall x, dynMap x <> None <-> x \226\136\136 dynMap_dom;
 dynMap_dom_nodup : NoDup dynMap_dom}.
Time Module OptionNotations.
Time Delimit Scope option_monad with opt.
Time
Notation "'Some!' x <- a ; f" := match a with
                                 | Some x => f
                                 | _ => None
                                 end
  (right associativity, at level 70, x pattern) : option_monad.
Time
Notation "'left!' H <- a ; f" :=
  match a with
  | left H => f
  | right _ => None
  end (right associativity, at level 60, f  at level 200) : option_monad.
Time Notation "'ret!' a" := (Some a) (at level 60) : option_monad.
Time End OptionNotations.
Time Import EqualDecNotation.
Time Import OptionNotations.
Time #[local]Open Scope option_monad.
Time
Definition getDyn A (Ref Model : A -> Type) (m : DynMap Ref Model) 
  a (r : Ref a) : option (Model a).
Time Proof.
Time (pose proof (m.(dynMap_wf) _ r)).
Time (destruct (m.(dynMap) (existT a r)); [ apply Some | exact None ]).
Time (destruct s).
Time exact (rew H in m0).
Time Defined.
Time Require Import Program.
Time
Lemma getDyn_lookup1 A (Ref Model : A -> Type) (m : DynMap Ref Model) 
  a (r : Ref a) (v : Model a) :
  m.(dynMap) (existT _ r) = Some (existT _ v) \226\134\146 getDyn m a r = Some v.
Time Proof.
Time (unfold getDyn).
Time (destruct m as [map wf]).
Time (simpl).
Time (generalize (wf a r)).
Time (generalize (map (existT a r))).
Time (intros ret Heq).
Time clear.
Time (destruct ret as [(?, ?)| ]; inversion 1).
Time subst.
Time (apply Eqdep.EqdepTheory.inj_pair2 in H2; subst; auto).
Time Qed.
Time
Lemma getDyn_lookup2 A (Ref Model : A -> Type) (m : DynMap Ref Model) 
  a (r : Ref a) (v : Model a) :
  getDyn m a r = Some v \226\134\146 m.(dynMap) (existT _ r) = Some (existT _ v).
Time Proof.
Time (unfold getDyn).
Time (destruct m as [map wf]).
Time (simpl).
Time (generalize (wf a r)).
Time (generalize (map (existT a r))).
Time (intros ret Heq).
Time clear.
Time (destruct ret as [(?, ?)| ]; inversion 1).
Time subst.
Time (unfold eq_rect).
Time auto.
Time Qed.
Time
Lemma getDyn_lookup_none A (Ref Model : A -> Type) 
  (m : DynMap Ref Model) a (r : Ref a) :
  getDyn m a r = None <-> m.(dynMap) (existT _ r) = None.
Time Proof.
Time (unfold getDyn).
Time (destruct m as [map wf]).
Time (simpl).
Time (generalize (wf a r)).
Time (generalize (map (existT a r))).
Time (intros ret Heq).
Time clear.
Time (destruct ret as [(?, ?)| ]; [  | intuition ]).
Time (split; inversion 1).
Time Qed.
Time
Lemma getDyn_lookup_none1 A (Ref Model : A -> Type) 
  (m : DynMap Ref Model) a (r : Ref a) :
  m.(dynMap) (existT _ r) = None -> getDyn m a r = None.
Time Proof.
Time (edestruct getDyn_lookup_none; eauto).
Time Qed.
Time
Lemma getDyn_lookup_none2 A (Ref Model : A -> Type) 
  (m : DynMap Ref Model) a (r : Ref a) :
  getDyn m a r = None -> m.(dynMap) (existT _ r) = None.
Time Proof.
Time (edestruct getDyn_lookup_none; eauto).
Time Qed.
Time Arguments getDyn {A} {Ref} {Model} m {a} r.
Time From stdpp Require Import list.
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
Time
Instance In_dec  {T} {dec : EqualDec T} (a : T) (l : list T):
 (Decision (a \226\136\136 l)).
Time by rewrite HX, (Hf z).
Time Proof.
Time (assert (EqDecision T)).
Time {
Time (unfold EqDecision, EqualDec, Decision in *; eauto).
Time }
Time (apply _).
Time Qed.
Time
Definition updDyn A (Ref Model : A -> Type) {dec : EqualDec (sigT Ref)} 
  a (v : Ref a) (x : Model a) (m : DynMap Ref Model) : 
  DynMap Ref Model.
Time Proof.
Time
refine
 {|
 dynMap := fun r => if r == existT a v then ret! existT a x else m.(dynMap) r;
 dynMap_dom := if decide (existT a v \226\136\136 m.(dynMap_dom))
               then m.(dynMap_dom)
               else existT a v :: m.(dynMap_dom) |}.
Time Qed.
Time {
Time (intros).
Time (destruct (existT _ v0 == existT _ v)).
Time -
Time (inversion e; auto).
Time -
Time (apply (m.(dynMap_wf) _ v0)).
Time }
Time {
Time (intros (a', v')).
Time (destruct (existT _ _ == existT _ v)).
Time #[global]
Instance set_join_proper  {A}: (Proper ((\226\137\161) ==> (\226\137\161)) (@mjoin M _ A)).
Time Proof.
Time (intros X1 X2 HX x).
Time (rewrite !elem_of_join).
Time (f_equiv; intros z).
Time by rewrite HX.
Time -
Time
(abstract (split; auto; intros _; inversion e; subst;
            apply Eqdep.EqdepTheory.inj_pair2 in e; subst; auto;
            case (decide); eauto; intros; by left)).
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
Time -
Time
(abstract (rewrite dynMap_dom_spec; split; case (decide); auto; intros ?;
            [ by
            right
            | rewrite elem_of_cons; intros [| ]; eauto; congruence ])).
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
Time }
Time {
Time (case (decide)).
Time Qed.
Time
Lemma set_unfold_iff P Q P' Q' :
  SetUnfold P P' \226\134\146 SetUnfold Q Q' \226\134\146 SetUnfold (P \226\134\148 Q) (P' \226\134\148 Q').
Time -
Time (intros; apply dynMap_dom_nodup).
Time -
Time (intros Hnotin).
Time (econstructor; [  | apply dynMap_dom_nodup ]; auto).
Time }
Time Defined.
Time Proof.
Time constructor.
Time by rewrite (set_unfold P P'), (set_unfold Q Q').
Time Qed.
Time
Lemma remove_elem_of {A : Type} dec (l : list A) (x : A) :
  ~ x \226\136\136 remove dec x l.
Time Proof.
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
Time (induction l; eauto; simpl; eauto).
Time *
Time (inversion 1).
Time *
Time (destruct dec; subst; eauto).
Time (rewrite elem_of_cons; intuition).
Time Qed.
Time Qed.
Time
Lemma set_unfold_exist {A} (P P' : A \226\134\146 Prop) :
  (\226\136\128 x, SetUnfold (P x) (P' x)) \226\134\146 SetUnfold (\226\136\131 x, P x) (\226\136\131 x, P' x).
Time Proof.
Time constructor.
Time naive_solver.
Time
Lemma remove_elem_of_ne {A : Type} dec (l : list A) 
  (x y : A) : ~ y = x -> y \226\136\136 remove dec x l <-> y \226\136\136 l.
Time Proof.
Time (induction l; eauto).
Time (intros Hneq).
Time (simpl).
Time (destruct dec; subst; rewrite ?elem_of_cons).
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
Time *
Time (rewrite IHl; intuition).
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
Time *
Time (rewrite ?IHl; eauto).
Time Qed.
Time Qed.
Time #[global]
Instance set_unfold_equiv_empty_l  X (P : A \226\134\146 Prop):
 ((\226\136\128 x, SetUnfoldElemOf x X (P x)) \226\134\146 SetUnfold (\226\136\133 \226\137\161 X) (\226\136\128 x, \194\172 P x)) |5.
Time Proof.
Time (intros ?; constructor).
Time (unfold equiv, set_equiv).
Time (pose proof (not_elem_of_empty (C:=C)); naive_solver).
Time
Lemma remove_In_ne {A : Type} dec (l : list A) (x y : A) :
  ~ x = y -> In y (remove dec x l) <-> In y l.
Time Proof.
Time (induction l; eauto).
Time (intros Hneq).
Time (simpl).
Time (destruct dec; subst).
Time *
Time (rewrite IHl; intuition).
Time *
Time (simpl).
Time (rewrite IHl; eauto).
Time Qed.
Time
Lemma remove_NoDup {A : Type} dec (l : list A) (x : A) :
  NoDup l \226\134\146 NoDup (remove dec x l).
Time Proof.
Time (induction 1; simpl).
Time econstructor.
Time (destruct dec; subst; eauto).
Time (econstructor; eauto).
Time (rewrite elem_of_list_In, remove_In_ne; eauto).
Time by rewrite <- elem_of_list_In.
Time Qed.
Time
Definition deleteDyn A (Ref Model : A -> Type) {dec : EqualDec (sigT Ref)} 
  a (v : Ref a) (m : DynMap Ref Model) : DynMap Ref Model.
Time Proof.
Time
refine
 {|
 dynMap := fun r => if r == existT a v then None else m.(dynMap) r;
 dynMap_dom := remove dec (existT a v) m.(dynMap_dom) |}.
Time (intros).
Time (destruct (existT _ v0 == existT _ v)).
Time -
Time auto.
Time -
Time (apply (m.(dynMap_wf) _ v0)).
Time -
Time {
Time (intros (a', v')).
Time (destruct (existT _ _ == existT _ v)).
Time -
Time (split; auto; intros Hin).
Time *
Time by eauto.
Time *
Time (inversion e).
Time subst.
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst; auto).
Time (exfalso; eapply remove_elem_of; eauto).
Time -
Time (rewrite dynMap_dom_spec).
Time (rewrite remove_elem_of_ne; auto).
Time }
Time -
Time (apply remove_NoDup, dynMap_dom_nodup).
Time Defined.
Time Arguments updDyn {A} {Ref} {Model} {dec} {a} v x m.
Time Arguments deleteDyn {A} {Ref} {Model} {dec} {a} v m.
Time Instance empty_dynmap  A Ref Model: (Empty (@DynMap A Ref Model)).
Time refine {| dynMap := fun _ => None; dynMap_dom := nil |}.
Time -
Time (intros; auto).
Time -
Time (abstract (intros; split; try inversion 1; congruence)).
Time -
Time econstructor.
Time Defined.
Time #[global]
Instance DynMap_equiv  A (Ref Model : A \226\134\146 Type): (Equiv (DynMap Ref Model))
 := (\206\187 m m', \226\136\128 a (r : Ref a), getDyn m r = getDyn m' r).
Time #[global]
Instance getDyn_Proper  A (Ref Model : A \226\134\146 Type):
 (Proper (equiv ==> forall_relation (\206\187 a : A, pointwise_relation (Ref a) eq))
    (@getDyn A Ref Model)).
Time Proof.
Time (intros m1 m2 Hequiv).
Time eauto.
Time Qed.
Time #[global]
Instance DynMap_equivalence  A (Ref Model : A \226\134\146 Type):
 (Equivalence (@equiv (DynMap Ref Model) (@DynMap_equiv _ Ref Model))).
Time Proof.
Time split.
Time -
Time (intros m a r; eauto).
Time -
Time (intros m1 m2 a r; eauto).
Time -
Time (intros m1 m2 m3 ? ? a r).
Time (etransitivity; eauto).
Time Qed.
Time
Lemma getDyn_deleteDyn A (Ref Model : A -> Type) {dec : EqualDec (sigT Ref)}
  (m : DynMap Ref Model) a (r : Ref a) : getDyn (deleteDyn r m) r = None.
Time Proof.
Time (intros).
Time (unfold getDyn, deleteDyn).
Time (destruct m as [map wf]).
Time (simpl).
Time (destruct (equal); [  | congruence ]; eauto).
Time Qed.
Time #[global]
Instance set_unfold_equiv_empty_r  (P : A \226\134\146 Prop) 
 X: ((\226\136\128 x, SetUnfoldElemOf x X (P x)) \226\134\146 SetUnfold (X \226\137\161 \226\136\133) (\226\136\128 x, \194\172 P x)) |5.
Time Proof.
Time Qed.
Time (intros ?; constructor).
Time (unfold equiv, set_equiv).
Time (pose proof (not_elem_of_empty (C:=C)); naive_solver).
Time
Lemma getDyn_deleteDyn_ne1 A (Ref Model : A -> Type)
  {dec : EqualDec (sigT Ref)} (m : DynMap Ref Model) 
  a (r1 : Ref a) (r2 : sigT Ref) :
  ~ existT _ r1 = r2 ->
  getDyn (deleteDyn r1 m) (projT2 r2) = getDyn m (projT2 r2).
Time Proof.
Time (unfold getDyn, deleteDyn; simpl).
Time (destruct equal; [  | by congruence ]).
Time (intros).
Time exfalso.
Time (destruct r2).
Time (simpl in *).
Time (inversion e; subst).
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst).
Time intuition.
Time Qed.
Time
Lemma getDyn_deleteDyn_ne2 A (Ref Model : A -> Type)
  {dec : EqualDec (sigT Ref)} (m : DynMap Ref Model) 
  a (r1 r2 : Ref a) : ~ r1 = r2 -> getDyn (deleteDyn r1 m) r2 = getDyn m r2.
Time Proof.
Time replace r2 with projT2 (existT _ r2) by auto.
Time (intros).
Time (apply (getDyn_deleteDyn_ne1 _ (r2:=existT a r2))).
Time (intros Heq).
Time (apply Eqdep.EqdepTheory.inj_pair2 in Heq; subst).
Time intuition.
Time Qed.
Time
Lemma updDyn_deleteDyn A (Ref Model : A -> Type) {dec : EqualDec (sigT Ref)}
  (m : DynMap Ref Model) a (r : Ref a) x :
  updDyn r x (deleteDyn r m) \226\137\161 updDyn r x m.
Time Proof.
Time (intros a' r').
Time (unfold getDyn, updDyn, deleteDyn; simpl).
Time (destruct (equal); eauto).
Time Qed.
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
Time
Lemma getDyn_updDyn A (Ref Model : A -> Type) {dec : EqualDec (sigT Ref)}
  (m : DynMap Ref Model) a x (r : Ref a) : getDyn (updDyn r x m) r = Some x.
Time Proof.
Time (intros ? ?; constructor).
Time
by
 rewrite elem_of_app, (set_unfold_elem_of x l P), (set_unfold_elem_of x k Q).
Time Proof.
Time (unfold getDyn, updDyn; simpl).
Time (destruct equal; [  | by congruence ]).
Time f_equal.
Time (rewrite <- Eqdep.Eq_rect_eq.eq_rect_eq; auto).
Time Qed.
Time Qed.
Time #[global]
Instance set_unfold_included  l k (P Q : A \226\134\146 Prop):
 ((\226\136\128 x, SetUnfoldElemOf x l (P x))
  \226\134\146 (\226\136\128 x, SetUnfoldElemOf x k (Q x)) \226\134\146 SetUnfold (l \226\138\134 k) (\226\136\128 x, P x \226\134\146 Q x)).
Time Proof.
Time (constructor; unfold subseteq, list_subseteq).
Time (apply forall_proper; naive_solver).
Time
Lemma getDyn_updDyn_ne1 A (Ref Model : A -> Type) 
  {dec : EqualDec (sigT Ref)} (m : DynMap Ref Model) 
  a x (r1 : Ref a) (r2 : sigT Ref) :
  ~ existT _ r1 = r2 ->
  getDyn (updDyn r1 x m) (projT2 r2) = getDyn m (projT2 r2).
Time Proof.
Time (unfold getDyn, updDyn; simpl).
Time (destruct equal; [  | by congruence ]).
Time (intros).
Time exfalso.
Time (destruct r2).
Time (simpl in *).
Time (inversion e; subst).
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst).
Time intuition.
Time Qed.
Time Qed.
Time #[global]
Instance set_unfold_reverse  x l P:
 (SetUnfoldElemOf x l P \226\134\146 SetUnfoldElemOf x (reverse l) P).
Time Proof.
Time constructor.
Time by rewrite elem_of_reverse, (set_unfold_elem_of x l P).
Time Qed.
Time #[global]
Instance set_unfold_list_fmap  {B} (f : A \226\134\146 B) l P:
 ((\226\136\128 y, SetUnfoldElemOf y l (P y))
  \226\134\146 SetUnfoldElemOf x (f <$> l) (\226\136\131 y, x = f y \226\136\167 P y)).
Time Proof.
Time constructor.
Time (rewrite elem_of_list_fmap).
Time
Lemma getDyn_updDyn_ne2 A (Ref Model : A -> Type) 
  {dec : EqualDec (sigT Ref)} (m : DynMap Ref Model) 
  a x (r1 r2 : Ref a) : ~ r1 = r2 -> getDyn (updDyn r1 x m) r2 = getDyn m r2.
Time Proof.
Time replace r2 with projT2 (existT _ r2) by auto.
Time (intros).
Time (apply (getDyn_updDyn_ne1 _ _ (r2:=existT a r2))).
Time (intros Heq).
Time (apply Eqdep.EqdepTheory.inj_pair2 in Heq; subst).
Time intuition.
Time Qed.
Time (f_equiv; intros y).
Time by rewrite (set_unfold_elem_of y l (P y)).
Time #[global]
Instance updDyn_Proper  A (Ref Model : A \226\134\146 Type) {dec : EqualDec (sigT Ref)}
 a (r : Ref a) (x : Model a): (Proper (equiv ==> equiv) (updDyn r x)).
Time Proof.
Time (intros m1 m2 Hequiv a' r').
Time (destruct (dec (existT _ r) (existT _ r'))).
Time -
Time (inversion e).
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
Time subst.
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst).
Time by rewrite ?getDyn_updDyn.
Time -
Time (rewrite ?(getDyn_updDyn_ne1 _ _ (r2:=existT a' r')); eauto).
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
Time #[global]
Instance deleteDyn_Proper  A (Ref Model : A \226\134\146 Type)
 {dec : EqualDec (sigT Ref)} a (r : Ref a):
 (Proper (equiv ==> equiv) (deleteDyn (Model:=Model) r)).
Time Proof.
Time (intros m1 m2 Hequiv a' r').
Time (destruct (dec (existT _ r) (existT _ r'))).
Time -
Time (inversion e).
Time subst.
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst).
Time by rewrite ?getDyn_deleteDyn.
Time -
Time (rewrite ?(getDyn_deleteDyn_ne1 _ (r2:=existT a' r')); eauto).
Time Qed.
Time
Lemma updDyn_identity A (Ref Model : A -> Type) {dec : EqualDec (sigT Ref)}
  (m : DynMap Ref Model) a (r : Ref a) x :
  getDyn m r = Some x \226\134\146 updDyn r x m \226\137\161 m.
Time Proof.
Time (intros Hlookup a' r').
Time (destruct (dec (existT _ r) (existT _ r'))).
Time Qed.
Time *
Time (inversion e; subst).
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst).
Time by rewrite getDyn_updDyn.
Time *
Time replace r' with projT2 (existT _ r') by auto.
Time #[global]Instance set_subseteq_antisymm : (AntiSymm (\226\137\161) (\226\138\134@{C} )).
Time Proof.
Time (intros ? ?).
Time set_solver.
Time (rewrite (getDyn_updDyn_ne1 _ _ (r2:=existT a' r')); eauto).
Time Qed.
Time
Lemma dynMap_dom_spec' A (Ref Model : A -> Type) (m : DynMap Ref Model) 
  a (x : Ref a) : getDyn m x <> None <-> existT _ x \226\136\136 dynMap_dom m.
Time Proof.
Time by rewrite <- dynMap_dom_spec, getDyn_lookup_none.
Time Qed.
Time
Lemma dynMap_dom_non_spec A (Ref Model : A -> Type) 
  (m : DynMap Ref Model) a (x : Ref a) :
  getDyn m x = None <-> \194\172 existT _ x \226\136\136 dynMap_dom m.
Time Proof.
Time (rewrite <- dynMap_dom_spec').
Time Qed.
Time #[global]Instance set_subseteq_preorder : (PreOrder (\226\138\134@{C} )).
Time Proof.
Time split.
Time by intros ? ?.
Time (intros ? ? ?; set_solver).
Time (destruct getDyn; auto; split; firstorder).
Time Qed.
Time
Lemma dynMap_equiv_perm_dom A (Ref Model : A -> Type)
  (m1 m2 : DynMap Ref Model) : m1 \226\137\161 m2 \226\134\146 dynMap_dom m1 \226\137\161\226\130\154 dynMap_dom m2.
Time Proof.
Time (intros Hequiv).
Time (apply NoDup_Permutation; eauto using dynMap_dom_nodup).
Time (intros (a, x)).
Time by rewrite <- ?dynMap_dom_spec', Hequiv.
Time Qed.
Time Lemma subseteq_union X Y : X \226\138\134 Y \226\134\148 X \226\136\170 Y \226\137\161 Y.
Time Proof.
Time set_solver.
Time Qed.
Time #[global]
Instance dynMap_dom_Proper  A (Ref Model : A \226\134\146 Type):
 (Proper (equiv ==> (\226\137\161\226\130\154)) (@dynMap_dom A Ref Model)).
Time Proof.
Time (intros m1 m2 Hequiv).
Time (eapply dynMap_equiv_perm_dom; eauto).
Time Qed.
Time
Lemma dynMap_dom_empty_iff A (Ref Model : A -> Type) 
  (m : DynMap Ref Model) : m \226\137\161 \226\136\133 <-> dynMap_dom m = [].
Time Proof.
Time split.
Time -
Time (intros Hequiv).
Time (apply Permutation_nil).
Time (rewrite Hequiv; eauto).
Time -
Time (intros Hdom a k).
Time (unfold getDyn at 2; simpl).
Time (rewrite dynMap_dom_non_spec, Hdom).
Time (inversion 1).
Time Qed.
Time
Lemma dynMap_dom_lookup A (Ref Model : A -> Type) 
  (m : DynMap Ref Model) (k : nat) (y : {a : A & Ref a}) :
  m.(dynMap_dom) !! k = Some y -> exists v, getDyn m (projT2 y) = Some v.
Time Proof.
Time (intros Hin%elem_of_list_lookup_2).
Time replace y with existT _ (projT2 y) in Hin by (destruct y; eauto).
Time (rewrite <- dynMap_dom_spec' in Hin).
Time Qed.
Time Lemma subseteq_union_1 X Y : X \226\138\134 Y \226\134\146 X \226\136\170 Y \226\137\161 Y.
Time Proof.
Time by rewrite subseteq_union.
Time (destruct getDyn as [?| ] eqn:Heq; eauto; congruence).
Time Qed.
Time Lemma subseteq_union_2 X Y : X \226\136\170 Y \226\137\161 Y \226\134\146 X \226\138\134 Y.
Time Proof.
Time by rewrite subseteq_union.
Time Qed.
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
Time Lemma subseteq_difference_r X Y1 Y2 : X ## Y2 \226\134\146 X \226\138\134 Y1 \226\134\146 X \226\138\134 Y1 \226\136\150 Y2.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma subseteq_difference_l X1 X2 Y : X1 \226\138\134 Y \226\134\146 X1 \226\136\150 X2 \226\138\134 Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_intersection X Y : X ## Y \226\134\148 X \226\136\169 Y \226\137\161 \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_difference_l1 X1 X2 Y : Y \226\138\134 X2 \226\134\146 X1 \226\136\150 X2 ## Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_difference_l2 X1 X2 Y : X1 ## Y \226\134\146 X1 \226\136\150 X2 ## Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_difference_r1 X Y1 Y2 : X \226\138\134 Y2 \226\134\146 X ## Y1 \226\136\150 Y2.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma disjoint_difference_r2 X Y1 Y2 : X ## Y1 \226\134\146 X ## Y1 \226\136\150 Y2.
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
Time
Lemma set_Forall_list_to_set l :
  set_Forall P (list_to_set (C:=C) l) \226\134\148 Forall P l.
Time Proof.
Time (rewrite Forall_forall).
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
Time
Lemma set_Exists_list_to_set l :
  set_Exists P (list_to_set (C:=C) l) \226\134\148 Exists P l.
Time Proof.
Time (rewrite Exists_exists).
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
