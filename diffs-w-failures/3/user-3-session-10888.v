Time From Classes Require Import EqualDec.
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
Instance In_dec  {T} {dec : EqualDec T} (a : T) (l : list T):
 (Decision (a \226\136\136 l)).
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
Time -
Time
(abstract (split; auto; intros _; inversion e; subst;
            apply Eqdep.EqdepTheory.inj_pair2 in e; subst; auto;
            case (decide); eauto; intros; by left)).
Time -
Time
(abstract (rewrite dynMap_dom_spec; split; case (decide); auto; intros ?;
            [ by
            right
            | rewrite elem_of_cons; intros [| ]; eauto; congruence ])).
Time }
Time {
Time (case (decide)).
Time -
Time (intros; apply dynMap_dom_nodup).
Time -
Time (intros Hnotin).
Time (econstructor; [  | apply dynMap_dom_nodup ]; auto).
Time }
Time Defined.
Time
Lemma remove_elem_of {A : Type} dec (l : list A) (x : A) :
  ~ x \226\136\136 remove dec x l.
Time Proof.
Time (induction l; eauto; simpl; eauto).
Time *
Time (inversion 1).
Time *
Time (destruct dec; subst; eauto).
Time (rewrite elem_of_cons; intuition).
Time Qed.
Time
Lemma remove_elem_of_ne {A : Type} dec (l : list A) 
  (x y : A) : ~ y = x -> y \226\136\136 remove dec x l <-> y \226\136\136 l.
Time Proof.
Time (induction l; eauto).
Time (intros Hneq).
Time (simpl).
Time (destruct dec; subst; rewrite ?elem_of_cons).
Time *
Time (rewrite IHl; intuition).
Time *
Time (rewrite ?IHl; eauto).
Time Qed.
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
Time
Lemma getDyn_updDyn A (Ref Model : A -> Type) {dec : EqualDec (sigT Ref)}
  (m : DynMap Ref Model) a x (r : Ref a) : getDyn (updDyn r x m) r = Some x.
Time Proof.
Time (unfold getDyn, updDyn; simpl).
Time (destruct equal; [  | by congruence ]).
Time f_equal.
Time (rewrite <- Eqdep.Eq_rect_eq.eq_rect_eq; auto).
Time Qed.
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
Time #[global]
Instance updDyn_Proper  A (Ref Model : A \226\134\146 Type) {dec : EqualDec (sigT Ref)}
 a (r : Ref a) (x : Model a): (Proper (equiv ==> equiv) (updDyn r x)).
Time Proof.
Time (intros m1 m2 Hequiv a' r').
Time (destruct (dec (existT _ r) (existT _ r'))).
Time -
Time (inversion e).
Time subst.
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst).
Time by rewrite ?getDyn_updDyn.
Time -
Time (rewrite ?(getDyn_updDyn_ne1 _ _ (r2:=existT a' r')); eauto).
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
Time *
Time (inversion e; subst).
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst).
Time by rewrite getDyn_updDyn.
Time *
Time replace r' with projT2 (existT _ r') by auto.
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
Time (destruct getDyn as [?| ] eqn:Heq; eauto; congruence).
Time Qed.
