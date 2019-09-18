Time From stdpp Require Export fin list.
Time From Classes Require Import EqualDec.
Time From stdpp Require Import base.
Time From Transitions Require Import Relations.
Time From Armada Require Import Spec.Proc.
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
Time Set Default Proof Using "Type".
Time Open Scope vector_scope.
Time Notation vec := Vector.t.
Time Notation vnil := Vector.nil.
Time Arguments vnil {_}.
Time Notation vcons := Vector.cons.
Time Notation vapp := Vector.append.
Time Arguments vcons {_} _ {_} _.
Time Infix ":::" := vcons (at level 60, right associativity) : vector_scope.
Time Notation "(:::)" := vcons (only parsing) : vector_scope.
Time Notation "( x :::)" := (vcons x) (only parsing) : vector_scope.
Time Notation "(::: v )" := (\206\187 x, vcons x v) (only parsing) : vector_scope.
Time Notation "[# ] " := vnil : vector_scope.
Time Notation "[# x ] " := (vcons x vnil) : vector_scope.
Time
Notation "[# x ; .. ; y ] " := (vcons x .. (vcons y vnil) ..) : vector_scope.
Time Infix "+++" := vapp (at level 60, right associativity) : vector_scope.
Time Notation "(+++)" := vapp (only parsing) : vector_scope.
Time Notation "( v +++)" := (vapp v) (only parsing) : vector_scope.
Time Notation "(+++ w )" := (\206\187 v, vapp v w) (only parsing) : vector_scope.
Time Arguments Vector.nth {_} {_} !_ !_%fin /.
Time Infix "!!!" := Vector.nth (at level 20) : vector_scope.
Time Notation vec_rect2 := Vector.rect2.
Time
Ltac
 vec_double_ind v1 v2 :=
  match type of v1 with
  | vec _ ?n =>
      repeat
       match goal with
       | H':context [ n ] |- _ => var_neq v1 H'; var_neq v2 H'; revert H'
       end; revert n v1 v2;
       match goal with
       | |- \226\136\128 n v1 v2, @?P n v1 v2 => apply (vec_rect2 P)
       end
  end.
Time Notation vcons_inj := VectorSpec.cons_inj.
Time
Lemma vcons_inj_1 {A} {n} x y (v w : vec A n) : x ::: v = y ::: w \226\134\146 x = y.
Time Proof.
Time (apply vcons_inj).
Time Qed.
Time
Lemma vcons_inj_2 {A} {n} x y (v w : vec A n) : x ::: v = y ::: w \226\134\146 v = w.
Time Proof.
Time (apply vcons_inj).
Time Qed.
Time Lemma vec_eq {A} {n} (v w : vec A n) : (\226\136\128 i, v !!! i = w !!! i) \226\134\146 v = w.
Time Proof.
Time (vec_double_ind v w; [ done |  ]).
Time (intros n v w IH x y Hi).
Time f_equal.
Time -
Time (apply (Hi 0%fin)).
Time -
Time (apply IH).
Time (intros i).
Time (apply (Hi (FS i))).
Time Qed.
Time Instance vec_dec  {A} {dec : EqDecision A} {n}: (EqDecision (vec A n)).
Time Proof.
Time
(refine
  (vec_rect2 (\206\187 n (v w : vec A n), {v = w} + {v \226\137\160 w}) 
     (left _) (\206\187 _ _ _ H x y, cast_if_and (dec x y) H)); f_equal; eauto
  using vcons_inj_1, vcons_inj_2).
Time Defined.
Time Notation vec_0_inv := Vector.case0.
Time
Definition vec_S_inv {A} {n} (P : vec A (S n) \226\134\146 Type)
  (Hcons : \226\136\128 x v, P (x ::: v)) v : P v.
Time Proof.
Time revert P Hcons.
Time refine match v with
            | [# ] => tt
            | x ::: v => \206\187 P Hcons, Hcons x v
            end.
Time Defined.
Time
Ltac
 inv_vec v :=
  let T := type of v in
  match eval hnf in T with
  | vec _ ?n =>
      match eval hnf in n with
      | 0 =>
          revert dependent v;
           match goal with
           | |- \226\136\128 v, @?P v => apply (vec_0_inv P)
           end
      | S ?n =>
          revert dependent v;
           match goal with
           | |- \226\136\128 v, @?P v => apply (vec_S_inv P)
           end; try (let x := fresh "x" in
                     intros x v; inv_vec v; revert x)
      end
  end.
Time
Ltac
 inv_all_vec_fin :=
  block_goal;
   repeat
    match goal with
    | v:vec _ _ |- _ => inv_vec v; intros
    | i:fin _ |- _ => inv_fin i; intros
    end; unblock_goal.
Time
Fixpoint vec_to_list {A n} (v : vec A n) : list A :=
  match v with
  | [# ] => []
  | x ::: v => x :: vec_to_list v
  end.
Time Coercion vec_to_list : vec >-> list.
Time Notation list_to_vec := Vector.of_list.
Time
Lemma vec_to_list_cons {A} {n} x (v : vec A n) :
  vec_to_list (x ::: v) = x :: vec_to_list v.
Time Proof.
Time done.
Time Qed.
Time
Lemma vec_to_list_app {A} {n} {m} (v : vec A n) (w : vec A m) :
  vec_to_list (v +++ w) = vec_to_list v ++ vec_to_list w.
Time Proof.
Time by induction v; f_equal /=.
Time Qed.
Time
Lemma vec_to_list_of_list {A} (l : list A) : vec_to_list (list_to_vec l) = l.
Time Proof.
Time by induction l; f_equal /=.
Time Qed.
Time
Lemma vec_to_list_length {A} {n} (v : vec A n) : length (vec_to_list v) = n.
Time Proof.
Time (induction v; simpl; by f_equal).
Time Qed.
Time
Lemma vec_to_list_same_length {A} {B} {n} (v : vec A n) 
  (w : vec B n) : length v = length w.
Time Proof.
Time by rewrite !vec_to_list_length.
Time Qed.
Time
Lemma vec_to_list_inj1 {A} {n} {m} (v : vec A n) (w : vec A m) :
  vec_to_list v = vec_to_list w \226\134\146 n = m.
Time Proof.
Time revert m w.
Time (induction v; intros ? [| ? ? ?] ?; simplify_eq /=; f_equal; eauto).
Time Qed.
Time
Lemma vec_to_list_inj2 {A} {n} (v : vec A n) (w : vec A n) :
  vec_to_list v = vec_to_list w \226\134\146 v = w.
Time Proof.
Time revert w.
Time
(induction v; intros w; inv_vec w; intros; simplify_eq /=; f_equal; eauto).
Time Qed.
Time
Lemma vlookup_middle {A} {n} {m} (v : vec A n) (w : vec A m) 
  x : \226\136\131 i : fin (n + S m), x = (v +++ x ::: w) !!! i.
Time Proof.
Time (induction v; simpl; [ by eexists 0%fin |  ]).
Time (destruct IHv as [i ?]).
Time by exists (FS i).
Time Qed.
Time
Lemma vec_to_list_lookup_middle {A} {n} (v : vec A n) 
  (l k : list A) x :
  vec_to_list v = l ++ x :: k
  \226\134\146 \226\136\131 i : fin n, l = take i v \226\136\167 x = v !!! i \226\136\167 k = drop (S i) v.
Time Proof.
Time (intros H).
Time (rewrite <- (vec_to_list_of_list l), <- (vec_to_list_of_list k) in H).
Time (rewrite <- vec_to_list_cons, <- vec_to_list_app in H).
Time (pose proof (vec_to_list_inj1 _ _ H); subst).
Time (apply vec_to_list_inj2 in H; subst).
Time (induction l).
Time (simpl).
Time -
Time eexists 0%fin.
Time (simpl).
Time by rewrite vec_to_list_of_list.
Time -
Time (destruct IHl as [i ?]).
Time exists (FS i).
Time (simpl).
Time intuition congruence.
Time Qed.
Time
Lemma vec_to_list_drop_lookup {A} {n} (v : vec A n) 
  (i : fin n) : drop i v = v !!! i :: drop (S i) v.
Time Proof.
Time (induction i; inv_vec v; simpl; intros; [ done | by rewrite IHi ]).
Time Qed.
Time
Lemma vec_to_list_take_drop_lookup {A} {n} (v : vec A n) 
  (i : fin n) : vec_to_list v = take i v ++ v !!! i :: drop (S i) v.
Time Proof.
Time (rewrite <- (take_drop i v)  at 1).
Time by rewrite vec_to_list_drop_lookup.
Time Qed.
Time
Lemma vlookup_lookup {A} {n} (v : vec A n) (i : fin n) 
  x : v !!! i = x \226\134\148 (v : list A) !! (i : nat) = Some x.
Time Proof.
Time (induction v as [| ? ? v IH]; inv_fin i).
Time (simpl; split; congruence).
Time done.
Time Qed.
Time
Lemma vlookup_lookup' {A} {n} (v : vec A n) (i : nat) 
  x : (\226\136\131 H : i < n, v !!! fin_of_nat H = x) \226\134\148 (v : list A) !! i = Some x.
Time Proof.
Time split.
Time -
Time (intros [Hlt ?]).
Time (rewrite <- (fin_to_of_nat i n Hlt)).
Time by apply vlookup_lookup.
Time -
Time (intros Hvix).
Time (pose proof (lookup_lt_Some _ _ _ Hvix) as Hlt).
Time (rewrite vec_to_list_length in Hlt).
Time exists Hlt.
Time (apply vlookup_lookup).
Time by rewrite fin_to_of_nat.
Time Qed.
Time
Lemma elem_of_vlookup {A} {n} (v : vec A n) x :
  x \226\136\136 vec_to_list v \226\134\148 (\226\136\131 i, v !!! i = x).
Time Proof.
Time (rewrite elem_of_list_lookup).
Time setoid_rewrite  <- vlookup_lookup'.
Time (split; [ by intros (?, (?, ?)); eauto |  ]).
Time (intros [i Hx]).
Time exists i,(fin_to_nat_lt _).
Time by rewrite fin_of_to_nat.
Time Qed.
Time
Lemma Forall_vlookup {A} (P : A \226\134\146 Prop) {n} (v : vec A n) :
  Forall P (vec_to_list v) \226\134\148 (\226\136\128 i, P (v !!! i)).
Time Proof.
Time (rewrite Forall_forall).
Time setoid_rewrite elem_of_vlookup.
Time naive_solver.
Time Qed.
Time
Lemma Forall_vlookup_1 {A} (P : A \226\134\146 Prop) {n} (v : vec A n) 
  i : Forall P (vec_to_list v) \226\134\146 P (v !!! i).
Time Proof.
Time by rewrite Forall_vlookup.
Time Qed.
Time
Lemma Forall_vlookup_2 {A} (P : A \226\134\146 Prop) {n} (v : vec A n) :
  (\226\136\128 i, P (v !!! i)) \226\134\146 Forall P (vec_to_list v).
Time Proof.
Time by rewrite Forall_vlookup.
Time Qed.
Time
Lemma Exists_vlookup {A} (P : A \226\134\146 Prop) {n} (v : vec A n) :
  Exists P (vec_to_list v) \226\134\148 (\226\136\131 i, P (v !!! i)).
Time Proof.
Time (rewrite Exists_exists).
Time setoid_rewrite elem_of_vlookup.
Time naive_solver.
Time Qed.
Time
Lemma Forall2_vlookup {A} {B} (P : A \226\134\146 B \226\134\146 Prop) {n} 
  (v1 : vec A n) (v2 : vec B n) :
  Forall2 P (vec_to_list v1) (vec_to_list v2)
  \226\134\148 (\226\136\128 i, P (v1 !!! i) (v2 !!! i)).
Time Proof.
Time split.
Time -
Time (vec_double_ind v1 v2; [ intros _ i; inv_fin i |  ]).
Time (intros n v1 v2 IH a b; simpl).
Time (inversion_clear 1).
Time (intros i).
Time (inv_fin i; simpl; auto).
Time -
Time (vec_double_ind v1 v2; [ constructor |  ]).
Time (intros ? ? ? IH ? ? H).
Time constructor.
Time (apply (H 0%fin)).
Time (apply IH, (\206\187 i, H (FS i))).
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
Time Qed.
Time Notation vmap := Vector.map.
Time
Lemma vlookup_map `(f : A \226\134\146 B) {n} (v : vec A n) i :
  vmap f v !!! i = f (v !!! i).
Time Proof.
Time by apply Vector.nth_map.
Time Qed.
Time
Lemma vec_to_list_map `(f : A \226\134\146 B) {n} (v : vec A n) :
  vec_to_list (vmap f v) = f <$> vec_to_list v.
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
Time Proof.
Time (induction v; simpl).
Time done.
Time by rewrite IHv.
Time Qed.
Time Notation vzip_with := Vector.map2.
Time
Lemma vlookup_zip_with `(f : A \226\134\146 B \226\134\146 C) {n} (v1 : vec A n) 
  (v2 : vec B n) i : vzip_with f v1 v2 !!! i = f (v1 !!! i) (v2 !!! i).
Time Proof.
Time by apply Vector.nth_map2.
Time Qed.
Time
Lemma vec_to_list_zip_with `(f : A \226\134\146 B \226\134\146 C) {n} (v1 : vec A n) 
  (v2 : vec B n) :
  vec_to_list (vzip_with f v1 v2) =
  zip_with f (vec_to_list v1) (vec_to_list v2).
Time -
Time (inversion e; auto).
Time -
Time (apply (m.(dynMap_wf) _ v0)).
Time }
Time {
Time (intros (a', v')).
Time (destruct (existT _ _ == existT _ v)).
Time Proof.
Time revert v2.
Time (induction v1; intros v2; inv_vec v2; intros; simpl; [ done |  ]).
Time by rewrite IHv1.
Time Qed.
Time
Fixpoint vinsert {A n} (i : fin n) (x : A) : vec A n \226\134\146 vec A n :=
  match i with
  | 0%fin => vec_S_inv _ (\206\187 _ v, x ::: v)
  | FS i => vec_S_inv _ (\206\187 y v, y ::: vinsert i x v)
  end.
Time
Lemma vec_to_list_insert {A} {n} i x (v : vec A n) :
  vec_to_list (vinsert i x v) = insert (fin_to_nat i) x (vec_to_list v).
Time Proof.
Time (induction v; inv_fin i).
Time done.
Time (simpl).
Time (intros).
Time by rewrite IHv.
Time Qed.
Time
Lemma vlookup_insert {A} {n} i x (v : vec A n) : vinsert i x v !!! i = x.
Time -
Time
(abstract (split; auto; intros _; inversion e; subst;
            apply Eqdep.EqdepTheory.inj_pair2 in e; subst; auto;
            case (decide); eauto; intros; by left)).
Time Proof.
Time by induction i; inv_vec v.
Time Qed.
Time
Lemma vlookup_insert_ne {A} {n} i j x (v : vec A n) :
  i \226\137\160 j \226\134\146 vinsert i x v !!! j = v !!! j.
Time Proof.
Time (induction i; inv_fin j; inv_vec v; simpl; try done).
Time (intros).
Time (apply IHi).
Time congruence.
Time Qed.
Time
Lemma vlookup_insert_self {A} {n} i (v : vec A n) : vinsert i (v !!! i) v = v.
Time Proof.
Time by induction v; inv_fin i; intros; f_equal /=.
Time -
Time
(abstract (rewrite dynMap_dom_spec; split; case (decide); auto; intros ?;
            [ by
            right
            | rewrite elem_of_cons; intros [| ]; eauto; congruence ])).
Time Qed.
Time
Lemma vmap_insert {A} {B} (f : A \226\134\146 B) (n : nat) i 
  x (v : vec A n) : vmap f (vinsert i x v) = vinsert i (f x) (vmap f v).
Time Proof.
Time (induction v; inv_fin i; intros; f_equal /=; auto).
Time Qed.
Time
Fixpoint vtake {A n} (i : fin n) : vec A n \226\134\146 vec A i :=
  match i in (fin n) return (vec A n \226\134\146 vec A i) with
  | 0%fin => \206\187 _, [# ]
  | FS i => vec_S_inv _ (\206\187 x v, x ::: vtake i v)
  end.
Time
Fixpoint vdrop {A n} (i : fin n) : vec A n \226\134\146 vec A (n - i) :=
  match i in (fin n) return (vec A n \226\134\146 vec A (n - i)) with
  | 0%fin => id
  | FS i => vec_S_inv _ (\206\187 _, vdrop i)
  end.
Time
Lemma vec_to_list_take {A} {n} i (v : vec A n) :
  vec_to_list (vtake i v) = take (fin_to_nat i) (vec_to_list v).
Time Proof.
Time (induction i; inv_vec v; intros; f_equal /=; auto).
Time Qed.
Time
Lemma vec_to_list_drop {A} {n} i (v : vec A n) :
  vec_to_list (vdrop i v) = drop (fin_to_nat i) (vec_to_list v).
Time Proof.
Time (induction i; inv_vec v; intros; f_equal /=; auto).
Time }
Time {
Time (case (decide)).
Time -
Time (intros; apply dynMap_dom_nodup).
Time -
Time (intros Hnotin).
Time (econstructor; [  | apply dynMap_dom_nodup ]; auto).
Time Qed.
Time
Fixpoint vreplicate {A} (n : nat) (x : A) : vec A n :=
  match n with
  | 0 => [# ]
  | S n => x ::: vreplicate n x
  end.
Time
Lemma vec_to_list_replicate {A} n (x : A) :
  vec_to_list (vreplicate n x) = replicate n x.
Time }
Time Defined.
Time Proof.
Time (induction n; by f_equal /=).
Time Qed.
Time Lemma vlookup_replicate {A} n (x : A) i : vreplicate n x !!! i = x.
Time Proof.
Time (induction i; f_equal /=; auto).
Time Qed.
Time
Lemma remove_elem_of {A : Type} dec (l : list A) (x : A) :
  ~ x \226\136\136 remove dec x l.
Time Proof.
Time (induction l; eauto; simpl; eauto).
Time *
Time (inversion 1).
Time
Lemma vmap_replicate {A} {B} (f : A \226\134\146 B) n (x : A) :
  vmap f (vreplicate n x) = vreplicate n (f x).
Time Proof.
Time (induction n; f_equal /=; auto).
Time Qed.
Time #[global]
Instance vec_0_inhabited  T: (Inhabited (vec T 0)) := (populate [# ]).
Time #[global]
Instance vec_inhabited  `{Inhabited T} n: (Inhabited (vec T n)) :=
 (populate (vreplicate n inhabitant)).
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
