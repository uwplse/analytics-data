Time From stdpp Require Import base tactics.
Time Set Default Proof Using "Type".
Time #[local]Set Universe Polymorphism.
Time
Inductive tele : Type :=
  | TeleO : tele
  | TeleS : forall {X} (binder : X \226\134\146 tele), tele.
Time Arguments TeleS {_} _.
Time
Fixpoint tele_fun (TT : tele) (T : Type) : Type :=
  match TT with
  | TeleO => T
  | TeleS b => \226\136\128 x, tele_fun (b x) T
  end.
Time
Notation "TT -t> A" := (tele_fun TT A)
  (at level 99, A  at level 200, right associativity).
Time
Definition tele_fold {X} {Y} {TT : tele} (step : \226\136\128 {A : Type}, (A \226\134\146 Y) \226\134\146 Y)
  (base : X \226\134\146 Y) : (TT -t> X) \226\134\146 Y :=
  (fix rec {TT} : (TT -t> X) \226\134\146 Y :=
     match TT as TT return ((TT -t> X) \226\134\146 Y) with
     | TeleO => \206\187 x : X, base x
     | TeleS b => \206\187 f, step (\206\187 x, rec (f x))
     end) TT.
Time Arguments tele_fold {_} {_} {!_} _ _ _ /.
Time
Inductive tele_arg : tele \226\134\146 Type :=
  | TargO : tele_arg TeleO
  | TargS :
      forall {X} {binder} (x : X),
      tele_arg (binder x) \226\134\146 tele_arg (TeleS binder).
Time
Definition tele_app {TT : tele} {T} (f : TT -t> T) : 
  tele_arg TT \226\134\146 T :=
  \206\187 a,
    (fix rec {TT} (a : tele_arg TT) : (TT -t> T) \226\134\146 T :=
       match a in (tele_arg TT) return ((TT -t> T) \226\134\146 T) with
       | TargO => \206\187 t : T, t
       | TargS x a => \206\187 f, rec a (f x)
       end) TT a f.
Time Arguments tele_app {!_} {_} _ !_ /.
Time Coercion tele_arg : tele >-> Sortclass.
Time #[local]Coercion tele_app : tele_fun >-> Funclass.
Time
Lemma tele_arg_inv {TT : tele} (a : TT) :
  match TT as TT return (TT \226\134\146 Prop) with
  | TeleO => \206\187 a, a = TargO
  | TeleS f => \206\187 a, \226\136\131 x a', a = TargS x a'
  end a.
Time Proof.
Time (induction a; eauto).
Time Qed.
Time Lemma tele_arg_O_inv (a : TeleO) : a = TargO.
Time Proof.
Time exact (tele_arg_inv a).
Time Qed.
Time
Lemma tele_arg_S_inv {X} {f : X \226\134\146 tele} (a : TeleS f) :
  \226\136\131 x a', a = TargS x a'.
Time Proof.
Time exact (tele_arg_inv a).
Time Qed.
Time
Fixpoint tele_map {T U} {TT : tele} : (T \226\134\146 U) \226\134\146 (TT -t> T) \226\134\146 TT -t> U :=
  match TT as TT return ((T \226\134\146 U) \226\134\146 (TT -t> T) \226\134\146 TT -t> U) with
  | TeleO => \206\187 F : T \226\134\146 U, F
  | @TeleS X b => \206\187 (F : T \226\134\146 U) (f : TeleS b -t> T) (x : X), tele_map F (f x)
  end.
Time Arguments tele_map {_} {_} {!_} _ _ /.
Time
Lemma tele_map_app {T} {U} {TT : tele} (F : T \226\134\146 U) 
  (t : TT -t> T) (x : TT) : (tele_map F t) x = F (t x).
Time Proof.
Time (induction TT as [| X f IH]; simpl in *).
Time -
Time (rewrite (tele_arg_O_inv x)).
Time done.
Time -
Time (destruct (tele_arg_S_inv x) as [x' [a' ->]]).
Time (simpl).
Time (rewrite <- IH).
Time done.
Time Qed.
Time #[global]
Instance tele_fmap  {TT : tele}: (FMap (tele_fun TT)) := (\206\187 T U, tele_map).
Time
Lemma tele_fmap_app {T} {U} {TT : tele} (F : T \226\134\146 U) 
  (t : TT -t> T) (x : TT) : (F <$> t) x = F (t x).
Time Proof.
Time (apply tele_map_app).
Time Qed.
Time
Fixpoint tele_bind {U} {TT : tele} : (TT \226\134\146 U) \226\134\146 TT -t> U :=
  match TT as TT return ((TT \226\134\146 U) \226\134\146 TT -t> U) with
  | TeleO => \206\187 F, F TargO
  | @TeleS X b => \206\187 (F : TeleS b \226\134\146 U) (x : X), tele_bind (\206\187 a, F (TargS x a))
  end.
Time Arguments tele_bind {_} {!_} _ /.
Time
Lemma tele_app_bind {U} {TT : tele} (f : TT \226\134\146 U) x :
  (tele_app $ tele_bind f) x = f x.
Time Proof.
Time (induction TT as [| X b IH]; simpl in *).
Time -
Time (rewrite (tele_arg_O_inv x)).
Time done.
Time -
Time (destruct (tele_arg_S_inv x) as [x' [a' ->]]).
Time (simpl).
Time (rewrite IH).
Time done.
Time Qed.
Time Definition tele_fun_id {TT : tele} : TT -t> TT := tele_bind id.
Time Lemma tele_fun_id_eq {TT : tele} (x : TT) : tele_fun_id x = x.
Time Proof.
Time (unfold tele_fun_id).
Time (rewrite tele_app_bind).
Time done.
Time Qed.
Time
Definition tele_fun_compose {TT1 TT2 TT3 : tele} :
  (TT2 -t> TT3) \226\134\146 (TT1 -t> TT2) \226\134\146 TT1 -t> TT3 :=
  \206\187 t1 t2, tele_bind (compose (tele_app t1) (tele_app t2)).
Time
Lemma tele_fun_compose_eq {TT1 TT2 TT3 : tele} (f : TT2 -t> TT3)
  (g : TT1 -t> TT2) x : tele_fun_compose f g $ x = (f \226\136\152 g) x.
Time Proof.
Time (unfold tele_fun_compose).
Time (rewrite tele_app_bind).
Time done.
Time Qed.
Time
Notation "'[tele' x .. z ]" :=
  (TeleS (fun x => .. (TeleS (fun z => TeleO)) ..))
  (x binder, z binder, format "[tele  '[hv' x  ..  z ']' ]").
Time Notation "'[tele' ]" := TeleO (format "[tele ]").
Time
Notation "'[tele_arg' x ; .. ; z ]" := (TargS x .. (TargS z TargO) ..)
  (format "[tele_arg  '[hv' x ;  .. ;  z ']' ]").
Time Notation "'[tele_arg' ]" := TargO (format "[tele_arg ]").
Time
Notation "'\206\187..' x .. y , e" :=
  (tele_app (tele_bind (\206\187 x, .. (tele_app (tele_bind (\206\187 y, e))) ..)))
  (at level 200, x binder, y binder, right associativity,
   format "'[  ' '\206\187..'  x  ..  y ']' ,  e") : stdpp_scope.
Time
Definition tforall {TT : tele} (\206\168 : TT \226\134\146 Prop) : Prop :=
  tele_fold (\206\187 (T : Type) (b : T \226\134\146 Prop), \226\136\128 x : T, b x) 
    (\206\187 x, x) (tele_bind \206\168).
Time Arguments tforall {!_} _ /.
Time
Definition texist {TT : tele} (\206\168 : TT \226\134\146 Prop) : Prop :=
  tele_fold ex (\206\187 x, x) (tele_bind \206\168).
Time Arguments texist {!_} _ /.
Time
Notation "'\226\136\128..' x .. y , P" := (tforall (\206\187 x, .. (tforall (\206\187 y, P)) ..))
  (at level 200, x binder, y binder, right associativity,
   format "\226\136\128..  x  ..  y ,  P") : stdpp_scope.
Time
Notation "'\226\136\131..' x .. y , P" := (texist (\206\187 x, .. (texist (\206\187 y, P)) ..))
  (at level 200, x binder, y binder, right associativity,
   format "\226\136\131..  x  ..  y ,  P") : stdpp_scope.
Time
Lemma tforall_forall {TT : tele} (\206\168 : TT \226\134\146 Prop) : tforall \206\168 \226\134\148 (\226\136\128 x, \206\168 x).
Time Proof.
Time symmetry.
Time (unfold tforall).
Time (induction TT as [| X ft IH]).
Time -
Time (simpl).
Time split.
Time +
Time done.
Time +
Time (intros ? p).
Time (rewrite (tele_arg_O_inv p)).
Time done.
Time -
Time (simpl).
Time (split; intros Hx a).
Time +
Time (rewrite <- IH).
Time done.
Time +
Time (destruct (tele_arg_S_inv a) as [x [pf ->]]).
Time revert pf.
Time setoid_rewrite IH.
Time done.
Time Qed.
Time Lemma texist_exist {TT : tele} (\206\168 : TT \226\134\146 Prop) : texist \206\168 \226\134\148 ex \206\168.
Time Proof.
Time symmetry.
Time (induction TT as [| X ft IH]).
Time -
Time (simpl).
Time split.
Time +
Time (intros [p Hp]).
Time (rewrite (tele_arg_O_inv p) in Hp).
Time done.
Time +
Time (intros).
Time by exists TargO.
Time -
Time (simpl).
Time (split; intros [p Hp]; revert Hp).
Time +
Time (destruct (tele_arg_S_inv p) as [x [pf ->]]).
Time (intros ?).
Time exists x.
Time (rewrite <- (IH x (\206\187 a, \206\168 (TargS x a)))).
Time eauto.
Time +
Time (rewrite <- (IH p (\206\187 a, \206\168 (TargS p a)))).
Time (intros [? ?]).
Time eauto.
Time Qed.
Time Typeclasses Opaque tforall texist.
Time
Hint Extern 1 (tforall _) =>
  (progress cbn[tforall tele_fold tele_bind tele_app]): typeclass_instances.
Time
Hint Extern 1 (texist _) =>
  (progress cbn[texist tele_fold tele_bind tele_app]): typeclass_instances.
