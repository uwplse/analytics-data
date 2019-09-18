Set Implicit Arguments.
Require Import List.
Local
Notation "f \226\136\152 g" := (fun x => f (g x)) (at level 40, left associativity).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Notation "f <*> a" := (liftA f a) (left associativity, at level 25).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Definition return_ {m : Type -> Type} `{M : Monad m} 
  {A : Type} : A -> m A := pure.
Notation "a >>= f" := (bind a f) (at level 50, left associativity).
Hint Unfold bind return_: monad_db.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Arguments Functor f : assert.
Arguments Functor_Correct f {F}.
Arguments Applicative f [F].
Arguments Applicative_Correct f {F} {A} : rename.
Arguments Monad m [F] [M].
Arguments Monad_Correct m [F] [A] [M] : rename.
Section monadic_functions.
Variable (m : Type -> Type).
Variable (F : Functor m).
Variable (A : Applicative m).
Variable (M : Monad m).
Definition wbind {A : Type} (ma : m A) {B : Type} 
  (mb : m B) := ma >>= (fun _ => mb).
Definition liftM {A B : Type} (f : A -> B) (ma : m A) : 
  m B := ma >>= (fun a => return_ (f a)).
Definition join {A : Type} (mma : m (m A)) : m A := mma >>= (fun ma => ma).
End monadic_functions.
Notation "a >> f" := (wbind _ a f) (at level 50, left associativity).
Notation "'do' a \226\134\144 e ; c" := (e >>= (fun a => c))
  (at level 60, right associativity).
Fixpoint foldM {A B m} `{Monad m} (f : B -> A -> m B) 
(b : B) (ls : list A) : m B :=
  match ls with
  | nil => return_ b
  | x :: ls' => do y \226\134\144 f b x; foldM f y ls'
  end.
Hint Unfold foldM: monad_db.
About fmap_compose.
Lemma fmap_compose' {f} (F : Functor f) `{Functor_Correct f} :
  forall {A} {B} {C} (g : A -> B) (h : B -> C) (a : f A),
  fmap h (fmap g a) = fmap (h \226\136\152 g) a.
Proof.
(intros).
(rewrite (fmap_compose g h)).
reflexivity.
Qed.
Require Import Program.
Lemma bind_eq :
  forall {A} {B} {m} `{Monad m} (a a' : m A) (f f' : A -> m B),
  a = a' -> (forall x, f x = f' x) -> bind a f = bind a' f'.
Proof.
(intros).
subst.
f_equal.
(apply functional_extensionality).
auto.
Qed.
Ltac
 simplify_monad_LHS :=
  repeat
   match goal with
   | |- bind (return_ _) _ = _ => rewrite <- bind_left_unit
   | |- bind (bind _ _) _ = _ => rewrite <- bind_associativity
   | |- _ = _ => reflexivity
   | |- bind ?a ?f = _ =>
         erewrite bind_eq; intros;
          [  | simplify_monad_LHS | simplify_monad_LHS ]
   end.
Ltac
 simplify_monad :=
  simplify_monad_LHS; apply eq_sym; simplify_monad_LHS; apply eq_sym.
Ltac
 simpl_m :=
  repeat
   (try
     match goal with
     | |- bind ?a _ = bind ?a _ => apply bind_eq; [ reflexivity | intros ]
     end; simplify_monad).
Proposition test :
  forall {m} `{Monad m} `{Monad_Correct m} (a b c : m unit),
  do x \226\134\144 a; do y \226\134\144 b; c = do y \226\134\144 do x \226\134\144 a; b; c.
Proof.
(intros).
simplify_monad.
Abort.
Open Scope list_scope.
Definition list_fmap := map.
Hint Unfold list_fmap: monad_db.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Hint Unfold list_liftA: monad_db.
Fixpoint list_bind {A} (xs : list A) {B} (f : A -> list B) : 
list B := match xs with
          | nil => nil
          | a :: xs' => f a ++ list_bind xs' f
          end.
Hint Unfold list_bind: monad_db.
Instance listF : (Functor list) := { fmap :=@list_fmap}.
Instance listA : (Applicative list) := { pure :=fun _ x => x :: nil;
 liftA :=@list_liftA}.
Instance listM : (Monad list) := { bind :=@list_bind}.
Instance listF_correct : (Functor_Correct list).
Proof.
constructor.
*
(intros).
(simpl).
(apply functional_extensionality; intros x).
(induction x; simpl; auto).
(rewrite IHx; auto).
*
(intros).
(simpl).
(apply functional_extensionality; intros x).
(induction x; simpl; auto).
(rewrite IHx).
auto.
Qed.
Instance listA_correct : (Applicative_Correct list).
Proof.
constructor.
*
(intros).
(simpl).
(apply functional_extensionality; intros l).
(induction l; simpl; auto).
(unfold list_liftA in *).
(simpl in *).
(rewrite IHl; easy).
Abort.
Instance listM_correct : (Monad_Correct list).
Abort.
Lemma fmap_app :
  forall {A} {B} (f : A -> B) ls1 ls2,
  fmap f (ls1 ++ ls2) = fmap f ls1 ++ fmap f ls2.
Proof.
(induction ls1; intros; simpl; auto).
(rewrite IHls1).
auto.
Qed.
Definition option_fmap {A} {B} (f : A -> B) (x : option A) : 
  option B := match x with
              | None => None
              | Some a => Some (f a)
              end.
Definition option_liftA {A} {B} (f : option (A -> B)) 
  (x : option A) : option B :=
  match f, x with
  | Some f', Some a => Some (f' a)
  | _, _ => None
  end.
Instance optionF : (Functor option) := { fmap :=@option_fmap}.
Instance optionA : (Applicative option) := { pure :=@Some;
 liftA :=@option_liftA}.
Instance optionM : (Monad option) := {
 bind :=fun A m B f => match m with
                       | None => None
                       | Some a => f a
                       end}.
Instance optionM_Laws : (Monad_Correct option).
Proof.
split.
-
(destruct a; auto).
-
(intros; auto).
-
(destruct ma; intros; auto).
Defined.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Definition optionT m (A : Type) : Type := m (option A).
Definition optionT_liftT {m} `{Monad m} {A} (x : m A) : optionT m A.
Proof.
(unfold optionT).
refine (do a \226\134\144 x; return_ (Some a)).
Defined.
Instance optionT_T : (MonadTrans optionT) := { liftT :=@optionT_liftT}.
Definition optionT_fmap {f} `{Functor f} {A} {B} (g : A -> B)
  (x : optionT f A) : optionT f B := @fmap f _ _ _ (fmap g) x.
Definition optionT_liftA {f} `{Applicative f} {A} 
  {B} (g : optionT f (A -> B)) (x : optionT f A) : 
  optionT f B.
Proof.
(unfold optionT in *).
exact (fmap liftA g <*> x).
Defined.
Definition optionT_pure {f} `{Applicative f} {A} (a : A) : 
  optionT f A := @pure f _ _ _ (pure a).
Definition optionT_bind {m} `{Monad m} {A} (ma : optionT m A) 
  {B} (f : A -> optionT m B) : optionT m B.
(unfold optionT in *).
exact (do oa \226\134\144 ma; match oa with
                   | None => pure None
                   | Some a => f a
                   end).
Defined.
Instance optionT_F  {f} `{Functor f}: (Functor (optionT f)) := {
 fmap :=@optionT_fmap f _}.
Instance optionT_A  {f} `{Applicative f}: (Applicative (optionT f)) := {
 pure :=@optionT_pure f _ _; liftA :=@optionT_liftA f _ _}.
Instance optionT_M  {m} `{Monad m}: (Monad (optionT m)) := {
 bind :=@optionT_bind m _ _ _}.
Axiom
  (Eta : forall A (B : A -> Type) (f : forall a, B a), f = (fun a => f a)).
Definition Reader (E : Type) := fun X => E -> X.
Definition reader_fmap E A B (f : A -> B) (r : Reader E A) : 
  Reader E B := fun x => f (r x).
Definition reader_liftA E A B (f : Reader E (A -> B)) 
  (r : Reader E A) := fun x => (f x) (r x).
Definition reader_bind E A (r : Reader E A) B (f : A -> Reader E B) :
  Reader E B := fun x => f (r x) x.
Instance readerF  E: (Functor (Reader E)) := { fmap :=@reader_fmap E}.
Instance readerA  E: (Applicative (Reader E)) := {
 pure :=fun A (a : A) e => a; liftA :=@reader_liftA E}.
Instance readerM  (E : Type): (Monad (Reader E)) := { bind :=@reader_bind E}.
Require Import Program.
Section State.
Variable (S : Type).
Definition State (A : Type) := S -> A * S.
Definition state_fmap A B (f : A -> B) (st : State A) : 
  State B := fun s => let (a, s) := st s in (f a, s).
Definition state_liftA A B (st_f : State (A -> B)) 
  (st_a : State A) :=
  fun s => let (f, s) := st_f s in let (a, s) := st_a s in (f a, s).
Definition state_bind A (st_a : State A) B (f : A -> State B) :=
  fun s => let (a, s) := st_a s in f a s.
Definition put (x : S) : State () := fun _ => (tt, x).
Definition get : State S := fun x => (x, x).
Definition runState {A} (op : State A) : S -> A * S := op.
Definition evalState {A} (op : State A) : S -> A := fst \226\136\152 op.
Definition execState {A} (op : State A) : S -> S := snd \226\136\152 op.
End State.
Hint Unfold put get runState evalState execState state_fmap state_liftA
  state_bind: monad_db.
Ltac
 fold_evalState :=
  match goal with
  | |- context [ fst (?c ?v) ] => replace (fst (c v)) with 
    evalState c v by reflexivity
  end.
Arguments get {S}.
Arguments put {S}.
Instance stateF  {A}: (Functor (State A)) := { fmap :=@state_fmap A}.
Instance stateA  {A}: (Applicative (State A)) := {
 pure :=fun A a s => (a, s); liftA :=@state_liftA A}.
Instance stateM  {A}: (Monad (State A)) := { bind :=@state_bind A}.
Instance stateF_correct  {A}: (Functor_Correct (State A)).
Proof.
(split; intros; apply functional_extensionality; intros op;
  apply functional_extensionality; intros x; simpl; 
  unfold state_fmap).
-
(destruct (op x); reflexivity).
-
(destruct (op x); reflexivity).
Qed.
Instance stateA_correct  {A}: (Applicative_Correct (State A)).
Proof.
(split; intros; apply functional_extensionality; intros op; simpl;
  unfold state_liftA).
-
(apply functional_extensionality; intros x).
(destruct (op x); reflexivity).
-
(destruct (u op)).
(destruct (v a)).
(destruct (w a0)).
reflexivity.
-
reflexivity.
-
(destruct (u op)).
reflexivity.
Qed.
Instance stateM_correct  {A}: (Monad_Correct (State A)).
Proof.
(split; intros; simpl; unfold state_bind).
-
(apply functional_extensionality; intros x).
(destruct (a x); reflexivity).
-
reflexivity.
-
(apply functional_extensionality; intros x).
(destruct (ma x)).
reflexivity.
Qed.
Hint Unfold Basics.compose: monad_db.
Hint Unfold stateM: monad_db.
