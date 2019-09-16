From QuickChick Require Import QuickChick.
Require Import ZArith Strings.Ascii Strings.String.
From ExtLib.Structures Require Import Functor Applicative.
Module Type QuickChickSig.
Declare Instance showNat : (Show nat).
Declare Instance showBool : (Show bool).
Declare Instance showZ : (Show Z).
Declare Instance showString : (Show string).
Declare Instance showList : (forall {A : Type} `{Show A}, Show (list A)).
Declare Instance showPair :
 (forall {A B : Type} `{Show A} `{Show B}, Show (A * B)).
Declare Instance showOpt : (forall {A : Type} `{Show A}, Show (option A)).
Declare Instance showEx : (forall {A} `{Show A} P, Show {x : A | P x}).
Definition nl : string := String (ascii_of_nat 10) EmptyString.
Parameter (RandomSeed : Type).
Parameter (G : Type -> Type).
Parameter (run : forall {A : Type}, G A -> nat -> RandomSeed -> A).
Parameter (semGen : forall {A : Type} (g : G A), set A).
Parameter (semGenSize : forall {A : Type} (g : G A) (size : nat), set A).
Declare Instance Monad_G : (Monad G).
Declare Instance Functor_G : (Functor G).
Declare Instance Applicative_G : (Applicative G).
Parameter
  (bindGen' :
     forall {A B : Type} (g : G A),
     (forall a : A, a \in semGen g -> G B) -> G B).
Parameter
  (bindGenOpt :
     forall {A B : Type}, G (option A) -> (A -> G (option B)) -> G (option B)).
Parameter (listOf : forall {A : Type}, G A -> G (list A)).
Parameter (vectorOf : forall {A : Type}, nat -> G A -> G (list A)).
Parameter (elems_ : forall {A : Type}, A -> list A -> G A).
Parameter (oneOf_ : forall {A : Type}, G A -> list (G A) -> G A).
Parameter (freq_ : forall {A : Type}, G A -> list (nat * G A) -> G A).
Parameter
  (backtrack : forall {A : Type}, list (nat * G (option A)) -> G (option A)).
Parameter (sized : forall {A : Type}, (nat -> G A) -> G A).
Parameter (resize : forall {A : Type}, nat -> G A -> G A).
Parameter
  (suchThatMaybe : forall {A : Type}, G A -> (A -> bool) -> G (option A)).
Parameter
  (suchThatMaybeOpt :
     forall {A : Type}, G (option A) -> (A -> bool) -> G (option A)).
Module QcDefaultNotation.
Notation " 'elems' [ x ] " := (elems_ x (cons x nil)) : qc_scope.
Notation " 'elems' [ x ; y ] " := (elems_ x (cons x (cons y nil))) : qc_scope.
Notation " 'elems' [ x ; y ; .. ; z ] " :=
  (elems_ x (cons x (cons y .. (cons z nil) ..))) : qc_scope.
Notation " 'elems' ( x ;; l ) " := (elems_ x (cons x l))
  (at level 1, no associativity) : qc_scope.
Notation " 'oneOf' [ x ] " := (oneOf_ x (cons x nil)) : qc_scope.
Notation " 'oneOf' [ x ; y ] " := (oneOf_ x (cons x (cons y nil))) : qc_scope.
Notation " 'oneOf' [ x ; y ; .. ; z ] " :=
  (oneOf_ x (cons x (cons y .. (cons z nil) ..))) : qc_scope.
Notation " 'oneOf' ( x ;; l ) " := (oneOf_ x (cons x l))
  (at level 1, no associativity) : qc_scope.
Notation " 'freq' [ x ] " := (freq_ x (cons x nil)) : qc_scope.
Notation " 'freq' [ ( n , x ) ; y ] " :=
  (freq_ x (cons (n, x) (cons y nil))) : qc_scope.
Notation " 'freq' [ ( n , x ) ; y ; .. ; z ] " :=
  (freq_ x (cons (n, x) (cons y .. (cons z nil) ..))) : qc_scope.
Notation " 'freq' ( ( n , x ) ;; l ) " := (freq_ x (cons (n, x) l))
  (at level 1, no associativity) : qc_scope.
End QcDefaultNotation.
Existing Class OrdType.
Declare Instance OrdBool : (OrdType bool).
Declare Instance OrdNat : (OrdType nat).
Declare Instance OrdZ : (OrdType Z).
Existing Class ChoosableFromInterval.
Declare Instance ChooseBool : (ChoosableFromInterval bool).
Declare Instance ChooseNat : (ChoosableFromInterval nat).
Declare Instance ChooseZ : (ChoosableFromInterval Z).
Parameter
  (choose : forall {A : Type} `{ChoosableFromInterval A}, A * A -> G A).
Declare Instance GenOfGenSized  {A} `{GenSized A}: (Gen A).
Declare Instance genBoolSized : (GenSized bool).
Declare Instance genNatSized : (GenSized nat).
Declare Instance genZSized : (GenSized Z).
Declare Instance genListSized :
 (forall {A : Type} `{GenSized A}, GenSized (list A)).
Declare Instance genList : (forall {A : Type} `{Gen A}, Gen (list A)).
Declare Instance genOption : (forall {A : Type} `{Gen A}, Gen (option A)).
Declare Instance genPairSized :
 (forall {A B : Type} `{GenSized A} `{GenSized B}, GenSized (A * B)).
Declare Instance genPair :
 (forall {A B : Type} `{Gen A} `{Gen B}, Gen (A * B)).
Notation "'genST' x" := (@arbitraryST _ x _) (at level 70).
Declare Instance shrinkBool : (Shrink bool).
Declare Instance shrinkNat : (Shrink nat).
Declare Instance shrinkZ : (Shrink Z).
Declare Instance shrinkList  {A : Type} `{Shrink A}: (Shrink (list A)).
Declare Instance shrinkPair  {A} {B} `{Shrink A} `{Shrink B}:
 (Shrink (A * B)).
Declare Instance shrinkOption  {A : Type} `{Shrink A}: (Shrink (option A)).
Declare Instance ArbitraryOfGenShrink :
 (forall {A} `{Gen A} `{Shrink A}, Arbitrary A).
Parameter (Checker : Type).
Declare Instance testBool : (Checkable bool).
Declare Instance testUnit : (Checkable unit).
Parameter
  (forAll :
     forall {A prop : Type} `{Checkable prop} `{Show A} 
       (gen : G A) (pf : A -> prop), Checker).
Parameter
  (forAllProof :
     forall {A prop : Type} `{Checkable prop} `{Show A} 
       (gen : G A) (pf : forall x : A, semGen gen x -> prop), Checker).
Parameter
  (forAllShrink :
     forall {A prop : Type} `{Checkable prop} `{Show A} 
       (gen : G A) (shrinker : A -> list A) (pf : A -> prop), Checker).
Declare Instance testFun :
 (forall {A prop : Type} `{Show A} `{Arbitrary A} `{Checkable prop},
  Checkable (A -> prop)).
Declare Instance testProd :
 (forall {A : Type} {prop : A -> Type} `{Show A} `{Arbitrary A}
    `{forall x : A, Checkable (prop x)}, Checkable (forall x : A, prop x)).
Declare Instance testPolyFun :
 (forall {prop : Type -> Type} `{Checkable (prop nat)},
  Checkable (forall T, prop T)).
Parameter
  (whenFail :
     forall {prop : Type} `{Checkable prop} (str : string), prop -> Checker).
Parameter
  (expectFailure : forall {prop : Type} `{Checkable prop} (p : prop), Checker).
Parameter
  (collect :
     forall {A prop : Type} `{Show A} `{Checkable prop} (x : A),
     prop -> Checker).
Parameter
  (tag : forall {prop : Type} `{Checkable prop} (t : string), prop -> Checker).
Parameter (conjoin : forall l : list Checker, Checker).
Parameter (disjoin : forall l : list Checker, Checker).
Parameter
  (implication :
     forall {prop : Type} `{Checkable prop} (b : bool) (p : prop), Checker).
Module QcNotation.
Export QcDefaultNotation.
Notation "x ==> y" := (implication x y) (at level 55, right associativity) :
  Checker_scope.
End QcNotation.
Declare Instance testDec  {P} `{H : Dec P}: (Checkable P).
Declare Instance Dec_neg  {P} {H : Dec P}: (Dec (~ P)).
Declare Instance Dec_conj  {P} {Q} {H : Dec P} {I : Dec Q}: (Dec (P /\ Q)).
Declare Instance Dec_disj  {P} {Q} {H : Dec P} {I : Dec Q}: (Dec (P \/ Q)).
Notation "P '?'" :=
  match @dec P _ with
  | left _ => true
  | right _ => false
  end (at level 100).
Declare Instance Eq__Dec  {A} `{H : Dec_Eq A} (x y : A): (Dec (x = y)).
Declare Instance Dec_eq_bool  (x y : bool): (Dec (x = y)).
Declare Instance Dec_eq_nat  (m n : nat): (Dec (m = n)).
Declare Instance Dec_eq_opt  (A : Type) (m n : option A)
 `{forall x y : A, Dec (x = y)}: (Dec (m = n)).
Declare Instance Dec_eq_prod  (A B : Type) (m n : A * B)
 `{forall x y : A, Dec (x = y)} `{forall x y : B, Dec (x = y)}: 
 (Dec (m = n)).
Declare Instance Dec_eq_list  (A : Type) (m n : list A)
 `{forall x y : A, Dec (x = y)}: (Dec (m = n)).
Declare Instance Dec_ascii  (m n : Ascii.ascii): (Dec (m = n)).
Declare Instance Dec_string  (m n : string): (Dec (m = n)).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Module QcDoNotation.
Notation "'do!' X <- A ; B" := (bindGen A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).
Notation "'do\'' X <- A ; B" := (bindGen' A (fun X H => B))
  (at level 200, X ident, A at level 100, B at level 200).
Notation "'doM!' X <- A ; B" := (bindGenOpt A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).
End QcDoNotation.
End QuickChickSig.
