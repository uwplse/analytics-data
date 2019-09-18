Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool.
Require Import QuickChick ZArith Strings.Ascii Strings.String.
Require Import QuickChickInterface.
Module ConsistencyCheck: QuickChickSig.
Definition RandomSeed := RandomSeed.
Definition G := @G.
Definition semGen := @semGen.
Definition semGenSize := @semGenSize.
Definition Functor_G := Functor_G.
Definition Applicative_G := Applicative_G.
Definition Monad_G := Monad_G.
Definition bindGen' := @bindGen'.
Definition bindGenOpt := @bindGenOpt.
Definition run := @run.
Definition listOf := @listOf.
Definition vectorOf := @vectorOf.
Definition elems_ := @elems_.
Definition oneOf_ := @oneOf_.
Definition freq_ := @freq_.
Definition backtrack := @backtrack.
Definition resize := @resize.
Definition sized := @sized.
Definition suchThatMaybe := @suchThatMaybe.
Definition suchThatMaybeOpt := @suchThatMaybeOpt.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Definition OrdBool := OrdBool.
Definition OrdNat := OrdNat.
Definition OrdZ := OrdZ.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Definition ChooseBool := ChooseBool.
Definition ChooseNat := ChooseNat.
Definition ChooseZ := ChooseZ.
Definition choose := @choose.
Module QcDefaultNotation.
End QcDefaultNotation.
Module QcDoNotation.
Notation "'do!' X <- A ; B" := (bindGen A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).
Notation "'do\'' X <- A ; B" := (bindGen' A (fun X H => B))
  (at level 200, X ident, A at level 100, B at level 200).
Notation "'doM!' X <- A ; B" := (bindGenOpt A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).
End QcDoNotation.
Definition showNat := showNat.
Definition showBool := showBool.
Definition showZ := showZ.
Definition showString := showString.
Definition showList := @showList.
Definition showPair := @showPair.
Definition showOpt := @showOpt.
Definition showEx := @showEx.
Definition nl := nl.
Definition GenOfGenSized := @GenOfGenSized.
Definition genBoolSized := @genBoolSized.
Definition genNatSized := @genNatSized.
Definition genZSized := @genZSized.
Definition genListSized := @genListSized.
Definition genList := @genList.
Definition genOption := @genOption.
Definition genPairSized := @genPairSized.
Definition genPair := @Instances.genPair.
Definition shrinkBool := shrinkBool.
Definition shrinkNat := shrinkNat.
Definition shrinkZ := shrinkZ.
Definition shrinkList := @shrinkList.
Definition shrinkPair := @shrinkPair.
Definition shrinkOption := @shrinkOption.
Definition ArbitraryOfGenShrink := @ArbitraryOfGenShrink.
Definition Checker := @Checker.
Definition testBool := testBool.
Definition testUnit := testUnit.
Definition forAll := @forAll.
Definition forAllProof := @forAllProof.
Definition forAllShrink := @forAllShrink.
Definition testFun := @testFun.
Definition testProd := @testProd.
Definition testPolyFun := @testPolyFun.
Definition whenFail := @whenFail.
Definition expectFailure := @expectFailure.
Definition collect := @collect.
Definition tag := @tag.
Definition conjoin := @conjoin.
Definition disjoin := @disjoin.
Definition implication := @implication.
Module QcNotation.
Export QcDefaultNotation.
Notation "x ==> y" := (implication x y) (at level 55, right associativity) :
  Checker_scope.
End QcNotation.
Definition testDec := @testDec.
Definition Dec_neg := @Dec_neg.
Definition Dec_conj := @Dec_conj.
Definition Dec_disj := @Dec_disj.
Notation "P '?'" :=
  match @dec P _ with
  | left _ => true
  | right _ => false
  end (at level 100).
Definition dec_if_dec_eq := @dec_if_dec_eq.
Definition Eq__Dec := @Eq__Dec.
Definition Dec_eq_bool := @Dec_eq_bool.
Definition Dec_eq_nat := @Dec_eq_nat.
Definition Dec_eq_opt := @Dec_eq_opt.
Definition Dec_eq_prod := @Dec_eq_prod.
Definition Dec_eq_list := @Dec_eq_list.
Definition Dec_ascii := @Dec_ascii.
Definition Dec_string := @Dec_string.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Notation "'genST' x" := (@arbitraryST _ x _) (at level 70).
End ConsistencyCheck.
