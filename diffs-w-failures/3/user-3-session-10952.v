Time From iris.base_logic Require Export base_logic.
Time From iris.algebra Require Import gmap.
Time From iris.algebra Require cofe_solver.
Time Set Default Proof Using "Type".
Time
Structure gFunctor :=
 GFunctor {gFunctor_F :> rFunctor;
           gFunctor_contractive : rFunctorContractive gFunctor_F}.
Time Arguments GFunctor _ {_}.
Time Existing Instance gFunctor_contractive.
Time Add Printing Constructor gFunctor.
Time Definition gFunctors := {n : nat & fin n \226\134\146 gFunctor}.
Time Definition gid (\206\163 : gFunctors) := fin (projT1 \206\163).
Time
Definition gFunctors_lookup (\206\163 : gFunctors) : gid \206\163 \226\134\146 gFunctor := projT2 \206\163.
Time Coercion gFunctors_lookup : gFunctors >-> Funclass.
Time Definition gname := positive.
Time Canonical Structure gnameO := leibnizO gname.
Time
Definition iResF (\206\163 : gFunctors) : urFunctor :=
  discrete_funURF (\206\187 i, gmapURF gname (\206\163 i)).
Time Module gFunctors.
Time Definition nil : gFunctors := existT 0 (fin_0_inv _).
Time
Definition singleton (F : gFunctor) : gFunctors :=
  existT 1 (fin_S_inv (\206\187 _, gFunctor) F (fin_0_inv _)).
Time
Definition app (\206\1631 \206\1632 : gFunctors) : gFunctors :=
  existT (projT1 \206\1631 + projT1 \206\1632) (fin_plus_inv _ (projT2 \206\1631) (projT2 \206\1632)).
Time End gFunctors.
Time Coercion gFunctors.singleton : gFunctor >-> gFunctors.
Time Notation "#[ ]" := gFunctors.nil (format "#[ ]").
Time
Notation "#[ \206\1631 ; .. ; \206\163n ]" :=
  (gFunctors.app \206\1631 .. (gFunctors.app \206\163n gFunctors.nil) ..).
Time
Class subG (\206\1631 \206\1632 : gFunctors) :=
    in_subG : forall i, {j | \206\1631 i = \206\1632 j}.
Time Hint Mode subG ! +: typeclass_instances.
Time
Lemma subG_inv \206\1631 \206\1632 \206\163 : subG (gFunctors.app \206\1631 \206\1632) \206\163 \226\134\146 subG \206\1631 \206\163 * subG \206\1632 \206\163.
Time Proof.
Time (move  {}=>H; split).
Time -
Time (move  {}=>i; move : {}H {} =>/(_ (Fin.L _ i)) [j] /=).
Time (rewrite fin_plus_inv_L; eauto).
Time -
Time (move  {}=>i; move : {}H {} =>/(_ (Fin.R _ i)) [j] /=).
Time (rewrite fin_plus_inv_R; eauto).
Time Qed.
Time Instance subG_refl  \206\163: (subG \206\163 \206\163).
Time Proof.
Time (move  {}=>i; by exists i).
Time Qed.
Time
Instance subG_app_l  \206\163 \206\1631 \206\1632: (subG \206\163 \206\1631 \226\134\146 subG \206\163 (gFunctors.app \206\1631 \206\1632)).
Time Proof.
Time (move  {}=>H i; move : {}H {} =>/(_ i) [j ?]).
Time exists (Fin.L _ j).
Time by rewrite /= fin_plus_inv_L.
Time Qed.
Time
Instance subG_app_r  \206\163 \206\1631 \206\1632: (subG \206\163 \206\1632 \226\134\146 subG \206\163 (gFunctors.app \206\1631 \206\1632)).
Time Proof.
Time (move  {}=>H i; move : {}H {} =>/(_ i) [j ?]).
Time exists (Fin.R _ j).
Time by rewrite /= fin_plus_inv_R.
Time Qed.
Time Module Type iProp_solution_sig.
Time Parameter (iPreProp : gFunctors \226\134\146 ofeT).
Time #[global]Declare Instance iPreProp_cofe  {\206\163}: (Cofe (iPreProp \206\163)).
Time
Definition iResUR (\206\163 : gFunctors) : ucmraT :=
  discrete_funUR (\206\187 i, gmapUR gname (\206\163 i (iPreProp \206\163) _)).
Time Notation iProp \206\163:= (uPredO (iResUR \206\163)).
Time Notation iPropI \206\163:= (uPredI (iResUR \206\163)).
Time Notation iPropSI \206\163:= (uPredSI (iResUR \206\163)).
Time Parameter (iProp_unfold : \226\136\128 {\206\163}, iProp \206\163 -n> iPreProp \206\163).
Time Parameter (iProp_fold : \226\136\128 {\206\163}, iPreProp \206\163 -n> iProp \206\163).
Time
Parameter
  (iProp_fold_unfold : \226\136\128 {\206\163} (P : iProp \206\163), iProp_fold (iProp_unfold P) \226\137\161 P).
Time
Parameter
  (iProp_unfold_fold :
     \226\136\128 {\206\163} (P : iPreProp \206\163), iProp_unfold (iProp_fold P) \226\137\161 P).
Time End iProp_solution_sig.
Time Module Export iProp_solution: iProp_solution_sig.
Time Import cofe_solver.
Time
Definition iProp_result (\206\163 : gFunctors) : solution (uPredOF (iResF \206\163)) :=
  solver.result _.
Time Definition iPreProp (\206\163 : gFunctors) : ofeT := iProp_result \206\163.
Time #[global]Instance iPreProp_cofe  {\206\163}: (Cofe (iPreProp \206\163)) := _.
Time
Definition iResUR (\206\163 : gFunctors) : ucmraT :=
  discrete_funUR (\206\187 i, gmapUR gname (\206\163 i (iPreProp \206\163) _)).
Time Notation iProp \206\163:= (uPredO (iResUR \206\163)).
Time
Definition iProp_unfold {\206\163} : iProp \206\163 -n> iPreProp \206\163 :=
  solution_fold (iProp_result \206\163).
Time Definition iProp_fold {\206\163} : iPreProp \206\163 -n> iProp \206\163 := solution_unfold _.
Time
Lemma iProp_fold_unfold {\206\163} (P : iProp \206\163) : iProp_fold (iProp_unfold P) \226\137\161 P.
Time Proof.
Time (apply solution_unfold_fold).
Time Qed.
Time
Lemma iProp_unfold_fold {\206\163} (P : iPreProp \206\163) :
  iProp_unfold (iProp_fold P) \226\137\161 P.
Time Proof.
Time (apply solution_fold_unfold).
Time Qed.
Time End iProp_solution.
Time
Lemma iProp_unfold_equivI {\206\163} (P Q : iProp \206\163) :
  iProp_unfold P \226\137\161 iProp_unfold Q \226\138\162@{ iPropI \206\163} P \226\137\161 Q.
Time Proof.
Time rewrite -{+2}(iProp_fold_unfold P) -{+2}(iProp_fold_unfold Q).
Time apply : {}bi.f_equiv {}.
Time Qed.
