Time From iris.bi Require Export bi.
Time From iris.proofmode Require Import base.
Time From iris.proofmode Require Export modalities.
Time From stdpp Require Import namespaces.
Time Set Default Proof Using "Type".
Time Import bi.
Time
Class FromAssumption {PROP : bi} (p : bool) (P Q : PROP) :=
    from_assumption : \226\150\161?p P \226\138\162 Q.
Time Arguments FromAssumption {_} _ _%I _%I : simpl never.
Time Arguments from_assumption {_} _ _%I _%I {_}.
Time Hint Mode FromAssumption + + - -: typeclass_instances.
Time
Class KnownLFromAssumption {PROP : bi} (p : bool) (P Q : PROP) :=
    knownl_from_assumption :> FromAssumption p P Q.
Time Arguments KnownLFromAssumption {_} _ _%I _%I : simpl never.
Time Arguments knownl_from_assumption {_} _ _%I _%I {_}.
Time Hint Mode KnownLFromAssumption + + ! -: typeclass_instances.
Time
Class KnownRFromAssumption {PROP : bi} (p : bool) (P Q : PROP) :=
    knownr_from_assumption :> FromAssumption p P Q.
Time Arguments KnownRFromAssumption {_} _ _%I _%I : simpl never.
Time Arguments knownr_from_assumption {_} _ _%I _%I {_}.
Time Hint Mode KnownRFromAssumption + + - !: typeclass_instances.
Time
Class IntoPure {PROP : bi} (P : PROP) (\207\134 : Prop) :=
    into_pure : P \226\138\162 \226\140\156\207\134\226\140\157.
Time Arguments IntoPure {_} _%I _%type_scope : simpl never.
Time Arguments into_pure {_} _%I _%type_scope {_}.
Time Hint Mode IntoPure + ! -: typeclass_instances.
Time
Class IntoPureT {PROP : bi} (P : PROP) (\207\134 : Type) :=
    into_pureT : \226\136\131 \207\136 : Prop, \207\134 = \207\136 \226\136\167 IntoPure P \207\136.
Time
Lemma into_pureT_hint {PROP : bi} (P : PROP) (\207\134 : Prop) :
  IntoPure P \207\134 \226\134\146 IntoPureT P \207\134.
Time Proof.
Time by exists \207\134.
Time Qed.
Time
Hint Extern 0 (IntoPureT _ _) => notypeclasses refine
  (into_pureT_hint _ _ _): typeclass_instances.
Time
Class FromPure {PROP : bi} (a : bool) (P : PROP) (\207\134 : Prop) :=
    from_pure : <affine>?a \226\140\156\207\134\226\140\157 \226\138\162 P.
Time Arguments FromPure {_} _ _%I _%type_scope : simpl never.
Time Arguments from_pure {_} _ _%I _%type_scope {_}.
Time Hint Mode FromPure + - ! -: typeclass_instances.
Time
Class FromPureT {PROP : bi} (a : bool) (P : PROP) (\207\134 : Type) :=
    from_pureT : \226\136\131 \207\136 : Prop, \207\134 = \207\136 \226\136\167 FromPure a P \207\136.
Time
Lemma from_pureT_hint {PROP : bi} (a : bool) (P : PROP) 
  (\207\134 : Prop) : FromPure a P \207\134 \226\134\146 FromPureT a P \207\134.
Time Proof.
Time by exists \207\134.
Time Qed.
Time
Hint Extern 0 (FromPureT _ _ _) => notypeclasses refine
  (from_pureT_hint _ _ _ _): typeclass_instances.
Time
Class IntoInternalEq {PROP : sbi} {A : ofeT} (P : PROP) (x y : A) :=
    into_internal_eq : P \226\138\162 x \226\137\161 y.
Time
Arguments IntoInternalEq {_} {_} _%I _%type_scope _%type_scope : simpl never.
Time Arguments into_internal_eq {_} {_} _%I _%type_scope _%type_scope {_}.
Time Hint Mode IntoInternalEq + - ! - -: typeclass_instances.
Time
Class IntoPersistent {PROP : bi} (p : bool) (P Q : PROP) :=
    into_persistent : <pers>?p P \226\138\162 <pers> Q.
Time Arguments IntoPersistent {_} _ _%I _%I : simpl never.
Time Arguments into_persistent {_} _ _%I _%I {_}.
Time Hint Mode IntoPersistent + + ! -: typeclass_instances.
Time
Class FromModal {PROP1 PROP2 : bi} {A} (M : modality PROP1 PROP2) 
(sel : A) (P : PROP2) (Q : PROP1) :=
    from_modal : M Q \226\138\162 P.
Time Arguments FromModal {_} {_} {_} _ _%I _%I _%I : simpl never.
Time Arguments from_modal {_} {_} {_} _ _ _%I _%I {_}.
Time Hint Mode FromModal - + - - - ! -: typeclass_instances.
Time
Class FromAffinely {PROP : bi} (P Q : PROP) :=
    from_affinely : <affine> Q \226\138\162 P.
Time Arguments FromAffinely {_} _%I _%I : simpl never.
Time Arguments from_affinely {_} _%I _%I {_}.
Time Hint Mode FromAffinely + - !: typeclass_instances.
Time
Class IntoAbsorbingly {PROP : bi} (P Q : PROP) :=
    into_absorbingly : P \226\138\162 <absorb> Q.
Time Arguments IntoAbsorbingly {_} _%I _%I.
Time Arguments into_absorbingly {_} _%I _%I {_}.
Time Hint Mode IntoAbsorbingly + - !: typeclass_instances.
Time
Class IntoWand {PROP : bi} (p q : bool) (R P Q : PROP) :=
    into_wand : \226\150\161?p R \226\138\162 \226\150\161?q P -\226\136\151 Q.
Time Arguments IntoWand {_} _ _ _%I _%I _%I : simpl never.
Time Arguments into_wand {_} _ _ _%I _%I _%I {_}.
Time Hint Mode IntoWand + + + ! - -: typeclass_instances.
Time
Class IntoWand' {PROP : bi} (p q : bool) (R P Q : PROP) :=
    into_wand' : IntoWand p q R P Q.
Time Arguments IntoWand' {_} _ _ _%I _%I _%I : simpl never.
Time Hint Mode IntoWand' + + + ! ! -: typeclass_instances.
Time Hint Mode IntoWand' + + + ! - !: typeclass_instances.
Time
Class FromWand {PROP : bi} (P Q1 Q2 : PROP) :=
    from_wand : (Q1 -\226\136\151 Q2) \226\138\162 P.
Time Arguments FromWand {_} _%I _%I _%I : simpl never.
Time Arguments from_wand {_} _%I _%I _%I {_}.
Time Hint Mode FromWand + ! - -: typeclass_instances.
Time
Class FromImpl {PROP : bi} (P Q1 Q2 : PROP) :=
    from_impl : (Q1 \226\134\146 Q2) \226\138\162 P.
Time Arguments FromImpl {_} _%I _%I _%I : simpl never.
Time Arguments from_impl {_} _%I _%I _%I {_}.
Time Hint Mode FromImpl + ! - -: typeclass_instances.
Time Class FromSep {PROP : bi} (P Q1 Q2 : PROP) :=
         from_sep : Q1 \226\136\151 Q2 \226\138\162 P.
Time Arguments FromSep {_} _%I _%I _%I : simpl never.
Time Arguments from_sep {_} _%I _%I _%I {_}.
Time Hint Mode FromSep + ! - -: typeclass_instances.
Time Hint Mode FromSep + - ! !: typeclass_instances.
Time Class FromAnd {PROP : bi} (P Q1 Q2 : PROP) :=
         from_and : Q1 \226\136\167 Q2 \226\138\162 P.
Time Arguments FromAnd {_} _%I _%I _%I : simpl never.
Time Arguments from_and {_} _%I _%I _%I {_}.
Time Hint Mode FromAnd + ! - -: typeclass_instances.
Time Hint Mode FromAnd + - ! !: typeclass_instances.
Time
Class IntoAnd {PROP : bi} (p : bool) (P Q1 Q2 : PROP) :=
    into_and : \226\150\161?p P \226\138\162 \226\150\161?p (Q1 \226\136\167 Q2).
Time Arguments IntoAnd {_} _ _%I _%I _%I : simpl never.
Time Arguments into_and {_} _ _%I _%I _%I {_}.
Time Hint Mode IntoAnd + + ! - -: typeclass_instances.
Time Class IntoSep {PROP : bi} (P Q1 Q2 : PROP) :=
         into_sep : P \226\138\162 Q1 \226\136\151 Q2.
Time Arguments IntoSep {_} _%I _%I _%I : simpl never.
Time Arguments into_sep {_} _%I _%I _%I {_}.
Time Hint Mode IntoSep + ! - -: typeclass_instances.
Time Class FromOr {PROP : bi} (P Q1 Q2 : PROP) :=
         from_or : Q1 \226\136\168 Q2 \226\138\162 P.
Time Arguments FromOr {_} _%I _%I _%I : simpl never.
Time Arguments from_or {_} _%I _%I _%I {_}.
Time Hint Mode FromOr + ! - -: typeclass_instances.
Time Class IntoOr {PROP : bi} (P Q1 Q2 : PROP) :=
         into_or : P \226\138\162 Q1 \226\136\168 Q2.
Time Arguments IntoOr {_} _%I _%I _%I : simpl never.
Time Arguments into_or {_} _%I _%I _%I {_}.
Time Hint Mode IntoOr + ! - -: typeclass_instances.
Time
Class FromExist {PROP : bi} {A} (P : PROP) (\206\166 : A \226\134\146 PROP) :=
    from_exist : (\226\136\131 x, \206\166 x) \226\138\162 P.
Time Arguments FromExist {_} {_} _%I _%I : simpl never.
Time Arguments from_exist {_} {_} _%I _%I {_}.
Time Hint Mode FromExist + - ! -: typeclass_instances.
Time
Class IntoExist {PROP : bi} {A} (P : PROP) (\206\166 : A \226\134\146 PROP) :=
    into_exist : P \226\138\162 \226\136\131 x, \206\166 x.
Time Arguments IntoExist {_} {_} _%I _%I : simpl never.
Time Arguments into_exist {_} {_} _%I _%I {_}.
Time Hint Mode IntoExist + - ! -: typeclass_instances.
Time
Class IntoForall {PROP : bi} {A} (P : PROP) (\206\166 : A \226\134\146 PROP) :=
    into_forall : P \226\138\162 \226\136\128 x, \206\166 x.
Time Arguments IntoForall {_} {_} _%I _%I : simpl never.
Time Arguments into_forall {_} {_} _%I _%I {_}.
Time Hint Mode IntoForall + - ! -: typeclass_instances.
Time
Class FromForall {PROP : bi} {A} (P : PROP) (\206\166 : A \226\134\146 PROP) :=
    from_forall : (\226\136\128 x, \206\166 x) \226\138\162 P.
Time Arguments FromForall {_} {_} _%I _%I : simpl never.
Time Arguments from_forall {_} {_} _%I _%I {_}.
Time Hint Mode FromForall + - ! -: typeclass_instances.
Time Class IsExcept0 {PROP : sbi} (Q : PROP) :=
         is_except_0 : \226\151\135 Q \226\138\162 Q.
Time Arguments IsExcept0 {_} _%I : simpl never.
Time Arguments is_except_0 {_} _%I {_}.
Time Hint Mode IsExcept0 + !: typeclass_instances.
Time
Class ElimModal {PROP : bi} (\207\134 : Prop) (p p' : bool) 
(P P' : PROP) (Q Q' : PROP) :=
    elim_modal : \207\134 \226\134\146 \226\150\161?p P \226\136\151 (\226\150\161?p' P' -\226\136\151 Q') \226\138\162 Q.
Time Arguments ElimModal {_} _ _ _ _%I _%I _%I _%I : simpl never.
Time Arguments elim_modal {_} _ _ _ _%I _%I _%I _%I {_}.
Time Hint Mode ElimModal + - ! - ! - ! -: typeclass_instances.
Time
Class AddModal {PROP : bi} (P P' : PROP) (Q : PROP) :=
    add_modal : P \226\136\151 (P' -\226\136\151 Q) \226\138\162 Q.
Time Arguments AddModal {_} _%I _%I _%I : simpl never.
Time Arguments add_modal {_} _%I _%I _%I {_}.
Time Hint Mode AddModal + - ! !: typeclass_instances.
Time Lemma add_modal_id {PROP : bi} (P Q : PROP) : AddModal P P Q.
Time Proof.
Time by rewrite /AddModal wand_elim_r.
Time Qed.
Time
Class IsCons {A} (l : list A) (x : A) (k : list A) :=
    is_cons : l = x :: k.
Time Class IsApp {A} (l k1 k2 : list A) :=
         is_app : l = k1 ++ k2.
Time #[global]Hint Mode IsCons + ! - -: typeclass_instances.
Time #[global]Hint Mode IsApp + ! - -: typeclass_instances.
Time Instance is_cons_cons  {A} (x : A) (l : list A): (IsCons (x :: l) x l).
Time Proof.
Time done.
Time Qed.
Time Instance is_app_app  {A} (l1 l2 : list A): (IsApp (l1 ++ l2) l1 l2).
Time Proof.
Time done.
Time Qed.
Time
Class Frame {PROP : bi} (p : bool) (R P Q : PROP) :=
    frame : \226\150\161?p R \226\136\151 Q \226\138\162 P.
Time Arguments Frame {_} _ _%I _%I _%I.
Time Arguments frame {_} _ _%I _%I _%I {_}.
Time Hint Mode Frame + + ! ! -: typeclass_instances.
Time
Class MaybeFrame {PROP : bi} (p : bool) (R P Q : PROP) (progress : bool) :=
    maybe_frame : \226\150\161?p R \226\136\151 Q \226\138\162 P.
Time Arguments MaybeFrame {_} _ _%I _%I _%I _.
Time Arguments maybe_frame {_} _ _%I _%I _%I _ {_}.
Time Hint Mode MaybeFrame + + ! - - -: typeclass_instances.
Time
Instance maybe_frame_frame  {PROP : bi} p (R P Q : PROP):
 (Frame p R P Q \226\134\146 MaybeFrame p R P Q true).
Time Proof.
Time done.
Time Qed.
Time
Instance maybe_frame_default_persistent  {PROP : bi} 
 (R P : PROP): (MaybeFrame true R P P false) |100.
Time Proof.
Time (intros).
Time rewrite /MaybeFrame /=.
Time by rewrite sep_elim_r.
Time Qed.
Time
Instance maybe_frame_default  {PROP : bi} (R P : PROP):
 (TCOr (Affine R) (Absorbing P) \226\134\146 MaybeFrame false R P P false) |100.
Time Proof.
Time (intros).
Time rewrite /MaybeFrame /=.
Time apply : {}sep_elim_r {}.
Time Qed.
Time
Class MakeEmbed {PROP PROP' : bi} `{BiEmbed PROP PROP'} 
(P : PROP) (Q : PROP') :=
    make_embed : \226\142\161 P \226\142\164 \226\138\163\226\138\162 Q.
Time Arguments MakeEmbed {_} {_} {_} _%I _%I.
Time Hint Mode MakeEmbed + + + - -: typeclass_instances.
Time
Class KnownMakeEmbed {PROP PROP' : bi} `{BiEmbed PROP PROP'} 
(P : PROP) (Q : PROP') :=
    known_make_embed :> MakeEmbed P Q.
Time Arguments KnownMakeEmbed {_} {_} {_} _%I _%I.
Time Hint Mode KnownMakeEmbed + + + ! -: typeclass_instances.
Time Class MakeSep {PROP : bi} (P Q PQ : PROP) :=
         make_sep : P \226\136\151 Q \226\138\163\226\138\162 PQ.
Time Arguments MakeSep {_} _%I _%I _%I.
Time Hint Mode MakeSep + - - -: typeclass_instances.
Time
Class KnownLMakeSep {PROP : bi} (P Q PQ : PROP) :=
    knownl_make_sep :> MakeSep P Q PQ.
Time Arguments KnownLMakeSep {_} _%I _%I _%I.
Time Hint Mode KnownLMakeSep + ! - -: typeclass_instances.
Time
Class KnownRMakeSep {PROP : bi} (P Q PQ : PROP) :=
    knownr_make_sep :> MakeSep P Q PQ.
Time Arguments KnownRMakeSep {_} _%I _%I _%I.
Time Hint Mode KnownRMakeSep + - ! -: typeclass_instances.
Time Class MakeAnd {PROP : bi} (P Q PQ : PROP) :=
         make_and_l : P \226\136\167 Q \226\138\163\226\138\162 PQ.
Time Arguments MakeAnd {_} _%I _%I _%I.
Time Hint Mode MakeAnd + - - -: typeclass_instances.
Time
Class KnownLMakeAnd {PROP : bi} (P Q PQ : PROP) :=
    knownl_make_and :> MakeAnd P Q PQ.
Time Arguments KnownLMakeAnd {_} _%I _%I _%I.
Time Hint Mode KnownLMakeAnd + ! - -: typeclass_instances.
Time
Class KnownRMakeAnd {PROP : bi} (P Q PQ : PROP) :=
    knownr_make_and :> MakeAnd P Q PQ.
Time Arguments KnownRMakeAnd {_} _%I _%I _%I.
Time Hint Mode KnownRMakeAnd + - ! -: typeclass_instances.
Time Class MakeOr {PROP : bi} (P Q PQ : PROP) :=
         make_or_l : P \226\136\168 Q \226\138\163\226\138\162 PQ.
Time Arguments MakeOr {_} _%I _%I _%I.
Time Hint Mode MakeOr + - - -: typeclass_instances.
Time
Class KnownLMakeOr {PROP : bi} (P Q PQ : PROP) :=
    knownl_make_or :> MakeOr P Q PQ.
Time Arguments KnownLMakeOr {_} _%I _%I _%I.
Time Hint Mode KnownLMakeOr + ! - -: typeclass_instances.
Time
Class KnownRMakeOr {PROP : bi} (P Q PQ : PROP) :=
    knownr_make_or :> MakeOr P Q PQ.
Time Arguments KnownRMakeOr {_} _%I _%I _%I.
Time Hint Mode KnownRMakeOr + - ! -: typeclass_instances.
Time
Class MakeAffinely {PROP : bi} (P Q : PROP) :=
    make_affinely : <affine> P \226\138\163\226\138\162 Q.
Time Arguments MakeAffinely {_} _%I _%I.
Time Hint Mode MakeAffinely + - -: typeclass_instances.
Time
Class KnownMakeAffinely {PROP : bi} (P Q : PROP) :=
    known_make_affinely :> MakeAffinely P Q.
Time Arguments KnownMakeAffinely {_} _%I _%I.
Time Hint Mode KnownMakeAffinely + ! -: typeclass_instances.
Time
Class MakeIntuitionistically {PROP : bi} (P Q : PROP) :=
    make_intuitionistically : \226\150\161 P \226\138\163\226\138\162 Q.
Time Arguments MakeIntuitionistically {_} _%I _%I.
Time Hint Mode MakeIntuitionistically + - -: typeclass_instances.
Time
Class KnownMakeIntuitionistically {PROP : bi} (P Q : PROP) :=
    known_make_intuitionistically :> MakeIntuitionistically P Q.
Time Arguments KnownMakeIntuitionistically {_} _%I _%I.
Time Hint Mode KnownMakeIntuitionistically + ! -: typeclass_instances.
Time
Class MakeAbsorbingly {PROP : bi} (P Q : PROP) :=
    make_absorbingly : <absorb> P \226\138\163\226\138\162 Q.
Time Arguments MakeAbsorbingly {_} _%I _%I.
Time Hint Mode MakeAbsorbingly + - -: typeclass_instances.
Time
Class KnownMakeAbsorbingly {PROP : bi} (P Q : PROP) :=
    known_make_absorbingly :> MakeAbsorbingly P Q.
Time Arguments KnownMakeAbsorbingly {_} _%I _%I.
Time Hint Mode KnownMakeAbsorbingly + ! -: typeclass_instances.
Time
Class MakePersistently {PROP : bi} (P Q : PROP) :=
    make_persistently : <pers> P \226\138\163\226\138\162 Q.
Time Arguments MakePersistently {_} _%I _%I.
Time Hint Mode MakePersistently + - -: typeclass_instances.
Time
Class KnownMakePersistently {PROP : bi} (P Q : PROP) :=
    known_make_persistently :> MakePersistently P Q.
Time Arguments KnownMakePersistently {_} _%I _%I.
Time Hint Mode KnownMakePersistently + ! -: typeclass_instances.
Time
Class MakeLaterN {PROP : sbi} (n : nat) (P lP : PROP) :=
    make_laterN : \226\150\183^n P \226\138\163\226\138\162 lP.
Time Arguments MakeLaterN {_} _%nat _%I _%I.
Time Hint Mode MakeLaterN + + - -: typeclass_instances.
Time
Class KnownMakeLaterN {PROP : sbi} (n : nat) (P lP : PROP) :=
    known_make_laterN :> MakeLaterN n P lP.
Time Arguments KnownMakeLaterN {_} _%nat _%I _%I.
Time Hint Mode KnownMakeLaterN + + ! -: typeclass_instances.
Time
Class MakeExcept0 {PROP : sbi} (P Q : PROP) :=
    make_except_0 : sbi_except_0 P \226\138\163\226\138\162 Q.
Time Arguments MakeExcept0 {_} _%I _%I.
Time Hint Mode MakeExcept0 + - -: typeclass_instances.
Time
Class KnownMakeExcept0 {PROP : sbi} (P Q : PROP) :=
    known_make_except_0 :> MakeExcept0 P Q.
Time Arguments KnownMakeExcept0 {_} _%I _%I.
Time Hint Mode KnownMakeExcept0 + ! -: typeclass_instances.
Time
Class IntoExcept0 {PROP : sbi} (P Q : PROP) :=
    into_except_0 : P \226\138\162 \226\151\135 Q.
Time Arguments IntoExcept0 {_} _%I _%I : simpl never.
Time Arguments into_except_0 {_} _%I _%I {_}.
Time Hint Mode IntoExcept0 + ! -: typeclass_instances.
Time Hint Mode IntoExcept0 + - !: typeclass_instances.
Time
Class MaybeIntoLaterN {PROP : sbi} (only_head : bool) 
(n : nat) (P Q : PROP) :=
    maybe_into_laterN : P \226\138\162 \226\150\183^n Q.
Time Arguments MaybeIntoLaterN {_} _ _%nat_scope _%I _%I.
Time Arguments maybe_into_laterN {_} _ _%nat_scope _%I _%I {_}.
Time Hint Mode MaybeIntoLaterN + + + - -: typeclass_instances.
Time
Class IntoLaterN {PROP : sbi} (only_head : bool) (n : nat) (P Q : PROP) :=
    into_laterN :> MaybeIntoLaterN only_head n P Q.
Time Arguments IntoLaterN {_} _ _%nat_scope _%I _%I.
Time Hint Mode IntoLaterN + + + ! -: typeclass_instances.
Time
Instance maybe_into_laterN_default  {PROP : sbi} only_head 
 n (P : PROP): (MaybeIntoLaterN only_head n P P) |1000.
Time Proof.
Time (apply laterN_intro).
Time Qed.
Time
Instance maybe_into_laterN_default_0  {PROP : sbi} 
 only_head (P : PROP): (MaybeIntoLaterN only_head 0 P P) |0.
Time Proof.
Time (apply _).
Time Qed.
Time
Class IntoEmbed {PROP PROP' : bi} `{BiEmbed PROP PROP'} 
(P : PROP') (Q : PROP) :=
    into_embed : P \226\138\162 \226\142\161 Q \226\142\164.
Time Arguments IntoEmbed {_} {_} {_} _%I _%I.
Time Arguments into_embed {_} {_} {_} _%I _%I {_}.
Time Hint Mode IntoEmbed + + + ! -: typeclass_instances.
Time
Class AsEmpValid {PROP : bi} (\207\134 : Prop) (P : PROP) :=
    as_emp_valid : \207\134 \226\134\148 bi_emp_valid P.
Time Arguments AsEmpValid {_} _%type _%I.
Time
Class AsEmpValid0 {PROP : bi} (\207\134 : Prop) (P : PROP) :=
    as_emp_valid_here : AsEmpValid \207\134 P.
Time Arguments AsEmpValid0 {_} _%type _%I.
Time Existing Instance as_emp_valid_here |0.
Time
Lemma as_emp_valid_1 (\207\134 : Prop) {PROP : bi} (P : PROP) 
  `{!AsEmpValid \207\134 P} : \207\134 \226\134\146 bi_emp_valid P.
Time Proof.
Time by apply as_emp_valid.
Time Qed.
Time
Lemma as_emp_valid_2 (\207\134 : Prop) {PROP : bi} (P : PROP) 
  `{!AsEmpValid \207\134 P} : bi_emp_valid P \226\134\146 \207\134.
Time Proof.
Time by apply as_emp_valid.
Time Qed.
Time Class IntoInv {PROP : bi} (P : PROP) (N : namespace) :={}.
Time Arguments IntoInv {_} _%I _.
Time Hint Mode IntoInv + ! -: typeclass_instances.
Time
Definition accessor {PROP : bi} {X : Type} (M1 M2 : PROP \226\134\146 PROP)
  (\206\177 \206\178 : X \226\134\146 PROP) (m\206\179 : X \226\134\146 option PROP) : PROP :=
  M1 (\226\136\131 x, \206\177 x \226\136\151 (\206\178 x -\226\136\151 M2 (default emp (m\206\179 x))))%I.
Time
Class ElimAcc {PROP : bi} {X : Type} (M1 M2 : PROP \226\134\146 PROP) 
(\206\177 \206\178 : X \226\134\146 PROP) (m\206\179 : X \226\134\146 option PROP) (Q : PROP) 
(Q' : X \226\134\146 PROP) :=
    elim_acc : (\226\136\128 x, \206\177 x -\226\136\151 Q' x) -\226\136\151 accessor M1 M2 \206\177 \206\178 m\206\179 -\226\136\151 Q.
Time Arguments ElimAcc {_} {_} _%I _%I _%I _%I _%I _%I : simpl never.
Time Arguments elim_acc {_} {_} _%I _%I _%I _%I _%I _%I {_}.
Time Hint Mode ElimAcc + ! ! ! ! ! ! ! -: typeclass_instances.
Time
Class IntoAcc {PROP : bi} {X : Type} (Pacc : PROP) 
(\207\134 : Prop) (Pin : PROP) (M1 M2 : PROP \226\134\146 PROP) (\206\177 \206\178 : X \226\134\146 PROP)
(m\206\179 : X \226\134\146 option PROP) :=
    into_acc : \207\134 \226\134\146 Pacc -\226\136\151 Pin -\226\136\151 accessor M1 M2 \206\177 \206\178 m\206\179.
Time Arguments IntoAcc {_} {_} _%I _ _%I _%I _%I _%I _%I _%I : simpl never.
Time
Arguments into_acc {_} {_} _%I _ _%I _%I _%I _%I _%I _%I {_} : simpl never.
Time Hint Mode IntoAcc + - ! - - - - - - -: typeclass_instances.
Time
Class ElimInv {PROP : bi} {X : Type} (\207\134 : Prop) (Pinv Pin : PROP)
(Pout : X \226\134\146 PROP) (mPclose : option (X \226\134\146 PROP)) (Q : PROP) 
(Q' : X \226\134\146 PROP) :=
    elim_inv :
      \207\134
      \226\134\146 Pinv \226\136\151 Pin \226\136\151 (\226\136\128 x, Pout x \226\136\151 (default (\206\187 _, emp) mPclose) x -\226\136\151 Q' x)
        \226\138\162 Q.
Time Arguments ElimInv {_} {_} _ _%I _%I _%I _%I _%I _%I : simpl never.
Time Arguments elim_inv {_} {_} _ _%I _%I _%I _%I _%I _%I {_}.
Time Hint Mode ElimInv + - - ! - - ! ! -: typeclass_instances.
Time
Instance into_pure_tc_opaque  {PROP : bi} (P : PROP) 
 \207\134: (IntoPure P \207\134 \226\134\146 IntoPure (tc_opaque P) \207\134) := id.
Time
Instance from_pure_tc_opaque  {PROP : bi} (a : bool) 
 (P : PROP) \207\134: (FromPure a P \207\134 \226\134\146 FromPure a (tc_opaque P) \207\134) := id.
Time
Instance from_wand_tc_opaque  {PROP : bi} (P Q1 Q2 : PROP):
 (FromWand P Q1 Q2 \226\134\146 FromWand (tc_opaque P) Q1 Q2) := id.
Time
Instance into_wand_tc_opaque  {PROP : bi} p q (R P Q : PROP):
 (IntoWand p q R P Q \226\134\146 IntoWand p q (tc_opaque R) P Q) := id.
Time
Instance from_and_tc_opaque  {PROP : bi} (P Q1 Q2 : PROP):
 (FromAnd P Q1 Q2 \226\134\146 FromAnd (tc_opaque P) Q1 Q2) |102 := id.
Time
Instance into_and_tc_opaque  {PROP : bi} p (P Q1 Q2 : PROP):
 (IntoAnd p P Q1 Q2 \226\134\146 IntoAnd p (tc_opaque P) Q1 Q2) := id.
Time
Instance into_sep_tc_opaque  {PROP : bi} (P Q1 Q2 : PROP):
 (IntoSep P Q1 Q2 \226\134\146 IntoSep (tc_opaque P) Q1 Q2) := id.
Time
Instance from_or_tc_opaque  {PROP : bi} (P Q1 Q2 : PROP):
 (FromOr P Q1 Q2 \226\134\146 FromOr (tc_opaque P) Q1 Q2) := id.
Time
Instance into_or_tc_opaque  {PROP : bi} (P Q1 Q2 : PROP):
 (IntoOr P Q1 Q2 \226\134\146 IntoOr (tc_opaque P) Q1 Q2) := id.
Time
Instance from_exist_tc_opaque  {PROP : bi} {A} (P : PROP) 
 (\206\166 : A \226\134\146 PROP): (FromExist P \206\166 \226\134\146 FromExist (tc_opaque P) \206\166) := id.
Time
Instance into_exist_tc_opaque  {PROP : bi} {A} (P : PROP) 
 (\206\166 : A \226\134\146 PROP): (IntoExist P \206\166 \226\134\146 IntoExist (tc_opaque P) \206\166) := id.
Time
Instance into_forall_tc_opaque  {PROP : bi} {A} (P : PROP) 
 (\206\166 : A \226\134\146 PROP): (IntoForall P \206\166 \226\134\146 IntoForall (tc_opaque P) \206\166) := id.
Time
Instance from_modal_tc_opaque  {PROP1 PROP2 : bi} 
 {A} M (sel : A) (P : PROP2) (Q : PROP1):
 (FromModal M sel P Q \226\134\146 FromModal M sel (tc_opaque P) Q) := id.
Time
Instance elim_modal_tc_opaque  {PROP : bi} \207\134 p p' 
 (P P' Q Q' : PROP):
 (ElimModal \207\134 p p' P P' Q Q' \226\134\146 ElimModal \207\134 p p' (tc_opaque P) P' Q Q') := id.
Time
Instance into_inv_tc_opaque  {PROP : bi} (P : PROP) 
 N: (IntoInv P N \226\134\146 IntoInv (tc_opaque P) N) := id.
Time
Instance elim_inv_tc_opaque  {PROP : sbi} {X} \207\134 Pinv 
 Pin Pout Pclose Q Q':
 (ElimInv (PROP:=PROP) (X:=X) \207\134 Pinv Pin Pout Pclose Q Q'
  \226\134\146 ElimInv \207\134 (tc_opaque Pinv) Pin Pout Pclose Q Q') := id.
