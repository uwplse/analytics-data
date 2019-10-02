Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqqDFGzi"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Export Contexts.
Require Export HOASCircuits.
Require Export HOASLib.
Require Export DBCircuits.
Require Export Quantum.
Require Export Denotation.
Require Import Setoid.
Lemma denote_box_compat :
  forall (safe : bool) (W1 W2 : WType) (c : Box W1 W2) \207\129 \207\129',
  \207\129 == \207\129' -> denote_box safe c \207\129 == denote_box safe c \207\129'.
Proof.
(intros).
(destruct c).
(unfold denote_box; simpl).
(rewrite add_fresh_split; simpl).
(remember (add_fresh_pat W1 []) as p).
(induction (c p)).
-
matrix_denote.
(match goal with
 | |- ?A => let A' := restore_dims_rec A in
            replace
            A
            with
            A'
 end).
2: {
(apply f_equal_gen; trivial).
(apply f_equal_gen; trivial).
(apply f_equal_gen; trivial).
(apply f_equal_gen; trivial).
Admitted.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqcIOPck"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Parametric Morphism  b W1 W2 c : @denote_box b W1 W2 c with signature
 mat_equiv ==> mat_equiv as denote_box_mor.
Proof.
(intros).
(apply denote_box_compat; easy).
Qed.
Fact denote_compose :
  forall safe w (c : Circuit w) (\206\147 : Ctx),
  forall w' (f : Pat w -> Circuit w') (\206\1470 \206\1471 \206\1471' \206\14701 : Ctx) \207\129,
  \206\147 \226\138\162 c :Circ ->
  \206\1471 \226\138\162 f :Fun ->
  \206\1471' \226\169\181 \206\1471 \226\136\153 \206\147 ->
  \206\14701 \226\169\181 \206\1470 \226\136\153 \206\1471 ->
  denote_circuit safe (compose c f) \206\1470 \206\1471' \207\129 =
  compose_super
    (denote_circuit safe (f (add_fresh_pat w \206\1471)) \206\1470 (add_fresh_state w \206\1471))
    (denote_circuit safe c \206\14701 \206\147) \207\129.
Proof.
(intros safe w c \206\147 w' f \206\1470 \206\1471 \206\1471' \206\14701 \207\129 TP).
dependent induction TP.
-
(intros WT pf_merge1 pf_merge2).
(simpl).
(unfold compose_super).
(unfold denote_circuit).
(simpl).
(unfold pad).
(rewrite (ctx_wtype_size w p \206\147) by easy).
(rewrite Nat.add_sub).
(rewrite size_fresh_ctx).
(destruct pf_merge1 as [V1 M1]).
replace (size_ctx \206\1471') with size_octx \206\1471' by easy.
(rewrite M1 in *).
(rewrite size_octx_merge by easy).
(simpl).
(rewrite (ctx_wtype_size w p \206\147 t)).
admit.
-
(intros WT pf_merge1 pf_merge2).
replace (compose (gate g p1 f0) f) with gate g p1 (fun p2 => compose (f0 p2) f)
 by auto.
(repeat rewrite denote_gate_circuit; fold_denotation).
(set (p2 := process_gate_pat g p1 \206\147)).
(set (\206\1473'' := process_gate_state g p1 \206\147)).
admit.
-
admit.
Admitted.
Theorem inSeq_correct :
  forall W1 W2 W3 (g : Box W2 W3) (f : Box W1 W2) (safe : bool) \207\129,
  Typed_Box g ->
  Typed_Box f ->
  denote_box safe (inSeq f g) \207\129 ==
  compose_super (denote_box safe g) (denote_box safe f) \207\129.
Proof.
(intros W1 W2 W3 g f safe \207\129 types_g types_f).
(autounfold with den_db; simpl).
(destruct f as [f]).
(destruct g as [g]).
(autounfold with den_db; simpl).
(destruct (add_fresh W1 []) as [p1 \206\1471] eqn:E1).
(simpl).
(destruct (add_fresh W2 []) as [p2 \206\1472] eqn:E2).
(simpl).
(rewrite add_fresh_split in E1, E2).
(inversion E1).
(inversion E2).
(assert (S1 : \226\159\166 \206\1471 \226\159\167 = \226\159\166 W1 \226\159\167)).
(rewrite <- H1).
(rewrite size_fresh_ctx; auto).
(assert (S2 : \226\159\166 \206\1472 \226\159\167 = \226\159\166 W2 \226\159\167)).
(rewrite <- H3).
(rewrite size_fresh_ctx; auto).
(rewrite H0, H1, H2, H3).
replace 0%nat with \226\159\166 [] : Ctx \226\159\167 : nat by auto.
replace (size_wtype W1) with \226\159\166 \206\1471 \226\159\167.
replace (size_wtype W2) with \226\159\166 \206\1472 \226\159\167.
specialize denote_compose as DC.
(unfold denote_circuit in DC).
(erewrite DC with (\206\1471 := []) (\206\14701 := [])).
(simpl).
(unfold compose_super).
(rewrite H2, H3).
reflexivity.
*
(apply types_f).
(rewrite <- H0, <- H1).
(apply add_fresh_typed_empty).
(rewrite add_fresh_split).
easy.
*
(unfold Typed_Box in types_g).
(intros \206\147 \206\147' p pf wf_p).
solve_merge.
(apply types_g).
monoid.
(rewrite merge_nil_r).
auto.
*
solve_merge.
*
(split; [ validate | monoid ]).
Qed.
Fact inPar_correct :
  forall W1 W1' W2 W2' (f : Box W1 W1') (g : Box W2 W2') 
    (safe : bool) (\207\1291 : Square (2 ^ \226\159\166 W1 \226\159\167)) (\207\1292 : Square (2 ^ \226\159\166 W2 \226\159\167)),
  Typed_Box f ->
  Typed_Box g ->
  denote_box safe (inPar f g) (\207\1291 \226\138\151 \207\1292)%M ==
  (denote_box safe f \207\1291 \226\138\151 denote_box safe g \207\1292)%M.
Proof.
Admitted.
Lemma HOAS_Equiv_inSeq :
  forall w1 w2 w3 (c1 c1' : Box w1 w2) (c2 c2' : Box w2 w3),
  Typed_Box c1 ->
  Typed_Box c1' ->
  Typed_Box c2 -> Typed_Box c2' -> c1 \226\137\161 c1' -> c2 \226\137\161 c2' -> c2 \194\183 c1 \226\137\161 c2' \194\183 c1'.
Proof.
(intros w1 w2 w3 c1 c1' c2 c2' T1 T1' T2 T2' E1 E2).
(intros \207\129 b).
(simpl_rewrite inSeq_correct; trivial).
(simpl_rewrite inSeq_correct; trivial).
(unfold compose_super).
(unfold HOAS_Equiv in *).
(rewrite E2).
(rewrite E1).
reflexivity.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqbLQ2oo"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
