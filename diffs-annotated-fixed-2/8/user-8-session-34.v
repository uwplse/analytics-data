Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqH1mLuD"
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
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqRfcFt8" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Timeout 1 About denote_circuit.
Timeout 1 Print denote_circuit.
Fact denote_compose :
  forall safe w (c : Circuit w) (\206\147 : Ctx),
  forall w' (f : Pat w -> Circuit w') (\206\1470 \206\1471 \206\1471' \206\14701 : Ctx) \207\129,
  \206\147 \226\138\162 c :Circ ->
  \206\1471 \226\138\162 f :Fun ->
  \206\1471' \226\169\181 \206\1471 \226\136\153 \206\147 ->
  \206\14701 \226\169\181 \206\1470 \226\136\153 \206\1471 ->
  denote_circuit safe (compose c f) \206\1470 \206\1471' \207\129 =
  compose_super (denote_circuit safe (f (add_fresh_pat w \206\1471)) \206\1470 (add_fresh_state w \206\1471)) (denote_circuit safe c \206\14701 \206\147) \207\129.
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
replace (compose (gate g p1 f0) f) with gate g p1 (fun p2 => compose (f0 p2) f) by auto.
(repeat rewrite denote_gate_circuit; fold_denotation).
(set (p2 := process_gate_pat g p1 \206\147)).
(set (\206\1473'' := process_gate_state g p1 \206\147)).
admit.
-
admit.
Admitted.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqKdN89S" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Theorem inSeq_correct :
  forall W1 W2 W3 (g : Box W2 W3) (f : Box W1 W2) (safe : bool) \207\129,
  Typed_Box g -> Typed_Box f -> denote_box safe (inSeq f g) \207\129 == compose_super (denote_box safe g) (denote_box safe f) \207\129.
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
(erewrite DC with (\206\1471 := []) (\206\14701 := \226\136\133)).
(* Auto-generated comment: Failed. *)

