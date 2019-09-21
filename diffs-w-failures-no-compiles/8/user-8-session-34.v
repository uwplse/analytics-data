Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqH1mLuD"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 96.
Set Silent.
Require Export Contexts.
Require Export HOASCircuits.
Require Export HOASLib.
Require Export DBCircuits.
Require Export Quantum.
Unset Silent.
Require Export Denotation.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqRfcFt8" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Printing Width 131.
Unset Silent.
Unset Silent.
Set Printing Width 131.
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
Set Silent.
Proof.
(intros safe w c \206\147 TP).
dependent induction TP.
-
(intros w' f \206\1470 \206\1471 \206\1471' \206\14701 WT pf_merge1 pf_merge2).
(simpl).
(unfold compose_super).
(unfold denote_circuit).
Unset Silent.
Show.
