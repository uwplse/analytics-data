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
Proof.
(intros safe w c \206\147 TP).
dependent induction TP.
-
(intros w' f \206\1470 \206\1471 \206\1471' \206\14701 WT pf_merge1 pf_merge2).
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
(intros w' h \206\1473 \206\1472 \206\1473' \206\14703 WT pf_merge1 pf_merge2).
replace (compose (gate g p1 f) h) with gate g p1 (fun p2 => compose (f p2) h) by auto.
(repeat rewrite denote_gate_circuit; fold_denotation).
(set (p2 := process_gate_pat g p1 \206\1473')).
(set (\206\1473'' := process_gate_state g p1 \206\1473')).
admit.
-
admit.
Admitted.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqey9Z9f" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
