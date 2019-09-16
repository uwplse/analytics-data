Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqFfyVxg"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqP5ea9o"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 79.
From ReductionEffect Require Import PrintingEffect.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqhrdAkM"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Eval compute in (fun f x => f (f (f x))) (fun x => S (print_id x)) 0.
Set Silent.
Eval cbn in (fun f x => f (f (f x))) print_id 0.
Eval hnf in (fun f x => f (f (f x))) print_id 0.
Eval simpl in (fun f x => f (f (f x))) (fun x => print_id (1 + x) + 1) 0.
Unset Silent.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
