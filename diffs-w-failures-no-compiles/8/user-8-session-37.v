Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqP3zR22"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 85.
Set Silent.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import Denotation.
Require Import Composition.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Unset Silent.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqLxBZpd"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqJ4AsTz"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Unset Silent.
Set Printing Width 85.
Definition valid_ancillae {W} (c : Circuit W) : Prop :=
  forall \206\147 \206\1470 : Ctx, \206\147 \226\138\162 c :Circ -> \226\159\168 \206\1470 | \206\147 \226\138\169 c \226\159\169 \226\137\161 \226\159\168! \206\1470 | \206\147 \226\138\169 c !\226\159\169.
