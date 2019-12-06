Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqP3zR22"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import DBCircuits.
Require Import TypeChecking.
Require Import Denotation.
Require Import Composition.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
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
Definition valid_ancillae {W} (c : Circuit W) : Prop :=
  forall (\206\147 \206\1470 : Ctx) \207\129, \206\147 \226\138\162 c :Circ -> (\226\159\168 \206\1470 | \206\147 \226\138\169 c \226\159\169) \207\129 == (\226\159\168! \206\1470 | \206\147 \226\138\169 c !\226\159\169) \207\129.
Definition valid_ancillae_box {W1} {W2} (c : Box W1 W2) :=
  forall \207\129, Typed_Box c -> denote_box true c \207\129 == denote_box false c \207\129.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqjMNFPS"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Definition valid_ancillae' {W} (c : Circuit W) :=
  forall (\206\147 \206\1470 : Ctx) \207\129,
  \206\147 \226\138\162 c :Circ -> Mixed_State \207\129 -> trace ((\226\159\168! \206\1470 | \206\147 \226\138\169 c !\226\159\169) \207\129) = 1.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqRFmcai"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Definition valid_ancillae_box' {W1} {W2} (c : Box W1 W2) : Prop :=
  forall \207\129, Typed_Box c -> Mixed_State \207\129 -> trace (denote_box false c \207\129) = 1.
Proposition valid_ancillae_equal :
  forall W (c : Circuit W), valid_ancillae c <-> valid_ancillae' c.
Proof.
(intros).
(unfold valid_ancillae, valid_ancillae').
split.
-
(intros H \206\147 \206\1470 \207\129 H0 H1).
(rewrite <- H; trivial).
(apply mixed_state_trace_1).
admit.
-
(induction c as [| W' W0 g p c IH| IH]).
+
reflexivity.
+
(intros H \206\147 \206\1470 \207\129 H').
replace (gate g p c) with compose (gate g p (fun p' => output p')) c by auto.
dependent destruction H'.
(destruct \206\1471 as [| \206\1471]; try invalid_contradiction).
(erewrite denote_compose with (\206\1471 := []); trivial).
Focus 3.
(intros \206\1473 \206\1470' p0 H0 H1).
(destruct H0).
(rewrite merge_nil_r in pf_merge).
subst.
(apply (t0 \206\1473); trivial).
Abort.
Fact valid_ancillae_box_equal :
  forall W1 W2 (c : Box W1 W2) \207\129, valid_ancillae_box c \207\129 <-> valid_ancillae_box' c.
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-08-12 14:21:22.790000.*)

