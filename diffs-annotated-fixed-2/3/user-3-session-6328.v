Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqQf8JcC"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import POCS.
Definition State : Type := list block.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqVa1ToI"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqTGk5fU"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Definition get_spec : Specification unit (list block) unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => r = state /\ state' = state;
  recovered := fun _ state' => state' = state |}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqSSrHnX"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqP9LnIh"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition append_spec v : Specification unit bool unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' =>
          r = true /\ state' = state ++ v \/ r = false /\ state' = state;
  recovered := fun _ state' => state' = state \/ state' = state ++ v |}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqeLGxni"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqil8sAz"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition reset_spec : Specification unit unit unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => r = tt /\ state' = nil;
  recovered := fun _ state' => state' = state \/ state' = nil |}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqroepxD"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqVoEmPd"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Module Type LogAPI.
Axiom (init : proc InitResult).
Axiom (get : proc (list block)).
Axiom (append : list block -> proc bool).
Axiom (reset : proc unit).
Axiom (recover : proc unit).
Axiom (abstr : Abstraction State).
Axiom (init_ok : init_abstraction init recover abstr inited_any).
Axiom (get_ok : proc_spec get_spec get recover abstr).
Axiom
  (append_ok : forall v, proc_spec (append_spec v) (append v) recover abstr).
Axiom (reset_ok : proc_spec reset_spec reset recover abstr).
Axiom (recover_wipe : rec_wipe recover abstr no_wipe).
Hint Resolve init_ok: core.
Hint Resolve get_ok: core.
Hint Resolve append_ok: core.
Hint Resolve reset_ok: core.
Hint Resolve recover_wipe: core.
End LogAPI.
(* Auto-generated comment: Succeeded. *)

