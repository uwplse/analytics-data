Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
(simpl in Hdep).
(pose proof (le_S_n _ _ Hdep) as Hdep').
(unfold sem_sub_k in Hsem).
specialize (Hsem _ Hma).
(apply match_ty_ref__inv in Hsem).
(* Failed. *)
