Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
+
(apply value_sem_sub_k_i_union__inv in Hsem; try assumption).
(destruct Hsem as [Hsem| Hsem]; [ apply union_right_1 | apply union_right_2 ]; auto).
+
(simpl in Hdep).
(pose proof (le_S_n _ _ Hdep) as Hdep').
(* Failed. *)
