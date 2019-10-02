Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
(apply match_ty_i_ref__inv in Hsem).
(destruct Hsem as [t' [Heqt' Href]]).
(inversion Heqt'; subst).
clear Heqt'.
constructor.
*
(apply IHk; try assumption).
(apply sem_eq_k_i__sem_sub_k in Href).
(* Failed. *)
