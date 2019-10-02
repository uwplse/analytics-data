Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(unfold sem_sub_k_i in Hsem).
(assert (Hv : value_type (TRef t)) by constructor).
Search -match_ty_i.
(assert (Hm : |-[ S k] TRef t <$ TRef t) by (apply match_ty_i__reflexive; assumption)).
(pose proof (Hse _ Hv Hm) as Hmu).
(* Failed. *)
