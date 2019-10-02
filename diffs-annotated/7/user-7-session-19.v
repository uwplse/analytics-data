Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_pair; auto).
Lemma match_ty_i_eq__inv_depth_eq :
  forall t t' : ty, (forall (k : nat) (v : ty), value_type v -> |-[ k] v <$ t <-> |-[ k] v <$ t') -> | t | = | t' |.
Proof.
(induction t; induction t'; intros H; try reflexivity).
(match goal with
 | |- | ?t1 | = | ?t2 | => assert (Hv : value_type t1) by constructor
 end).
(* Failed. *)
