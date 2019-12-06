Goal _ ~ (forall a b, a /\ b).
intro H.
specialize H with False False.
intuition.
Qed.
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-08-28 12:44:33.220000.*)

