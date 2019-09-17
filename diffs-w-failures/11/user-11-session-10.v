Redirect "/tmp/coq16819X7M" Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 115.
Unset Silent.
Redirect "/tmp/coq16819kFT" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Printing Width 115.
Set Silent.
From Coq Require Import NArith String.
From QuickChick Require Import Decidability Show.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Arguments kvs_data : clear implicits.
Instance eqKvs_data  (x y : kvs_data id): (Dec (x = y)).
Proof.
dec_eq.
Defined.
Instance showData : (Show (kvs_data id)) :=
 {|
 show := fun d =>
         match d with
         | Kvs_GET k => "GET " ++ show k
         | Kvs_PUT k v => "PUT " ++ show k ++ " " ++ show v
         | Kvs_CAS k x v => "CAS " ++ show k ++ " " ++ show x ++ " " ++ show v
         | Kvs_OK v => "OK  " ++ show (v : N)
         | Kvs_NoContent => "204"
         | Kvs_BadRequest => "400"
         | Kvs_PreconditionFailed => "412"
         end |}.
