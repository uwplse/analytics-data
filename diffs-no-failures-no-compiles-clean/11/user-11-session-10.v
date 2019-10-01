Redirect "/tmp/coq16819X7M" Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Redirect "/tmp/coq16819kFT" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Redirect "/tmp/coq16819-Zf" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Redirect "/tmp/coq16819Yur" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
From Coq Require Import Basics List NArith String.
From ExtLib Require Import Functor.
From QuickChick Require Import Decidability Show.
From DeepWeb Require Import Exp.
Open Scope string_scope.
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
Instance showDataX : (Show (kvs_data exp)) :=
 {|
 show := fun d =>
         match d with
         | Kvs_GET k => "GET " ++ show k
         | Kvs_PUT k v => "PUT " ++ show k ++ " " ++ show v
         | Kvs_CAS k x v => "CAS " ++ show k ++ " " ++ show x ++ " " ++ show v
         | Kvs_OK v => "OK  " ++ show v
         | Kvs_NoContent => "204"
         | Kvs_BadRequest => "400"
         | Kvs_PreconditionFailed => "412"
         end |}.
Definition kvs_get {V} (k : N) : list (N * V) -> option V := fmap snd \226\136\152 find (N.eqb k \226\136\152 fst).
Definition kvs_put {K} {V} : K -> V -> list (K * V) -> list (K * V) := compose cons \226\136\152 pair.
Redirect "/tmp/coq16819l4x" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
