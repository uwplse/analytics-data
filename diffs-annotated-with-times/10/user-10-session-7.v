Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqz0V4TO"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import Basics ExtrOcamlIntConv List NArith String.
From ExtLib Require Import Applicative Functor Monad StateMonad.
From ITree Require Import Exception ITree Nondeterminism.
From SimpleIO Require Import IO_Random SimpleIO.
From QuickChick Require Import Decidability Show.
From DeepWeb Require Import Exp.
Import ApplicativeNotation FunctorNotation ListNotations MonadNotation
SumNotations.
Open Scope N_scope.
Open Scope monad_scope.
Open Scope program_scope.
Open Scope sum_scope.
Definition secret_key := N.
Definition public_key := N.
Definition shared_key := N.
Definition base := 5.
Definition prime := 23.
Definition derive_public (k : secret_key) : public_key := base ^ k mod prime.
Definition calculate_shared (s : secret_key) (p : public_key) : shared_key :=
  p ^ s mod prime.
Definition cipher_text := prod shared_key.
Definition cipher {plain_text} :
  shared_key -> plain_text -> cipher_text plain_text := pair.
Definition decipher {plain_text} (s : shared_key)
  (c : cipher_text plain_text) : option plain_text :=
  let (k, t) := c in if s =? k then Some t else None.
Definition random := N.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
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
         | Kvs_CAS k x v =>
             "CAS " ++ show k ++ " " ++ show x ++ " " ++ show v
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
         | Kvs_CAS k x v =>
             "CAS " ++ show k ++ " " ++ show x ++ " " ++ show v
         | Kvs_OK v => "OK  " ++ show v
         | Kvs_NoContent => "204"
         | Kvs_BadRequest => "400"
         | Kvs_PreconditionFailed => "412"
         end |}.
Definition kvs_get {V} (k : N) : list (N * V) -> option V :=
  fmap snd \226\136\152 find (N.eqb k \226\136\152 fst).
Definition kvs_put {K} {V} : K -> V -> list (K * V) -> list (K * V) :=
  compose cons \226\136\152 pair.
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-08-22 03:23:43.370000.*)

