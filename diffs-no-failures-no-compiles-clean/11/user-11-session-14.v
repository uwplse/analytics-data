Redirect "/tmp/coq16819l_l" Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import ExtrOcamlIntConv.
From ExtLib Require Import Applicative StateMonad Monad.
From ITree Require Import Exception Nondeterminism ITree.
From SimpleIO Require Import IO_Random SimpleIO.
From DeepWeb Require Import CryptoLib KvsLib.
Redirect "/tmp/coq16819_Ty" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Redirect "/tmp/coq16819xdB" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Redirect "/tmp/coq16819-nH" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Redirect "/tmp/coq16819LyN" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Redirect "/tmp/coq16819Y8T" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Import ApplicativeNotation FunctorNotation ListNotations MonadNotation SumNotations.
Open Scope sum_scope.
Open Scope N_scope.
Module App.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Arguments serverAppE : clear implicits.
Definition smE := serverAppE exp +' evalE.
Definition kvs_state exp_ := list (N * exp_ N).
Definition kvs : itree smE void :=
  rec
    (fun st : kvs_state exp =>
     req <- trigger ServerApp_Recv;;
     match req with
     | Kvs_GET k =>
         match kvs_get k st with
         | Some v => embed ServerApp_Send (Kvs_OK v);; call st
         | None => v <- trigger (@ServerApp_Fresh exp);; embed ServerApp_Send (Kvs_OK v);; call (kvs_put k v st)
         end
     | Kvs_PUT k v => embed ServerApp_Send Kvs_NoContent;; call (kvs_put k (exp_int v) st)
     | Kvs_CAS k x v' =>
         match kvs_get k st with
         | Some v =>
             b <- trigger (Eval (exp_eq x v));;
             (if b : bool
              then embed ServerApp_Send Kvs_NoContent;; call (kvs_put k (exp_int v') st)
              else embed ServerApp_Send Kvs_PreconditionFailed;; call st)
         | None =>
             v <- trigger (@ServerApp_Fresh exp);;
             b <- trigger (Eval (exp_eq x v));;
             (if b : bool
              then embed ServerApp_Send Kvs_NoContent;; call (kvs_put k (exp_int v') st)
              else embed ServerApp_Send Kvs_PreconditionFailed;; call (kvs_put k v st))
         end
     | _ => embed ServerApp_Send Kvs_BadRequest;; call st
     end) [].
