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
Import ApplicativeNotation FunctorNotation ListNotations MonadNotation.
Open Scope program_scope.
Open Scope sum_scope.
Open Scope monad_scope.
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
Definition unwrap_data (rx : kvs_data exp) : kvs_data id :=
  match rx with
  | Kvs_GET k => Kvs_GET k
  | Kvs_PUT k v => Kvs_PUT k v
  | Kvs_CAS k x v => Kvs_CAS k x v
  | Kvs_OK vx => Kvs_OK (unwrap vx)
  | Kvs_NoContent => Kvs_NoContent
  | Kvs_BadRequest => Kvs_BadRequest
  | Kvs_PreconditionFailed => Kvs_PreconditionFailed
  end.
Definition embed_exp {T} {E} `{serverAppE id -< E} (ex : serverAppE exp T) : itree E T :=
  match ex in (serverAppE _ T) return (itree E T) with
  | ServerApp_Recv => trigger ServerApp_Recv
  | ServerApp_Send rx => trigger (ServerApp_Send (unwrap_data rx))
  | ServerApp_Fresh => i <- trigger ServerApp_Fresh;; Ret (exp_int (i : id N))
  end.
