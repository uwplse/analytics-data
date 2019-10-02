Redirect "/tmp/coq16819Zvy" Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import ExtrOcamlIntConv.
From ExtLib Require Import Applicative Monad StateMonad.
From ITree Require Import Exception ITree Nondeterminism.
From SimpleIO Require Import IO_Random SimpleIO.
From DeepWeb Require Import CryptoLib KvsLib.
Import ApplicativeNotation FunctorNotation ListNotations MonadNotation
SumNotations.
Open Scope N_scope.
Open Scope monad_scope.
Open Scope sum_scope.
Module App.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Arguments appE : clear implicits.
Instance showAppE  {T}: (Show (appE id T)) :=
 {|
 show := fun ae =>
         match ae with
         | App_Accept => "Application Accept"
         | App_Recv c => "Application Receive " ++ show c
         | App_Send c msg => "Application Send " ++ show c ++ " \226\159\185 " ++ show msg
         end |}.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Definition smE := appE exp +' evalE +' nondetE.
Definition kvs_state exp_ : Type := list connection * list (N * exp_ N).
Fixpoint choose {A E} `{nondetE -< E} (a : A) (l : list A) : itree E A :=
  match l with
  | [] => ret a
  | x :: l' => b <- trigger Or;; (if b : bool then ret x else choose x l')
  end.
Definition smi : itree smE void :=
  rec
    (fun cst : kvs_state exp =>
     let (cs, st) := cst in
     match conns with
     | [] => conn <- trigger App_Accept;; call ([conn], st)
     | c0 :: cs' =>
         or (c <- trigger App_Accept;; call (c :: cs, st))
           (c <- choose c0 cs';;
            req <- embed App_Recv c;;
            match req with
            | Kvs_GET k =>
                match kvs_get k st with
                | Some v => embed App_Send c (Kvs_OK v);; call cst
                | None => v <- trigger Eval_Var;; embed App_Send c (Kvs_OK v);; call (cs, kvs_put k v st)
                end
            | Kvs_PUT k v => embed App_Send c Kvs_NoContent;; call (cs, kvs_put k (exp_int v) st)
            | Kvs_CAS k x v' =>
                match kvs_get k st with
                | Some v =>
                    b <- trigger (Eval_Decide (exp_eq x v));;
                    (if b : bool
                     then embed App_Send c Kvs_NoContent;; call (cs, kvs_put k (exp_int v') st)
                     else embed App_Send c Kvs_PreconditionFailed;; call cst)
                | None =>
                    v <- trigger Eval_Var;;
                    b <- trigger (Eval_Decide (exp_eq x v));;
                    (if b : bool
                     then embed App_Send c Kvs_NoContent;; call (cs, kvs_put k (exp_int v') st)
                     else embed App_Send c Kvs_PreconditionFailed;; call (cs, kvs_put k v st))
                end
            | _ => embed App_Send c Kvs_BadRequest;; call cst
            end)
     end) ([], []).
(* Auto-generated comment: Failed. *)

