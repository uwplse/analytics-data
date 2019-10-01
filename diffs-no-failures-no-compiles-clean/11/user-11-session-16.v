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
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Arguments appE : clear implicits.
Redirect "/tmp/coq16819L5B" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Instance showAppE  {T}: (Show (appE id T)) :=
 {|
 show := fun ae =>
         match ae with
         | App_Accept => "Application Accept"
         | App_Recv c => "Application Receive " ++ show c
         | App_Send c msg =>
             "Application Send " ++ show c ++ " \226\159\185 " ++ show msg
         end |}.
Redirect "/tmp/coq16819YDI" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Redirect "/tmp/coq16819lNO" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Definition smE := appE exp +' evalE +' nondetE.
Definition kvs_state exp_ : Type := list connection * list (N * exp_ N).
Redirect "/tmp/coq16819Z2m" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Fixpoint choose {A E} `{nondetE -< E} (a : A) (l : list A) : itree E A :=
  match l with
  | [] => ret a
  | x :: l' => b <- trigger Or;; (if b : bool then ret x else choose x l')
  end.
Redirect "/tmp/coq16819mAt" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Definition smi : itree smE void :=
  rec
    (fun cst : kvs_state exp =>
     let (conns, st) := cst in
     match conns with
     | [] => conn <- trigger App_Accept;; call ([conn], st)
     | c0 :: cs => call cst
     end).
