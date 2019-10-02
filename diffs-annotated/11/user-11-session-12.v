Redirect "/tmp/coq16819xWN" Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import Basics ExtrOcamlIntConv List NArith String.
From ExtLib Require Import Applicative Functor Monad.
From ITree Require Import Exception ITree.
From SimpleIO Require Import IO_Random SimpleIO.
From DeepWeb Require Import CryptoLib KvsLib.
Import ApplicativeNotation ListNotations MonadNotation SumNotations.
Open Scope program_scope.
Open Scope sum_scope.
Open Scope monad_scope.
Open Scope N_scope.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Definition Message_Finished (k : shared_key) (verifyData : N) : message :=
  Message_Cipher (cipher k (PlainMessage_Finished verifyData)).
Definition Message_Hello (messageRandom : random) (messagePublic : public_key) : message :=
  Message_Plain (PlainMessage_Hello messageRandom messagePublic).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Definition failWith {E} {R} `{exceptE error -< E} (err : error) : itree E R :=
  vd <- trigger (Throw err);; match vd in void with
                              end.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Module App.
