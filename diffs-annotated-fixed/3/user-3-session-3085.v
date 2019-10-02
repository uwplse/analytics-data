Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqjKDz4I"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqOruyQE"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqWlP2BK"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From Armada.Examples.MailServer Require Import MailAPI MailAPILemmas MailHeap
  MailTriples.
From Armada.Goose.Examples Require Import MailServer.
From Armada.Goose.Proof Require Import Interp.
Require Import Goose.Proof.RefinementAdequacy.
From Armada Require AtomicPair.Helpers.
From Armada.Goose Require Import Machine GoZeroValues Heap GoLayer.
From Armada.Goose Require Import ExplicitModel.
From Armada.Goose Require Import GoZeroValues.
Inductive compile_mail_base {gm : GoModel} :
forall {T}, proc Mail.Op T \226\134\146 proc GoLayer.Op T \226\134\146 Prop :=
  | cm_open : compile_mail_base (Call Mail.Open) MailServer.Open
  | cm_pickup :
      forall uid, compile_mail_base (Mail.pickup uid) (MailServer.Pickup uid)
  | cm_deliver :
      forall uid msg,
      compile_mail_base (Mail.deliver uid msg) (MailServer.Deliver uid msg)
  | cm_delete :
      forall uid msg,
      compile_mail_base (Call (Mail.Delete uid msg))
        (MailServer.Delete uid msg)
  | cm_lock :
      forall uid,
      compile_mail_base (Call (Mail.Lock uid)) (MailServer.Lock uid)
  | cm_unlock :
      forall uid,
      compile_mail_base (Call (Mail.Unlock uid)) (MailServer.Unlock uid)
  | cm_dataop :
      forall {T} (op : Data.Op T),
      compile_mail_base (Call (Mail.DataOp op)) (Call (DataOp op)).
Definition mail_impl {gm : GoModel} :=
  {|
  compile_rel_base := @compile_mail_base gm;
  recover_rel := rec_singleton MailServer.Recover |}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqyTX2C7"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqKZSx3Y"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
(* Auto-generated comment: Succeeded. *)

