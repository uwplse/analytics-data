Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqTnNDzy"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From Armada.Examples.MailServer Require Import MailAPI.
From Armada.Goose.Examples Require Import MailServer.
From Armada.Goose.Proof Require Import Interp.
Require Import Goose.Proof.Interp.
From Armada Require AtomicPair.Helpers.
From Armada.Goose Require Import Machine GoZeroValues Heap GoLayer.
From Armada.Goose Require Import Machine.
From Armada.Goose Require Import GoZeroValues.
Existing Instance AtomicPair.Helpers.from_exist_left_sep_later.
Existing Instance AtomicPair.Helpers.from_exist_left_sep.
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Import Filesys.FS.
Import GoLayer.Go.
Import Mail.
Ltac
 non_err' :=
  match goal with
  | |- context [ ?x = Some _ ] =>
        match x with
        | None => fail 1
        | Some _ => fail 1
        | _ => let Heq := fresh "Heq" in
               destruct x as [?| ] eqn:Heq
        end
  | |- lookup _ _ _ _ => unfold lookup
  | |- unwrap _ _ _ => unfold unwrap
  | |- readSome _ _ _ => unfold readSome
  | |- context [ match ?x with
                 | _ => _
                 end ] => match goal with
                          | H:x = _ |- _ => rewrite H
                          end
  end.
Ltac non_err := repeat non_err'; trivial.
Ltac
 ghost_err :=
  iMod (ghost_step_err with "[$] [$] [$]") ||
    match goal with
    | |- context [ (_ \226\164\135 ?K _)%I ] => iMod
      (@ghost_step_err _ _ _ _ _ _ _ _ _ _ (\206\187 x, K (Bind x _))
      with "[$] [$] [$]")
    end; eauto.
Ltac do_then := repeat (do 2 eexists; split; non_err).
Ltac
 err_start := <ssreflect_plugin::ssrtclseq@0>
 left; right; do_then; destruct (open) ; last  by econstructor.
Ltac err_hd := left; non_err; try econstructor.
Ltac err_cons := right; do_then.
Ltac err0 := err_start; err_hd.
Ltac err1 := err_start; err_cons; err_hd.
Ltac err2 := err_start; err_cons; err_cons; err_hd.
Ltac err3 := err_start; err_cons; err_cons; err_cons; err_hd.
Ltac solve_err := ghost_err; (solve [ err0 | err1 | err2 | err3 ]).
Section api_lemmas.
Context `{@gooseG gmodel gmodelHwf \206\163} `{!@cfgG Mail.Op Mail.l \206\163}.
#[global]Instance source_state_inhab : (Inhabited State).
Proof.
eexists.
exact {| heap := \226\136\133; messages := \226\136\133; open := false |}.
Qed.
#[global]Instance LockRef_inhab : (Inhabited LockRef).
Proof.
eexists.
(apply nullptr).
Qed.
Lemma open_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call Open)
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\140\156\207\131.(open) = false\226\140\157 \226\136\151 j \226\164\135 K (Call Open) \226\136\151 source_state \207\131.
Proof.
iIntros.
(destruct \207\131.(open) as [| ] eqn:Heq).
-
ghost_err.
(intros n).
left.
right.
(do 2 eexists).
split.
{
rewrite /reads.
rewrite Heq.
econstructor.
}
(simpl).
econstructor.
-
by iFrame.
Qed.
Lemma open_open_step_inv {T} {T'} j j' K K' `{LanguageCtx _ _ T Mail.l K}
  `{LanguageCtx _ _ T' Mail.l K'} (\207\131 : l.(OpState)) 
  E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call Open)
    -\226\136\151 j' \226\164\135 K' (Call Open) -\226\136\151 source_ctx -\226\136\151 source_state \207\131 ={E}=\226\136\151 False.
Proof.
iIntros ( ? ) "Hj Hj' #Hsrc Hstate".
(<ssreflect_plugin::ssrtclseq@0> iMod (open_step_inv with "[$] [$] [$]") as (
 Hopen ) "(?&?)" ; first  auto).
iMod (ghost_step_call with "[$] [$] [$]") as "(?&?&?)".
{
(intros n).
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  by econstructor).
(econstructor; auto).
(do 2 eexists; split).
{
rewrite /reads Hopen //=.
}
(simpl).
(do 2 eexists).
split.
*
econstructor.
*
econstructor.
}
{
auto.
}
(<ssreflect_plugin::ssrtclseq@0> iMod (open_step_inv with "[$] [$] [$]") as (
 Hopen' ) "(?&?)" ; first  auto).
(simpl in Hopen').
congruence.
Qed.
Lemma pickup_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (pickup uid)
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\140\156\226\136\131 v, \207\131.(messages) !! uid = Some v\226\140\157
                 \226\136\151 j \226\164\135 K (pickup uid) \226\136\151 source_state \207\131.
Proof.
iIntros.
(<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
(iIntros; iFrame; eauto).
Qed.
Lemma pickup_end_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid (\207\131 : l.(OpState)) msgs E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Pickup_End uid msgs))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 v,
                   \226\140\156\207\131.(messages) !! uid = Some (MPickingUp, v)\226\140\157
                   \226\136\151 j \226\164\135 K (Call (Pickup_End uid msgs)) \226\136\151 source_state \207\131.
Proof.
iIntros.
non_err.
-
(destruct p as ([], ?); try by iFrame; auto; solve_err).
-
solve_err.
Qed.
Lemma lock_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Lock uid))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s v,
                   \226\140\156\207\131.(messages) !! uid = Some (s, v)\226\140\157
                   \226\136\151 j \226\164\135 K (Call (Lock uid)) \226\136\151 source_state \207\131.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqbavy4p"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqYujO0z"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Proof.
iIntros.
non_err.
-
(destruct p as ([], ?); try by iFrame; eauto; solve_err).
-
solve_err.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqyGYTDJ"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqBbhjWy"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqh3se1F"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Lemma unlock_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Unlock uid))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 v,
                   \226\140\156\207\131.(messages) !! uid = Some (MLocked, v)\226\140\157
                   \226\136\151 j \226\164\135 K (Call (Unlock uid)) \226\136\151 source_state \207\131.
Proof.
iIntros.
non_err.
-
(* Auto-generated comment: Succeeded. *)

