Time From iris.algebra Require Import auth gmap frac agree.
Time
Require Export CSL.WeakestPre CSL.Lifting CSL.Adequacy CSL.RefinementAdequacy
  CSL.RefinementIdempotenceFunModule.
Time Require Export CSL.Leased_Heap.
Time From iris.algebra Require Export functions.
Time From iris.base_logic.lib Require Export invariants gen_heap.
Time From iris.proofmode Require Export tactics.
Time Require Export ExMach.ExMachAPI ExMach.WeakestPre.
Time
Class exmachPreG \206\163 :=
 ExMachPreG {exm_preG_iris :> invPreG \206\163;
             exm_preG_mem :> gen_heapPreG nat nat \206\163;
             exm_preG_disk :> leased_heapPreG nat nat \206\163;
             exm_preG_treg_inG :>
              inG \206\163 (csumR countingR (authR (optionUR (exclR unitO))))}.
Time
Definition exmach\206\163 : gFunctors :=
  #[ inv\206\163; gen_heap\206\163 nat nat; leased_heap\206\163 nat nat;
  GFunctor (csumR countingR (authR (optionUR (exclR unitO))))].
Time Instance subG_exmachPreG  {\206\163}: (subG exmach\206\163 \206\163 \226\134\146 exmachPreG \206\163).
Time Proof.
Time solve_inG.
Time Qed.
Time Import ExMach.
