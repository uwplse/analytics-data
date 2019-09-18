Time
From iris.algebra Require Import auth gmap frac agree namespace_map excl.
Time From stdpp Require Export namespaces.
Time From iris.base_logic.lib Require Export own.
Time From iris.base_logic.lib Require Import gen_heap.
Time From iris.bi.lib Require Import fractional.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time Import uPred.
Time
Class leased_heapG (L V : Type) (\206\163 : gFunctors) `{Countable L} :=
 LeasedHeapG {leased_heap_heapG :> gen_heapG L V \206\163;
              leased_heap_exclG :>
               inG \206\163 (authR (optionUR (exclR (leibnizC V))));
              leased_heap_gen : namespace}.
