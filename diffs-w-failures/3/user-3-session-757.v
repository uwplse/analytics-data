Time From iris.base_logic.lib Require Export fancy_updates.
Time From iris.program_logic Require Export language.
Time From iris.bi Require Export weakestpre.
Time From iris.proofmode Require Import base tactics classes.
Time Set Default Proof Using "Type".
Time Import uPred.
Time
Class irisG (\206\155 : language) (\206\163 : gFunctors) :=
 IrisG {iris_invG :> invG \206\163;
        state_interp : state \206\155 \226\134\146 list (observation \206\155) \226\134\146 nat \226\134\146 iProp \206\163;
        fork_post : val \206\155 \226\134\146 iProp \206\163}.
Time #[global]Opaque iris_invG.
Time
Definition wp_pre `{!irisG \206\155 \206\163} (s : stuckness)
  (wp : coPset -c> expr \206\155 -c> (val \206\155 -c> iProp \206\163) -c> iProp \206\163) :
  coPset -c> expr \206\155 -c> (val \206\155 -c> iProp \206\163) -c> iProp \206\163 :=
  \206\187 E e1 \206\166,
    match to_val e1 with
    | Some v => |={E}=> \206\166 v
    | None =>
        \226\136\128 \207\1311 \206\186 \206\186s n,
          state_interp \207\1311 (\206\186 ++ \206\186s) n
          ={E,\226\136\133}=\226\136\151 \226\140\156match s with
                    | NotStuck => reducible e1 \207\1311
                    | _ => True
                    end\226\140\157
                   \226\136\151 (\226\136\128 e2 \207\1312 efs,
                        \226\140\156prim_step e1 \207\1311 \206\186 e2 \207\1312 efs\226\140\157
                        ={\226\136\133,\226\136\133,E}\226\150\183=\226\136\151 state_interp \207\1312 \206\186s (length efs + n)
                                    \226\136\151 wp E e2 \206\166
                                      \226\136\151 ([\226\136\151 list] i\226\134\166ef \226\136\136 efs, 
                                         wp \226\138\164 ef fork_post))
    end%I.
Time #[local]
Instance wp_pre_contractive  `{!irisG \206\155 \206\163} s: (Contractive (wp_pre s)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /wp_pre =>n wp wp' Hwp E e1 \206\166).
Time (repeat f_contractive || f_equiv; apply Hwp).
Time Qed.
Time
Definition wp_def `{!irisG \206\155 \206\163} (s : stuckness) :
  coPset \226\134\146 expr \206\155 \226\134\146 (val \206\155 \226\134\146 iProp \206\163) \226\134\146 iProp \206\163 := 
  fixpoint (wp_pre s).
Time Definition wp_aux `{!irisG \206\155 \206\163} : seal (@wp_def \206\155 \206\163 _).
Time by eexists.
Time Qed.
Time
Instance wp'  `{!irisG \206\155 \206\163}: (Wp \206\155 (iProp \206\163) stuckness) := wp_aux.(unseal).
Time Definition wp_eq `{!irisG \206\155 \206\163} : wp = @wp_def \206\155 \206\163 _ := wp_aux.(seal_eq).
Time Section wp.
Time Context `{!irisG \206\155 \206\163}.
Time Implicit Type s : stuckness.
Time Implicit Type P : iProp \206\163.
Time Implicit Type \206\166 : val \206\155 \226\134\146 iProp \206\163.
Time Implicit Type v : val \206\155.
Time Implicit Type e : expr \206\155.
Time
Lemma wp_unfold s E e \206\166 :
  WP e @ s; E {{\206\166} } \226\138\163\226\138\162 wp_pre s (wp (PROP:=iProp \206\163) s) E e \206\166.
Time Proof.
Time rewrite wp_eq.
Time (apply (fixpoint_unfold (wp_pre s))).
Time Qed.
Time #[global]
Instance wp_ne  s E e n:
 (Proper (pointwise_relation _ (dist n) ==> dist n)
    (wp (PROP:=iProp \206\163) s E e)).
Time Proof.
Time revert e.
Time
(<ssreflect_plugin::ssrtclintros@0> induction (lt_wf n) as [n _ IH] =>e \206\166 \206\168
 H\206\166).
Time rewrite !wp_unfold /wp_pre.
Time (do 24 f_contractive || f_equiv).
Time (<ssreflect_plugin::ssrtclseq@0> apply IH ; first  lia).
