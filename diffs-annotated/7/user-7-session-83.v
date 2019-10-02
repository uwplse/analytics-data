Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
(induction k;
  match goal with
  | |- forall t1 : ty, InNF( t1) -> | t1 | <= ?k -> forall t2 : ty, ||-[ ?k][t1]<= [t2] -> |- t1 << t2 =>
        apply
         (in_nf_mut (fun (t1 : ty) (_ : atom_type t1) => | t1 | <= k -> forall t2 : ty, ||-[ k][t1]<= [t2] -> |- t1 << t2)
            (fun (t1 : ty) (_ : in_nf t1) => | t1 | <= k -> forall t2 : ty, ||-[ k][t1]<= [t2] -> |- t1 << t2))
  end; try tauto;
  try
   match goal with
   | |- context [ |- TCName _ << _ ] => intros c Hdep; apply cname_sem_sub_k_i__sub_d; assumption
   | |- context [ |- TPair _ _ << _ ] =>
         intros ta1 ta2 Hat1 IH1 Hat2 IH2 Hdep; assert (Hat : atom_type (TPair ta1 ta2)) by (constructor; assumption);
          destruct (max_inv_depth_le__inv _ _ _ Hdep) as [Hdep1 Hdep2]; apply pair_sem_sub_k_i__sub_d; tauto
   | |- context [ |- TUnion _ _ << _ ] =>
         intros t1 t2 Hnf1 IH1 Hnf2 IH2 Hdep; destruct (max_inv_depth_le__inv _ _ _ Hdep) as [Hdep1 Hdep2]; intros t' Hsem;
          apply sem_sub_k_i_union_l__inv in Hsem; destruct Hsem as [Hsem1 Hsem2]; constructor; auto
   end).
(* Failed. *)
