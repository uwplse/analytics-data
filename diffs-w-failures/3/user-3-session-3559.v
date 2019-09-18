From RecordUpdate Require Import RecordUpdate.
Set Implicit Arguments.
Generalizable Variables all.
Class Lens X A :={proj : X -> A; inj : A -> X -> X}.
Class LensWf X A (lens : Lens X A) :={inj_proj : forall x, inj (proj x) x = x;
                                      proj_inj :
                                       forall a x, proj (inj a x) = a}.
Instance Setter_Lens  `{proj : X -> A} (setter : SetterWf proj): 
 (Lens X A) := (Build_Lens proj (fun a => set proj (fun _ => a))).
Arguments Setter_Lens {X} {A} proj {setter}.
Instance Setter_LensWf  `(proj : X -> A) (setter_wf : SetterWf proj):
 (LensWf (Setter_Lens proj)).
Proof.
(unfold Setter_Lens; constructor; simpl; intros).
(rewrite set_eq; auto).
(rewrite set_get; auto).
Qed.
