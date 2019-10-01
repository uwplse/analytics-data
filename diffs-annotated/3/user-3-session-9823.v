Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqsuQtcv"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import POCS.
Require Import OneDiskAPI.
Require Import BadBlockAPI.
(constructor; intuition; autorewrite with upd in *; intuition).
-
(rewrite diskShrink_preserves; auto).
(rewrite diskShrink_size; lia).
-
(rewrite diskUpd_eq; auto).
(rewrite diskShrink_size; lia).
-
lia.
}
{
(exfalso; eapply disk_inbounds_not_none; [  | eauto ]; lia).
}
+
step_proc.
Qed.
Theorem read_ok :
  forall a, proc_spec (OneDiskAPI.read_spec a) (read a) recover abstr.
Proof.
(unfold read).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc; intros).
(destruct a'; simpl in *; intuition).
{
eauto.
}
(destruct (a == r)).
-
invert_abstraction.
(step_proc; intuition).
{
eauto.
