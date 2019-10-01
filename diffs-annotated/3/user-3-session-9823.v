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
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
(eapply then_init_compose; eauto).
step_proc.
(destruct (r == 0)).
-
step_proc.
-
step_proc.
(destruct (lt_dec r0 (diskSize (stateDisk state)))).
+
step_proc.
(case_eq (diskGet (stateDisk state) (diskSize (stateDisk state) - 1)); intros).
{
exists (diskUpd (diskShrink (stateDisk state)) (stateBadBlock state) b).
(unfold inited_any; split; auto).
(constructor; intuition; autorewrite with upd in *; intuition).
-
