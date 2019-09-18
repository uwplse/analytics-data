Time From iris.algebra Require Import auth gmap frac agree.
Time
Require Export CSL.WeakestPre CSL.Lifting CSL.Counting CSL.ThreadReg
  CSL.Leased_Heap.
Time From iris.algebra Require Export functions csum.
Time From iris.base_logic.lib Require Export invariants gen_heap.
Time From iris.proofmode Require Export tactics.
Time Require Export ExMach.ExMachAPI.
Time Set Default Proof Using "Type".
Time
Class exmachG \206\163 :=
 ExMachG {exm_invG : invG \206\163;
          exm_mem_inG :> gen_heapG nat nat \206\163;
          exm_disk_inG :> leased_heapG nat nat \206\163;
          exm_treg_inG :> tregG \206\163}.
Time Import ExMach.
Time
Lemma gen_heap_strong_init `{H : gen_heapPreG L V \206\163} 
  \207\131s :
  (|==> \226\136\131 (H0 : gen_heapG L V \206\163) (Hpf : @gen_heap_inG _ _ _ _ _ H0 =
                                        gen_heap_preG_inG),
          gen_heap_ctx \207\131s \226\136\151 own (gen_heap_name H0) (\226\151\175 to_gen_heap \207\131s))%I.
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_heap \207\131s \226\139\133 \226\151\175 to_gen_heap \207\131s)) as ( \206\179 ) "(?&?)".
Time {
Time (apply auth_both_valid; split; auto).
Time exact : {}to_gen_heap_valid {}.
Time }
Time iMod (own_alloc (\226\151\143 to_gen_meta \226\136\133)) as ( \206\179m ) "Hm".
Time {
Time rewrite auth_auth_valid.
Time exact : {}to_gen_meta_valid {}.
Time }
Time iModIntro.
Time iExists (GenHeapG L V \206\163 _ _ _ _ _ \206\179 \206\179m) , eq_refl.
Time iFrame.
Time iExists _.
Time iFrame.
Time eauto.
Time Qed.
Time
Definition disk_state_interp {\206\163} (hM : gen_heapG addr nat \206\163)
  (hD : leased_heapG addr nat \206\163) :=
  (\206\187 s,
     \226\136\131 mem disk,
       gen_heap_ctx mem (hG:=hM)
       \226\136\151 gen_heap_ctx disk (hG:=leased_heap_heapG hD)
         \226\136\151 \226\140\156mem = mem_state s
            \226\136\167 disk = disk_state s
              \226\136\167 (\226\136\128 i, is_Some (mem_state s !! i) \226\134\146 i < size)
                \226\136\167 (\226\136\128 i, is_Some (disk_state s !! i) \226\134\146 i < size)\226\140\157)%I.
Time
Definition ex_mach_interp {\206\163} {hM : gen_heapG addr nat \206\163}
  {hD : leased_heapG addr nat \206\163} {tr : tregG \206\163} :=
  (\206\187 s, thread_count_interp (fst s) \226\136\151 disk_state_interp hM hD (snd s))%I.
Time
Definition ex_mach_interp' `{exmachG \206\163} :=
  @ex_mach_interp _ exm_mem_inG exm_disk_inG exm_treg_inG.
Time
Instance exmachG_irisG  `{exmachG \206\163}: (irisG ExMach.Op ExMach.l \206\163) := {
 iris_invG :=exm_invG; state_interp :=ex_mach_interp'}.
Time
Definition mem_mapsto_vs k v k' :=
  match Nat.compare k' k with
  | Lt => None
  | Eq => Some v
  | Gt => Some 0
  end.
Time #[global]
Notation "l m\226\134\166{ q } v " := (mapsto (hG:=exm_mem_inG) l q v)
  (at level 20, q  at level 50, format "l  m\226\134\166{ q } v") : bi_scope.
Time #[global]
Notation "l m\226\134\166 v " := (mapsto (hG:=exm_mem_inG) l 1 v) 
  (at level 20) : bi_scope.
Time #[global]
Notation "l d\226\151\175\226\134\166 v " := (mapsto (hG:=leased_heap_heapG exm_disk_inG) l 1 v)
  (at level 20) : bi_scope.
Time #[global]
Notation "l d\226\134\166 v " :=
  (mapsto (hG:=leased_heap_heapG exm_disk_inG) l 1 v \226\136\151 master l v)%I
  (at level 20) : bi_scope.
Time Section lifting.
Time Context `{exmachG \206\163}.
Time Lemma nat_compare_lt_Lt : \226\136\128 n m : nat, n < m \226\134\146 (n ?= m) = Lt.
Time Proof.
Time (intros).
Time by apply nat_compare_lt.
Time Qed.
Time Lemma nat_compare_gt_Gt : \226\136\128 n m : nat, n > m \226\134\146 (n ?= m) = Gt.
Time Proof.
Time (intros).
Time by apply nat_compare_gt.
Time Qed.
Time
Lemma mem_init_to_bigOp mem :
  own (i:=@gen_heap_inG _ _ _ _ _ exm_mem_inG) (gen_heap_name exm_mem_inG)
    (\226\151\175 to_gen_heap mem) -\226\136\151 [\226\136\151 map] i\226\134\166v \226\136\136 mem, i m\226\134\166 v.
Time Proof.
Time (induction mem using map_ind).
Time -
Time iIntros.
Time rewrite //=.
Time -
Time iIntros "Hown".
Time rewrite big_opM_insert //.
Time
iAssert
 (own (i:=@gen_heap_inG _ _ _ _ _ exm_mem_inG) (gen_heap_name exm_mem_inG)
    (\226\151\175 to_gen_heap m) \226\136\151 i m\226\134\166 x)%I with "[Hown]" as "[Hrest $]".
Time {
Time rewrite mapsto_eq /mapsto_def //.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite to_gen_heap_insert
 insert_singleton_op ; last  by apply lookup_to_gen_heap_None).
Time rewrite auth_frag_op.
Time iDestruct "Hown" as "(?&?)".
Time iFrame.
Time }
Time by iApply IHmem.
Time Qed.
Time Import Reg_wp.
Time
Lemma thread_reg1 :
  \226\136\128 n \207\131,
    state_interp (n, \207\131)
    -\226\136\151 thread_count_interp n \226\136\151 disk_state_interp exm_mem_inG exm_disk_inG \207\131.
Time Proof.
Time eauto.
Time Qed.
Time
Lemma thread_reg2 :
  \226\136\128 n \207\131,
    thread_count_interp n \226\136\151 disk_state_interp exm_mem_inG exm_disk_inG \207\131
    -\226\136\151 state_interp (n, \207\131).
Time Proof.
Time auto.
Time Qed.
Time
Lemma wp_spawn {T} s E (e : proc _ T) \206\166 :
  \226\150\183 Registered
  -\226\136\151 \226\150\183 (Registered -\226\136\151 WP (let! _ <- e; Unregister)%proc @ s; \226\138\164 {{ _, True }})
     -\226\136\151 \226\150\183 (Registered -\226\136\151 \206\166 tt) -\226\136\151 WP Spawn e @ s; E {{ \206\166 }}.
Time Proof.
Time (eapply wp_spawn; eauto using thread_reg1, thread_reg2).
Time Qed.
Time
Lemma wp_unregister s E :
  {{{ \226\150\183 Registered }}} Unregister @ s; E {{{ RET tt; True}}}.
Time Proof.
Time (eapply wp_unregister; eauto using thread_reg1, thread_reg2).
Time Qed.
Time
Lemma wp_wait s E : {{{ \226\150\183 Registered }}} Wait @ s; E {{{ RET tt; AllDone}}}.
Time Proof.
Time (eapply wp_wait; eauto using thread_reg1, thread_reg2).
Time Qed.
Time
Lemma wp_write_mem s E i v' v :
  {{{ \226\150\183 i m\226\134\166 v' }}} write_mem i v @ s; E {{{ RET tt; 
  i m\226\134\166 v}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time (<ssreflect_plugin::ssrtclseq@0> iSplit ; first  by destruct s).
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time (inversion H0).
Time subst.
Time (inversion Hstep; subst).
Time iDestruct "Hown" as "(?&Hown)".
Time rewrite /disk_state_interp.
Time iDestruct "Hown" as ( mems disks ) "(Hown1&Hown2&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (?, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown1 Hi") as % Hin_bound.
Time iMod (@gen_heap_update with "Hown1 Hi") as "[Hown1 Hi]".
Time iModIntro.
Time iSplitR "Hi H\206\166".
Time -
Time iFrame.
Time iExists _ , _.
Time iFrame.
Time iPureIntro.
Time split_and !.
Time *
Time rewrite /set_mem /set_default -Heq_mem Hin_bound //.
Time *
Time done.
Time *
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /set_mem /set_default //= =>i').
Time specialize (Hsize i').
Time (destruct (mem_state \207\131 !! i) eqn:Heq; rewrite Heq).
Time **
Time (case (decide (i = i'))).
Time ***
Time (intros -> ?).
Time (apply Hsize; eauto).
Time ***
Time (intros ?).
Time rewrite lookup_insert_ne //=.
Time **
Time (apply Hsize).
Time *
Time eauto.
Time -
Time iApply "H\206\166".
Time eauto.
Time Qed.
Time
Lemma wp_read_mem s E i v :
  {{{ \226\150\183 i m\226\134\166 v }}} read_mem i @ s; E {{{ RET v; i m\226\134\166 v}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time (<ssreflect_plugin::ssrtclseq@0> iSplit ; first  by destruct s).
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time (inversion H0).
Time subst.
Time (inversion Hstep; subst).
Time (inversion Hstep; subst).
Time iDestruct "Hown" as "(?&Hown)".
Time iDestruct "Hown" as ( mems disks ) "(Hown1&Hown2&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (?, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown1 Hi") as % Hin_bound.
Time iModIntro.
Time iSplitR "Hi H\206\166".
Time -
Time iFrame.
Time iExists _ , _.
Time (iFrame; iPureIntro; split_and !; eauto).
Time -
Time rewrite /get_mem /get_default -Heq_mem Hin_bound.
Time by iApply "H\206\166".
Time Qed.
Time Lemma cas_non_stuck i v1 v2 \207\131 : \194\172 ExMach.l.(step) (CAS i v1 v2) \207\131 Err.
Time Proof.
Time (intros Hstuck).
Time (destruct Hstuck as [Hread| (v', (?, (Hread, Hrest)))]).
Time -
Time (inversion Hread).
Time -
Time
(destruct nat_eq_dec; subst; [ apply bind_pure_no_err in Hrest |  ];
  inversion Hrest).
Time Qed.
Time
Lemma wp_cas_fail s E i v1 v2 v3 :
  v1 \226\137\160 v2 \226\134\146 {{{ \226\150\183 i m\226\134\166 v1 }}} cas i v2 v3 @ s; E {{{ RET v1; i m\226\134\166 v1}}}.
Time Proof.
Time iIntros ( Hneq \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (eapply snd_lift_non_err, cas_non_stuck).
Time }
Time iIntros ( e2 (n2, \207\1312) Hstep ) "!>".
Time iDestruct "Hown" as "(?&Hown)".
Time iDestruct "Hown" as ( mems disks ) "(Hown1&Hown2&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (?, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown1 Hi") as % Hin_bound.
Time (assert (Hlookup : \207\131.(mem_state) !! i = Some v1)).
Time {
Time rewrite -Heq_mem.
Time (apply Hin_bound).
Time }
Time (inversion Hstep; subst).
Time (inversion H2 as (v', (\207\1312', (Hread, Hrest))); subst).
Time rewrite /get_mem /get_default /reads Hlookup in  {} Hread.
Time (inversion Hread; subst).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct nat_eq_dec ; first  by exfalso).
Time (inversion Hrest; subst).
Time iModIntro.
Time iSplitR "Hi H\206\166".
Time -
Time iFrame.
Time iExists _ , _.
Time (iFrame; iPureIntro; split_and !; eauto).
Time -
Time by iApply "H\206\166".
Time Qed.
Time
Lemma wp_cas_suc s E i v1 v2 :
  {{{ \226\150\183 i m\226\134\166 v1 }}} cas i v1 v2 @ s; E {{{ RET v1; 
  i m\226\134\166 v2}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto using snd_lift_non_err, cas_non_stuck).
Time }
Time iIntros ( v2' (n2, \207\1312) Hstep ) "!>".
Time iDestruct "Hown" as "(?&Hown)".
Time iDestruct "Hown" as ( mems disks ) "(Hown1&Hown2&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (?, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown1 Hi") as % Hin_bound.
Time (assert (Hlookup : \207\131.(mem_state) !! i = Some v1)).
Time {
Time rewrite -Heq_mem.
Time (apply Hin_bound).
Time }
Time (inversion Hstep; subst).
Time (inversion H2 as (v', (\207\1312', (Hread, Hrest))); subst).
Time (inversion Hread; subst).
Time rewrite /get_mem /get_default /reads Hlookup in  {} Hread  {} Hrest.
Time (<ssreflect_plugin::ssrtclseq@0> destruct nat_eq_dec ; last  by eauto).
Time (destruct Hrest as ([], (?, (Hputs, Hpure)))).
Time (inversion Hpure; subst).
Time (inversion Hputs; inversion Hpure; subst).
Time iMod (@gen_heap_update with "Hown1 Hi") as "(Hown1&Hi)".
Time iModIntro.
Time iSplitR "Hi H\206\166".
Time -
Time iFrame.
Time iExists _ , _.
Time iFrame.
Time iPureIntro.
Time split_and !.
Time *
Time rewrite /set_mem /set_default //= Hin_bound //.
Time *
Time done.
Time *
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /set_mem /set_default //= =>i').
Time specialize (Hsize i').
Time (destruct (mem_state \207\1312' !! i) eqn:Heq; rewrite Heq).
Time **
Time (case (decide (i = i'))).
Time ***
Time (intros -> ?).
Time (apply Hsize; eauto).
Time ***
Time (intros ?).
Time rewrite lookup_insert_ne //=.
Time **
Time (apply Hsize).
Time *
Time eauto.
Time -
Time iApply "H\206\166".
Time eauto.
Time Qed.
Time
Lemma wp_write_disk' s E i v' v :
  {{{ \226\150\183 i d\226\151\175\226\134\166 v' }}} write_disk i v @ s; E {{{ RET tt; 
  i d\226\151\175\226\134\166 v}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time (<ssreflect_plugin::ssrtclseq@0> iSplit ; first  by destruct s).
Time iIntros ( e2 (n2, \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time (inversion H0; subst).
Time iDestruct "Hown" as "(?&Hown)".
Time iDestruct "Hown" as ( mems disks ) "(Hown1&Hown2&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (Heq_disk, (?, Hsize))).
Time iDestruct (gen_heap_valid with "Hown2 Hi") as % Hin_bound.
Time iMod (@gen_heap_update with "Hown2 Hi") as "[Hown2 Hi]".
Time iModIntro.
Time iSplitR "Hi H\206\166".
Time -
Time iFrame.
Time iExists _ , _.
Time iFrame.
Time iPureIntro.
Time split_and !.
Time *
Time done.
Time *
Time rewrite /set_disk /set_default -Heq_disk Hin_bound //.
Time *
Time eauto.
Time *
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /set_disk /set_default //= =>i').
Time specialize (Hsize i').
Time (destruct (disk_state \207\131 !! i) eqn:Heq; rewrite Heq).
Time **
Time (case (decide (i = i'))).
Time ***
Time (intros -> ?).
Time (apply Hsize; eauto).
Time ***
Time (intros ?).
Time rewrite lookup_insert_ne //=.
Time **
Time (apply Hsize).
Time -
Time iApply "H\206\166".
Time eauto.
Time Qed.
Time
Lemma wp_read_disk' s E i v :
  {{{ \226\150\183 i d\226\151\175\226\134\166 v }}} read_disk i @ s; E {{{ RET v; 
  i d\226\151\175\226\134\166 v}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time (<ssreflect_plugin::ssrtclseq@0> iSplit ; first  by destruct s).
Time iIntros ( e2 (n2, \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time (inversion H0; subst).
Time iDestruct "Hown" as "(?&Hown)".
Time iDestruct "Hown" as ( mems disks ) "(Hown1&Hown2&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (Heq_disk, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown2 Hi") as % Hin_bound.
Time iModIntro.
Time iSplitR "Hi H\206\166".
Time -
Time iFrame.
Time iExists _ , _.
Time (iFrame; iPureIntro; split_and !; eauto).
Time -
Time rewrite /get_disk /get_default -Heq_disk Hin_bound.
Time by iApply "H\206\166".
Time Qed.
Time
Lemma wp_write_disk s E i v' v v0 :
  {{{ \226\150\183 i d\226\134\166 v' \226\136\151 \226\150\183 lease i v0 }}} write_disk i v @ s; E {{{ RET tt; 
  i d\226\134\166 v \226\136\151 lease i v}}}.
Time Proof.
Time iIntros ( \206\166 ) "(>(Hi&Hmaster)&>Hlease) H\206\166".
Time iMod (master_lease_update i v' v0 v with "[$] [$]") as "(?&?)".
Time iApply (wp_write_disk' with "[$]").
Time iNext.
Time iIntros.
Time (iApply "H\206\166"; iFrame).
Time Qed.
Time
Lemma wp_read_disk s E i v :
  {{{ \226\150\183 i d\226\134\166 v }}} read_disk i @ s; E {{{ RET v; i d\226\134\166 v}}}.
Time Proof.
Time iIntros ( \206\166 ) ">(Hi&?) H\206\166".
Time iApply (wp_read_disk' with "[$]").
Time iNext.
Time iIntros.
Time (iApply "H\206\166"; iFrame).
Time Qed.
Time
Lemma wp_assert s E b :
  b = true \226\134\146 {{{ True }}} assert b @ s; E {{{ RET (); True}}}.
Time Proof.
Time iIntros ( Hb \206\166 ) "_ H\206\166".
Time rewrite Hb -wp_bind_proc_val.
Time iNext.
Time wp_ret.
Time by iApply "H\206\166".
Time Qed.
Time Lemma disk_lease_agree i v1 v2 : i d\226\134\166 v1 -\226\136\151 lease i v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time iIntros "(_&?) ?".
Time iApply (master_lease_agree with "[$] [$]").
Time Qed.
Time
Lemma disk_next i v : i d\226\134\166 v ==\226\136\151 (i d\226\151\175\226\134\166 v \226\136\151 next_master i v) \226\136\151 next_lease i v.
Time Proof.
Time iIntros "(?&?)".
Time by iMod (master_next with "[$]") as "($&$)".
Time Qed.
Time Section PtrIter.
Time Context (ptsto : nat -> nat -> iProp \206\163).
Time Infix "g\226\134\166" := ptsto (at level 0).
Time
Fixpoint ptr_iter (n : nat) (iters : nat) :=
  match iters with
  | O => (n) g\226\134\166 (0)
  | S n' => (n) g\226\134\166 (0) \226\136\151 ptr_iter (S n) n'
  end%I.
Time
Fixpoint rep_delete n (mem : gmap addr nat) :=
  match n with
  | O => mem
  | S n' => delete n' (rep_delete n' mem)
  end.
Time
Lemma rep_delete_lookup m n :
  m \226\137\165 n \226\134\146 rep_delete n ExMach.init_zero !! m = ExMach.init_zero !! m.
Time Proof.
Time (intros ?).
Time (induction n).
Time *
Time rewrite /rep_delete.
Time auto.
Time *
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite /rep_delete lookup_delete_ne ; last 
 lia).
Time (eapply IHn).
Time lia.
Time Qed.
Time
Lemma gen_ptr_iter_split_aux n iters :
  n + iters < size
  \226\134\146 (([\226\136\151 map] i\226\134\166v \226\136\136 rep_delete n ExMach.init_zero, (i) g\226\134\166 (v))
     -\226\136\151 ptr_iter n iters
        \226\136\151 ([\226\136\151 map] i\226\134\166v \226\136\136 rep_delete (n + S iters) ExMach.init_zero, 
           (i) g\226\134\166 (v)))%I.
Time Proof.
Time revert n.
Time (induction iters).
Time -
Time (intros n ?).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (big_opM_delete _ _ n 0) ; last 
 first).
Time rewrite rep_delete_lookup.
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> apply init_zero_lookup_lt_zero ; first  by
 lia).
Time }
Time {
Time auto.
Time }
Time replace (n + 1) with S n by lia.
Time iIntros "(?&?)".
Time iFrame.
Time -
Time (intros n ?).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (big_opM_delete _ _ n 0) ; last 
 first).
Time rewrite rep_delete_lookup.
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> apply init_zero_lookup_lt_zero ; first  by
 lia).
Time }
Time {
Time auto.
Time }
Time replace (n + S (S iters)) with S n + S iters by lia.
Time iIntros "(?&?)".
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iApply IHiters ; first  by lia).
Time eauto.
Time Qed.
Time End PtrIter.
Time
Definition disk_ptr_iter_split_aux :=
  gen_ptr_iter_split_aux (fun l v => l d\226\134\166 v \226\136\151 lease l v)%I.
Time
Definition mem_ptr_iter_split_aux :=
  gen_ptr_iter_split_aux (fun l v => l m\226\134\166 v)%I.
Time End lifting.
Time Class lockG \206\163 := LockG {lock_tokG :> inG \206\163 (exclR unitO)}.
Time Definition lock\206\163 : gFunctors := #[ GFunctor (exclR unitO)].
Time Instance subG_lock\206\163  {\206\163}: (subG lock\206\163 \206\163 \226\134\146 lockG \206\163).
Time Proof.
Time solve_inG.
Time Qed.
Time Section lock.
Time Context `{!exmachG \206\163} `{!lockG \206\163}.
Time
Definition lock_inv (\206\179 : gname) (i : addr) (P : iProp \206\163) : 
  iProp \206\163 := (i m\226\134\166 0 \226\136\151 P \226\136\151 own \206\179 (Excl ()) \226\136\168 (\226\136\131 v, i m\226\134\166 v \226\136\151 \226\140\156v \226\137\160 0\226\140\157))%I.
Time
Definition is_lock (N : namespace) (\206\179 : gname) (i : addr) 
  (P : iProp \206\163) : iProp \206\163 := (inv N (lock_inv \206\179 i P))%I.
Time Definition locked (\206\179 : gname) : iProp \206\163 := own \206\179 (Excl ()).
Time #[global]
Instance is_lock_persistent  N \206\179 i R: (Persistent (is_lock N \206\179 i R)).
Time Proof.
Time (apply _).
Time Qed.
Time #[global]Instance locked_timless  \206\179: (Timeless (locked \206\179)).
Time Proof.
Time (apply _).
Time Qed.
Time
Lemma lock_init N i v (R : iProp \206\163) E :
  i m\226\134\166 v -\226\136\151 (\226\140\156v = 0\226\140\157 -\226\136\151 R) ={E}=\226\136\151 \226\136\131 \206\179, is_lock N \206\179 i R.
Time Proof.
Time iIntros "Hl HR".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (own_alloc (Excl ())) as ( \206\179 ) "Hexcl"
 ; first  done).
Time iMod (inv_alloc N _ (lock_inv \206\179 i R) with "[-]").
Time {
Time iNext.
Time (destruct (nat_eq_dec v 0)).
Time *
Time subst.
Time (iLeft; iFrame).
Time (iApply "HR"; auto).
Time *
Time iRight.
Time iExists _.
Time iFrame.
Time eauto.
Time }
Time (iModIntro; iExists _; done).
Time Qed.
Time
Lemma lock_init_unlocked N i (R : iProp \206\163) E :
  i m\226\134\166 0 -\226\136\151 R ={E}=\226\136\151 \226\136\131 \206\179, is_lock N \206\179 i R.
Time Proof.
Time iIntros "Hl HR".
Time iApply (lock_init with "Hl").
Time (iIntros "_"; iFrame).
Time Qed.
Time
Lemma lock_crack N i (R : iProp \206\163) \206\179 E :
  \226\134\145N \226\138\134 E \226\134\146 is_lock N \206\179 i R ={E,E \226\136\150 \226\134\145N}=\226\136\151 \226\150\183 (\226\136\131 v, i m\226\134\166 v \226\136\151 (\226\140\156v = 0\226\140\157 -\226\136\151 R)).
Time Proof.
Time (intros).
Time rewrite /is_lock.
Time iIntros "Hinv".
Time iInv "Hinv" as "[(?&?&?)|HR]" "_".
Time -
Time iModIntro.
Time iExists 0.
Time iNext.
Time (iFrame; iIntros; auto).
Time -
Time iModIntro.
Time iNext.
Time iDestruct "HR" as ( v ) "(?&%)".
Time iExists v.
Time iFrame.
Time (iIntros; congruence).
Time Qed.
Time
Lemma wp_lock N \206\179 i (R : iProp \206\163) :
  {{{ is_lock N \206\179 i R }}} lock i {{{ RET tt; locked \206\179 \226\136\151 R}}}.
Time Proof.
Time iIntros ( \206\166 ) "#Hlock H\206\166".
Time iL\195\182b as "IH".
Time (wp_loop; wp_bind).
Time iInv N as "[HL|>HUL]".
Time -
Time iDestruct "HL" as "(>H&?&>?)".
Time iApply (wp_cas_suc with "[$]").
Time (iIntros "!> Hl !>"; iFrame).
Time iSplitL "Hl".
Time {
Time iRight.
Time iNext.
Time iExists _.
Time iFrame.
Time eauto.
Time }
Time rewrite //=.
Time wp_ret.
Time wp_ret.
Time (iApply "H\206\166"; iFrame).
Time -
Time iDestruct "HUL" as ( v ) "(?&%)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (wp_cas_fail with "[$]") ; first 
 done).
Time (iIntros "!> Hl !>"; iFrame).
Time iSplitL "Hl".
Time {
Time iRight.
Time iNext.
Time iExists _.
Time iFrame.
Time eauto.
Time }
Time rewrite //=.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct nat_eq_dec ; first  by congruence).
Time wp_ret.
Time (iApply "IH"; eauto).
Time Qed.
Time
Lemma wp_unlock N \206\179 i (R : iProp \206\163) :
  {{{ is_lock N \206\179 i R \226\136\151 locked \206\179 \226\136\151 R }}} unlock i {{{ RET tt; True}}}.
Time Proof.
Time iIntros ( \206\166 ) "(#Hlock&Hlocked&HR) H\206\166".
Time iInv N as "[HL|>HUL]".
Time -
Time iDestruct "HL" as "(>H&?&>Htok)".
Time
(<ssreflect_plugin::ssrtclintros@0> iDestruct
 (own_valid_2 with "Htok Hlocked") as % H =>//=).
Time -
Time iDestruct "HUL" as ( v ) "(?&%)".
Time (iApply (wp_write_mem with "[$]"); iIntros "!> H !>").
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR "H\206\166" ; last  by iApply "H\206\166").
Time iLeft.
Time iFrame.
Time Qed.
Time
Lemma wp_unlock' N \206\179 i (R : iProp \206\163) :
  is_lock N \206\179 i R -\226\136\151 {{{ locked \206\179 \226\136\151 R }}} unlock i {{{ RET tt; True}}}.
Time Proof.
Time iIntros "#Hlock".
Time iAlways.
Time iIntros ( \206\166 ) "(Hlocked&HR) H\206\166".
Time iApply (wp_unlock with "[-H\206\166]").
Time {
Time iFrame "Hlock".
Time iFrame.
Time }
Time eauto.
Time Qed.
Time End lock.
Time Import spec_patterns.
Time
Definition spec_goal_extend (g : list spec_patterns.spec_pat) 
  (s : ident) :=
  match g with
  | SGoal g :: nil =>
      [SGoal
         {|
         spec_goal_kind := spec_goal_kind g;
         spec_goal_negate := spec_goal_negate g;
         spec_goal_frame := spec_goal_frame g;
         spec_goal_hyps := match spec_goal_negate g with
                           | false => s :: spec_goal_hyps g
                           | _ => spec_goal_hyps g
                           end;
         spec_goal_done := spec_goal_done g |}]
  | _ => []
  end.
Time
Ltac
 wp_write_disk :=
  try wp_bind;
   match goal with
   | |- context [ environments.envs_entails ?x ?igoal ] =>
         match igoal with
         | @wp _ _ _ _ _ _ _ (write_disk ?loc ?val) _ =>
             match goal with
             | |- context [ environments.Esnoc _ (INamed ?pts) (loc d\226\134\166 _) ]
               =>
                   match goal with
                   | |-
                     context [ environments.Esnoc _ 
                                 (INamed ?lh) (lease loc _) ] =>
                         let spat_parse := spec_patterns.spec_pat.parse "[]"
                         in
                         let spat' :=
                          eval vm_compute in
                          (spec_goal_extend spat_parse pts)
                         in
                         let spat'' :=
                          eval vm_compute in (spec_goal_extend spat' lh)
                         in
                         let ipat :=
                          constr:([intro_patterns.IModalIntro;
                                  intro_patterns.IList
                                    [[intro_patterns.IIdent (INamed pts);
                                     intro_patterns.IIdent (INamed lh)]]])
                         in
                         iApply (wp_write_disk with spat'');
                          [ iFrame | iIntros ipat ]
                   end
             end
         end
   end.
Time
Ltac
 wp_read_disk :=
  try wp_bind;
   match goal with
   | |- context [ environments.envs_entails ?x ?igoal ] =>
         match igoal with
         | @wp _ _ _ _ _ _ _ (read_disk ?loc) _ =>
             match goal with
             | |- context [ environments.Esnoc _ (INamed ?pts) (loc d\226\134\166 _) ]
               =>
                   let spat :=
                    constr:([spec_patterns.SIdent (INamed pts) nil])
                   in
                   let ipat :=
                    constr:([intro_patterns.IModalIntro;
                            intro_patterns.IIdent (INamed pts)])
                   in
                   iApply (wp_read_disk with spat); iIntros ipat
             end
         end
   end.
Time
Ltac
 wp_write_mem :=
  try wp_bind;
   match goal with
   | |- context [ environments.envs_entails ?x ?igoal ] =>
         match igoal with
         | @wp _ _ _ _ _ _ _ (write_mem ?loc ?val) _ =>
             match goal with
             | |- context [ environments.Esnoc _ (INamed ?pts) (loc m\226\134\166 _) ]
               =>
                   let spat :=
                    constr:([spec_patterns.SIdent (INamed pts) nil])
                   in
                   let ipat :=
                    constr:([intro_patterns.IModalIntro;
                            intro_patterns.IIdent (INamed pts)])
                   in
                   iApply (wp_write_mem with spat); iIntros ipat
             end
         end
   end.
Time
Ltac
 wp_read_mem :=
  try wp_bind;
   match goal with
   | |- context [ environments.envs_entails ?x ?igoal ] =>
         match igoal with
         | @wp _ _ _ _ _ _ _ (read_mem ?loc) _ =>
             match goal with
             | |- context [ environments.Esnoc _ (INamed ?pts) (loc m\226\134\166 _) ]
               =>
                   let spat :=
                    constr:([spec_patterns.SIdent (INamed pts) nil])
                   in
                   let ipat :=
                    constr:([intro_patterns.IModalIntro;
                            intro_patterns.IIdent (INamed pts)])
                   in
                   iApply (wp_read_mem with spat); iIntros ipat
             end
         end
   end.
Time
Ltac
 wp_lock H :=
  try wp_bind;
   match goal with
   | |- context [ environments.envs_entails ?x ?igoal ] =>
         match igoal with
         | @wp _ _ _ _ _ _ _ (lock ?loc) _ =>
             match goal with
             | |-
               context [ environments.Esnoc _ (INamed ?Hlock)
                           (is_lock _ _ ?loc _) ] =>
                   let spat :=
                    constr:([spec_patterns.SIdent (INamed Hlock) nil])
                   in
                   iApply (wp_lock with spat); iIntros "!>"; iIntros H
             end
         end
   end.
Time
Ltac
 wp_step := first
 [ wp_read_disk | wp_write_disk | wp_read_mem | wp_write_mem | wp_ret ].
Time
Ltac
 wp_unlock s :=
  try wp_bind;
   match goal with
   | |- context [ environments.envs_entails ?x ?igoal ] =>
         match igoal with
         | @wp _ _ _ _ _ _ _ (unlock ?loc) _ =>
             match goal with
             | |-
               context [ environments.Esnoc _ (INamed ?ilock)
                           (is_lock _ ?name loc _) ] =>
                   match goal with
                   | |-
                     context [ environments.Esnoc _ 
                                 (INamed ?ilocked) 
                                 (locked name) ] =>
                         let spat_parse := spec_patterns.spec_pat.parse s in
                         let spat' :=
                          eval vm_compute in
                          (spec_goal_extend spat_parse ilocked)
                         in
                         let spat :=
                          constr:(spec_patterns.SIdent (INamed ilock) nil
                                  :: spat')
                         in
                         let sel_frame_locked :=
                          constr:(sel_patterns.SelIdent (INamed ilocked)
                                  :: nil)
                         in
                         iApply (wp_unlock' with spat);
                          [ iFrame sel_frame_locked | iIntros "!> _" ]
                   end
             end
         end
   end.
Time
Ltac
 unify_lease :=
  match goal with
  | |- context [ environments.Esnoc _ (INamed ?auth_name) (?y d\226\134\166 ?x) ] =>
        match goal with
        | |- context [ lease y x ] => fail 1
        | |-
          context [ environments.Esnoc _ (INamed ?frag_name) (lease y ?z) ]
          =>
              let pat :=
               constr:([SIdent (INamed auth_name) nil;
                       SIdent (INamed frag_name) nil])
              in
              iDestruct (disk_lease_agree with pat) as % Hp;
               inversion_clear Hp; subst; [  ]
        end
  end.
