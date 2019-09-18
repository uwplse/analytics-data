From Array Require Export MultiAssign.
From RecoveryRefinement Require Import Lib.
Require Import Spec.HoareTactics.
Require Import Examples.Logging.Impl.
Require Import Examples.Logging.LogLayout.
Import EqualDecNotation.
Opaque plus.
Opaque lt.
Opaque D.ODLayer.
Implicit Types (d : disk) (log : list (addr * block)).
Record LogicalState :={ls_committed : bool;
                       ls_log : list (addr * block);
                       ls_disk : disk}.
Inductive LogDecode : PhysicalState -> LogicalState -> Prop :=
    log_decode :
      forall hdr (desc : Descriptor) (log_values : LogValues) 
        log commit data_region data,
      forall (Hloglen : length log = hdr.(log_length))
        (Hlogcontents : forall i,
                        i < hdr.(log_length) ->
                        index log i = Some (sel desc i, sel log_values i))
        (Hcommitted : hdr.(committed) = commit) (Hdisk : data_region = data),
      LogDecode
        {|
        p_hdr := hdr;
        p_desc := desc;
        p_log_values := log_values;
        p_data_region := data_region |}
        {| ls_committed := commit; ls_log := log; ls_disk := data |}.
#[local]Notation proc_hspec := (Hoare.proc_hspec D.ODLayer.(sem)).
#[local]Hint Resolve data_read_ok: core.
Ltac
 match_abs ::=
  match goal with
  | H:PhyDecode ?d _ |- PhyDecode ?d _ => exact H
  | H:PhyDecode ?d ?ps
    |- context [ PhyDecode ?d _ ] =>
        match goal with
        | |- exists _, _ => solve [ destruct ps; descend; eauto ]
        end
  | H:LogDecode ?d _ |- LogDecode ?d _ => exact H
  | H:PhyDecode ?d ?ps
    |- exists ps, PhyDecode ?d ps /\ _ => exists ps; split; [ exact H |  ]
  | H:LogDecode ?ps ?ls
    |- context [ LogDecode ?ps _ ] =>
        match goal with
        | |- exists _, _ => solve [ destruct ls; descend; eauto ]
        end
  end.
Lemma logd_disk ps ls : LogDecode ps ls -> ps.(p_data_region) = ls.(ls_disk).
Proof.
(inversion 1; auto).
Qed.
Hint Resolve logd_disk: core.
Lemma logd_loglen ps ls :
  LogDecode ps ls -> ps.(p_hdr).(log_length) = length ls.(ls_log).
Proof.
(inversion 1; auto).
Qed.
Lemma logd_committed ps ls :
  LogDecode ps ls -> ps.(p_hdr).(committed) = ls.(ls_committed).
Proof.
(inversion 1; auto).
Qed.
Hint Resolve logd_committed: core.
Lemma logd_log_contents ps ls :
  LogDecode ps ls ->
  forall i,
  i < ps.(p_hdr).(log_length) ->
  index ls.(ls_log) i = Some (sel ps.(p_desc) i, sel ps.(p_log_values) i).
Proof.
(inversion 1; auto).
Qed.
Lemma logd_log_value ps ls :
  LogDecode ps ls ->
  forall i,
  i < length ls.(ls_log) ->
  index ls.(ls_log) i = Some (sel ps.(p_desc) i, sel ps.(p_log_values) i).
Proof.
(intros).
(erewrite logd_log_contents; eauto).
(erewrite logd_loglen by eauto).
auto.
Qed.
Lemma logd_log_bounds ps ls :
  LogDecode ps ls -> length ls.(ls_log) <= LOG_LENGTH.
Proof.
(inversion 1; simpl).
(pose proof hdr.(log_length_ok)).
congruence.
Qed.
Theorem log_read_ok ps ls a :
  proc_hspec (log_read a)
    (fun state =>
     {|
     pre := PhyDecode state ps /\
            LogDecode ps ls /\ ls.(ls_committed) = false;
     post := fun state' r => state' = state /\ index ls.(ls_disk) a ?|= eq r;
     alternate := fun state' _ => state' = state |}).
Proof.
(unfold log_read).
(spec_impl; split_cases; simplify; finish).
(rewrite (logd_disk _) in *; auto).
Qed.
#[local]Hint Resolve log_write_ok: core.
Lemma length_descriptor (desc : Descriptor) : length desc = LOG_LENGTH.
Proof.
(destruct desc; auto).
Qed.
Hint Rewrite length_descriptor : length.
Lemma log_decode_app :
  forall (ps : PhysicalState) (ls : LogicalState) 
    (a : addr) (v : block) (s : D.ODLayer.(State)),
  PhyDecode s ps ->
  LogDecode ps ls ->
  ls.(ls_committed) = false ->
  forall pf : ps.(p_hdr).(log_length) < LOG_LENGTH,
  LogDecode
    {|
    p_hdr := hdr_inc ps.(p_hdr) pf;
    p_desc := desc_assign ps.(p_desc) ps.(p_hdr).(log_length) a;
    p_log_values := log_assign ps.(p_log_values) ps.(p_hdr).(log_length) v;
    p_data_region := ps.(p_data_region) |}
    {|
    ls_committed := false;
    ls_log := ls.(ls_log) ++ (a, v) :: nil;
    ls_disk := ls.(ls_disk) |}.
Proof.
(intros ps ls a v s Hphy Hlog Hcommit_false pf).
(pose proof (logd_log_bounds Hlog)).
(constructor; simpl; eauto).
-
(rewrite app_length; simpl).
(rewrite (logd_loglen _); auto).
-
(intros).
(pose proof (logd_log_contents Hlog (i:=i))).
(rewrite (logd_loglen _) in *).
(destruct (i == length ls.(ls_log)); subst; array).
+
(rewrite Nat.sub_diag; simpl; auto).
+
(apply H1; omega).
Qed.
Hint Resolve log_decode_app: core.
Fixpoint zip A B (l1 : list A) (l2 : list B) : list (A * B) :=
  match l1, l2 with
  | x :: xs, y :: ys => (x, y) :: zip xs ys
  | _, _ => nil
  end.
Theorem zip_index A B {defA : Default A} {defB : Default B} 
  (l1 : list A) (l2 : list B) :
  forall i,
  i < length l1 ->
  i < length l2 -> index (zip l1 l2) i = Some (sel l1 i, sel l2 i).
Proof.
generalize dependent l2.
(induction l1; simpl; intros).
omega.
(destruct l2; simpl in *; try omega).
(destruct i; simpl).
reflexivity.
(rewrite IHl1 by omega).
reflexivity.
Qed.
Theorem zip_length1 A B (l1 : list A) (l2 : list B) :
  length l1 <= length l2 -> length (zip l1 l2) = length l1.
Proof.
generalize dependent l2.
(induction l1; simpl; intros; auto).
(destruct l2; simpl in *; try omega).
(rewrite IHl1 by omega; auto).
Qed.
Lemma log_decode_some_log :
  forall (ps : PhysicalState) (ls : LogicalState) (s : D.ODLayer.(State)),
  PhyDecode s ps ->
  LogDecode ps ls ->
  ls.(ls_committed) = false ->
  forall (hdr : LogHdr) (desc : Descriptor) (log_values : LogValues),
  hdr.(committed) = ps.(p_hdr).(committed) ->
  exists log : list (addr * block),
    LogDecode
      {|
      p_hdr := hdr;
      p_desc := desc;
      p_log_values := log_values;
      p_data_region := ps.(p_data_region) |}
      {| ls_committed := false; ls_log := log; ls_disk := ls.(ls_disk) |}.
Proof.
(intros ps ls s Hphy Hlog Hcommit_false hdr desc log_values Hcommit).
exists (firstn hdr.(log_length) (zip desc log_values)).
(constructor; eauto).
-
(rewrite firstn_length).
(rewrite zip_length1; autorewrite with length; auto).
(rewrite Nat.min_l; auto).
(apply hdr.(log_length_ok)).
-
(intros).
(rewrite index_firstn by auto).
(pose proof hdr.(log_length_ok)).
(erewrite zip_index; eauto; autorewrite with length; try omega).
Qed.
Hint Resolve log_decode_some_log: core.
Theorem log_write_ok ps ls a v :
  proc_hspec (log_write a v)
    (fun state =>
     {|
     pre := PhyDecode state ps /\
            LogDecode ps ls /\ ls.(ls_committed) = false;
     post := fun state' r =>
             match r with
             | TxnD.WriteOK =>
                 exists ps',
                   PhyDecode state' ps' /\
                   LogDecode ps'
                     {|
                     ls_committed := false;
                     ls_log := ls.(ls_log) ++ (a, v) :: nil;
                     ls_disk := ls.(ls_disk) |}
             | TxnD.WriteErr =>
                 exists ps', PhyDecode state' ps' /\ LogDecode ps' ls
             end;
     alternate := fun state' _ =>
                  exists ps',
                    PhyDecode state' ps' /\
                    (exists log,
                       LogDecode ps'
                         {|
                         ls_committed := false;
                         ls_log := log;
                         ls_disk := ls.(ls_disk) |}) |}).
Proof.
(spec_impl; split_cases; simplify; finish).
(destruct v0; simplify; finish).
Qed.
Lemma log_decode_apply_one :
  forall (len : nat) (ps : PhysicalState) (ls : LogicalState) 
    (i : nat) (state : D.ODLayer.(State)),
  PhyDecode state ps ->
  LogDecode ps ls ->
  i + S len = length ls.(ls_log) ->
  ls.(ls_committed) = true ->
  LogDecode
    {|
    p_hdr := ps.(p_hdr);
    p_desc := ps.(p_desc);
    p_log_values := ps.(p_log_values);
    p_data_region := assign ps.(p_data_region) (sel ps.(p_desc) i)
                       (sel ps.(p_log_values) i) |}
    {|
    ls_committed := true;
    ls_log := ls.(ls_log);
    ls_disk := assign ps.(p_data_region) (sel ps.(p_desc) i)
                 (sel ps.(p_log_values) i) |}.
Proof.
(intros len ps ls i state Hphy Hlog H H0).
(constructor; try erewrite logd_loglen by eauto;
  try erewrite logd_committed by eauto; intros; array).
(erewrite logd_log_value by eauto; auto).
Qed.
Hint Resolve log_decode_apply_one: core.
Theorem log_apply_one_more :
  forall d log i a v len,
  index log i = Some (a, v) ->
  i + 1 + len = length log ->
  massign (subslice log (i + 1) len) (assign d a v) =
  massign (subslice log i (S len)) d.
Proof.
(intros).
replace (i + 1) with S i in * by omega.
(erewrite subslice_one_more; eauto; try omega).
(simpl; auto).
Qed.
Theorem log_apply_reapply_one :
  forall log i d a v,
  index log i = Some (a, v) -> massign log d = massign log (assign d a v).
Proof.
(induction log; simpl; intros).
-
congruence.
-
(destruct a as [a v']).
(destruct i; simpl).
(inv_clear H).
array.
(destruct (a == a0); subst; array).
(erewrite IHlog; eauto).
(rewrite assign_assign_ne by auto; auto).
Qed.
Hint Resolve logd_log_value: core.
Hint Extern 3 (_ < _) => omega: core.
Hint Extern 3 (_ <= _) => omega: core.
Hint Extern 3 (@eq nat _ _) => omega: core.
Definition applied_after log i d0 :=
  massign (subslice log i (length log - i)) d0.
Definition fully_applied log d0 := massign log d0.
Section ApplyAtRespec.
Hint Resolve apply_at_ok: core.
Theorem log_apply_at_ok ps ls d0 desc i :
  proc_hspec (apply_at desc i)
    (fun state =>
     {|
     pre := PhyDecode state ps /\
            LogDecode ps ls /\
            desc = ps.(p_desc) /\
            i < length ls.(ls_log) /\
            ls.(ls_committed) = true /\
            applied_after ls.(ls_log) i ls.(ls_disk) =
            fully_applied ls.(ls_log) d0 /\
            fully_applied ls.(ls_log) ls.(ls_disk) =
            fully_applied ls.(ls_log) d0;
     post := fun state' r =>
             r = tt /\
             (exists ps',
                PhyDecode state' ps' /\
                ps'.(p_desc) = desc /\
                (exists a v,
                   index ls.(ls_log) i = Some (a, v) /\
                   LogDecode ps'
                     {|
                     ls_committed := true;
                     ls_log := ls.(ls_log);
                     ls_disk := assign ls.(ls_disk) a v |}));
     alternate := fun state' _ =>
                  exists ps',
                    PhyDecode state' ps' /\
                    ps'.(p_desc) = desc /\
                    (exists disk,
                       (disk = ls.(ls_disk) \/
                        (exists a v,
                           index ls.(ls_log) i = Some (a, v) /\
                           disk = assign ls.(ls_disk) a v)) /\
                       LogDecode ps'
                         {|
                         ls_committed := true;
                         ls_log := ls.(ls_log);
                         ls_disk := disk |}) |}).
Proof.
(spec_impl; split_cases; simplify; finish).
(pose proof (logd_log_bounds _)).
omega.
-
(destruct (index_dec ls.(ls_log) i); propositional; try omega).
(destruct (sel ls.(ls_log) i) as [a v]).
(descend; intuition eauto).
(erewrite logd_log_value in * by eauto; eauto).
(inv_clear H7).
(erewrite logd_disk in * by eauto).
(destruct H0; econstructor; simpl in *; eauto).
-
(exists ls.(ls_disk); intuition eauto).
(destruct ps, ls; simpl in *; congruence).
-
(eexists; split).
(right; eauto).
(erewrite logd_disk in * by eauto).
(destruct H0; econstructor; simpl in *; eauto).
Qed.
End ApplyAtRespec.
Hint Resolve log_apply_at_ok: core.
Theorem apply_upto_ok ps ls d0 desc len i :
  proc_hspec (apply_upto desc i len)
    (fun state =>
     {|
     pre := PhyDecode state ps /\
            LogDecode ps ls /\
            desc = ps.(p_desc) /\
            i + len = length ls.(ls_log) /\
            ls.(ls_committed) = true /\
            massign (subslice ls.(ls_log) i len) ls.(ls_disk) =
            massign ls.(ls_log) d0 /\
            massign ls.(ls_log) ls.(ls_disk) = massign ls.(ls_log) d0;
     post := fun state' r =>
             r = tt /\
             (exists ps',
                PhyDecode state' ps' /\
                LogDecode ps'
                  {|
                  ls_committed := true;
                  ls_log := ls.(ls_log);
                  ls_disk := massign ls.(ls_log) d0 |});
     alternate := fun state' _ =>
                  exists ps',
                    PhyDecode state' ps' /\
                    ps'.(p_desc) = desc /\
                    (exists disk,
                       LogDecode ps'
                         {|
                         ls_committed := true;
                         ls_log := ls.(ls_log);
                         ls_disk := disk |} /\
                       massign ls.(ls_log) disk = massign ls.(ls_log) d0) |}).
Proof.
gen ps ls d0 desc i.
(induction len; simpl; intros).
-
(step; split_cases; simplify; finish).
(destruct ls; simpl in *; congruence).
exists ls.(ls_disk).
intuition eauto.
(destruct ls; simpl in *; congruence).
-
(step; split_cases; simplify; finish).
(unfold applied_after, fully_applied).
replace (length ls.(ls_log) - i) with S len by omega.
auto.
(spec_intros; simplify).
(lazymatch goal with
 | H:PhyDecode _ ?ps'
   |- _ =>
       eapply proc_hspec_impl;
        [ unfold spec_impl
        | apply
           (IHlen ps'
              {|
              ls_committed := true;
              ls_log := ls.(ls_log);
              ls_disk := ps'.(p_data_region) |}) ]
 end; simpl; split_cases; simplify; try erewrite logd_disk in * by eauto;
  finish; simpl in *).
{
(fold addr block in *).
(rewrite log_apply_one_more; eauto).
(fold addr block in *).
(rewrite H4).
(rewrite <- H5).
(erewrite <- log_apply_reapply_one by eauto; auto).
}
{
(erewrite <- log_apply_reapply_one in * by eauto).
congruence.
}
{
(eexists; intuition eauto).
replace (massign ls.(ls_log) disk).
(erewrite <- log_apply_reapply_one by eauto; auto).
}
{
(eexists; intuition eauto).
(erewrite <- log_apply_reapply_one by eauto; auto).
}
Qed.
#[local]Hint Resolve gethdr_ok: core.
#[local]Hint Resolve getdesc_ok: core.
#[local]Hint Resolve apply_upto_ok: core.
#[local]Hint Resolve writehdr_ok: core.
Lemma LogDecode_clear_hdr :
  forall desc log_values data_region d',
  data_region = d' ->
  LogDecode
    {|
    p_hdr := empty_hdr;
    p_desc := desc;
    p_log_values := log_values;
    p_data_region := data_region |}
    {| ls_committed := false; ls_log := nil; ls_disk := d' |}.
Proof.
(intros; subst).
(constructor; simpl; intros; array).
omega.
Qed.
Hint Resolve LogDecode_clear_hdr: core.
Definition log_apply_spec ps ls d0 is_commit :
  Specification unit unit disk :=
  fun state =>
  {|
  pre := PhyDecode state ps /\
         LogDecode ps ls /\
         massign ls.(ls_log) ls.(ls_disk) = massign ls.(ls_log) d0 /\
         ls.(ls_committed) = is_commit;
  post := fun state' r =>
          exists ps',
            PhyDecode state' ps' /\
            (if is_commit
             then
              LogDecode ps'
                {|
                ls_committed := false;
                ls_log := nil;
                ls_disk := massign ls.(ls_log) d0 |}
             else
              LogDecode ps'
                {|
                ls_committed := false;
                ls_log := nil;
                ls_disk := ls.(ls_disk) |});
  alternate := fun state' _ =>
               exists ps',
                 PhyDecode state' ps' /\
                 match is_commit with
                 | true =>
                     (exists disk,
                        LogDecode ps'
                          {|
                          ls_committed := true;
                          ls_log := ls.(ls_log);
                          ls_disk := disk |} /\
                        massign ls.(ls_log) disk = massign ls.(ls_log) d0) \/
                     LogDecode ps'
                       {|
                       ls_committed := false;
                       ls_log := nil;
                       ls_disk := massign ls.(ls_log) d0 |}
                 | false =>
                     exists log,
                       LogDecode ps'
                         {|
                         ls_committed := false;
                         ls_log := log;
                         ls_disk := ls.(ls_disk) |}
                 end |}.
Theorem log_apply_ok ps ls is_commit :
  proc_hspec log_apply (log_apply_spec ps ls ls.(ls_disk) is_commit).
Proof.
(unfold log_apply, log_apply_spec).
(step; split_cases; simplify; finish).
destruct_with_eqn r.(committed).
(step; split_cases; simplify; finish; erewrite logd_committed in * by eauto;
  repeat simpl_match).
(step; split_cases; simplify; finish).
(erewrite logd_loglen by eauto; omega).
(rewrite subslice_whole; eauto).
(erewrite logd_loglen by eauto; omega).
(spec_intros; simplify).
(spec_impl; split_cases; simplify; finish).
(erewrite logd_disk in * by eauto; simpl in *; auto).
left.
(eexists; intuition eauto).
(rewrite massign_idempotent; auto).
right.
(erewrite logd_disk in * by eauto; simpl in *; auto).
left.
(exists ls.(ls_disk); intuition eauto).
(destruct ls; simpl in *; congruence).
monad_simpl.
(spec_impl; split_cases; simplify; finish;
  erewrite logd_committed in * by eauto; repeat simpl_match; eauto).
exists ls.(ls_log).
(destruct ls; simpl in *; congruence).
(destruct_with_eqn ls.(ls_committed); eauto).
left.
(exists ls.(ls_disk); intuition eauto).
(destruct ls; simpl in *; congruence).
exists ls.(ls_log).
(destruct ls; simpl in *; congruence).
Qed.
Theorem recovery_ok ps ls is_commit :
  proc_hspec recovery (log_apply_spec ps ls ls.(ls_disk) is_commit).
Proof.
(unfold recovery).
(apply log_apply_ok).
Qed.
Inductive Recghost (restrict : LogicalState -> Prop) :=
    recghost :
      forall (ps : PhysicalState) (ls : LogicalState) (pf : restrict ls), _.
Arguments recghost {restrict}.
Theorem log_apply_spec_idempotent :
  idempotent
    (fun '(ps, ls) => log_apply_spec ps ls ls.(ls_disk) ls.(ls_committed)).
Proof.
(unfold idempotent; intuition eauto; simplify).
(simpl in H0; propositional).
(destruct_with_eqn b.(ls_committed); split_cases;
  match goal with
  | H:PhyDecode state' ?ps', H':LogDecode ?ps' ?ls' |- _ => exists (ps', ls')
  end; simpl in *; repeat simpl_match; simplify; finish).
Qed.
Theorem log_apply_spec_idempotent' ls0 :
  idempotent
    (fun
       a : Recghost
             (fun ls =>
              if ls.(ls_committed)
              then
               massign ls.(ls_log) ls.(ls_disk) =
               massign ls0.(ls_log) ls0.(ls_disk)
              else
               ls.(ls_disk) = ls0.(ls_disk) \/
               ls.(ls_disk) = massign ls0.(ls_log) ls0.(ls_disk)) =>
     let
     'recghost ps ls _ := a in
      log_apply_spec ps ls ls.(ls_disk) ls.(ls_committed)).
Proof.
(unfold idempotent; intuition eauto; simplify).
(destruct a).
(simpl in *; propositional).
(destruct_with_eqn ls.(ls_committed); split_cases;
  lazymatch goal with
  | H:PhyDecode state' ?ps', H':LogDecode ?ps' ?ls'
    |- _ => unshelve eexists (recghost ps' ls' _)
  end; simpl; simplify; finish).
Qed.
Theorem log_apply_spec_idempotent_notxn' ls0 :
  idempotent
    (fun a : Recghost (fun ls => ls.(ls_disk) = ls0.(ls_disk)) =>
     let 'recghost ps ls _ := a in log_apply_spec ps ls ls.(ls_disk) false).
Proof.
(unfold idempotent; intuition eauto; simplify).
(destruct a).
(simpl in H0; propositional).
(destruct_with_eqn ls.(ls_committed); split_cases;
  match goal with
  | H:PhyDecode _ ?ps, H':LogDecode ?ps ?ls
    |- _ => unshelve eexists (recghost ps ls _)
  end; simpl in *; repeat simpl_match; simplify; finish).
Qed.
#[local]Hint Resolve phy_log_size_ok: core.
Theorem log_size_ok ps ls :
  proc_hspec log_size
    (fun state =>
     {|
     pre := PhyDecode state ps /\
            LogDecode ps ls /\ ls.(ls_committed) = false;
     post := fun state' r => r = length ls.(ls_disk) /\ state' = state;
     alternate := fun state' _ => state' = state |}).
Proof.
(spec_impl; split_cases; simplify).
(erewrite logd_disk by eauto; auto).
Qed.
#[local]Hint Resolve phy_log_init_ok: core.
Theorem log_init_ok :
  proc_hspec log_init
    (fun state =>
     {|
     pre := True;
     post := fun state' r =>
             match r with
             | Initialized =>
                 exists ps ls,
                   PhyDecode state' ps /\
                   LogDecode ps ls /\
                   ls.(ls_committed) = false /\ ls.(ls_log) = nil
             | InitFailed => True
             end;
     alternate := fun state' _ => True |}).
Proof.
(spec_impl; simplify).
(destruct v; simplify; finish).
(exists ps,
   {| ls_committed := false; ls_log := nil; ls_disk := ps.(p_data_region) |};
  simpl; intuition eauto).
(destruct ps; simpl in *).
(constructor; intros; array; eauto).
omega.
Qed.
Hint Resolve log_apply_ok: core.
Lemma LogDecode_setcommit :
  forall (ps : PhysicalState) (ls : LogicalState),
  LogDecode ps ls ->
  LogDecode
    {|
    p_hdr := hdr_setcommit ps.(p_hdr);
    p_desc := ps.(p_desc);
    p_log_values := ps.(p_log_values);
    p_data_region := ps.(p_data_region) |}
    {|
    ls_committed := true;
    ls_log := ls.(ls_log);
    ls_disk := ls.(ls_disk) |}.
Proof.
(intros ps ls H0).
(destruct H0; constructor; simpl; propositional; array).
Qed.
Hint Resolve LogDecode_setcommit: core.
Theorem log_commit_ok ps ls :
  proc_hspec commit
    (fun state =>
     {|
     pre := PhyDecode state ps /\
            LogDecode ps ls /\ ls.(ls_committed) = false;
     post := fun state' r =>
             exists ps' ls',
               PhyDecode state' ps' /\
               LogDecode ps' ls' /\
               ls'.(ls_committed) = false /\
               ls'.(ls_log) = nil /\
               ls'.(ls_disk) = massign ls.(ls_log) ls.(ls_disk);
     alternate := fun state' _ =>
                  exists ps',
                    PhyDecode state' ps' /\
                    (((exists disk,
                         LogDecode ps'
                           {|
                           ls_committed := true;
                           ls_log := ls.(ls_log);
                           ls_disk := disk |} /\
                         massign ls.(ls_log) disk =
                         massign ls.(ls_log) ls.(ls_disk)) \/
                      LogDecode ps'
                        {|
                        ls_committed := false;
                        ls_log := nil;
                        ls_disk := massign ls.(ls_log) ls.(ls_disk) |}) \/
                     (exists log,
                        LogDecode ps'
                          {|
                          ls_committed := false;
                          ls_log := log;
                          ls_disk := ls.(ls_disk) |})) |}).
Proof.
(step; split_cases; simplify; finish).
(step; split_cases; simplify; finish).
(spec_impl; simpl; split_cases; simplify; finish).
(simpl in *).
(descend; intuition eauto).
-
right.
exists ls.(ls_log).
(destruct ls; simpl in *; congruence).
-
(left; left; eauto).
-
right.
exists ls.(ls_log).
(destruct ls; simpl in *; congruence).
Qed.
