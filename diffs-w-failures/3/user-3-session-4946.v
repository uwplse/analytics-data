Time From Transitions Require Import Relations Rewriting.
Time Require Import Spec.Proc.
Time Require Import Spec.ProcTheorems.
Time Require Import Spec.Layer.
Time From iris.base_logic.lib Require Export fancy_updates.
Time From iris.proofmode Require Import base tactics classes.
Time Set Default Proof Using "Type".
Time Unset Implicit Arguments.
Time Import uPred.
Time
Definition reducible {OpT} {T} {\206\155} (e : proc OpT T) 
  (\207\131 : State \206\155) := \226\136\131 e' \207\131' efs, exec_step \206\155.(sem) e \207\131 (Val \207\131' (e', efs)).
Time
Definition non_errorable {OpT} {T} {\206\155} (e : proc OpT T) 
  (\207\131 : State \206\155) := \194\172 exec_step \206\155.(sem) e \207\131 Err.
Time
Definition to_val {OpT} {T} (e : proc OpT T) : option T :=
  match e in (proc _ T0) return (option T0) with
  | @Ret _ T0 v => Some v
  | @Call _ T0 _ | @Bind _ T0 _ _ _ | @Loop _ T0 _ _ _ => None
  | @Unregister _ => None
  | @Wait _ => None
  | @Spawn _ _ _ => None
  end.
Time Definition of_val {OpT} {T} (v : T) : proc OpT T := Ret v.
Time Lemma to_of_val {OpT} {T} (v : T) : to_val (@of_val OpT _ v) = Some v.
Time Proof.
Time auto.
Time Qed.
Time
Lemma of_to_val {OpT} {T} (e : proc OpT T) (v : T) :
  to_val e = Some v \226\134\146 of_val v = e.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> destruct e =>//=).
Time rewrite /of_val //=.
Time congruence.
Time Qed.
Time
Lemma val_non_errorable {OpT} {T} {\206\155} (e : proc OpT T) 
  \207\131 v : to_val e = Some v \226\134\146 @non_errorable _ _ \206\155 e \207\131.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> destruct e =>//= _ Hexec).
Time (inversion Hexec).
Time Qed.
Time
Class IntoVal {OpT} {T} (e : proc OpT T) (v : T) :=
    into_val : of_val v = e.
Time
Definition irreducible {OpT} {T} {\206\155} (e : proc OpT T) 
  (\207\131 : State \206\155) := is_Some (to_val e) \226\136\168 exec_step \206\155.(sem) e \207\131 Err.
Time Inductive atomicity :=
       | StronglyAtomic : _
       | WeaklyAtomic : _.
Time
Class Atomic {OpT} {T} \206\155 (a : atomicity) (e : proc OpT T) : Prop :=
    atomic :
      forall \207\131 e' \207\131' efs,
      exec_step \206\155.(sem) e \207\131 (Val \207\131' (e', efs))
      \226\134\146 match a with
        | WeaklyAtomic => irreducible e' \207\131'
        | _ => is_Some (to_val e')
        end.
Time Inductive stuckness :=
       | NotStuck : _
       | MaybeStuck : _.
Time
Definition stuckness_leb (s1 s2 : stuckness) : bool :=
  match s1, s2 with
  | MaybeStuck, NotStuck => false
  | _, _ => true
  end.
Time Instance stuckness_le : (SqSubsetEq stuckness) := stuckness_leb.
Time Instance stuckness_le_po : (PreOrder stuckness_le).
Time Proof.
Time (split; by repeat intros []).
Time Qed.
Time
Definition stuckness_to_atomicity (s : stuckness) : atomicity :=
  match s with
  | MaybeStuck => StronglyAtomic
  | _ => WeaklyAtomic
  end.
Time
Class LanguageCtx {OpT : Type \226\134\146 Type} {T1} {T2} \206\155
(K : proc OpT T1 \226\134\146 proc OpT T2) :={fill_not_val :
                                    forall e : proc OpT T1,
                                    to_val e = None \226\134\146 to_val (K e) = None;
                                   fill_step_valid :
                                    forall e1 \207\1311 e2 \207\1312 efs,
                                    exec_step \206\155.(sem) e1 \207\1311
                                      (Val \207\1312 (e2, efs))
                                    \226\134\146 exec_step \206\155.(sem) 
                                        (K e1) \207\1311 
                                        (Val \207\1312 (K e2, efs));
                                   fill_step_err :
                                    forall e1 \207\1311,
                                    exec_step \206\155.(sem) e1 \207\1311 Err
                                    \226\134\146 exec_step \206\155.(sem) (K e1) \207\1311 Err;
                                   fill_step_inv_valid :
                                    forall e1' \207\1311 e2 \207\1312 efs,
                                    to_val e1' = None
                                    \226\134\146 exec_step \206\155.(sem) 
                                        (K e1') \207\1311 
                                        (Val \207\1312 (e2, efs))
                                      \226\134\146 \226\136\131 e2',
                                          e2 = K e2'
                                          \226\136\167 exec_step 
                                              \206\155.(sem) e1' \207\1311
                                              (Val \207\1312 (e2', efs));
                                   fill_step_inv_err :
                                    forall e1' \207\1311,
                                    to_val e1' = None
                                    \226\134\146 exec_step \206\155.(sem) (K e1') \207\1311 Err
                                      \226\134\146 exec_step \206\155.(sem) e1' \207\1311 Err}.
Time
Lemma reducible_fill {OpT} {T1} {T2} K `{LanguageCtx OpT T1 T2 \206\155 K} 
  e (\207\131 : State \206\155) : to_val e = None \226\134\146 reducible (K e) \207\131 \226\134\146 reducible e \207\131.
Time Proof.
Time (intros ? (e', (\207\131', (efs, Hstep))); unfold reducible).
Time (apply fill_step_inv_valid in Hstep as (e2', (_, Hstep)); eauto).
Time Qed.
Time
Lemma non_errorable_fill_inv {OpT} {T1} {T2} K `{LanguageCtx OpT T1 T2 \206\155 K} 
  e (\207\131 : State \206\155) :
  to_val e = None \226\134\146 non_errorable (K e) \207\131 \226\134\146 non_errorable e \207\131.
Time Proof.
Time (intros ? Hnon Hstep; unfold non_errorable).
Time (eapply Hnon).
Time (apply fill_step_err; eauto).
Time Qed.
Time
Lemma non_errorable_fill {OpT} {T1} {T2} K `{LanguageCtx OpT T1 T2 \206\155 K} 
  e (\207\131 : State \206\155) :
  to_val e = None \226\134\146 non_errorable e \207\131 \226\134\146 non_errorable (K e) \207\131.
Time Proof.
Time (intros ? Hnon Hstep; unfold non_errorable).
Time (eapply Hnon).
Time (apply fill_step_inv_err; eauto).
Time Qed.
Time
Class irisG' (OpT : Type -> Type) (\206\155state : Type) (\206\163 : gFunctors) :=
 IrisG {iris_invG :> invG \206\163; state_interp : \206\155state \226\134\146 iProp \206\163}.
Time Notation irisG OpT \206\155 \206\163:= (irisG' OpT (State \206\155) \206\163).
Time #[global]Opaque iris_invG.
Time
Definition wp_pre {OpT} `{\206\155 : Layer OpT} `{irisG OpT \206\155 \206\163} 
  (s : stuckness)
  (wp : discrete_funO
          (\206\187 T, coPset -d> proc OpT T -d> (T -d> iProp \206\163) -d> iProp \206\163)) :
  discrete_funO (\206\187 T, coPset -d> proc OpT T -d> (T -d> iProp \206\163) -d> iProp \206\163) :=
  \206\187 T E e1 \206\166,
    match to_val e1 with
    | Some v => |={E}=> \206\166 v
    | None =>
        \226\136\128 \207\1311,
          state_interp \207\1311
          ={E,\226\136\133}=\226\136\151 \226\140\156match s with
                    | NotStuck => non_errorable e1 \207\1311
                    | _ => True
                    end\226\140\157
                   \226\136\151 (\226\136\128 e2 \207\1312 efs,
                        \226\140\156exec_step \206\155.(sem) e1 \207\1311 (Val \207\1312 (e2, efs))\226\140\157
                        ={\226\136\133,\226\136\133,E}\226\150\183=\226\136\151 state_interp \207\1312
                                    \226\136\151 wp T E e2 \206\166
                                      \226\136\151 ([\226\136\151 list] ef \226\136\136 efs, 
                                         wp (projT1 ef) \226\138\164 
                                           (projT2 ef) 
                                           (\206\187 _, True)))
    end%I.
Time #[local]
Instance wp_pre_contractive  `{irisG OpT \206\155 \206\163} s:
 (Contractive (@wp_pre _ _ _ _ s)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /wp_pre =>n wp wp' Hwp T E e1 \206\166).
Time (repeat f_contractive || f_equiv; apply Hwp).
Time Qed.
Time
Definition wp_def `{irisG OpT \206\155 \206\163} (s : stuckness) :
  forall T, coPset \226\134\146 proc OpT T \226\134\146 (T \226\134\146 iProp \206\163) \226\134\146 iProp \206\163 :=
  fixpoint (@wp_pre _ _ _ _ s).
Time Definition wp_aux `{irisG OpT \206\155 \206\163} : seal (@wp_def OpT \206\155 \206\163 _).
Time by eexists.
Time Qed.
Time Definition wp `{irisG OpT \206\155 \206\163} := unseal (@wp_aux OpT \206\155 \206\163 _).
Time
Definition wp_eq {OpT} `{irisG OpT \206\155 \206\163} : wp = @wp_def OpT \206\155 \206\163 _ :=
  wp_aux.(seal_eq).
Time Arguments wp {_} {_} {_} {_} _ {_} _ _.
Time Instance: (Params (@wp) 8) := _.
Time
Notation "'WP' e @ s ; E {{ \206\166 } }" := (wp s E e \206\166)
  (at level 20, e, \206\166  at level 200,
   format "'[' 'WP'  e  '/' @  s ;  E  {{  \206\166  } } ']'") : bi_scope.
Time
Notation "'WP' e @ E {{ \206\166 } }" := (wp NotStuck E e \206\166)
  (at level 20, e, \206\166  at level 200,
   format "'[' 'WP'  e  '/' @  E  {{  \206\166  } } ']'") : bi_scope.
Time
Notation "'WP' e @ E ? {{ \206\166 } }" := (wp MaybeStuck E e \206\166)
  (at level 20, e, \206\166  at level 200,
   format "'[' 'WP'  e  '/' @  E  ? {{  \206\166  } } ']'") : bi_scope.
Time
Notation "'WP' e {{ \206\166 } }" := (wp NotStuck \226\138\164 e \206\166)
  (at level 20, e, \206\166  at level 200, format "'[' 'WP'  e  '/' {{  \206\166  } } ']'") :
  bi_scope.
Time
Notation "'WP' e ? {{ \206\166 } }" := (wp MaybeStuck \226\138\164 e \206\166)
  (at level 20, e, \206\166  at level 200,
   format "'[' 'WP'  e  '/' ? {{  \206\166  } } ']'") : bi_scope.
Time
Notation "'WP' e @ s ; E {{ v , Q } }" := (wp s E e (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' @  s ;  E  {{  v ,  Q  } } ']'") : bi_scope.
Time
Notation "'WP' e @ E {{ v , Q } }" := (wp NotStuck E e (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' @  E  {{  v ,  Q  } } ']'") : bi_scope.
Time
Notation "'WP' e @ E ? {{ v , Q } }" := (wp MaybeStuck E e (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' @  E  ? {{  v ,  Q  } } ']'") : bi_scope.
Time
Notation "'WP' e {{ v , Q } }" := (wp NotStuck \226\138\164 e (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' {{  v ,  Q  } } ']'") : bi_scope.
Time
Notation "'WP' e ? {{ v , Q } }" := (wp MaybeStuck \226\138\164 e (\206\187 v, Q))
  (at level 20, e, Q  at level 200,
   format "'[' 'WP'  e  '/' ? {{  v ,  Q  } } ']'") : bi_scope.
Time
Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat) ..) -\226\136\151 WP e @ s; E {{ \206\166 }}))%I
  (at level 20, x closed binder, y closed binder,
   format "{{{  P  } } }  e  @  s ;  E  {{{  x .. y ,  RET  pat ;  Q } } }") :
  bi_scope.
Time
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat) ..) -\226\136\151 WP e @ E {{ \206\166 }}))%I
  (at level 20, x closed binder, y closed binder,
   format "{{{  P  } } }  e  @  E  {{{  x .. y ,  RET  pat ;  Q } } }") :
  bi_scope.
Time
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat) ..) -\226\136\151 WP e @ E ?{{ \206\166 }}))%I
  (at level 20, x closed binder, y closed binder,
   format "{{{  P  } } }  e  @  E  ? {{{  x .. y ,  RET  pat ;  Q } } }") :
  bi_scope.
Time
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat) ..) -\226\136\151 WP e {{ \206\166 }}))%I
  (at level 20, x closed binder, y closed binder,
   format "{{{  P  } } }  e  {{{  x .. y ,   RET  pat ;  Q } } }") : bi_scope.
Time
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat) ..) -\226\136\151 WP e ?{{ \206\166 }}))%I
  (at level 20, x closed binder, y closed binder,
   format "{{{  P  } } }  e  ? {{{  x .. y ,   RET  pat ;  Q } } }") :
  bi_scope.
Time
Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat) -\226\136\151 WP e @ s; E {{ \206\166 }}))%I
  (at level 20,
   format "{{{  P  } } }  e  @  s ;  E  {{{  RET  pat ;  Q } } }") : bi_scope.
Time
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat) -\226\136\151 WP e @ E {{ \206\166 }}))%I
  (at level 20, format "{{{  P  } } }  e  @  E  {{{  RET  pat ;  Q } } }") :
  bi_scope.
Time
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat) -\226\136\151 WP e @ E ?{{ \206\166 }}))%I
  (at level 20, format "{{{  P  } } }  e  @  E  ? {{{  RET  pat ;  Q } } }") :
  bi_scope.
Time
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat) -\226\136\151 WP e {{ \206\166 }}))%I
  (at level 20, format "{{{  P  } } }  e  {{{  RET  pat ;  Q } } }") :
  bi_scope.
Time
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (\226\150\161 (\226\136\128 \206\166, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat) -\226\136\151 WP e ?{{ \206\166 }}))%I
  (at level 20, format "{{{  P  } } }  e  ? {{{  RET  pat ;  Q } } }") :
  bi_scope.
Time
Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166 : _ \226\134\146 uPred _,
     P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat) ..) -\226\136\151 WP e @ s; E {{ \206\166 }})
  (at level 20, x closed binder, y closed binder,
   format "{{{  P  } } }  e  @  s ;  E  {{{  x .. y ,  RET  pat ;  Q } } }") :
  stdpp_scope.
Time
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166 : _ \226\134\146 uPred _,
     P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat) ..) -\226\136\151 WP e @ E {{ \206\166 }})
  (at level 20, x closed binder, y closed binder,
   format "{{{  P  } } }  e  @  E  {{{  x .. y ,  RET  pat ;  Q } } }") :
  stdpp_scope.
Time
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166 : _ \226\134\146 uPred _,
     P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat) ..) -\226\136\151 WP e @ E ?{{ \206\166 }})
  (at level 20, x closed binder, y closed binder,
   format "{{{  P  } } }  e  @  E  ? {{{  x .. y ,  RET  pat ;  Q } } }") :
  stdpp_scope.
Time
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166 : _ \226\134\146 uPred _, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat) ..) -\226\136\151 WP e {{ \206\166 }})
  (at level 20, x closed binder, y closed binder,
   format "{{{  P  } } }  e  {{{  x .. y ,  RET  pat ;  Q } } }") :
  stdpp_scope.
Time
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166 : _ \226\134\146 uPred _, P -\226\136\151 \226\150\183 (\226\136\128 x, .. (\226\136\128 y, Q -\226\136\151 \206\166 pat) ..) -\226\136\151 WP e ?{{ \206\166 }})
  (at level 20, x closed binder, y closed binder,
   format "{{{  P  } } }  e  ? {{{  x .. y ,  RET  pat ;  Q } } }") :
  stdpp_scope.
Time
Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166 : _ \226\134\146 uPred _, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat) -\226\136\151 WP e @ s; E {{ \206\166 }})
  (at level 20,
   format "{{{  P  } } }  e  @  s ;  E  {{{  RET  pat ;  Q } } }") :
  stdpp_scope.
Time
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166 : _ \226\134\146 uPred _, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat) -\226\136\151 WP e @ E {{ \206\166 }})
  (at level 20, format "{{{  P  } } }  e  @  E  {{{  RET  pat ;  Q } } }") :
  stdpp_scope.
Time
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166 : _ \226\134\146 uPred _, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat) -\226\136\151 WP e @ E ?{{ \206\166 }})
  (at level 20, format "{{{  P  } } }  e  @  E  ? {{{  RET  pat ;  Q } } }") :
  stdpp_scope.
Time
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166 : _ \226\134\146 uPred _, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat) -\226\136\151 WP e {{ \206\166 }})
  (at level 20, format "{{{  P  } } }  e  {{{  RET  pat ;  Q } } }") :
  stdpp_scope.
Time
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (\226\136\128 \206\166 : _ \226\134\146 uPred _, P -\226\136\151 \226\150\183 (Q -\226\136\151 \206\166 pat) -\226\136\151 WP e ?{{ \206\166 }})
  (at level 20, format "{{{  P  } } }  e  ? {{{  RET  pat ;  Q } } }") :
  stdpp_scope.
Time Section wp.
Time Context {OpT : Type -> Type}.
Time Context `{\206\155 : Layer OpT} `{irisG OpT \206\155 \206\163}.
Time Implicit Type s : stuckness.
Time Implicit Type P : iProp \206\163.
Time
Lemma wp_unfold {T} s E (e : proc OpT T) \206\166 :
  WP e @ s; E {{ \206\166 }} \226\138\163\226\138\162 @wp_pre _ _ _ _ s (@wp _ _ _ _ s) T E e \206\166.
Time Proof.
Time rewrite wp_eq /wp_def.
Time (apply (fixpoint_unfold (wp_pre s))).
Time Qed.
Time #[global]
Instance wp_ne  {T} s E (e : proc OpT T) n:
 (Proper (pointwise_relation _ (dist n) ==> dist n) (wp s E e)).
Time Proof.
Time revert e.
Time
(<ssreflect_plugin::ssrtclintros@0> induction (lt_wf n) as [n _ IH] =>e \206\166 \206\168
 H\206\166).
Time rewrite !wp_unfold /wp_pre.
Time (do 18 f_contractive || f_equiv).
Time (<ssreflect_plugin::ssrtclseq@0> apply IH ; first  lia).
Time (intros v).
Time (eapply dist_le; eauto with lia).
Time Qed.
Time #[global]
Instance wp_proper  {T} s E (e : proc OpT T):
 (Proper (pointwise_relation _ (\226\137\161) ==> (\226\137\161)) (wp s E e)).
Time Proof.
Time
by
 intros \206\166 \206\166' ?; <ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n;
  <ssreflect_plugin::ssrtclintros@0> apply wp_ne =>v; 
  apply equiv_dist.
Time Qed.
Time Lemma wp_value' {T} s E \206\166 (v : T) : \206\166 v \226\138\162 WP Ret v @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros "H\206\166".
Time rewrite wp_unfold /wp_pre //=.
Time Qed.
Time
Lemma wp_value_inv' {T} s E \206\166 (v : T) : WP Ret v @ s; E {{ \206\166 }} ={E}=\226\136\151 \206\166 v.
Time Proof.
Time by rewrite wp_unfold /wp_pre //=.
Time Qed.
Time
Lemma wp_strong_mono {T} s1 s2 E1 E2 (e : proc OpT T) 
  \206\166 \206\168 :
  s1 \226\138\145 s2
  \226\134\146 E1 \226\138\134 E2
    \226\134\146 WP e @ s1; E1 {{ \206\166 }}
      -\226\136\151 (\226\136\128 v, \206\166 v ={E2}=\226\136\151 \206\168 v) -\226\136\151 WP e @ s2; E2 {{ \206\168 }}.
Time Proof.
Time iIntros ( ? HE ) "H H\206\166".
Time iL\195\182b as "IH" forall ( T e E1 E2 HE \206\166 \206\168 ).
Time rewrite !wp_unfold /wp_pre.
Time (destruct (to_val e) as [v| ] eqn:?).
Time {
Time iApply ("H\206\166" with "[> -]").
Time by iApply (fupd_mask_mono E1 _).
Time }
Time iIntros ( \207\1311 ) "H\207\131".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (fupd_intro_mask' E2 E1) as "Hclose" ;
 first  done).
Time iMod ("H" with "[$]") as "[% H]".
Time iModIntro.
Time (iSplit; [ by destruct s1, s2 |  ]).
Time iIntros ( e2 \207\1312 efs Hstep ).
Time iMod ("H" with "[//]") as "H".
Time iIntros "!> !>".
Time iMod "H" as "($ & H & Hefs)".
Time iMod "Hclose" as "_".
Time iModIntro.
Time iSplitR "Hefs".
Time -
Time iApply ("IH" with "[//] H H\206\166").
Time -
Time (iApply (big_sepL_impl with "[$Hefs]"); iIntros "!#" ( k ef _ ) "H").
Time by iApply ("IH" with "[] H").
Time Qed.
Time
Lemma fupd_wp {T} s E (e : proc OpT T) \206\166 :
  (|={E}=> WP e @ s; E {{ \206\166 }}) \226\138\162 WP e @ s; E {{ \206\166 }}.
Time Proof.
Time rewrite wp_unfold /wp_pre.
Time iIntros "H".
Time (destruct (to_val e) as [v| ] eqn:?).
Time {
Time by iMod "H".
Time }
Time iIntros ( \207\1311 ) "H\207\1311".
Time iMod "H".
Time by iApply "H".
Time Qed.
Time
Lemma wp_fupd {T} s E (e : proc OpT T) \206\166 :
  WP e @ s; E {{ v, |={E}=> \206\166 v }} \226\138\162 WP e @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros "H".
Time (iApply (wp_strong_mono s s E with "H"); auto).
Time Qed.
Time
Lemma wp_atomic {T} s E1 E2 (e : proc OpT T) \206\166
  `{!Atomic \206\155 (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> \206\166 v }}) \226\138\162 WP e @ s; E1 {{ \206\166 }}.
Time Proof.
Time iIntros "H".
Time rewrite !wp_unfold /wp_pre.
Time (destruct (to_val e) as [v| ] eqn:He).
Time {
Time by iDestruct "H" as ">>> $".
Time }
Time iIntros ( \207\1311 ) "H\207\131".
Time iMod "H".
Time iMod ("H" $! \207\1311 with "H\207\131") as "[$ H]".
Time iModIntro.
Time iIntros ( e2 \207\1312 efs Hstep ).
Time iMod ("H" with "[//]") as "H".
Time iIntros "!>!>".
Time iMod "H" as "(Hphy & H & $)".
Time (destruct s).
Time -
Time rewrite !wp_unfold /wp_pre.
Time (destruct (to_val e2) as [v2| ] eqn:He2).
Time +
Time iDestruct "H" as ">> $".
Time by iFrame.
Time +
Time iMod ("H" with "[$]") as "[% H]".
Time (edestruct (atomic _ _ _ _ Hstep) as [Hval| Herr]).
Time *
Time (rewrite He2 //= in  {} Hval; exfalso).
Time (eapply is_Some_None; eauto).
Time *
Time (exfalso; eauto).
Time -
Time (destruct (atomic _ _ _ _ Hstep) as [v <-%of_to_val]).
Time iMod (wp_value_inv' with "H") as ">H".
Time iFrame "Hphy".
Time by iApply wp_value'.
Time Qed.
Time
Lemma wp_step_fupd {T} s E1 E2 (e : proc OpT T) P 
  \206\166 :
  to_val e = None
  \226\134\146 E2 \226\138\134 E1
    \226\134\146 (|={E1,E2}\226\150\183=> P)
      -\226\136\151 WP e @ s; E2 {{ v, P ={E1}=\226\136\151 \206\166 v }} -\226\136\151 WP e @ s; E1 {{ \206\166 }}.
Time Proof.
Time rewrite !wp_unfold /wp_pre.
Time iIntros ( -> ? ) "HR H".
Time iIntros ( \207\1311 ) "H\207\131".
Time iMod "HR".
Time iMod ("H" with "[$]") as "[$ H]".
Time iIntros "!>" ( e2 \207\1312 efs Hstep ).
Time iMod ("H" $! e2 \207\1312 efs with "[% //]") as "H".
Time iIntros "!>!>".
Time iMod "H" as "($ & H & $)".
Time iMod "HR".
Time iModIntro.
Time (iApply (wp_strong_mono s s E2 with "H"); [ done.. | idtac ]).
Time iIntros ( v ) "H".
Time by iApply "H".
Time Qed.
Time
Lemma wp_bind {T1} {T2} (K : proc OpT T1 -> proc OpT T2) 
  `{!LanguageCtx \206\155 K} s E (e : proc OpT T1) \206\166 :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ \206\166 }} }} \226\138\162 WP K e @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros "H".
Time iL\195\182b as "IH" forall ( E e \206\166 ).
Time rewrite wp_unfold /wp_pre.
Time (destruct (to_val e) as [v| ] eqn:He).
Time {
Time (apply of_to_val in He as <-).
Time by iApply fupd_wp.
Time }
Time rewrite wp_unfold /wp_pre fill_not_val //.
Time iIntros ( \207\1311 ) "H\207\131".
Time iMod ("H" with "[$]") as "[% H]".
Time (iModIntro; iSplit).
Time {
Time iPureIntro.
Time (<ssreflect_plugin::ssrtclseq@0> destruct s ; last  done).
Time (eapply non_errorable_fill; eauto).
Time }
Time iIntros ( e2 \207\1312 efs Hstep ).
Time (destruct (fill_step_inv_valid e \207\1311 e2 \207\1312 efs) as (e2', (->, ?)); auto).
Time iMod ("H" $! e2' \207\1312 efs with "[//]") as "H".
Time iIntros "!>!>".
Time iMod "H" as "($ & H & $)".
Time by iApply "IH".
Time Qed.
Time
Lemma wp_bind_inv {T1} {T2} (K : proc OpT T1 -> proc OpT T2)
  `{!LanguageCtx \206\155 K} s E (e : proc OpT T1) \206\166 :
  WP K e @ s; E {{ \206\166 }} \226\138\162 WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ \206\166 }} }}.
Time Proof.
Time iIntros "H".
Time iL\195\182b as "IH" forall ( E e \206\166 ).
Time rewrite !wp_unfold /wp_pre.
Time (destruct (to_val e) as [v| ] eqn:He).
Time {
Time (apply of_to_val in He as <-).
Time by rewrite !wp_unfold /wp_pre.
Time }
Time rewrite fill_not_val //.
Time iIntros ( \207\1311 ) "H\207\131".
Time iMod ("H" with "[$]") as "[% H]".
Time (iModIntro; iSplit).
Time {
Time (destruct s; eauto using non_errorable_fill_inv).
Time }
Time iIntros ( e2 \207\1312 efs Hstep ).
Time
(iMod ("H" $! (K e2) \207\1312 efs with "[]") as "H";
  [ by eauto using fill_step_valid |  ]).
Time iIntros "!>!>".
Time iMod "H" as "($ & H & $)".
Time by iApply "IH".
Time Qed.
Time Section derived.
Time Context {T : Type}.
Time Implicit Type e : proc OpT T.
Time Implicit Type v : T.
Time
Lemma wp_mono s E e \206\166 \206\168 :
  (\226\136\128 v, \206\166 v \226\138\162 \206\168 v) \226\134\146 WP e @ s; E {{ \206\166 }} \226\138\162 WP e @ s; E {{ \206\168 }}.
Time Proof.
Time (iIntros ( H\206\166 ) "H"; iApply (wp_strong_mono with "H"); auto).
Time iIntros ( v ) "?".
Time by iApply H\206\166.
Time Qed.
Time
Lemma wp_stuck_mono s1 s2 E (e : proc OpT T) \206\166 :
  s1 \226\138\145 s2 \226\134\146 WP e @ s1; E {{ \206\166 }} \226\138\162 WP e @ s2; E {{ \206\166 }}.
Time Proof.
Time iIntros ( ? ) "H".
Time (iApply (wp_strong_mono with "H"); auto).
Time Qed.
Time
Lemma wp_stuck_weaken s E (e : proc OpT T) \206\166 :
  WP e @ s; E {{ \206\166 }} \226\138\162 WP e @ E ?{{ \206\166 }}.
Time Proof.
Time (apply wp_stuck_mono).
Time by destruct s.
Time Qed.
Time
Lemma wp_mask_mono s E1 E2 (e : proc OpT T) \206\166 :
  E1 \226\138\134 E2 \226\134\146 WP e @ s; E1 {{ \206\166 }} \226\138\162 WP e @ s; E2 {{ \206\166 }}.
Time Proof.
Time (iIntros ( ? ) "H"; iApply (wp_strong_mono with "H"); auto).
Time Qed.
Time #[global]
Instance wp_mono'  s E (e : proc OpT T):
 (Proper (pointwise_relation _ (\226\138\162) ==> (\226\138\162)) (wp s E e)).
Time Proof.
Time by intros \206\166 \206\166' ?; apply wp_mono.
Time Qed.
Time Lemma wp_value s E \206\166 e v : IntoVal e v \226\134\146 \206\166 v \226\138\162 WP e @ s; E {{ \206\166 }}.
Time Proof.
Time (intros <-).
Time by apply wp_value'.
Time Qed.
Time
Lemma wp_value_fupd' s E \206\166 v : (|={E}=> \206\166 v) \226\138\162 WP of_val v @ s; E {{ \206\166 }}.
Time Proof.
Time (intros).
Time by rewrite -wp_fupd -wp_value'.
Time Qed.
Time
Lemma wp_value_fupd s E \206\166 e v `{!IntoVal e v} :
  (|={E}=> \206\166 v) \226\138\162 WP e @ s; E {{ \206\166 }}.
Time Proof.
Time (intros).
Time rewrite -wp_fupd -wp_value //.
Time Qed.
Time
Lemma wp_value_inv s E \206\166 e v : IntoVal e v \226\134\146 WP e @ s; E {{ \206\166 }} ={E}=\226\136\151 \206\166 v.
Time Proof.
Time (intros <-).
Time by apply wp_value_inv'.
Time Qed.
Time
Lemma wp_frame_l s E e \206\166 R :
  R \226\136\151 WP e @ s; E {{ \206\166 }} \226\138\162 WP e @ s; E {{ v, R \226\136\151 \206\166 v }}.
Time Proof.
Time iIntros "[? H]".
Time (iApply (wp_strong_mono with "H"); auto with iFrame).
Time Qed.
Time
Lemma wp_frame_r s E e \206\166 R :
  WP e @ s; E {{ \206\166 }} \226\136\151 R \226\138\162 WP e @ s; E {{ v, \206\166 v \226\136\151 R }}.
Time Proof.
Time iIntros "[H ?]".
Time (iApply (wp_strong_mono with "H"); auto with iFrame).
Time Qed.
Time
Lemma wp_frame_step_l s E1 E2 e \206\166 R :
  to_val e = None
  \226\134\146 E2 \226\138\134 E1
    \226\134\146 (|={E1,E2}\226\150\183=> R) \226\136\151 WP e @ s; E2 {{ \206\166 }} \226\138\162 WP e @ s; E1 {{ v, R \226\136\151 \206\166 v }}.
Time Proof.
Time iIntros ( ? ? ) "[Hu Hwp]".
Time (iApply (wp_step_fupd with "Hu"); try done).
Time iApply (wp_mono with "Hwp").
Time by iIntros ( ? ) "$$".
Time Qed.
Time
Lemma wp_frame_step_r s E1 E2 e \206\166 R :
  to_val e = None
  \226\134\146 E2 \226\138\134 E1
    \226\134\146 WP e @ s; E2 {{ \206\166 }} \226\136\151 (|={E1,E2}\226\150\183=> R) \226\138\162 WP e @ s; E1 {{ v, \206\166 v \226\136\151 R }}.
Time Proof.
Time
(rewrite [(WP _ @ _; _ {{ _ }} \226\136\151 _)%I]comm; setoid_rewrite (comm _ _ R)).
Time (apply wp_frame_step_l).
Time Qed.
Time
Lemma wp_frame_step_l' s E e \206\166 R :
  to_val e = None \226\134\146 \226\150\183 R \226\136\151 WP e @ s; E {{ \206\166 }} \226\138\162 WP e @ s; E {{ v, R \226\136\151 \206\166 v }}.
Time Proof.
Time iIntros ( ? ) "[??]".
Time (iApply (wp_frame_step_l s E E); try iFrame; eauto).
Time Qed.
Time
Lemma wp_frame_step_r' s E e \206\166 R :
  to_val e = None \226\134\146 WP e @ s; E {{ \206\166 }} \226\136\151 \226\150\183 R \226\138\162 WP e @ s; E {{ v, \206\166 v \226\136\151 R }}.
Time Proof.
Time iIntros ( ? ) "[??]".
Time (iApply (wp_frame_step_r s E E); try iFrame; eauto).
Time Qed.
Time
Lemma wp_wand s E e \206\166 \206\168 :
  WP e @ s; E {{ \206\166 }} -\226\136\151 (\226\136\128 v, \206\166 v -\226\136\151 \206\168 v) -\226\136\151 WP e @ s; E {{ \206\168 }}.
Time Proof.
Time iIntros "Hwp H".
Time (iApply (wp_strong_mono with "Hwp"); auto).
Time iIntros ( ? ) "?".
Time by iApply "H".
Time Qed.
Time
Lemma wp_wand_l s E e \206\166 \206\168 :
  (\226\136\128 v, \206\166 v -\226\136\151 \206\168 v) \226\136\151 WP e @ s; E {{ \206\166 }} \226\138\162 WP e @ s; E {{ \206\168 }}.
Time Proof.
Time iIntros "[H Hwp]".
Time iApply (wp_wand with "Hwp H").
Time Qed.
Time
Lemma wp_wand_r s E e \206\166 \206\168 :
  WP e @ s; E {{ \206\166 }} \226\136\151 (\226\136\128 v, \206\166 v -\226\136\151 \206\168 v) \226\138\162 WP e @ s; E {{ \206\168 }}.
Time Proof.
Time iIntros "[Hwp H]".
Time iApply (wp_wand with "Hwp H").
Time Qed.
Time End derived.
Time End wp.
Time Section proofmode_classes.
Time Context `{\206\155 : Layer OpT} `{irisG OpT \206\155 \206\163}.
Time Context {T : Type}.
Time Implicit Types P Q : iProp \206\163.
Time Implicit Type e : proc OpT T.
Time #[global]
Instance frame_wp  p s E e R \206\166 \206\168:
 ((\226\136\128 v, Frame p R (\206\166 v) (\206\168 v))
  \226\134\146 Frame p R (WP e @ s; E {{ \206\166 }}) (WP e @ s; E {{ \206\168 }})).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Frame =>HR).
Time rewrite wp_frame_l.
Time (apply wp_mono, HR).
Time Qed.
Time #[global]
Instance is_except_0_wp  s E e \206\166: (IsExcept0 (WP e @ s; E {{ \206\166 }})).
Time Proof.
Time by rewrite /IsExcept0 -{+2}fupd_wp -except_0_fupd -fupd_intro.
Time Qed.
Time #[global]
Instance elim_modal_bupd_wp  p s E e P \206\166:
 (ElimModal True p false (|==> P) P (WP e @ s; E {{ \206\166 }})
    (WP e @ s; E {{ \206\166 }})).
Time Proof.
Time
by rewrite /ElimModal intuitionistically_if_elim (bupd_fupd E) fupd_frame_r
 wand_elim_r fupd_wp.
Time Qed.
Time #[global]
Instance elim_modal_fupd_wp  p s E e P \206\166:
 (ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ \206\166 }})
    (WP e @ s; E {{ \206\166 }})).
Time Proof.
Time
by rewrite /ElimModal intuitionistically_if_elim fupd_frame_r wand_elim_r
 fupd_wp.
Time Qed.
Time #[global]
Instance elim_modal_fupd_wp_atomic  p s E1 E2 e P 
 \206\166:
 (Atomic \206\155 (stuckness_to_atomicity s) e
  \226\134\146 ElimModal True p false (|={E1,E2}=> P) P (WP e @ s; E1 {{ \206\166 }})
      (WP e @ s; E2 {{ v, |={E2,E1}=> \206\166 v }})%I).
Time Proof.
Time (intros).
Time
by rewrite /ElimModal intuitionistically_if_elim fupd_frame_r wand_elim_r
 wp_atomic.
Time Qed.
Time #[global]
Instance add_modal_fupd_wp  s E e P \206\166:
 (AddModal (|={E}=> P) P (WP e @ s; E {{ \206\166 }})).
Time Proof.
Time by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp.
Time Qed.
Time #[global]
Instance elim_acc_wp  {X} E1 E2 \206\177 \206\178 \206\179 e s \206\166:
 (Atomic \206\155 (stuckness_to_atomicity s) e
  \226\134\146 ElimAcc (X:=X) (fupd E1 E2) (fupd E2 E1) \206\177 \206\178 \206\179 
      (WP e @ s; E1 {{ \206\166 }})
      (\206\187 x, WP e @ s; E2 {{ v, |={E2}=> \206\178 x \226\136\151 (\206\179 x -\226\136\151? \206\166 v) }})%I).
Time Proof.
Time (intros ?).
Time rewrite /ElimAcc.
Time iIntros "Hinner >Hacc".
Time iDestruct "Hacc" as ( x ) "[H\206\177 Hclose]".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (wp_wand with "[Hinner H\206\177]") ; first 
 by iApply "Hinner").
Time iIntros ( v ) ">[H\206\178 H\206\166]".
Time iApply "H\206\166".
Time by iApply "Hclose".
Time Qed.
Time #[global]
Instance elim_acc_wp_nonatomic  {X} E \206\177 \206\178 \206\179 e s \206\166:
 (ElimAcc (X:=X) (fupd E E) (fupd E E) \206\177 \206\178 \206\179 (WP e @ s; E {{ \206\166 }})
    (\206\187 x, WP e @ s; E {{ v, |={E}=> \206\178 x \226\136\151 (\206\179 x -\226\136\151? \206\166 v) }})%I).
Time Proof.
Time rewrite /ElimAcc.
Time iIntros "Hinner >Hacc".
Time iDestruct "Hacc" as ( x ) "[H\206\177 Hclose]".
Time iApply wp_fupd.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (wp_wand with "[Hinner H\206\177]") ; first 
 by iApply "Hinner").
Time iIntros ( v ) ">[H\206\178 H\206\166]".
Time iApply "H\206\166".
Time by iApply "Hclose".
Time Qed.
Time End proofmode_classes.
Time From iris.base_logic.lib Require Export invariants.
Time
Lemma wp_fast_inv `{irisG OpT \206\155 \206\163} {T} E N P \206\166 (e : proc OpT T) 
  s :
  Atomic \206\155 (stuckness_to_atomicity s) e
  \226\134\146 \226\134\145N \226\138\134 E
    \226\134\146 inv N P
      -\226\136\151 (\226\150\183 P -\226\136\151 WP e @ s; E \226\136\150 \226\134\145N {{ v, |={E \226\136\150 \226\134\145N}=> \226\150\183 P \226\136\151 \206\166 v }})
         -\226\136\151 WP e @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros ( ? ? ) "Hinv HPQ".
Time iInv "Hinv" as "H".
Time by iApply "HPQ".
Time Qed.
Time
Ltac
 iFastInv H1 H2 :=
  <ssreflect_plugin::ssrtclseq@0> iApply (wp_fast_inv with H1) ; first  by
   set_solver +; iIntros H2.
