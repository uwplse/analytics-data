Time From Coq Require Import Omega.
Time From Coq Require Export Lia.
Time From stdpp Require Export decidable.
Time Set Default Proof Using "Type".
Time Lemma f_equal_dep {A} {B} (f g : \226\136\128 x : A, B x) x : f = g \226\134\146 f x = g x.
Time Proof.
Time (intros ->; reflexivity).
Time Qed.
Time
Lemma f_equal_help {A} {B} (f g : A \226\134\146 B) x y : f = g \226\134\146 x = y \226\134\146 f x = g y.
Time Proof.
Time (intros -> ->; reflexivity).
Time Qed.
Time
Ltac
 f_equal :=
  let rec go :=
   match goal with
   | _ => reflexivity
   | _ =>
       apply f_equal_help; [ go | try reflexivity ]
   | |- ?f ?x = ?g ?x => apply (f_equal_dep f g); go
   end
  in
  try go.
Time Hint Extern 998 (_ = _) => f_equal: f_equal.
Time Hint Extern 999  => congruence: congruence.
Time Hint Extern 1000  => lia: lia.
Time Hint Extern 1000  => omega: omega.
Time Hint Extern 1001  => (progress subst): subst.
Time Tactic Notation "intuition" := intuition auto.
Time
Ltac
 fast_done := solve
 [ eassumption
 | symmetry; eassumption
 | apply not_symmetry; eassumption
 | reflexivity ].
Time Tactic Notation "fast_by" tactic(tac) := (tac; fast_done).
Time
Ltac
 done := solve
 [ repeat (first
    [ fast_done
    | solve
    [ trivial ]
    | progress intros
    | solve
    [ symmetry; trivial ]
    | solve
    [ apply not_symmetry; trivial ]
    | discriminate
    | contradiction
    | split
    | match goal with
      | H:\194\172 _ |- _ => case H; clear H; fast_done
      end ]) ].
Time Tactic Notation "by" tactic(tac) := (tac; done).
Time Ltac done_if b := match b with
                       | true => done
                       | false => idtac
                       end.
Time Tactic Notation "trans" constr(A) := (transitivity A).
Time Tactic Notation "etrans" := etransitivity.
Time
Tactic Notation "split_and" :=
 (match goal with
  | |- _ \226\136\167 _ => split
  | |- Is_true (_ && _) => apply andb_True; split
  end).
Time Tactic Notation "split_and" "?" := (repeat split_and).
Time Tactic Notation "split_and" "!" := (hnf; split_and; split_and ?).
Time
Tactic Notation "destruct_and" "?" :=
 (repeat
   match goal with
   | H:False |- _ => destruct H
   | H:_ \226\136\167 _ |- _ => destruct H
   | H:Is_true (bool_decide _) |- _ => apply (bool_decide_unpack _) in H
   | H:Is_true (_ && _) |- _ => apply andb_True in H; destruct H
   end).
Time Tactic Notation "destruct_and" "!" := (progress destruct_and ?).
Time
Ltac
 case_match :=
  match goal with
  | H:context [ match ?x with
                | _ => _
                end ] |- _ => destruct x eqn:?
  | |- context [ match ?x with
                 | _ => _
                 end ] => destruct x eqn:?
  end.
Time
Tactic Notation "unless" constr(T) "by" tactic3(tac_fail) := (first
 [ assert T by tac_fail; fail 1 | idtac ]).
Time
Tactic Notation "repeat_on_hyps" tactic3(tac) :=
 (repeat match goal with
         | H:_ |- _ => progress tac H
         end).
Time
Tactic Notation "clear" "dependent" hyp(H1) hyp(H2) :=
 (clear dependent H1; clear dependent H2).
Time
Tactic Notation "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) :=
 (clear dependent H1 H2; clear dependent H3).
Time
Tactic Notation "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4) :=
 (clear dependent H1 H2 H3; clear dependent H4).
Time
Tactic Notation "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
 := (clear dependent H1 H2 H3 H4; clear dependent H5).
Time
Tactic Notation
 "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5) hyp(H6) :=
 (clear dependent H1 H2 H3 H4 H5; clear dependent H6).
Time
Tactic Notation
 "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5) hyp(H6) hyp(H7)
 := (clear dependent H1 H2 H3 H4 H5 H6; clear dependent H7).
Time
Tactic Notation
 "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5) hyp(H6) hyp(H7)
 hyp(H8) := (clear dependent H1 H2 H3 H4 H5 H6 H7; clear dependent H8).
Time
Tactic Notation
 "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5) hyp(H6) hyp(H7)
 hyp(H8) hyp(H9) :=
 (clear dependent H1 H2 H3 H4 H5 H6 H7 H8; clear dependent H9).
Time
Tactic Notation
 "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5) hyp(H6) hyp(H7)
 hyp(H8) hyp(H9) hyp(H10) :=
 (clear dependent H1 H2 H3 H4 H5 H6 H7 H8 H9; clear dependent H10).
Time
Tactic Notation "is_non_dependent" constr(H) :=
 (match goal with
  | _:context [ H ] |- _ => fail 1
  | |- context [ H ] => fail 1
  | _ => idtac
  end).
Time Ltac var_eq x1 x2 := match x1 with
                          | x2 => idtac
                          | _ => fail 1
                          end.
Time Ltac var_neq x1 x2 := match x1 with
                           | x2 => fail 1
                           | _ => idtac
                           end.
Time
Ltac
 fold_classes :=
  repeat
   match goal with
   | |- context [ ?F ] =>
         progress
          match type of F with
          | FMap _ =>
              change_no_check F with (@fmap _ F);
               repeat change_no_check (@fmap _ (@fmap _ F)) with (@fmap _ F)
          | MBind _ =>
              change_no_check F with (@mbind _ F);
               repeat
                change_no_check (@mbind _ (@mbind _ F)) with (@mbind _ F)
          | OMap _ =>
              change_no_check F with (@omap _ F);
               repeat change_no_check (@omap _ (@omap _ F)) with (@omap _ F)
          | Alter _ _ _ =>
              change_no_check F with (@alter _ _ _ F);
               repeat
                change_no_check (@alter _ _ _ (@alter _ _ _ F)) with
                 (@alter _ _ _ F)
          end
   end.
Time
Ltac
 fold_classes_hyps H :=
  repeat
   match type of H with
   | context [ ?F ] =>
       progress
        match type of F with
        | FMap _ =>
            change_no_check F with (@fmap _ F) in H;
             repeat
              change_no_check (@fmap _ (@fmap _ F)) with (@fmap _ F) in H
        | MBind _ =>
            change_no_check F with (@mbind _ F) in H;
             repeat
              change_no_check (@mbind _ (@mbind _ F)) with (@mbind _ F) in H
        | OMap _ =>
            change_no_check F with (@omap _ F) in H;
             repeat
              change_no_check (@omap _ (@omap _ F)) with (@omap _ F) in H
        | Alter _ _ _ =>
            change_no_check F with (@alter _ _ _ F) in H;
             repeat
              change_no_check (@alter _ _ _ (@alter _ _ _ F)) with
               (@alter _ _ _ F) in H
        end
   end.
Time
Tactic Notation "csimpl" "in" hyp(H) :=
 (try (progress simpl in H; fold_classes_hyps H)).
Time Tactic Notation "csimpl" := (try (progress simpl; fold_classes)).
Time
Tactic Notation "csimpl" "in" "*" :=
 (repeat_on_hyps fun H => csimpl in H; csimpl).
Time
Tactic Notation "simplify_eq" :=
 (repeat
   match goal with
   | H:_ \226\137\160 _ |- _ => by case H; try clear H
   | H:_ = _ \226\134\146 False |- _ => by case H; try clear H
   | H:?x = _ |- _ => subst x
   | H:_ = ?x |- _ => subst x
   | H:_ = _ |- _ => discriminate H
   | H:_ \226\137\161 _ |- _ => apply leibniz_equiv in H
   | H:?f _ = ?f _ |- _ => apply (inj f) in H
   | H:?f _ _ = ?f _ _ |- _ => apply (inj2 f) in H; destruct H
   | H:?f _ = ?f _ |- _ => progress injection H as H
   | H:?f _ _ = ?f _ _ |- _ => progress injection H as H
   | H:?f _ _ _ = ?f _ _ _ |- _ => progress injection H as H
   | H:?f _ _ _ _ = ?f _ _ _ _ |- _ => progress injection H as H
   | H:?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ => progress injection H as H
   | H:?f _ _ _ _ _ _ = ?f _ _ _ _ _ _ |- _ => progress injection H as H
   | H:?x = ?x |- _ => clear H
   | H1:?o = Some ?x, H2:?o = Some ?y
     |- _ => assert (y = x) by congruence; clear H2
   | H1:?o = Some ?x, H2:?o = None |- _ => congruence
   | H:@existT ?A _ _ _ = existT _ _
     |- _ => apply (Eqdep_dec.inj_pair2_eq_dec _ (decide_rel (=@{A} ))) in H
   end).
Time
Tactic Notation "simplify_eq" "/=" :=
 (repeat progress csimpl in * || simplify_eq).
Time Tactic Notation "f_equal" "/=" := (csimpl in *; f_equal).
Time
Ltac
 setoid_subst_aux R x :=
  match goal with
  | H:R x ?y
    |- _ =>
        is_var x; try match y with
                      | x _ => fail 2
                      end;
         repeat
          match goal with
          | |- context [ x ] => setoid_rewrite H
          | H':context [ x ]
            |- _ => try match H' with
                        | H => fail 2
                        end; setoid_rewrite H in H'
          end; clear x H
  end.
Time
Ltac
 setoid_subst :=
  repeat
   match goal with
   | _ =>
       progress simplify_eq /=
   | H:@equiv ?A ?e ?x _ |- _ => setoid_subst_aux (@equiv A e) x
   | H:@equiv ?A ?e _ ?x
     |- _ => symmetry in H; setoid_subst_aux (@equiv A e) x
   end.
Time
Ltac
 f_equiv :=
  match goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  | |- ?R match ?x with
          | _ => _
          end match ?x with
              | _ => _
              end => destruct x
  | H:?R ?x ?y
    |- ?R2 match ?x with
           | _ => _
           end match ?y with
               | _ => _
               end => destruct H
  | |- ?R (?f _) _ => simple apply (_ : Proper (R ==> R) f)
  | |- ?R (?f _ _) _ => simple apply (_ : Proper (R ==> R ==> R) f)
  | |- ?R (?f _ _ _) _ => simple apply (_ : Proper (R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _) _ =>
        simple apply (_ : Proper (R ==> R ==> R ==> R ==> R) f)
  | |- (?R _) (?f _) _ => simple apply (_ : Proper (R _ ==> _) f)
  | |- (?R _ _) (?f _) _ => simple apply (_ : Proper (R _ _ ==> _) f)
  | |- (?R _ _ _) (?f _) _ => simple apply (_ : Proper (R _ _ _ ==> _) f)
  | |- (?R _) (?f _ _) _ => simple apply (_ : Proper (R _ ==> R _ ==> _) f)
  | |- (?R _ _) (?f _ _) _ =>
        simple apply (_ : Proper (R _ _ ==> R _ _ ==> _) f)
  | |- (?R _ _ _) (?f _ _) _ =>
        simple apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> _) f)
  | |- (?R _) (?f _ _ _) _ =>
        simple apply (_ : Proper (R _ ==> R _ ==> R _ ==> _) f)
  | |- (?R _ _) (?f _ _ _) _ =>
        simple apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> _) f)
  | |- (?R _ _ _) (?f _ _ _) _ =>
        simple apply (_ : Proper (R _ _ _ ==> R _ _ _ R _ _ _ ==> _) f)
  | |- (?R _) (?f _ _ _ _) _ =>
        simple apply (_ : Proper (R _ ==> R _ ==> R _ ==> R _ ==> _) f)
  | |- (?R _ _) (?f _ _ _ _) _ =>
        simple apply
         (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> _) f)
  | |- (?R _ _ _) (?f _ _ _ _) _ =>
        simple apply
         (_ : Proper (R _ _ _ ==> R _ _ _ R _ _ _ ==> R _ _ _ ==> _) f)
  | |- ?R (?f _) _ => simple apply (_ : Proper (_ ==> R) f)
  | |- ?R (?f _ _) _ => simple apply (_ : Proper (_ ==> _ ==> R) f)
  | |- ?R (?f _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _) _ =>
        simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> R) f)
  | H:pointwise_relation _ ?R ?f ?g |- ?R (?f ?x) (?g ?x) => simple apply H
  | H:pointwise_relation _ (pointwise_relation _ ?R) ?f ?g
    |- ?R (?f ?x ?y) (?g ?x ?y) => simple apply H
  end; try simple apply reflexivity.
Time Tactic Notation "f_equiv" "/=" := (csimpl in *; f_equiv).
Time
Ltac
 solve_proper_unfold :=
  lazymatch goal with
  | |- ?R (?f _ _ _ _ _ _ _ _ _ _) (?f _ _ _ _ _ _ _ _ _ _) => unfold f
  | |- ?R (?f _ _ _ _ _ _ _ _ _) (?f _ _ _ _ _ _ _ _ _) => unfold f
  | |- ?R (?f _ _ _ _ _ _ _ _) (?f _ _ _ _ _ _ _ _) => unfold f
  | |- ?R (?f _ _ _ _ _ _ _) (?f _ _ _ _ _ _ _) => unfold f
  | |- ?R (?f _ _ _ _ _ _) (?f _ _ _ _ _ _) => unfold f
  | |- ?R (?f _ _ _ _ _) (?f _ _ _ _ _) => unfold f
  | |- ?R (?f _ _ _ _) (?f _ _ _ _) => unfold f
  | |- ?R (?f _ _ _) (?f _ _ _) => unfold f
  | |- ?R (?f _ _) (?f _ _) => unfold f
  | |- ?R (?f _) (?f _) => unfold f
  end.
Time
Ltac
 solve_proper_prepare :=
  intros;
   repeat
    lazymatch goal with
    | |- Proper _ _ => intros ? ? ?
    | |- (_ ==> _)%signature _ _ => intros ? ? ?
    | |- pointwise_relation _ _ _ _ => intros ?
    | |- ?R ?f _ => let f' := constr:(\206\187 x, f x) in
                    intros ?; intros
    end; simplify_eq; solve_proper_unfold + idtac; 
   simpl.
Time
Ltac
 solve_proper_core tac :=
  solve_proper_prepare; (solve
   [ repeat (first [ eassumption | tac ltac:(()) ]) ]).
Time Ltac solve_proper := solve_proper_core ltac:(fun _ => f_equiv).
Time
Ltac
 intros_revert tac :=
  lazymatch goal with
  | |- \226\136\128 _, _ => let H := fresh in
                 intro H; intros_revert tac; revert H
  | |- _ => tac
  end.
Time
Tactic Notation "iter" tactic(tac) tactic(l) :=
 (let rec go l := match l with
                  | ?x :: ?l => tac x || go l
                  end in
  go l).
Time
Tactic Notation "feed" tactic(tac) constr(H) :=
 (let rec go H :=
   let T := type of H in
   lazymatch eval hnf in T with
   | ?T1 \226\134\146 ?T2 =>
       let HT1 := fresh "feed" in
       assert (HT1 : T1); [  | go (H HT1); clear HT1 ]
   | ?T1 => tac H
   end
  in
  go H).
Time
Tactic Notation "efeed" constr(H) "using" tactic3(tac) "by" tactic3(bytac) :=
 (let rec go H :=
   let T := type of H in
   lazymatch eval hnf in T with
   | ?T1 \226\134\146 ?T2 =>
       let HT1 := fresh "feed" in
       assert (HT1 : T1); [ bytac | go (H HT1); clear HT1 ]
   | ?T1 \226\134\146 _ =>
       let e := fresh "feed" in
       evar ( e : T1 ); (let e' := eval unfold e in e in
                         clear e; go (H e'))
   | ?T1 => tac H
   end
  in
  go H).
Time
Tactic Notation "efeed" constr(H) "using" tactic3(tac) := efeed H using tac
 by idtac.
Time
Tactic Notation "feed" "pose" "proof" constr(H) "as" ident(H') := feed
 fun p => pose proof p as H' H.
Time
Tactic Notation "feed" "pose" "proof" constr(H) := feed 
 fun p => pose proof p H.
Time
Tactic Notation "efeed" "pose" "proof" constr(H) "as" ident(H') := efeed H
 using fun p => pose proof p as H'.
Time
Tactic Notation "efeed" "pose" "proof" constr(H) := efeed H using
 fun p => pose proof p.
Time
Tactic Notation "feed" "specialize" hyp(H) := feed fun p => specialize p H.
Time
Tactic Notation "efeed" "specialize" hyp(H) := efeed H using
 fun p => specialize p.
Time
Tactic Notation "feed" "inversion" constr(H) := feed
 fun p => let H' := fresh in
          pose proof p as H'; inversion H' H.
Time
Tactic Notation "feed" "inversion" constr(H) "as" simple_intropattern(IP) :=
 feed fun p => let H' := fresh in
               pose proof p as H'; inversion H' as IP H.
Time
Tactic Notation "feed" "destruct" constr(H) := feed
 fun p => let H' := fresh in
          pose proof p as H'; destruct H' H.
Time
Tactic Notation "feed" "destruct" constr(H) "as" simple_intropattern(IP) :=
 feed fun p => let H' := fresh in
               pose proof p as H'; destruct H' as IP H.
Time Definition block {A : Type} (a : A) := a.
Time
Ltac block_goal := match goal with
                   | |- ?T => change_no_check (block T)
                   end.
Time Ltac unblock_goal := unfold block in *.
Time
Ltac
 find_pat pat tac :=
  match goal with
  | |- context [ ?x ] =>
        unify pat x with typeclass_instances;
         tryif tac x then idtac else fail 2 
  end.
Time
Lemma forall_and_distr (A : Type) (P Q : A \226\134\146 Prop) :
  (\226\136\128 x, P x \226\136\167 Q x) \226\134\148 (\226\136\128 x, P x) \226\136\167 (\226\136\128 x, Q x).
Time Proof.
Time firstorder.
Time Qed.
Time Ltac no_new_unsolved_evars tac := exact _.
Time
Tactic Notation "naive_solver" tactic(tac) :=
 (unfold iff, not in *;
   repeat
    match goal with
    | H:context [ \226\136\128 _, _ \226\136\167 _ ]
      |- _ => repeat setoid_rewrite forall_and_distr in H; revert H
    end;
   (let rec go n :=
     repeat
      match goal with
      | |- _ => fast_done
      | |- \226\136\128 _, _ => intro
      | H:False |- _ => destruct H
      | H:_ \226\136\167 _
        |- _ =>
            let H1 := fresh in
            let H2 := fresh in
            destruct H as [H1 H2]; try clear H
      | H:\226\136\131 _, _
        |- _ =>
            let x := fresh in
            let Hx := fresh in
            destruct H as [x Hx]; try clear H
      | H:?P \226\134\146 ?Q, H2:?P |- _ => specialize (H H2)
      | H:Is_true (bool_decide _) |- _ => apply (bool_decide_unpack _) in H
      | H:Is_true (_ && _) |- _ => apply andb_True in H; destruct H
      | |- _ => progress simplify_eq /=
      | |- _ \226\136\167 _ => split
      | |- Is_true (bool_decide _) => apply (bool_decide_pack _)
      | |- Is_true (_ && _) => apply andb_True; split
      | H:_ \226\136\168 _ |- _ => let H1 := fresh in
                        destruct H as [H1| H1]; try clear H
      | H:Is_true (_ || _)
        |- _ =>
            apply orb_True in H;
             (let H1 := fresh in
              destruct H as [H1| H1]; try clear H)
      | |- _ => solve [ tac ]
      end;
      match goal with
      | |- \226\136\131 x, _ => no_new_unsolved_evars ltac:(eexists; go n)
      | |- _ \226\136\168 _ => first [ left; go n | right; go n ]
      | |- Is_true (_ || _) =>
            apply orb_True; (first [ left; go n | right; go n ])
      | _ =>
          lazymatch n with
          | S ?n' =>
              match goal with
              | H:_ \226\134\146 _
                |- _ =>
                    is_non_dependent H;
                     no_new_unsolved_evars
                      ltac:((first [ eapply H | efeed pose proof H ]); clear
                             H; go n')
              end
          end
      end
    in
    iter
    fun n' => go n'
    eval compute in (seq 1 6))).
Time Tactic Notation "naive_solver" := naive_solver eauto.
