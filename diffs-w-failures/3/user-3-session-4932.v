Time From iris.proofmode Require Import coq_tactics reduction.
Time
From iris.proofmode Require Import base intro_patterns spec_patterns
  sel_patterns.
Time From iris.bi Require Export bi telescopes.
Time From stdpp Require Import namespaces.
Time From iris.proofmode Require Export classes notation.
Time From stdpp Require Import hlist pretty.
Time Set Default Proof Using "Type".
Time Export ident.
Time Ltac iSolveTC := solve [ once typeclasses eauto ].
Time
Ltac
 iSolveSideCondition := split_and ?; try (solve [ fast_done | solve_ndisj ]).
Time Ltac pretty_ident H := lazymatch H with
                            | INamed ?H => H
                            | ?H => H
                            end.
Time
Ltac
 iGetCtx :=
  lazymatch goal with
  | |- envs_entails ?\206\148 _ => \206\148
  | |- context [ envs_split _ _ ?\206\148 ] => \206\148
  end.
Time
Ltac
 iMissingHypsCore \206\148 Hs :=
  let Hhyps := pm_eval (envs_dom \206\148) in
  eval vm_compute in (list_difference Hs Hhyps).
Time Ltac iMissingHyps Hs := let \206\148 := iGetCtx in
                             iMissingHypsCore \206\148 Hs.
Time
Ltac
 iTypeOf H :=
  let \206\148 := match goal with
           | |- envs_entails ?\206\148 _ => \206\148
           end in
  pm_eval (envs_lookup H \206\148).
Time
Ltac iBiOfGoal := match goal with
                  | |- @envs_entails ?PROP _ _ => PROP
                  end.
Time
Tactic Notation "iMatchHyp" tactic1(tac) :=
 (match goal with
  | |- context [ environments.Esnoc _ ?x ?P ] => tac x P
  end).
Time
Tactic Notation "iStartProof" :=
 (lazymatch goal with
  | |- envs_entails _ _ => idtac
  | |- ?\207\134 =>
        notypeclasses refine (as_emp_valid_2 \207\134 _ _);
         [ iSolveTC || fail "iStartProof: not a BI assertion"
         | apply tac_adequate ]
  end).
Time
Tactic Notation "iStartProof" uconstr(PROP) :=
 (lazymatch goal with
  | |- @envs_entails ?PROP' _ _ =>
        let x := type_term(eq_refl : @eq Type PROP PROP') in
        idtac
  | |- ?\207\134 =>
        notypeclasses refine ((\206\187 P : PROP, @as_emp_valid_2 \207\134 _ P) _ _ _);
         [ iSolveTC || fail "iStartProof: not a BI assertion"
         | apply tac_adequate ]
  end).
Time
Ltac
 iFresh :=
  let start := lazymatch goal with
               | _ => iStartProof
               end in
  let c := lazymatch goal with
           | |- envs_entails (Envs _ _ ?c) _ => c
           end in
  let inc :=
   lazymatch goal with
   | |- envs_entails (Envs ?\206\148p ?\206\148s _) ?Q =>
         let c' := eval vm_compute in (Pos.succ c) in
         convert_concl_no_check (envs_entails (Envs \206\148p \206\148s c') Q)
   end
  in
  IAnon c.
Time
Tactic Notation "iRename" constr(H1) "into" constr(H2) :=
 (eapply tac_rename with H1 H2 _ _;
   [ pm_reflexivity ||
       (let H1 := pretty_ident H1 in
        fail "iRename:" H1 "not found")
   | pm_reduce;
      lazymatch goal with
      | |- False =>
            let H2 := pretty_ident H2 in
            fail "iRename:" H2 "not fresh"
      | _ => idtac
      end ]).
Time
Inductive esel_pat :=
  | ESelPure : _
  | ESelIdent : bool \226\134\146 ident \226\134\146 esel_pat.
Time #[local]
Ltac
 iElaborateSelPat_go pat \206\148 Hs :=
  lazymatch pat with
  | [] => eval compute in Hs
  | SelPure :: ?pat =>
      iElaborateSelPat_go pat \206\148 (ESelPure :: Hs)
  | SelIntuitionistic :: ?pat =>
      let Hs' := pm_eval (env_dom (env_intuitionistic \206\148)) in
      let \206\148' := pm_eval (envs_clear_intuitionistic \206\148) in
      iElaborateSelPat_go pat \206\148' ((ESelIdent true <$> Hs') ++ Hs)
  | SelSpatial :: ?pat =>
      let Hs' := pm_eval (env_dom (env_spatial \206\148)) in
      let \206\148' := pm_eval (envs_clear_spatial \206\148) in
      iElaborateSelPat_go pat \206\148' ((ESelIdent false <$> Hs') ++ Hs)
  | SelIdent ?H :: ?pat =>
      lazymatch pm_eval (envs_lookup_delete false H \206\148)
      with
      | Some (?p, _, ?\206\148') =>
          iElaborateSelPat_go pat \206\148' (ESelIdent p H :: Hs)
      | None =>
          let H := pretty_ident H in
          fail "iElaborateSelPat:" H "not found"
      end
  end.
Time
Ltac
 iElaborateSelPat pat :=
  lazymatch goal with
  | |- envs_entails ?\206\148 _ =>
        let pat := sel_pat.parse pat in
        iElaborateSelPat_go pat \206\148 (@nil esel_pat)
  end.
Time #[local]
Ltac
 iClearHyp H :=
  eapply tac_clear with H _ _;
   [ pm_reflexivity ||
       (let H := pretty_ident H in
        fail "iClear:" H "not found")
   | pm_reduce;
      iSolveTC ||
        (let H := pretty_ident H in
         let P := match goal with
                  | |- TCOr (Affine ?P) _ => P
                  end in
         fail "iClear:" H ":" P "not affine and the goal not absorbing")
   | pm_reduce ].
Time #[local]
Ltac
 iClear_go Hs :=
  lazymatch Hs with
  | [] => idtac
  | ESelPure :: ?Hs => clear; iClear_go Hs
  | ESelIdent _ ?H :: ?Hs => iClearHyp H; iClear_go Hs
  end.
Time
Tactic Notation "iClear" constr(Hs) :=
 (iStartProof; (let Hs := iElaborateSelPat Hs in
                iClear_go Hs)).
Time
Tactic Notation "iClear" "(" ident_list(xs) ")" constr(Hs) :=
 (iClear Hs; clear xs).
Time
Tactic Notation "iEval" tactic3(t) :=
 (iStartProof; eapply tac_eval;
   [ let x := fresh in
     intros x; t; unfold x; reflexivity |  ]).
Time #[local]
Ltac
 iEval_go t Hs :=
  lazymatch Hs with
  | [] => idtac
  | ESelPure :: ?Hs =>
      fail "iEval: %: unsupported selection pattern"
  | ESelIdent _ ?H :: ?Hs =>
      eapply tac_eval_in with H _ _ _;
       [ pm_reflexivity ||
           (let H := pretty_ident H in
            fail "iEval:" H "not found")
       | let x := fresh in
         intros x; t; unfold x; reflexivity
       | pm_reduce; iEval_go t Hs ]
  end.
Time
Tactic Notation "iEval" tactic3(t) "in" constr(Hs) :=
 (iStartProof; (let Hs := iElaborateSelPat Hs in
                iEval_go t Hs)).
Time Tactic Notation "iSimpl" := iEval simpl.
Time Tactic Notation "iSimpl" "in" constr(H) := iEval simpl in H.
Time
Tactic Notation "iExact" constr(H) :=
 (eapply tac_assumption with H _ _;
   [ pm_reflexivity ||
       (let H := pretty_ident H in
        fail "iExact:" H "not found")
   | iSolveTC ||
       (let H := pretty_ident H in
        let P := match goal with
                 | |- FromAssumption _ ?P _ => P
                 end in
        fail "iExact:" H ":" P "does not match goal")
   | pm_reduce;
      iSolveTC ||
        (let H := pretty_ident H in
         fail "iExact:" H
          "not absorbing and the remaining hypotheses not affine") ]).
Time
Tactic Notation "iAssumptionCore" :=
 (let rec find \206\147 i P :=
   lazymatch \206\147 with
   | Esnoc ?\206\147 ?j ?Q => first [ unify P Q; unify i j | find \206\147 i P ]
   end
  in
  match goal with
  | |- envs_lookup ?i (Envs ?\206\147p ?\206\147s _) = Some (_, ?P) => first
    [ is_evar i; fail 1 | pm_reflexivity ]
  | |- envs_lookup ?i (Envs ?\206\147p ?\206\147s _) = Some (_, ?P) =>
        is_evar i; (first [ find \206\147p i P | find \206\147s i P ]); pm_reflexivity
  | |- envs_lookup_delete _ ?i (Envs ?\206\147p ?\206\147s _) = Some (_, ?P, _) => first
    [ is_evar i; fail 1 | pm_reflexivity ]
  | |- envs_lookup_delete _ ?i (Envs ?\206\147p ?\206\147s _) = Some (_, ?P, _) =>
        is_evar i; (first [ find \206\147p i P | find \206\147s i P ]); pm_reflexivity
  end).
Time
Tactic Notation "iAssumption" :=
 (let Hass := fresh in
  let rec find p \206\147 Q :=
   lazymatch \206\147 with
   | Esnoc ?\206\147 ?j ?P => first
   [ pose proof (_ : FromAssumption p P Q) as Hass;
      eapply (tac_assumption _ j p P);
      [ pm_reflexivity
      | apply Hass
      | pm_reduce;
         iSolveTC ||
           fail 1 "iAssumption:" j
            "not absorbing and the remaining hypotheses not affine" ]
   | assert (Hass : P = False%I) by reflexivity;
      apply (tac_false_destruct _ j p P); [ pm_reflexivity | exact Hass ]
   | find p \206\147 Q ]
   end
  in
  lazymatch goal with
  | |- envs_entails (Envs ?\206\147p ?\206\147s _) ?Q => first
    [ find true \206\147p Q | find false \206\147s Q | fail "iAssumption:" Q "not found" ]
  end).
Time Tactic Notation "iExFalso" := (apply tac_ex_falso).
Time #[local]
Tactic Notation "iIntuitionistic" constr(H) :=
 (eapply tac_intuitionistic with H _ _ _;
   [ pm_reflexivity ||
       (let H := pretty_ident H in
        fail "iIntuitionistic:" H "not found")
   | iSolveTC ||
       (let P := match goal with
                 | |- IntoPersistent _ ?P _ => P
                 end in
        fail "iIntuitionistic:" P "not persistent")
   | pm_reduce;
      iSolveTC ||
        (let P := match goal with
                  | |- TCOr (Affine ?P) _ => P
                  end in
         fail "iIntuitionistic:" P "not affine and the goal not absorbing")
   | pm_reduce ]).
Time
Tactic Notation "iPure" constr(H) "as" simple_intropattern(pat) :=
 (eapply tac_pure with H _ _ _;
   [ pm_reflexivity ||
       (let H := pretty_ident H in
        fail "iPure:" H "not found")
   | iSolveTC ||
       (let P := match goal with
                 | |- IntoPure ?P _ => P
                 end in
        fail "iPure:" P "not pure")
   | pm_reduce;
      iSolveTC ||
        (let P := match goal with
                  | |- TCOr (Affine ?P) _ => P
                  end in
         fail "iPure:" P "not affine and the goal not absorbing")
   | pm_reduce; intros pat ]).
Time
Tactic Notation "iEmpIntro" :=
 (iStartProof; eapply tac_emp_intro;
   [ pm_reduce;
      iSolveTC ||
        fail "iEmpIntro: spatial context contains non-affine hypotheses" ]).
Time
Tactic Notation "iPureIntro" :=
 (iStartProof; eapply tac_pure_intro;
   [ iSolveTC ||
       (let P := match goal with
                 | |- FromPure _ ?P _ => P
                 end in
        fail "iPureIntro:" P "not pure")
   | pm_reduce;
      iSolveTC ||
        fail "iPureIntro: spatial context contains non-affine hypotheses"
   |  ]).
Time #[local]
Ltac
 iFrameFinish :=
  pm_prettify;
   try
    match goal with
    | |- envs_entails _ True => by iPureIntro
    | |- envs_entails _ emp => iEmpIntro
    end.
Time #[local]
Ltac
 iFramePure t :=
  iStartProof;
   (let \207\134 := type of t in
    eapply (tac_frame_pure _ _ _ _ t);
     [ iSolveTC || fail "iFrame: cannot frame" \207\134 | iFrameFinish ]).
Time #[local]
Ltac
 iFrameHyp H :=
  iStartProof; eapply tac_frame with H _ _ _;
   [ pm_reflexivity ||
       (let H := pretty_ident H in
        fail "iFrame:" H "not found")
   | iSolveTC ||
       (let R := match goal with
                 | |- Frame _ ?R _ _ => R
                 end in
        fail "iFrame: cannot frame" R)
   | pm_reduce; iFrameFinish ].
Time #[local]
Ltac iFrameAnyPure := repeat match goal with
                             | H:_ |- _ => iFramePure H
                             end.
Time #[local]
Ltac
 iFrameAnyIntuitionistic :=
  iStartProof;
   (let rec go Hs :=
     match Hs with
     | [] => idtac
     | ?H :: ?Hs => repeat iFrameHyp H; go Hs
     end
    in
    match goal with
    | |- envs_entails ?\206\148 _ =>
          let Hs := eval compute in (env_dom (env_intuitionistic \206\148)) in
          go Hs
    end).
Time #[local]
Ltac
 iFrameAnySpatial :=
  iStartProof;
   (let rec go Hs :=
     match Hs with
     | [] => idtac
     | ?H :: ?Hs => try iFrameHyp H; go Hs
     end
    in
    match goal with
    | |- envs_entails ?\206\148 _ =>
          let Hs := eval compute in (env_dom (env_spatial \206\148)) in
          go Hs
    end).
Time Tactic Notation "iFrame" := iFrameAnySpatial.
Time Tactic Notation "iFrame" "(" constr(t1) ")" := (iFramePure t1).
Time
Tactic Notation "iFrame" "(" constr(t1) constr(t2) ")" :=
 (iFramePure t1; iFrame ( t2 )).
Time
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) ")" :=
 (iFramePure t1; iFrame ( t2 t3 )).
Time
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) ")"
 := (iFramePure t1; iFrame ( t2 t3 t4 )).
Time
Tactic Notation
 "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) ")" :=
 (iFramePure t1; iFrame ( t2 t3 t4 t5 )).
Time
Tactic Notation
 "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) constr(t5)
 constr(t6) ")" := (iFramePure t1; iFrame ( t2 t3 t4 t5 t6 )).
Time
Tactic Notation
 "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) constr(t5)
 constr(t6) constr(t7) ")" := (iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 )).
Time
Tactic Notation
 "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) constr(t5)
 constr(t6) constr(t7) constr(t8) ")" :=
 (iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 t8 )).
Time #[local]
Ltac
 iFrame_go Hs :=
  lazymatch Hs with
  | [] => idtac
  | SelPure :: ?Hs => iFrameAnyPure; iFrame_go Hs
  | SelIntuitionistic :: ?Hs =>
      iFrameAnyIntuitionistic; iFrame_go Hs
  | SelSpatial :: ?Hs => iFrameAnySpatial; iFrame_go Hs
  | SelIdent ?H :: ?Hs => iFrameHyp H; iFrame_go Hs
  end.
Time
Tactic Notation "iFrame" constr(Hs) :=
 (let Hs := sel_pat.parse Hs in
  iFrame_go Hs).
Time
Tactic Notation "iFrame" "(" constr(t1) ")" constr(Hs) :=
 (iFramePure t1; iFrame Hs).
Time
Tactic Notation "iFrame" "(" constr(t1) constr(t2) ")" constr(Hs) :=
 (iFramePure t1; iFrame ( t2 ) Hs).
Time
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) ")" constr(Hs)
 := (iFramePure t1; iFrame ( t2 t3 ) Hs).
Time
Tactic Notation
 "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) ")" constr(Hs) :=
 (iFramePure t1; iFrame ( t2 t3 t4 ) Hs).
Time
Tactic Notation
 "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) 
 ")" constr(Hs) := (iFramePure t1; iFrame ( t2 t3 t4 t5 ) Hs).
Time
Tactic Notation
 "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) constr(t5)
 constr(t6) ")" constr(Hs) := (iFramePure t1; iFrame ( t2 t3 t4 t5 t6 ) Hs).
Time
Tactic Notation
 "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) constr(t5)
 constr(t6) constr(t7) ")" constr(Hs) :=
 (iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 ) Hs).
Time
Tactic Notation
 "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) constr(t5)
 constr(t6) constr(t7) constr(t8) ")" constr(Hs) :=
 (iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 t8 ) Hs).
Time #[local]
Tactic Notation "iIntro" "(" simple_intropattern(x) ")" :=
 (intros x ||
    (iStartProof;
      lazymatch goal with
      | |- envs_entails _ _ =>
            eapply tac_forall_intro;
             [ iSolveTC ||
                 (let P := match goal with
                           | |- FromForall ?P _ => P
                           end in
                  fail "iIntro: cannot turn" P "into a universal quantifier")
             | pm_prettify; intros x ]
      end)).
Time #[local]
Tactic Notation "iIntro" constr(H) :=
 (iStartProof; (first
   [ eapply tac_impl_intro with H _ _ _;
      [ iSolveTC
      | pm_reduce;
         iSolveTC ||
           (let P := lazymatch goal with
                     | |- Persistent ?P => P
                     end in
            fail 1 "iIntro: introducing non-persistent" H ":" P
             "into non-empty spatial context")
      | iSolveTC
      | pm_reduce;
         (let H := pretty_ident H in
          lazymatch goal with
          | |- False =>
                let H := pretty_ident H in
                fail 1 "iIntro:" H "not fresh"
          | _ => idtac
          end) ]
   | eapply tac_wand_intro with H _ _;
      [ iSolveTC
      | pm_reduce;
         lazymatch goal with
         | |- False =>
               let H := pretty_ident H in
               fail 1 "iIntro:" H "not fresh"
         | _ => idtac
         end ]
   | fail 1 "iIntro: nothing to introduce" ])).
Time #[local]
Tactic Notation "iIntro" "#" constr(H) :=
 (iStartProof; (first
   [ eapply tac_impl_intro_intuitionistic with H _ _ _;
      [ iSolveTC
      | iSolveTC ||
          (let P := match goal with
                    | |- IntoPersistent _ ?P _ => P
                    end in
           fail 1 "iIntro:" P "not persistent")
      | pm_reduce;
         lazymatch goal with
         | |- False =>
               let H := pretty_ident H in
               fail 1 "iIntro:" H "not fresh"
         | _ => idtac
         end ]
   | eapply tac_wand_intro_intuitionistic with H _ _ _;
      [ iSolveTC
      | iSolveTC ||
          (let P := match goal with
                    | |- IntoPersistent _ ?P _ => P
                    end in
           fail 1 "iIntro:" P "not intuitionistic")
      | iSolveTC ||
          (let P := match goal with
                    | |- TCOr (Affine ?P) _ => P
                    end in
           fail 1 "iIntro:" P "not affine and the goal not absorbing")
      | pm_reduce;
         lazymatch goal with
         | |- False =>
               let H := pretty_ident H in
               fail 1 "iIntro:" H "not fresh"
         | _ => idtac
         end ]
   | fail 1 "iIntro: nothing to introduce" ])).
Time #[local]
Tactic Notation "iIntro" constr(H) "as" constr(p) :=
 (lazymatch p with
  | true => iIntro # H
  | _ => iIntro H
  end).
Time #[local]
Tactic Notation "iIntro" "_" :=
 (iStartProof; (first
   [ eapply tac_impl_intro_drop; [ iSolveTC |  ]
   | eapply tac_wand_intro_drop;
      [ iSolveTC
      | iSolveTC ||
          (let P := match goal with
                    | |- TCOr (Affine ?P) _ => P
                    end in
           fail 1 "iIntro:" P "not affine and the goal not absorbing")
      |  ]
   | iIntro
   (
   _
   )
   | fail 1 "iIntro: nothing to introduce" ])).
Time #[local]
Tactic Notation "iIntroForall" :=
 (lazymatch goal with
  | |- \226\136\128 _, ?P => fail
  | |- \226\136\128 _, _ => intro
  | |- let _ := _ in _ => intro
  | |- _ =>
        iStartProof;
         lazymatch goal with
         | |- envs_entails _ (\226\136\128 x, _) => let x' := fresh x in
                                         iIntro
                                         (
                                         x'
                                         )
         end
  end).
Time #[local]
Tactic Notation "iIntro" :=
 (lazymatch goal with
  | |- _ \226\134\146 ?P => intro
  | |- _ =>
        iStartProof;
         lazymatch goal with
         | |- envs_entails _ (_ -\226\136\151 _) =>
               iIntro ( ? ) || (let H := iFresh in
                                iIntro # H || iIntro H)
         | |- envs_entails _ (_ \226\134\146 _) =>
               iIntro ( ? ) || (let H := iFresh in
                                iIntro # H || iIntro H)
         end
  end).
Time #[local]
Tactic Notation "iForallRevert" ident(x) :=
 (let err x :=
   intros x; iMatchHyp
    fun H P =>
      lazymatch P with
      | context [ x ] =>
          let H := pretty_ident H in
          fail 2 "iRevert:" x "is used in hypothesis" H
      end
  in
  iStartProof; (first
   [ let A := type of x in
     idtac | fail 1 "iRevert:" x "not in scope" ]);
   (let A := type of x in
    lazymatch type of A with
    | Prop => revert x; (first [ apply tac_pure_revert | err x ])
    | _ => revert x; (first [ apply tac_forall_revert | err x ])
    end)).
Time
Tactic Notation "iRevertHyp" constr(H) "with" tactic1(tac) :=
 (eapply tac_revert with H;
   [ lazymatch goal with
     | |- match envs_lookup_delete true ?i ?\206\148 with
          | _ => _
          end =>
           lazymatch eval pm_eval in (envs_lookup_delete true i \206\148)
           with
           | Some (?p, _, _) => pm_reduce; tac p
           | None =>
               let H := pretty_ident H in
               fail "iRevert:" H "not found"
           end
     end ]).
Time
Tactic Notation "iRevertHyp" constr(H) := iRevertHyp H with fun _ => idtac.
Time
Tactic Notation "iRevert" constr(Hs) :=
 (let rec go Hs :=
   lazymatch Hs with
   | [] => idtac
   | ESelPure :: ?Hs =>
       repeat match goal with
              | x:_ |- _ => revert x
              end; go Hs
   | ESelIdent _ ?H :: ?Hs => iRevertHyp H; go Hs
   end
  in
  iStartProof; (let Hs := iElaborateSelPat Hs in
                go Hs)).
Time Tactic Notation "iRevert" "(" ident(x1) ")" := iForallRevert x1.
Time
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ")" :=
 (iForallRevert x2; iRevert ( x1 )).
Time
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ")" :=
 (iForallRevert x3; iRevert ( x1 x2 )).
Time
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")" :=
 (iForallRevert x4; iRevert ( x1 x2 x3 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ")" :=
 (iForallRevert x5; iRevert ( x1 x2 x3 x4 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ")" := (iForallRevert x6; iRevert ( x1 x2 x3 x4 x5 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ")" := (iForallRevert x7; iRevert ( x1 x2 x3 x4 x5 x6 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ")" :=
 (iForallRevert x8; iRevert ( x1 x2 x3 x4 x5 x6 x7 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ")" :=
 (iForallRevert x9; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ")" :=
 (iForallRevert x10; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) 
 ")" := (iForallRevert x11; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) 
 ")" := (iForallRevert x12; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) ident(x13)
 ")" :=
 (iForallRevert x13; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) ident(x13)
 ident(x14) ")" :=
 (iForallRevert x14; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) ident(x13)
 ident(x14) ident(x15) ")" :=
 (iForallRevert x15; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
   )).
Time
Tactic Notation "iRevert" "(" ident(x1) ")" constr(Hs) :=
 (iRevert Hs; iRevert ( x1 )).
Time
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ")" constr(Hs) :=
 (iRevert Hs; iRevert ( x1 x2 )).
Time
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ")" constr(Hs) :=
 (iRevert Hs; iRevert ( x1 x2 x3 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")" constr(Hs) :=
 (iRevert Hs; iRevert ( x1 x2 x3 x4 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) 
 ")" constr(Hs) := (iRevert Hs; iRevert ( x1 x2 x3 x4 x5 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ")" constr(Hs) := (iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ")" constr(Hs) := (iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ")" constr(Hs) :=
 (iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ")" constr(Hs) :=
 (iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ")" constr(Hs) :=
 (iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) 
 ")" constr(Hs) :=
 (iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) 
 ")" constr(Hs) :=
 (iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) ident(x13)
 ")" constr(Hs) :=
 (iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) ident(x13)
 ident(x14) ")" constr(Hs) :=
 (iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 )).
Time
Tactic Notation
 "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) ident(x13)
 ident(x14) ident(x15) ")" constr(Hs) :=
 (iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 )).
Time
Record iTrm {X} {As} {S} :=
 ITrm {itrm : X; itrm_vars : hlist As; itrm_hyps : S}.
Time Arguments ITrm {_} {_} {_} _ _ _.
Time
Notation "( H $! x1 .. xn )" := (ITrm H (hcons x1 .. (hcons xn hnil) ..) "")
  (at level 0, x1, xn  at level 9).
Time
Notation "( H $! x1 .. xn 'with' pat )" :=
  (ITrm H (hcons x1 .. (hcons xn hnil) ..) pat)
  (at level 0, x1, xn  at level 9).
Time Notation "( H 'with' pat )" := (ITrm H hnil pat) (at level 0).
Time #[local]
Ltac
 iIntoEmpValid t :=
  let go_specialize t tT :=
   lazymatch tT with
   | ?P \226\134\146 ?Q =>
       let H := fresh in
       assert (H : P); [  | iIntoEmpValid ltac:((t H)); clear H ]
   | \226\136\128 _ : ?T, _ =>
       let e := fresh in
       evar ( e : id T );
        (let e' := eval unfold e in e in
         clear e; iIntoEmpValid (t e'))
   end
  in
  let tT := type of t in
  first
  [ let tT' := eval hnf in tT in
    go_specialize t tT'
  | let tT' := eval cbv zeta in tT in
    go_specialize t tT'
  | let tT' := eval cbv zeta in tT in
    notypeclasses refine (as_emp_valid_1 tT _ _);
     [ iSolveTC || fail 1 "iPoseProof: not a BI assertion" | exact t ] ].
Time
Tactic Notation "iPoseProofCoreHyp" constr(H) "as" constr(Hnew) :=
 (let \206\148 := iGetCtx in
  eapply tac_pose_proof_hyp with H Hnew; pm_reduce;
   lazymatch goal with
   | |- False =>
         let lookup := pm_eval (envs_lookup_delete false H \206\148) in
         lazymatch lookup with
         | None =>
             let H := pretty_ident H in
             fail "iPoseProof:" H "not found"
         | _ =>
             let Hnew := pretty_ident Hnew in
             fail "iPoseProof:" Hnew "not fresh"
         end
   | _ => idtac
   end).
Time
Tactic Notation "iPoseProofCoreLem" constr(lem) "as" tactic3(tac) :=
 (let Hnew := iFresh in
  eapply tac_pose_proof with Hnew _;
   [ iIntoEmpValid lem
   | pm_reduce;
      lazymatch goal with
      | |- False =>
            let Hnew := pretty_ident Hnew in
            fail "iPoseProof:" Hnew "not fresh"
      | _ => tac Hnew
      end ]; try iSolveTC).
Time #[local]
Ltac
 iSpecializeArgs_go H xs :=
  lazymatch xs with
  | hnil => idtac
  | hcons ?x ?xs =>
      notypeclasses refine (tac_forall_specialize _ H _ _ _ _ _ _ _);
       [ pm_reflexivity ||
           (let H := pretty_ident H in
            fail "iSpecialize:" H "not found")
       | iSolveTC ||
           (let P := match goal with
                     | |- IntoForall ?P _ => P
                     end in
            fail "iSpecialize: cannot instantiate" P "with" x)
       | lazymatch goal with
         | |- \226\136\131 _ : ?A, _ => notypeclasses refine (@ex_intro A _ x _)
         end; [ shelve.. | pm_reduce; iSpecializeArgs_go H xs ] ]
  end.
Time #[local]
Tactic Notation "iSpecializeArgs" constr(H) open_constr(xs) :=
 (iSpecializeArgs_go H xs).
Time
Ltac
 iSpecializePat_go H1 pats :=
  let solve_to_wand H1 :=
   iSolveTC ||
     (let P := match goal with
               | |- IntoWand _ _ ?P _ _ => P
               end in
      fail "iSpecialize:" P "not an implication/wand")
  in
  let solve_done d :=
   lazymatch d with
   | true =>
       done ||
         (let Q := match goal with
                   | |- envs_entails _ ?Q => Q
                   end in
          fail "iSpecialize: cannot solve" Q "using done")
   | false => idtac
   end
  in
  let \206\148 := iGetCtx in
  lazymatch pats with
  | [] => idtac
  | SForall :: ?pats =>
      idtac
       "[IPM] The * specialization pattern is deprecated because it is applied implicitly.";
       iSpecializePat_go H1 pats
  | SIdent ?H2 [] :: ?pats =>
      notypeclasses refine
       (tac_specialize false _ H2 _ H1 _ _ _ _ _ _ _ _ _);
       [ pm_reflexivity ||
           (let H2 := pretty_ident H2 in
            fail "iSpecialize:" H2 "not found")
       | pm_reflexivity ||
           (let H1 := pretty_ident H1 in
            fail "iSpecialize:" H1 "not found")
       | iSolveTC ||
           (let P := match goal with
                     | |- IntoWand _ _ ?P ?Q _ => P
                     end in
            let Q := match goal with
                     | |- IntoWand _ _ ?P ?Q _ => Q
                     end in
            fail "iSpecialize: cannot instantiate" P "with" Q)
       | pm_reduce; iSpecializePat_go H1 pats ]
  | SIdent ?H2 ?pats1 :: ?pats =>
      let H2tmp := iFresh in
      iPoseProofCoreHyp H2 as H2tmp; iRevertHyp H1 with
       fun p => iSpecializePat_go H2tmp pats1; [ .. | iIntro H1 as p ];
       [ ..
       | notypeclasses refine
          (tac_specialize true _ H2tmp _ H1 _ _ _ _ _ _ _ _ _);
          [ pm_reflexivity ||
              (let H2tmp := pretty_ident H2tmp in
               fail "iSpecialize:" H2tmp "not found")
          | pm_reflexivity ||
              (let H1 := pretty_ident H1 in
               fail "iSpecialize:" H1 "not found")
          | iSolveTC ||
              (let P := match goal with
                        | |- IntoWand _ _ ?P ?Q _ => P
                        end in
               let Q := match goal with
                        | |- IntoWand _ _ ?P ?Q _ => Q
                        end in
               fail "iSpecialize: cannot instantiate" P "with" Q)
          | pm_reduce; iSpecializePat_go H1 pats ] ]
  | SPureGoal ?d :: ?pats =>
      notypeclasses refine
       (tac_specialize_assert_pure _ H1 _ _ _ _ _ _ _ _ _ _ _ _);
       [ pm_reflexivity ||
           (let H1 := pretty_ident H1 in
            fail "iSpecialize:" H1 "not found")
       | solve_to_wand H1
       | iSolveTC ||
           (let Q := match goal with
                     | |- FromPure _ ?Q _ => Q
                     end in
            fail "iSpecialize:" Q "not pure")
       | solve_done d
       | pm_reduce; iSpecializePat_go H1 pats ]
  | SGoal (SpecGoal GIntuitionistic false ?Hs_frame [] ?d) :: ?pats =>
      notypeclasses refine
       (tac_specialize_assert_intuitionistic _ H1 _ _ _ _ _ _ _ _ _ _ _ _);
       [ pm_reflexivity ||
           (let H1 := pretty_ident H1 in
            fail "iSpecialize:" H1 "not found")
       | solve_to_wand H1
       | iSolveTC ||
           (let Q := match goal with
                     | |- Persistent ?Q => Q
                     end in
            fail "iSpecialize:" Q "not persistent")
       | iSolveTC
       | pm_reduce; iFrame Hs_frame; solve_done d
       | pm_reduce; iSpecializePat_go H1 pats ]
  | SGoal (SpecGoal GIntuitionistic _ _ _ _) :: ?pats =>
      fail "iSpecialize: cannot select hypotheses for intuitionistic premise"
  | SGoal (SpecGoal ?m ?lr ?Hs_frame ?Hs ?d) :: ?pats =>
      let Hs' := eval compute in (if lr then Hs else Hs_frame ++ Hs) in
      notypeclasses refine
       (tac_specialize_assert _ H1 _ lr Hs' _ _ _ _ _ _ _ _ _);
       [ pm_reflexivity ||
           (let H1 := pretty_ident H1 in
            fail "iSpecialize:" H1 "not found")
       | solve_to_wand H1
       | lazymatch m with
         | GSpatial => class_apply add_modal_id
         | GModal => iSolveTC || fail "iSpecialize: goal not a modality"
         end
       | pm_reduce;
          lazymatch goal with
          | |- False =>
                let Hs' := iMissingHypsCore \206\148 Hs' in
                fail "iSpecialize: hypotheses" Hs' "not found"
          | _ =>
              notypeclasses refine (conj _ _);
               [ iFrame Hs_frame; solve_done d | iSpecializePat_go H1 pats ]
          end ]
  | SAutoFrame GIntuitionistic :: ?pats =>
      notypeclasses refine
       (tac_specialize_assert_intuitionistic _ H1 _ _ _ _ _ _ _ _ _ _ _ _);
       [ pm_reflexivity ||
           (let H1 := pretty_ident H1 in
            fail "iSpecialize:" H1 "not found")
       | solve_to_wand H1
       | iSolveTC ||
           (let Q := match goal with
                     | |- Persistent ?Q => Q
                     end in
            fail "iSpecialize:" Q "not persistent")
       | pm_reduce; (solve [ iFrame "\226\136\151 #" ])
       | pm_reduce; iSpecializePat_go H1 pats ]
  | SAutoFrame ?m :: ?pats =>
      notypeclasses refine
       (tac_specialize_frame _ H1 _ _ _ _ _ _ _ _ _ _ _ _);
       [ pm_reflexivity ||
           (let H1 := pretty_ident H1 in
            fail "iSpecialize:" H1 "not found")
       | solve_to_wand H1
       | lazymatch m with
         | GSpatial => class_apply add_modal_id
         | GModal => iSolveTC || fail "iSpecialize: goal not a modality"
         end
       | pm_reduce; (first
          [ notypeclasses
          refine
          (tac_unlock_emp _ _ _)
          | notypeclasses
          refine
          (tac_unlock_True _ _ _)
          | iFrame "\226\136\151 #"; notypeclasses refine (tac_unlock _ _ _)
          | fail "iSpecialize: premise cannot be solved by framing" ])
       | exact
       eq_refl ]; iIntro H1; iSpecializePat_go H1 pats
  end.
Time #[local]
Tactic Notation "iSpecializePat" open_constr(H) constr(pat) :=
 (let pats := spec_pat.parse pat in
  iSpecializePat_go H pats).
Time
Tactic Notation
 "iSpecializeCore" open_constr(H) "with" open_constr(xs) open_constr(pat)
 "as" constr(p) :=
 (let p := intro_pat_intuitionistic p in
  let pat := spec_pat.parse pat in
  let H := lazymatch type of H with
           | string => INamed H
           | _ => H
           end in
  iSpecializeArgs H xs;
   [ ..
   | lazymatch type of H with
     | ident =>
         let pat := spec_pat.parse pat in
         lazymatch
         eval compute in
         (p && bool_decide (pat \226\137\160 []) && negb (existsb spec_pat_modal pat))
         with
         | true =>
             lazymatch iTypeOf H with
             | Some (?q, _) =>
                 let PROP := iBiOfGoal in
                 lazymatch eval compute in (q || tc_to_bool (BiAffine PROP))
                 with
                 | true =>
                     notypeclasses refine
                      (tac_specialize_intuitionistic_helper _ H _ _ _ _ _ _ _
                         _ _ _);
                      [ pm_reflexivity
                      | pm_reduce; iSolveTC
                      | iSpecializePat H pat;
                         [ ..
                         | notypeclasses refine
                            (tac_specialize_intuitionistic_helper_done _ H _
                               _ _); pm_reflexivity ]
                      | iSolveTC ||
                          (let Q :=
                            match goal with
                            | |- IntoPersistent _ ?Q _ => Q
                            end
                           in
                           fail "iSpecialize:" Q "not persistent")
                      | pm_reduce ]
                 | false => iSpecializePat H pat
                 end
             | None =>
                 let H := pretty_ident H in
                 fail "iSpecialize:" H "not found"
             end
         | false => iSpecializePat H pat
         end
     | _ =>
         fail "iSpecialize:" H
          "should be a hypothesis, use iPoseProof instead"
     end ]).
Time
Tactic Notation "iSpecializeCore" open_constr(t) "as" constr(p) :=
 (lazymatch type of t with
  | string => iSpecializeCore t with hnil "" as p
  | ident => iSpecializeCore t with hnil "" as p
  | _ =>
      lazymatch t with
      | ITrm ?H ?xs ?pat => iSpecializeCore H with xs pat as p
      | _ => fail "iSpecialize:" t "should be a proof mode term"
      end
  end).
Time
Tactic Notation "iSpecialize" open_constr(t) := iSpecializeCore t as false.
Time
Tactic Notation "iSpecialize" open_constr(t) "as" "#" := iSpecializeCore t as
 true.
Time
Tactic Notation "iPoseProofCore" open_constr(lem) "as" constr(p) tactic3(tac)
 :=
 (iStartProof;
   (let t := lazymatch lem with
             | ITrm ?t ?xs ?pat => t
             | _ => lem
             end in
    let t := lazymatch type of t with
             | string => INamed t
             | _ => t
             end in
    let spec_tac Htmp :=
     lazymatch lem with
     | ITrm _ ?xs ?pat => iSpecializeCore (ITrm Htmp xs pat) as p
     | _ => idtac
     end
    in
    lazymatch type of t with
    | ident =>
        let Htmp := iFresh in
        iPoseProofCoreHyp t as Htmp; spec_tac Htmp; [ .. | tac Htmp ]
    | _ => iPoseProofCoreLem t as
    fun Htmp => spec_tac Htmp; [ .. | tac Htmp ]
    end)).
Time #[local]
Ltac
 iApplyHypExact H := first
 [ eapply tac_assumption with H _ _;
    [ pm_reflexivity || fail 1 | iSolveTC || fail 1 | pm_reduce; iSolveTC ]
 | lazymatch iTypeOf H with
   | Some (_, ?Q) =>
       fail 2 "iApply:" Q
        "not absorbing and the remaining hypotheses not affine"
   end ].
Time #[local]
Ltac
 iApplyHypLoop H := first
 [ eapply tac_apply with H _ _ _;
    [ pm_reflexivity | iSolveTC | pm_reduce; pm_prettify ]
 | <ssreflect_plugin::ssrtclseq@0>
 iSpecializePat
 H
 "[]"
 ;
 last 
 iApplyHypLoop H ].
Time
Tactic Notation "iApplyHyp" constr(H) := (first
 [ iApplyHypExact H
 | iApplyHypLoop H
 | lazymatch iTypeOf H with
   | Some (_, ?Q) => fail 1 "iApply: cannot apply" Q
   end ]).
Time
Tactic Notation "iApply" open_constr(lem) := iPoseProofCore lem as false
 fun H => iApplyHyp H.
Time
Tactic Notation "iLeft" :=
 (iStartProof; eapply tac_or_l;
   [ iSolveTC ||
       (let P := match goal with
                 | |- FromOr ?P _ _ => P
                 end in
        fail "iLeft:" P "not a disjunction")
   |  ]).
Time
Tactic Notation "iRight" :=
 (iStartProof; eapply tac_or_r;
   [ iSolveTC ||
       (let P := match goal with
                 | |- FromOr ?P _ _ => P
                 end in
        fail "iRight:" P "not a disjunction")
   |  ]).
Time
Tactic Notation "iOrDestruct" constr(H) "as" constr(H1) constr(H2) :=
 (eapply tac_or_destruct with H _ H1 H2 _ _ _;
   [ pm_reflexivity ||
       (let H := pretty_ident H in
        fail "iOrDestruct:" H "not found")
   | iSolveTC ||
       (let P := match goal with
                 | |- IntoOr ?P _ _ => P
                 end in
        fail "iOrDestruct: cannot destruct" P)
   | pm_reduce;
      lazymatch goal with
      | |- False =>
            let H1 := pretty_ident H1 in
            let H2 := pretty_ident H2 in
            fail "iOrDestruct:" H1 "or" H2 "not fresh"
      | _ => split
      end ]).
Time
Tactic Notation "iSplit" :=
 (iStartProof; eapply tac_and_split;
   [ iSolveTC ||
       (let P := match goal with
                 | |- FromAnd ?P _ _ => P
                 end in
        fail "iSplit:" P "not a conjunction")
   | 
   |  ]).
Time
Tactic Notation "iSplitL" constr(Hs) :=
 (iStartProof;
   (let Hs := words Hs in
    let Hs := eval vm_compute in (INamed <$> Hs) in
    let \206\148 := iGetCtx in
    eapply tac_sep_split with Left Hs _ _;
     [ iSolveTC ||
         (let P := match goal with
                   | |- FromSep ?P _ _ => P
                   end in
          fail "iSplitL:" P "not a separating conjunction")
     | pm_reduce;
        lazymatch goal with
        | |- False =>
              let Hs := iMissingHypsCore \206\148 Hs in
              fail "iSplitL: hypotheses" Hs "not found"
        | _ => split; [  |  ]
        end ])).
Time
Tactic Notation "iSplitR" constr(Hs) :=
 (iStartProof;
   (let Hs := words Hs in
    let Hs := eval vm_compute in (INamed <$> Hs) in
    let \206\148 := iGetCtx in
    eapply tac_sep_split with Right Hs _ _;
     [ iSolveTC ||
         (let P := match goal with
                   | |- FromSep ?P _ _ => P
                   end in
          fail "iSplitR:" P "not a separating conjunction")
     | pm_reduce;
        lazymatch goal with
        | |- False =>
              let Hs := iMissingHypsCore \206\148 Hs in
              fail "iSplitR: hypotheses" Hs "not found"
        | _ => split; [  |  ]
        end ])).
Time Tactic Notation "iSplitL" := iSplitR "".
Time Tactic Notation "iSplitR" := iSplitL "".
Time #[local]
Tactic Notation "iAndDestruct" constr(H) "as" constr(H1) constr(H2) :=
 (eapply tac_and_destruct with H _ H1 H2 _ _ _;
   [ pm_reflexivity ||
       (let H := pretty_ident H in
        fail "iAndDestruct:" H "not found")
   | pm_reduce;
      iSolveTC ||
        (let P :=
          lazymatch goal with
          | |- IntoSep ?P _ _ => P
          | |- IntoAnd _ ?P _ _ => P
          end
         in
         fail "iAndDestruct: cannot destruct" P)
   | pm_reduce;
      lazymatch goal with
      | |- False =>
            let H1 := pretty_ident H1 in
            let H2 := pretty_ident H2 in
            fail "iAndDestruct:" H1 "or" H2 "not fresh"
      | _ => idtac
      end ]).
Time #[local]
Tactic Notation "iAndDestructChoice" constr(H) "as" constr(d) constr(H') :=
 (eapply tac_and_destruct_choice with H _ d H' _ _ _;
   [ pm_reflexivity || fail "iAndDestructChoice:" H "not found"
   | pm_reduce;
      iSolveTC ||
        (let P := match goal with
                  | |- TCOr (IntoAnd _ ?P _ _) _ => P
                  end in
         fail "iAndDestructChoice: cannot destruct" P)
   | pm_reduce;
      lazymatch goal with
      | |- False =>
            let H' := pretty_ident H' in
            fail "iAndDestructChoice:" H' "not fresh"
      | _ => idtac
      end ]).
Time
Tactic Notation "iExists" uconstr(x1) :=
 (iStartProof; eapply tac_exist;
   [ iSolveTC ||
       (let P := match goal with
                 | |- FromExist ?P _ => P
                 end in
        fail "iExists:" P "not an existential")
   | pm_prettify; eexists x1 ]).
Time
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) :=
 (iExists x1; iExists x2).
Time
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) :=
 (iExists x1; iExists x2 , x3).
Time
Tactic Notation
 "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) "," uconstr(x4) :=
 (iExists x1; iExists x2 , x3 , x4).
Time
Tactic Notation
 "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) 
 "," uconstr(x4) "," uconstr(x5) := (iExists x1; iExists x2 , x3 , x4 , x5).
Time
Tactic Notation
 "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) 
 "," uconstr(x4) "," uconstr(x5) "," uconstr(x6) :=
 (iExists x1; iExists x2 , x3 , x4 , x5 , x6).
Time
Tactic Notation
 "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) 
 "," uconstr(x4) "," uconstr(x5) "," uconstr(x6) "," uconstr(x7) :=
 (iExists x1; iExists x2 , x3 , x4 , x5 , x6 , x7).
Time
Tactic Notation
 "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) 
 "," uconstr(x4) "," uconstr(x5) "," uconstr(x6) "," uconstr(x7) 
 "," uconstr(x8) := (iExists x1; iExists x2 , x3 , x4 , x5 , x6 , x7 , x8).
Time #[local]
Tactic Notation
 "iExistDestruct" constr(H) "as" simple_intropattern(x) constr(Hx) :=
 (eapply tac_exist_destruct with H _ Hx _ _;
   [ pm_reflexivity ||
       (let H := pretty_ident H in
        fail "iExistDestruct:" H "not found")
   | iSolveTC ||
       (let P := match goal with
                 | |- IntoExist ?P _ => P
                 end in
        fail "iExistDestruct: cannot destruct" P)
   |  ];
   (let y := fresh in
    intros y; pm_reduce;
     match goal with
     | |- False =>
           let Hx := pretty_ident Hx in
           fail "iExistDestruct:" Hx "not fresh"
     | _ => revert y; intros x
     end)).
Time
Tactic Notation "iModIntro" uconstr(sel) :=
 (iStartProof; notypeclasses refine
   (tac_modal_intro _ sel _ _ _ _ _ _ _ _ _ _ _ _ _);
   [ iSolveTC || fail "iModIntro: the goal is not a modality"
   | iSolveTC ||
       (let s :=
         lazymatch goal with
         | |- IntoModalIntuitionisticEnv _ _ _ ?s => s
         end
        in
        lazymatch eval hnf in s with
        | MIEnvForall ?C =>
            fail "iModIntro: intuitionistic context does not satisfy" C
        | MIEnvIsEmpty =>
            fail "iModIntro: intuitionistic context is non-empty"
        end)
   | iSolveTC ||
       (let s :=
         lazymatch goal with
         | |- IntoModalSpatialEnv _ _ _ ?s _ => s
         end
        in
        lazymatch eval hnf in s with
        | MIEnvForall ?C =>
            fail "iModIntro: spatial context does not satisfy" C
        | MIEnvIsEmpty => fail "iModIntro: spatial context is non-empty"
        end)
   | pm_reduce;
      iSolveTC ||
        fail
         "iModIntro: cannot filter spatial context when goal is not absorbing"
   | pm_prettify ]).
Time Tactic Notation "iModIntro" := iModIntro _.
Time Tactic Notation "iAlways" := iModIntro.
Time Tactic Notation "iNext" open_constr(n) := iModIntro (\226\150\183^n _)%I.
Time Tactic Notation "iNext" := iModIntro (\226\150\183^_ _)%I.
Time
Tactic Notation "iModCore" constr(H) :=
 (eapply tac_modal_elim with H _ _ _ _ _ _;
   [ pm_reflexivity || fail "iMod:" H "not found"
   | iSolveTC ||
       (let P := match goal with
                 | |- ElimModal _ _ _ ?P _ _ _ => P
                 end in
        let Q := match goal with
                 | |- ElimModal _ _ _ _ _ ?Q _ => Q
                 end in
        fail "iMod: cannot eliminate modality" P "in" Q)
   | iSolveSideCondition
   | pm_reduce; pm_prettify ]).
Time #[local]
Ltac
 iDestructHypGo Hz pat :=
  lazymatch pat with
  | IFresh =>
      lazymatch Hz with
      | IAnon _ => idtac
      | INamed ?Hz => let Hz' := iFresh in
                      iRename
                      Hz
                      into
                      Hz'
      end
  | IDrop => iClearHyp Hz
  | IFrame => iFrameHyp Hz
  | IIdent ?y => iRename Hz into y
  | IList [[]] => iExFalso; iExact Hz
  | IList [[?pat1; IDrop]] =>
      iAndDestructChoice Hz as Left Hz; iDestructHypGo Hz pat1
  | IList [[IDrop; ?pat2]] =>
      iAndDestructChoice Hz as Right Hz; iDestructHypGo Hz pat2
  | IList [[?pat1; ?pat2]] =>
      let Hy := iFresh in
      iAndDestruct Hz as Hz Hy; iDestructHypGo Hz pat1;
       iDestructHypGo Hy pat2
  | IList [[?pat1]; [?pat2]] =>
      iOrDestruct Hz as Hz Hz;
       [ iDestructHypGo Hz pat1 | iDestructHypGo Hz pat2 ]
  | IPureElim => iPure Hz as ?
  | IRewrite Right => iPure Hz as ->
  | IRewrite Left => iPure Hz as <-
  | IAlwaysElim ?pat =>
      iIntuitionistic Hz; iDestructHypGo Hz pat
  | IModalElim ?pat => iModCore Hz; iDestructHypGo Hz pat
  | _ => fail "iDestruct:" pat "invalid"
  end.
Time #[local]
Ltac
 iDestructHypFindPat Hgo pat found pats :=
  lazymatch pats with
  | [] =>
      lazymatch found with
      | true => pm_prettify
      | false =>
          fail "iDestruct:" pat
           "should contain exactly one proper introduction pattern"
      end
  | ISimpl :: ?pats =>
      simpl; iDestructHypFindPat Hgo pat found pats
  | IClear ?H :: ?pats =>
      iClear H; iDestructHypFindPat Hgo pat found pats
  | IClearFrame ?H :: ?pats =>
      iFrame H; iDestructHypFindPat Hgo pat found pats
  | ?pat :: ?pats =>
      lazymatch found with
      | false =>
          iDestructHypGo Hgo pat; iDestructHypFindPat Hgo pat true pats
      | true =>
          fail "iDestruct:" pat
           "should contain exactly one proper introduction pattern"
      end
  end.
Time
Tactic Notation "iDestructHyp" constr(H) "as" constr(pat) :=
 (let pats := intro_pat.parse pat in
  iDestructHypFindPat H pat false pats).
Time
Tactic Notation
 "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1) ")" constr(pat) :=
 (iExistDestruct H as x1 H; iDestructHyp H as @pat).
Time
Tactic Notation
 "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) ")" constr(pat) :=
 (iExistDestruct H as x1 H; iDestructHyp H as ( x2 ) pat).
Time
Tactic Notation
 "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
 (iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 ) pat).
Time
Tactic Notation
 "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) 
 ")" constr(pat) :=
 (iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 ) pat).
Time
Tactic Notation
 "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) ")" constr(pat) :=
 (iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 ) pat).
Time
Tactic Notation
 "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
 (iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 ) pat).
Time
Tactic Notation
 "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) 
 ")" constr(pat) :=
 (iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 ) pat).
Time
Tactic Notation
 "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) ")" constr(pat) :=
 (iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 ) pat).
Time
Tactic Notation
 "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
 (iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 x9 ) pat).
Time
Tactic Notation
 "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) 
 ")" constr(pat) :=
 (iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 x9 x10 )
   pat).
Time
Tactic Notation "iCombine" constr(Hs) "as" constr(pat) :=
 (let Hs := words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  let H := iFresh in
  let \206\148 := iGetCtx in
  eapply tac_combine with _ _ Hs _ _ H _;
   [ pm_reflexivity ||
       (let Hs := iMissingHypsCore \206\148 Hs in
        fail "iCombine: hypotheses" Hs "not found")
   | iSolveTC
   | pm_reflexivity ||
       (let H := pretty_ident H in
        fail "iCombine:" H "not fresh")
   | iDestructHyp
   H
   as
   pat ]).
Time
Tactic Notation "iCombine" constr(H1) constr(H2) "as" constr(pat) := iCombine
 [H1; H2] as pat.
Time
Ltac
 iIntros_go pats startproof :=
  lazymatch pats with
  | [] =>
      lazymatch startproof with
      | true => iStartProof
      | false => idtac
      end
  | IPureElim :: ?pats =>
      iIntro ( ? ); iIntros_go pats startproof
  | IAlwaysElim (IIdent ?H) :: ?pats =>
      iIntro # H; iIntros_go pats false
  | IDrop :: ?pats =>
      iIntro _; iIntros_go pats startproof
  | IIdent ?H :: ?pats =>
      iIntro H; iIntros_go pats startproof
  | IPureIntro :: ?pats =>
      iPureIntro; iIntros_go pats false
  | IAlwaysIntro :: ?pats =>
      iAlways; iIntros_go pats false
  | IModalIntro :: ?pats =>
      iModIntro; iIntros_go pats false
  | IForall :: ?pats =>
      repeat iIntroForall; iIntros_go pats startproof
  | IAll :: ?pats =>
      repeat iIntroForall || iIntro; iIntros_go pats startproof
  | ISimpl :: ?pats => simpl; iIntros_go pats startproof
  | IClear ?H :: ?pats =>
      iClear H; iIntros_go pats false
  | IClearFrame ?H :: ?pats =>
      iFrame H; iIntros_go pats false
  | IDone :: ?pats =>
      try done; iIntros_go pats startproof
  | IAlwaysElim ?pat :: ?pats =>
      let H := iFresh in
      iIntro # H; iDestructHyp H as pat; iIntros_go pats false
  | ?pat :: ?pats =>
      let H := iFresh in
      iIntro H; iDestructHyp H as pat; iIntros_go pats false
  end.
Time
Tactic Notation "iIntros" constr(pat) :=
 (let pats := intro_pat.parse pat in
  iIntros_go pats true).
Time Tactic Notation "iIntros" := iIntros [IAll].
Time
Tactic Notation "iIntros" "(" simple_intropattern(x1) ")" := iIntro ( x1 ).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2) ")" :=
 (iIntros ( x1 ); iIntro ( x2 )).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) ")" := (iIntros ( x1 x2 ); iIntro ( x3 )).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) ")" :=
 (iIntros ( x1 x2 x3 ); iIntro ( x4 )).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) 
 ")" := (iIntros ( x1 x2 x3 x4 ); iIntro ( x5 )).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) ")" := (iIntros ( x1 x2 x3 x4 x5 ); iIntro ( x6 )).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) ")" :=
 (iIntros ( x1 x2 x3 x4 x5 x6 ); iIntro ( x7 )).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8) 
 ")" := (iIntros ( x1 x2 x3 x4 x5 x6 x7 ); iIntro ( x8 )).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) ")" :=
 (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ); iIntro ( x9 )).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) 
 ")" := (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ); iIntro ( x10 )).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 ")" := (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ); iIntro ( x11 )).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) ")" :=
 (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ); iIntro ( x12 )).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) simple_intropattern(x13) 
 ")" := (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ); iIntro ( x13 )).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) simple_intropattern(x13) simple_intropattern(x14)
 ")" :=
 (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ); iIntro ( x14 )).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) simple_intropattern(x13) simple_intropattern(x14)
 simple_intropattern(x15) ")" :=
 (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ); iIntro ( x15 )).
Time
Tactic Notation "iIntros" "(" simple_intropattern(x1) ")" constr(p) :=
 (iIntros ( x1 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2) ")" constr(p)
 := (iIntros ( x1 x2 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) ")" constr(p) := (iIntros ( x1 x2 x3 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) ")" constr(p) :=
 (iIntros ( x1 x2 x3 x4 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) 
 ")" constr(p) := (iIntros ( x1 x2 x3 x4 x5 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) ")" constr(p) :=
 (iIntros ( x1 x2 x3 x4 x5 x6 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) ")" constr(p) :=
 (iIntros ( x1 x2 x3 x4 x5 x6 x7 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8) 
 ")" constr(p) := (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) ")" constr(p) :=
 (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) 
 ")" constr(p) := (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 ")" constr(p) := (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) ")" constr(p) :=
 (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) simple_intropattern(x13) 
 ")" constr(p) :=
 (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) simple_intropattern(x13) simple_intropattern(x14)
 ")" constr(p) :=
 (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ); iIntros p).
Time
Tactic Notation
 "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) simple_intropattern(x13) simple_intropattern(x14)
 simple_intropattern(x15) ")" constr(p) :=
 (iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ); iIntros p).
Time
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1) ")" :=
 (iIntros p; iIntros ( x1 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2) ")"
 := (iIntros p; iIntros ( x1 x2 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) ")" := (iIntros p; iIntros ( x1 x2 x3 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) ")" :=
 (iIntros p; iIntros ( x1 x2 x3 x4 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) 
 ")" := (iIntros p; iIntros ( x1 x2 x3 x4 x5 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) ")" := (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) ")" :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8) 
 ")" := (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) ")" :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) 
 ")" := (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 ")" := (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) ")" :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) simple_intropattern(x13) 
 ")" := (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) simple_intropattern(x13) simple_intropattern(x14)
 ")" :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) simple_intropattern(x13) simple_intropattern(x14)
 simple_intropattern(x15) ")" :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 )).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) ")" constr(p2) :=
 (iIntros p; iIntros ( x1 ); iIntros p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2) 
 ")" constr(p2) := (iIntros p; iIntros ( x1 x2 ); iIntros p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) ")" constr(p2) :=
 (iIntros p; iIntros ( x1 x2 x3 ); iIntros p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) ")" constr(p2) :=
 (iIntros p; iIntros ( x1 x2 x3 x4 ); iIntros p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) 
 ")" constr(p2) := (iIntros p; iIntros ( x1 x2 x3 x4 x5 ); iIntros p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) ")" constr(p2) :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 ); iIntros p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) ")" constr(p2) :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 ); iIntros p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8) 
 ")" constr(p2) :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ); iIntros p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) ")" constr(p2) :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ); iIntros p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) 
 ")" constr(p2) :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ); iIntros p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 ")" constr(p2) :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ); iIntros p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) ")" constr(p2) :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ); iIntros p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) simple_intropattern(x13) 
 ")" constr(p2) :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ); iIntros
   p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) simple_intropattern(x13) simple_intropattern(x14)
 ")" constr(p2) :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 );
   iIntros p2).
Time
Tactic Notation
 "iIntros" constr(p) "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
 simple_intropattern(x12) simple_intropattern(x13) simple_intropattern(x14)
 simple_intropattern(x15) ")" constr(p2) :=
 (iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 );
   iIntros p2).
Time
Ltac
 iRevertIntros_go Hs tac :=
  lazymatch Hs with
  | [] => tac
  | ESelPure :: ?Hs =>
      fail "iRevertIntros: % not supported"
  | ESelIdent ?p ?H :: ?Hs =>
      iRevertHyp H; iRevertIntros_go Hs tac; iIntro H as p
  end.
Time
Tactic Notation "iRevertIntros" constr(Hs) "with" tactic3(tac) :=
 (try iStartProof; (let Hs := iElaborateSelPat Hs in
                    iRevertIntros_go Hs tac)).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ")" constr(Hs) "with" tactic3(tac) :=
 iRevertIntros Hs with iRevert ( x1 ); tac; iIntros ( x1 ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ")" constr(Hs) "with" tactic3(tac)
 := iRevertIntros Hs with iRevert ( x1 x2 ); tac; iIntros ( x1 x2 ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) 
 ")" constr(Hs) "with" tactic3(tac) := iRevertIntros Hs with
 iRevert ( x1 x2 x3 ); tac; iIntros ( x1 x2 x3 ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) 
 ")" constr(Hs) "with" tactic3(tac) := iRevertIntros Hs with
 iRevert ( x1 x2 x3 x4 ); tac; iIntros ( x1 x2 x3 x4 ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) 
 ")" constr(Hs) "with" tactic3(tac) := iRevertIntros Hs with
 iRevert ( x1 x2 x3 x4 x5 ); tac; iIntros ( x1 x2 x3 x4 x5 ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ")" constr(Hs) "with" tactic3(tac) := iRevertIntros Hs with
 iRevert ( x1 x2 x3 x4 x5 x6 ); tac; iIntros ( x1 x2 x3 x4 x5 x6 ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ")" constr(Hs) "with" tactic3(tac) := iRevertIntros Hs
 with iRevert ( x1 x2 x3 x4 x5 x6 x7 ); tac; iIntros ( x1 x2 x3 x4 x5 x6 x7 ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ")" constr(Hs) "with" tactic3(tac) :=
 iRevertIntros Hs with
 iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 ); tac; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8
  ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ")" constr(Hs) 
 "with" tactic3(tac) := iRevertIntros Hs with
 iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ); tac; iIntros ( x1 x2 x3 x4 x5 x6 x7
  x8 x9 ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) 
 ")" constr(Hs) "with" tactic3(tac) := iRevertIntros Hs with
 iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ); tac; iIntros ( x1 x2 x3 x4 x5 x6
  x7 x8 x9 x10 ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) 
 ")" constr(Hs) "with" tactic3(tac) := iRevertIntros Hs with
 iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ); tac; iIntros ( x1 x2 x3 x4
  x5 x6 x7 x8 x9 x10 x11 ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) 
 ")" constr(Hs) "with" tactic3(tac) := iRevertIntros Hs with
 iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ); tac; iIntros ( x1 x2 x3
  x4 x5 x6 x7 x8 x9 x10 x11 x12 ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12)
 ident(x13) ")" constr(Hs) "with" tactic3(tac) := iRevertIntros Hs with
 iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ); tac; iIntros ( x1 x2
  x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12)
 ident(x13) ident(x14) ")" constr(Hs) "with" tactic3(tac) := iRevertIntros Hs
 with
 iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ); tac; iIntros (
  x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ).
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12)
 ident(x13) ident(x14) ident(x15) ")" constr(Hs) "with" tactic3(tac) :=
 iRevertIntros Hs with
 iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x14 ); tac; iIntros
  ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ).
Time
Tactic Notation "iRevertIntros" "with" tactic3(tac) := iRevertIntros "" with
 tac.
Time
Tactic Notation "iRevertIntros" "(" ident(x1) ")" "with" tactic3(tac) :=
 iRevertIntros ( x1 ) "" with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ")" "with" tactic3(tac) :=
 iRevertIntros ( x1 x2 ) "" with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ")" "with" tactic3(tac) :=
 iRevertIntros ( x1 x2 x3 ) "" with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) 
 ")" "with" tactic3(tac) := iRevertIntros ( x1 x2 x3 x4 ) "" with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) 
 ")" "with" tactic3(tac) := iRevertIntros ( x1 x2 x3 x4 x5 ) "" with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ")" "with" tactic3(tac) := iRevertIntros ( x1 x2 x3 x4 x5 x6 ) ""
 with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ")" "with" tactic3(tac) := iRevertIntros ( x1 x2 x3 x4
 x5 x6 x7 ) "" with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ")" "with" tactic3(tac) := iRevertIntros ( x1
 x2 x3 x4 x5 x6 x7 x8 ) "" with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ")" "with" tactic3(tac) :=
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) "" with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) 
 ")" "with" tactic3(tac) := iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 )
 "" with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) 
 ")" "with" tactic3(tac) := iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
 x11 ) "" with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) 
 ")" "with" tactic3(tac) := iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
 x11 x12 ) "" with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12)
 ident(x13) ")" "with" tactic3(tac) := iRevertIntros ( x1 x2 x3 x4 x5 x6 x7
 x8 x9 x10 x11 x12 x13 ) "" with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12)
 ident(x13) ident(x14) ")" "with" tactic3(tac) := iRevertIntros ( x1 x2 x3 x4
 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ) "" with tac.
Time
Tactic Notation
 "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
 ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12)
 ident(x13) ident(x14) ident(x15) ")" "with" tactic3(tac) := iRevertIntros (
 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ) "" with tac.
Time Class CopyDestruct {PROP : bi} (P : PROP) :={}.
Time Arguments CopyDestruct {_} _%I.
Time Hint Mode CopyDestruct + !: typeclass_instances.
Time
Instance copy_destruct_forall  {PROP : bi} {A} (\206\166 : A \226\134\146 PROP):
 (CopyDestruct (\226\136\128 x, \206\166 x)) := { }.
Time
Instance copy_destruct_impl  {PROP : bi} (P Q : PROP):
 (CopyDestruct Q \226\134\146 CopyDestruct (P \226\134\146 Q)) := { }.
Time
Instance copy_destruct_wand  {PROP : bi} (P Q : PROP):
 (CopyDestruct Q \226\134\146 CopyDestruct (P -\226\136\151 Q)) := { }.
Time
Instance copy_destruct_affinely  {PROP : bi} (P : PROP):
 (CopyDestruct P \226\134\146 CopyDestruct (<affine> P)) := { }.
Time
Instance copy_destruct_persistently  {PROP : bi} (P : PROP):
 (CopyDestruct P \226\134\146 CopyDestruct (<pers> P)) := { }.
Time
Tactic Notation "iDestructCore" open_constr(lem) "as" constr(p) tactic3(tac)
 :=
 (let ident :=
   lazymatch type of lem with
   | ident => Some lem
   | string => Some (INamed lem)
   | iTrm =>
       lazymatch lem with
       | @iTrm ident ?H _ _ => Some H
       | @iTrm string ?H _ _ => Some (INamed H)
       | _ => @None ident
       end
   | _ => @None ident
   end
  in
  let intro_destruct n :=
   let rec go n' :=
    lazymatch n' with
    | 0 => fail "iDestruct: cannot introduce" n "hypotheses"
    | 1 => repeat iIntroForall; (let H := iFresh in
                                 iIntro H; tac H)
    | S ?n' => repeat iIntroForall; (let H := iFresh in
                                     iIntro H; go n')
    end
   in
   intros; go n
  in
  lazymatch type of lem with
  | nat => intro_destruct lem
  | Z => let n := eval compute in (Z.to_nat lem) in
         intro_destruct n
  | _ =>
      iStartProof;
       lazymatch ident with
       | None => iPoseProofCore lem as p tac
       | Some ?H =>
           lazymatch iTypeOf H with
           | None =>
               let H := pretty_ident H in
               fail "iDestruct:" H "not found"
           | Some (true, ?P) =>
               tryif (let dummy := constr:(_ : CopyDestruct P) in
                      idtac) then iPoseProofCore lem as p tac else
                (iSpecializeCore lem as p; [ .. | tac H ]) 
           | Some (false, ?P) => iSpecializeCore lem as p; [ .. | tac H ]
           end
       end
  end).
Time
Tactic Notation "iDestruct" open_constr(lem) "as" constr(pat) :=
 iDestructCore lem as pat fun H => iDestructHyp H as pat.
Time
Tactic Notation
 "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1) 
 ")" constr(pat) := iDestructCore lem as pat
 fun H => iDestructHyp H as ( x1 ) pat.
Time
Tactic Notation
 "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) ")" constr(pat) := iDestructCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 ) pat.
Time
Tactic Notation
 "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
 iDestructCore lem as pat fun H => iDestructHyp H as ( x1 x2 x3 ) pat.
Time
Tactic Notation
 "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) 
 ")" constr(pat) := iDestructCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 ) pat.
Time
Tactic Notation
 "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) ")" constr(pat) := iDestructCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat.
Time
Tactic Notation
 "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
 iDestructCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat.
Time
Tactic Notation
 "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) 
 ")" constr(pat) := iDestructCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Time
Tactic Notation
 "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) ")" constr(pat) := iDestructCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Time
Tactic Notation
 "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
 iDestructCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Time
Tactic Notation
 "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) 
 ")" constr(pat) := iDestructCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.
Time
Tactic Notation
 "iDestruct" open_constr(lem) "as" "%" simple_intropattern(pat) :=
 iDestructCore lem as true fun H => iPure H as pat.
Time
Tactic Notation "iPoseProof" open_constr(lem) "as" constr(pat) :=
 iPoseProofCore lem as pat fun H => iDestructHyp H as pat.
Time
Tactic Notation
 "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1) 
 ")" constr(pat) := iPoseProofCore lem as pat
 fun H => iDestructHyp H as ( x1 ) pat.
Time
Tactic Notation
 "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) ")" constr(pat) := iPoseProofCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 ) pat.
Time
Tactic Notation
 "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
 iPoseProofCore lem as pat fun H => iDestructHyp H as ( x1 x2 x3 ) pat.
Time
Tactic Notation
 "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) 
 ")" constr(pat) := iPoseProofCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 ) pat.
Time
Tactic Notation
 "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) ")" constr(pat) := iPoseProofCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat.
Time
Tactic Notation
 "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
 iPoseProofCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat.
Time
Tactic Notation
 "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) 
 ")" constr(pat) := iPoseProofCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Time
Tactic Notation
 "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) ")" constr(pat) := iPoseProofCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Time
Tactic Notation
 "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
 iPoseProofCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Time
Tactic Notation
 "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) 
 ")" constr(pat) := iPoseProofCore lem as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.
Time
Tactic Notation "iInductionCore" tactic3(tac) "as" constr(IH) :=
 (let rec fix_ihs rev_tac :=
   lazymatch goal with
   | H:context [ envs_entails _ _ ]
     |- _ =>
         eapply (tac_revert_ih _ _ _ H _);
          [ pm_reflexivity ||
              fail
               "iInduction: spatial context not empty, this should not happen"
          | clear
          H ];
          fix_ihs
           ltac:(fun j =>
                   let IH' :=
                    eval vm_compute in
                    match j with
                    | 0%N => IH
                    | _ => IH +:+ pretty j
                    end
                   in
                   iIntros [IAlwaysElim (IIdent IH')];
                    (let j := eval vm_compute in (1 + j)%N in
                     rev_tac j))
   | _ => rev_tac 0%N
   end
  in
  tac; fix_ihs ltac:(fun _ => idtac)).
Time
Ltac
 iHypsContaining x :=
  let rec go \206\147 x Hs :=
   lazymatch \206\147 with
   | Enil => Hs
   | Esnoc ?\206\147 ?H ?Q =>
       match Q with
       | context [ x ] => go \206\147 x (H :: Hs)
       | _ => go \206\147 x Hs
       end
   end
  in
  let \206\147p := lazymatch goal with
            | |- envs_entails (Envs ?\206\147p _ _) _ => \206\147p
            end in
  let \206\147s := lazymatch goal with
            | |- envs_entails (Envs _ ?\206\147s _) _ => \206\147s
            end in
  let Hs := go \206\147p x (@nil ident) in
  go \206\147s x Hs.
Time
Tactic Notation "iInductionRevert" constr(x) constr(Hs) "with" tactic3(tac)
 := iRevertIntros Hs with iRevertIntros "\226\136\151" with
 idtac; (let Hsx := iHypsContaining x in
         iRevertIntros
         Hsx
         with
         tac).
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) :=
 iInductionRevert x "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ")" := iInductionRevert x "" with iRevertIntros ( x1
 ) "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ")" := iInductionRevert x "" with
 iRevertIntros ( x1 x2 ) "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ")" := iInductionRevert x "" with
 iRevertIntros ( x1 x2 x3 ) "" with iInductionCore 
 induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) 
 ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 ) "" with
 iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) 
 ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 x5 ) "" with
 iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) 
 ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 x5 x6 ) ""
 with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 x5
 x6 x7 ) "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ")" := iInductionRevert x "" with iRevertIntros ( x1 x2
 x3 x4 x5 x6 x7 x8 ) "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ")" := iInductionRevert x "" with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) "" with iInductionCore
 induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ")" := iInductionRevert x "" with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) "" with iInductionCore
 induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) 
 ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9
 x10 x11 ) "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) 
 ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9
 x10 x11 x12 ) "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) ident(x13)
 ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9
 x10 x11 x12 x13 ) "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) ident(x13)
 ident(x14) ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 x5
 x6 x7 x8 x9 x10 x11 x12 x13 x14 ) "" with iInductionCore 
 induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) ident(x13)
 ident(x14) ident(x15) ")" := iInductionRevert x "" with iRevertIntros ( x1
 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ) "" with iInductionCore
 induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" constr(Hs) := iInductionRevert x Hs with iInductionCore
 induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ")" constr(Hs) := iInductionRevert x Hs with
 iRevertIntros ( x1 ) "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ")" constr(Hs) := iInductionRevert x Hs
 with iRevertIntros ( x1 x2 ) "" with iInductionCore 
 induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ")" constr(Hs) :=
 iInductionRevert x Hs with iRevertIntros ( x1 x2 x3 ) "" with iInductionCore
 induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) 
 ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2 x3 x4 )
 "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) 
 ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2 x3 x4 x5
 ) "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) 
 ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2 x3 x4 x5
 x6 ) "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2
 x3 x4 x5 x6 x7 ) "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ")" constr(Hs) := iInductionRevert x Hs with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) "" with iInductionCore
 induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ")" constr(Hs) := iInductionRevert x Hs with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) "" with iInductionCore
 induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ")" constr(Hs) := iInductionRevert
 x Hs with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) "" with
 iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) 
 ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2 x3 x4 x5
 x6 x7 x8 x9 x10 x11 ) "" with iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) 
 ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2 x3 x4 x5
 x6 x7 x8 x9 x10 x11 x12 ) "" with iInductionCore 
 induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) ident(x13)
 ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2 x3 x4 x5
 x6 x7 x8 x9 x10 x11 x12 x13 ) "" with iInductionCore 
 induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) ident(x13)
 ident(x14) ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1
 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ) "" with iInductionCore
 induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
 ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ident(x12) ident(x13)
 ident(x14) ident(x15) ")" constr(Hs) := iInductionRevert x Hs with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ) "" with
 iInductionCore induction x as pat as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) := iInductionRevert x "" with iInductionCore
 induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ")" := iInductionRevert x "" with
 iRevertIntros ( x1 ) "" with iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) 
 ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 ) "" with
 iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) 
 ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 ) "" with
 iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) 
 ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 ) "" with
 iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 x5 )
 "" with iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ")" := iInductionRevert x "" with iRevertIntros ( x1 x2
 x3 x4 x5 x6 ) "" with iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ")" := iInductionRevert x "" with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 ) "" with iInductionCore
 induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ")" := iInductionRevert x "" with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) "" with iInductionCore
 induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) 
 ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9
 ) "" with iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) 
 ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9
 x10 ) "" with iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) 
 ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9
 x10 x11 ) "" with iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ")" := iInductionRevert x "" with iRevertIntros ( x1 x2 x3 x4 x5
 x6 x7 x8 x9 x10 x11 x12 ) "" with iInductionCore 
 induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ident(x13) ")" := iInductionRevert x "" with iRevertIntros ( x1
 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) "" with iInductionCore
 induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ident(x13) ident(x14) ")" := iInductionRevert x "" with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ) "" with
 iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ident(x13) ident(x14) ident(x15) ")" := iInductionRevert x ""
 with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ) ""
 with iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" constr(Hs) := iInductionRevert x Hs with
 iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ")" constr(Hs) := iInductionRevert
 x Hs with iRevertIntros ( x1 ) "" with iInductionCore
 induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) 
 ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2 ) "" with
 iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) 
 ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2 x3 ) ""
 with iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) 
 ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2 x3 x4 )
 "" with iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2
 x3 x4 x5 ) "" with iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ")" constr(Hs) := iInductionRevert x Hs with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 ) "" with iInductionCore
 induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ")" constr(Hs) := iInductionRevert x Hs with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 ) "" with iInductionCore
 induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ")" constr(Hs) := iInductionRevert x
 Hs with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) "" with iInductionCore
 induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) 
 ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2 x3 x4 x5
 x6 x7 x8 x9 ) "" with iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) 
 ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2 x3 x4 x5
 x6 x7 x8 x9 x10 ) "" with iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) 
 ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1 x2 x3 x4 x5
 x6 x7 x8 x9 x10 x11 ) "" with iInductionCore induction x as pat using u as
 IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ")" constr(Hs) := iInductionRevert x Hs with iRevertIntros ( x1
 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ) "" with iInductionCore
 induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ident(x13) ")" constr(Hs) := iInductionRevert x Hs with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) "" with
 iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ident(x13) ident(x14) ")" constr(Hs) := iInductionRevert x Hs
 with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ) ""
 with iInductionCore induction x as pat using u as IH.
Time
Tactic Notation
 "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) 
 "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ident(x13) ident(x14) ident(x15) ")" constr(Hs) :=
 iInductionRevert x Hs with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
 x11 x12 x13 x14 x15 ) "" with iInductionCore induction x as pat using u as
 IH.
Time
Tactic Notation "iL\195\182bCore" "as" constr(IH) :=
 (iStartProof; (first
   [ notypeclasses
   refine
   (tac_l\195\182b _ IH _ _ _)
   | fail 1 "iL\195\182b: not a step-indexed BI entailment" ]);
   [ reflexivity ||
       fail "iL\195\182b: spatial context not empty, this should not happen"
   | pm_reduce;
      lazymatch goal with
      | |- False => let IH := pretty_ident IH in
                    fail "iL\195\182b:" IH "not fresh"
      | _ => idtac
      end ]).
Time
Tactic Notation "iL\195\182bRevert" constr(Hs) "with" tactic3(tac) := iRevertIntros
 Hs with iRevertIntros "\226\136\151" with tac.
Time
Tactic Notation "iL\195\182b" "as" constr(IH) := iL\195\182bRevert "" with iL\195\182bCore as IH.
Time
Tactic Notation "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ")" :=
 iL\195\182bRevert "" with iRevertIntros ( x1 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ")"
 := iL\195\182bRevert "" with iRevertIntros ( x1 x2 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ")" :=
 iL\195\182bRevert "" with iRevertIntros ( x1 x2 x3 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ")" := iL\195\182bRevert "" with iRevertIntros ( x1 x2 x3 x4 ) "" with iL\195\182bCore as
 IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ")" := iL\195\182bRevert "" with iRevertIntros ( x1 x2 x3 x4 x5 ) "" with
 iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ")" := iL\195\182bRevert "" with iRevertIntros ( x1 x2 x3 x4 x5
 x6 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ")" := iL\195\182bRevert "" with iRevertIntros ( x1
 x2 x3 x4 x5 x6 x7 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ")" := iL\195\182bRevert "" with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) 
 ")" := iL\195\182bRevert "" with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) ""
 with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) 
 ")" := iL\195\182bRevert "" with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 )
 "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) 
 ")" := iL\195\182bRevert "" with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ")" := iL\195\182bRevert "" with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8
 x9 x10 x11 x12 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ident(x13) ")" := iL\195\182bRevert "" with iRevertIntros ( x1 x2 x3 x4
 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ident(x13) ident(x14) ")" := iL\195\182bRevert "" with iRevertIntros (
 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ident(x13) ident(x14) ident(x15) ")" := iL\195\182bRevert "" with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ) "" with
 iL\195\182bCore as IH.
Time
Tactic Notation "iL\195\182b" "as" constr(IH) "forall" constr(Hs) := iL\195\182bRevert Hs
 with iL\195\182bCore as IH.
Time
Tactic Notation "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ")" constr(Hs)
 := iL\195\182bRevert Hs with iRevertIntros ( x1 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ")" constr(Hs) :=
 iL\195\182bRevert Hs with iRevertIntros ( x1 x2 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) 
 ")" constr(Hs) := iL\195\182bRevert Hs with iRevertIntros ( x1 x2 x3 ) "" with
 iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ")" constr(Hs) := iL\195\182bRevert Hs with iRevertIntros ( x1 x2 x3 x4 ) "" with
 iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ")" constr(Hs) := iL\195\182bRevert Hs with iRevertIntros ( x1 x2 x3 x4
 x5 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ")" constr(Hs) := iL\195\182bRevert Hs with iRevertIntros ( x1
 x2 x3 x4 x5 x6 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ")" constr(Hs) := iL\195\182bRevert Hs with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ")" constr(Hs) := iL\195\182bRevert Hs with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) 
 ")" constr(Hs) := iL\195\182bRevert Hs with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8
 x9 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) 
 ")" constr(Hs) := iL\195\182bRevert Hs with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8
 x9 x10 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) 
 ")" constr(Hs) := iL\195\182bRevert Hs with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8
 x9 x10 x11 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ")" constr(Hs) := iL\195\182bRevert Hs with iRevertIntros ( x1 x2 x3 x4
 x5 x6 x7 x8 x9 x10 x11 x12 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ident(x13) ")" constr(Hs) := iL\195\182bRevert Hs with iRevertIntros (
 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) "" with iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ident(x13) ident(x14) ")" constr(Hs) := iL\195\182bRevert Hs with
 iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ) "" with
 iL\195\182bCore as IH.
Time
Tactic Notation
 "iL\195\182b" "as" constr(IH) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
 ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
 ident(x12) ident(x13) ident(x14) ident(x15) ")" constr(Hs) := iL\195\182bRevert Hs
 with iRevertIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ) ""
 with iL\195\182bCore as IH.
Time
Tactic Notation
 "iAssertCore" open_constr(Q) "with" constr(Hs) "as" constr(p) tactic3(tac)
 :=
 (iStartProof;
   (let pats := spec_pat.parse Hs in
    lazymatch pats with
    | [_] => idtac
    | _ =>
        fail "iAssert: exactly one specialization pattern should be given"
    end;
     (let H := iFresh in
      eapply tac_assert with H Q;
       [ pm_reduce; iSpecializeCore H with hnil pats as p; [ .. | tac H ] ]))).
Time
Tactic Notation "iAssertCore" open_constr(Q) "as" constr(p) tactic3(tac) :=
 (let p := intro_pat_intuitionistic p in
  lazymatch p with
  | true => iAssertCore Q with "[#]" as p tac
  | false => iAssertCore Q with "[]" as p tac
  end).
Time
Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as" constr(pat)
 := iAssertCore Q with Hs as pat fun H => iDestructHyp H as pat.
Time
Tactic Notation
 "iAssert" open_constr(Q) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 ")" constr(pat) := iAssertCore Q with Hs as pat
 fun H => iDestructHyp H as ( x1 ) pat.
Time
Tactic Notation
 "iAssert" open_constr(Q) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) ")" constr(pat) := iAssertCore Q with Hs as pat
 fun H => iDestructHyp H as ( x1 x2 ) pat.
Time
Tactic Notation
 "iAssert" open_constr(Q) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
 iAssertCore Q with Hs as pat fun H => iDestructHyp H as ( x1 x2 x3 ) pat.
Time
Tactic Notation
 "iAssert" open_constr(Q) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) 
 ")" constr(pat) := iAssertCore Q with Hs as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 ) pat.
Time
Tactic Notation "iAssert" open_constr(Q) "as" constr(pat) := iAssertCore Q as
 pat fun H => iDestructHyp H as pat.
Time
Tactic Notation
 "iAssert" open_constr(Q) "as" "(" simple_intropattern(x1) ")" constr(pat) :=
 iAssertCore Q as pat fun H => iDestructHyp H as ( x1 ) pat.
Time
Tactic Notation
 "iAssert" open_constr(Q) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) ")" constr(pat) := iAssertCore Q as pat
 fun H => iDestructHyp H as ( x1 x2 ) pat.
Time
Tactic Notation
 "iAssert" open_constr(Q) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
 iAssertCore Q as pat fun H => iDestructHyp H as ( x1 x2 x3 ) pat.
Time
Tactic Notation
 "iAssert" open_constr(Q) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) 
 ")" constr(pat) := iAssertCore Q as pat
 fun H => iDestructHyp H as ( x1 x2 x3 x4 ) pat.
Time
Tactic Notation
 "iAssert" open_constr(Q) "with" constr(Hs) "as" "%" simple_intropattern(pat)
 := iAssertCore Q with Hs as true fun H => iPure H as pat.
Time
Tactic Notation "iAssert" open_constr(Q) "as" "%" simple_intropattern(pat) :=
 iAssert Q with "[-]" as % pat.
Time #[local]
Ltac
 iRewriteFindPred :=
  match goal with
  | |- _ \226\138\163\226\138\162 ?\206\166 ?x =>
        generalize x;
         match goal with
         | |- \226\136\128 y, @?\206\168 y \226\138\163\226\138\162 _ => unify \206\166 \206\168; reflexivity
         end
  end.
Time #[local]
Tactic Notation "iRewriteCore" constr(lr) open_constr(lem) := iPoseProofCore
 lem as true
 fun Heq =>
   (first
    [ eapply (tac_rewrite _ Heq _ _ lr)
    | fail 1 "iRewrite: not a step-indexed BI entailment" ]);
    [ pm_reflexivity ||
        (let Heq := pretty_ident Heq in
         fail "iRewrite:" Heq "not found")
    | iSolveTC ||
        (let P := match goal with
                  | |- IntoInternalEq ?P _ _ \226\138\162 _ => P
                  end in
         fail "iRewrite:" P "not an equality")
    | iRewriteFindPred
    | intros ? ? ? ->; reflexivity
    | pm_prettify; iClearHyp Heq ].
Time Tactic Notation "iRewrite" open_constr(lem) := iRewriteCore Right lem.
Time
Tactic Notation "iRewrite" "-" open_constr(lem) := iRewriteCore Left lem.
Time #[local]
Tactic Notation "iRewriteCore" constr(lr) open_constr(lem) "in" constr(H) :=
 iPoseProofCore lem as true
 fun Heq =>
   eapply (tac_rewrite_in _ Heq _ _ H _ _ lr);
    [ pm_reflexivity ||
        (let Heq := pretty_ident Heq in
         fail "iRewrite:" Heq "not found")
    | pm_reflexivity ||
        (let H := pretty_ident H in
         fail "iRewrite:" H "not found")
    | iSolveTC ||
        (let P := match goal with
                  | |- IntoInternalEq ?P _ _ \226\138\162 _ => P
                  end in
         fail "iRewrite:" P "not an equality")
    | iRewriteFindPred
    | intros ? ? ? ->; reflexivity
    | pm_reduce; pm_prettify; iClearHyp Heq ].
Time
Tactic Notation "iRewrite" open_constr(lem) "in" constr(H) := iRewriteCore
 Right lem in H.
Time
Tactic Notation "iRewrite" "-" open_constr(lem) "in" constr(H) :=
 iRewriteCore Left lem in H.
Time
Ltac
 iSimplifyEq :=
  repeat
   iMatchHyp fun H P => match P with
                        | \226\140\156_ = _\226\140\157%I => iDestruct H as % ?
                        end || simplify_eq /=.
Time
Tactic Notation "iMod" open_constr(lem) := iDestructCore lem as false
 fun H => iModCore H.
Time
Tactic Notation "iMod" open_constr(lem) "as" constr(pat) := iDestructCore lem
 as false
 fun H => <ssreflect_plugin::ssrtclseq@0> iModCore H ; last  iDestructHyp H
   as pat.
Time
Tactic Notation
 "iMod" open_constr(lem) "as" "(" simple_intropattern(x1) ")" constr(pat) :=
 iDestructCore lem as false
 fun H => <ssreflect_plugin::ssrtclseq@0> iModCore H ; last  iDestructHyp H
   as ( x1 ) pat.
Time
Tactic Notation
 "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) ")" constr(pat) := iDestructCore lem as false
 fun H => <ssreflect_plugin::ssrtclseq@0> iModCore H ; last  iDestructHyp H
   as ( x1 x2 ) pat.
Time
Tactic Notation
 "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
 iDestructCore lem as false
 fun H => <ssreflect_plugin::ssrtclseq@0> iModCore H ; last  iDestructHyp H
   as ( x1 x2 x3 ) pat.
Time
Tactic Notation
 "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) 
 ")" constr(pat) := iDestructCore lem as false
 fun H => <ssreflect_plugin::ssrtclseq@0> iModCore H ; last  iDestructHyp H
   as ( x1 x2 x3 x4 ) pat.
Time
Tactic Notation
 "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) ")" constr(pat) := iDestructCore lem as false
 fun H => <ssreflect_plugin::ssrtclseq@0> iModCore H ; last  iDestructHyp H
   as ( x1 x2 x3 x4 x5 ) pat.
Time
Tactic Notation
 "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
 iDestructCore lem as false
 fun H => <ssreflect_plugin::ssrtclseq@0> iModCore H ; last  iDestructHyp H
   as ( x1 x2 x3 x4 x5 x6 ) pat.
Time
Tactic Notation
 "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) 
 ")" constr(pat) := iDestructCore lem as false
 fun H => <ssreflect_plugin::ssrtclseq@0> iModCore H ; last  iDestructHyp H
   as ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Time
Tactic Notation
 "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) ")" constr(pat) := iDestructCore lem as false
 fun H => <ssreflect_plugin::ssrtclseq@0> iModCore H ; last  iDestructHyp H
   as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Time
Tactic Notation "iMod" open_constr(lem) "as" "%" simple_intropattern(pat) :=
 iDestructCore lem as false fun H => iModCore H; iPure H as pat.
Time
Tactic Notation "iAssumptionInv" constr(N) :=
 (let rec find \206\147 i :=
   lazymatch \206\147 with
   | Esnoc ?\206\147 ?j ?P' => first
   [ let H := constr:(_ : IntoInv P' N) in
     unify
     i
     j | find \206\147 i ]
   end
  in
  lazymatch goal with
  | |- envs_lookup ?i (Envs ?\206\147p ?\206\147s _) = Some _ =>
        (first [ find \206\147p i | find \206\147s i ]); pm_reflexivity
  end).
Time
Tactic Notation
 "iInvCore" constr(select) "with" constr(pats) "as" open_constr(Hclose) 
 "in" tactic3(tac) :=
 (iStartProof;
   (let pats := spec_pat.parse pats in
    lazymatch pats with
    | [_] => idtac
    | _ => fail "iInv: exactly one specialization pattern should be given"
    end;
     (let H := iFresh in
      let Pclose_pat :=
       lazymatch Hclose with
       | Some _ => (Some _)
       | None => None
       end
      in
      lazymatch type of select with
      | string =>
          eapply @tac_inv_elim with (i := select) (
           j := H) (Pclose := Pclose_pat);
           [ by iAssumptionCore || fail "iInv: invariant" select "not found"
           | .. ]
      | ident =>
          eapply @tac_inv_elim with (i := select) (
           j := H) (Pclose := Pclose_pat);
           [ by iAssumptionCore || fail "iInv: invariant" select "not found"
           | .. ]
      | namespace =>
          eapply @tac_inv_elim with (j := H) (Pclose := Pclose_pat);
           [ by iAssumptionInv select ||
               fail "iInv: invariant" select "not found"
           | .. ]
      | _ => fail "iInv: selector" select "is not of the right type "
      end;
       [ iSolveTC ||
           (let I := match goal with
                     | |- ElimInv _ ?I _ _ _ _ _ => I
                     end in
            fail "iInv: cannot eliminate invariant" I)
       | iSolveSideCondition
       | let R := fresh in
         <ssreflect_plugin::ssrtclseq@0>
         intros R; pm_reduce; iSpecializePat H pats
         ;
         last 
         iApplyHyp H; clear R; pm_reduce;
          (let x := fresh in
           iIntros ( x ); iIntro H;
            lazymatch Hclose with
            | Some ?Hcl => iIntros Hcl
            | None => idtac
            end; tac x H) ]))).
Time
Tactic Notation "iInvCore" constr(N) "with" constr(pats) "in" tactic3(tac) :=
 iInvCore N with pats as (@None string) in tac.
Time
Tactic Notation "iInvCore" constr(N) "as" constr(Hclose) "in" tactic3(tac) :=
 iInvCore N with "[$]" as Hclose in tac.
Time
Tactic Notation "iInvCore" constr(N) "in" tactic3(tac) := iInvCore N with
 "[$]" as (@None string) in tac.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" constr(pat) constr(Hclose) :=
 iInvCore N with Hs as (Some Hclose) in fun x H => iDestructHyp H as pat.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1) 
 ")" constr(pat) constr(Hclose) := iInvCore N with Hs as 
 (Some Hclose) in fun x H => iDestructHyp H as ( x1 ) pat.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) ")" constr(pat) constr(Hclose) := iInvCore N with Hs
 as (Some Hclose) in fun x H => iDestructHyp H as ( x1 x2 ) pat.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat)
 constr(Hclose) := iInvCore N with Hs as (Some Hclose) in
 fun x H => iDestructHyp H as ( x1 x2 x3 ) pat.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) 
 ")" constr(pat) constr(Hclose) := iInvCore N with Hs as 
 (Some Hclose) in fun x H => iDestructHyp H as ( x1 x2 x3 x4 ) pat.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) ")" constr(pat) constr(Hclose) := iInvCore N with Hs
 as (Some Hclose) in fun x H => iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat)
 constr(Hclose) := iInvCore N with Hs as (Some Hclose) in
 fun x H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) 
 ")" constr(pat) constr(Hclose) := iInvCore N with Hs as 
 (Some Hclose) in fun x H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) ")" constr(pat) constr(Hclose) := iInvCore N with Hs
 as (Some Hclose) in
 fun x H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat)
 constr(Hclose) := iInvCore N with Hs as (Some Hclose) in
 fun x H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) 
 ")" constr(pat) constr(Hclose) := iInvCore N with Hs as 
 (Some Hclose) in
 fun x H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.
Time
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" constr(pat) :=
 iInvCore N with Hs in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as pat
   | _ => fail "Missing intro pattern for accessor variable"
   end.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1) 
 ")" constr(pat) := iInvCore N with Hs in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 ) pat
   | _ => revert x; intros x1; iDestructHyp H as pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) ")" constr(pat) := iInvCore N with Hs in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) := iInvCore
 N with Hs in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 x3 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) 
 ")" constr(pat) := iInvCore N with Hs in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 x4 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) ")" constr(pat) := iInvCore N with Hs in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) := iInvCore
 N with Hs in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) 
 ")" constr(pat) := iInvCore N with Hs in
 fun x H =>
   lazymatch type of x with
   | unit =>
       destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) ")" constr(pat) := iInvCore N with Hs in
 fun x H =>
   lazymatch type of x with
   | unit =>
       destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat
   | _ =>
       revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) := iInvCore
 N with Hs in
 fun x H =>
   lazymatch type of x with
   | unit =>
       destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat
   | _ =>
       revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 x9 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
 simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
 simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) 
 ")" constr(pat) := iInvCore N with Hs in
 fun x H =>
   lazymatch type of x with
   | unit =>
       destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 )
        pat
   | _ =>
       revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 x9 x10 )
        pat
   end.
Time
Tactic Notation "iInv" constr(N) "as" constr(pat) constr(Hclose) := iInvCore
 N as Some Hclose in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as pat
   | _ => fail "Missing intro pattern for accessor variable"
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) 
 ")" constr(pat) constr(Hclose) := iInvCore N as Some Hclose in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 ) pat
   | _ => revert x; intros x1; iDestructHyp H as pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 ")" constr(pat) constr(Hclose) := iInvCore N as Some Hclose in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) ")" constr(pat) constr(Hclose) := iInvCore N as
 Some Hclose in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 x3 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) ")" constr(pat)
 constr(Hclose) := iInvCore N as Some Hclose in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 x4 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) 
 ")" constr(pat) constr(Hclose) := iInvCore N as Some Hclose in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) ")" constr(pat) constr(Hclose) := iInvCore N as
 Some Hclose in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) ")" constr(pat)
 constr(Hclose) := iInvCore N as Some Hclose in
 fun x H =>
   lazymatch type of x with
   | unit =>
       destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8) 
 ")" constr(pat) constr(Hclose) := iInvCore N as Some Hclose in
 fun x H =>
   lazymatch type of x with
   | unit =>
       destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat
   | _ =>
       revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) ")" constr(pat) constr(Hclose) := iInvCore N as
 Some Hclose in
 fun x H =>
   lazymatch type of x with
   | unit =>
       destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat
   | _ =>
       revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 x9 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) 
 ")" constr(pat) constr(Hclose) := iInvCore N as Some Hclose in
 fun x H =>
   lazymatch type of x with
   | unit =>
       destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 )
        pat
   | _ =>
       revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 x9 x10 )
        pat
   end.
Time
Tactic Notation "iInv" constr(N) "as" constr(pat) := iInvCore N in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as pat
   | _ => fail "Missing intro pattern for accessor variable"
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) ")" constr(pat) :=
 iInvCore N in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 ) pat
   | _ => revert x; intros x1; iDestructHyp H as pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 ")" constr(pat) := iInvCore N in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) ")" constr(pat) := iInvCore N in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 x3 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) ")" constr(pat) := iInvCore
 N in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 x4 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) 
 ")" constr(pat) := iInvCore N in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) ")" constr(pat) := iInvCore N in
 fun x H =>
   lazymatch type of x with
   | unit => destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) ")" constr(pat) := iInvCore
 N in
 fun x H =>
   lazymatch type of x with
   | unit =>
       destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat
   | _ => revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8) 
 ")" constr(pat) := iInvCore N in
 fun x H =>
   lazymatch type of x with
   | unit =>
       destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat
   | _ =>
       revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) ")" constr(pat) := iInvCore N in
 fun x H =>
   lazymatch type of x with
   | unit =>
       destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat
   | _ =>
       revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 x9 ) pat
   end.
Time
Tactic Notation
 "iInv" constr(N) "as" "(" simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
 simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) 
 ")" constr(pat) := iInvCore N in
 fun x H =>
   lazymatch type of x with
   | unit =>
       destruct x as []; iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 )
        pat
   | _ =>
       revert x; intros x1; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 x9 x10 )
        pat
   end.
Time
Tactic Notation "iAccu" :=
 (iStartProof; eapply tac_accu;
   [ pm_reflexivity || fail "iAccu: not an evar" ]).
Time Hint Extern 0 (_ \226\138\162 _) => iStartProof: core.
Time Hint Extern 0 (envs_entails _ _) => (iPureIntro; try done): core.
Time
Hint Extern 0 (envs_entails _ ?Q) => (first
  [ is_evar Q; fail 1 | iAssumption ]): core.
Time Hint Extern 0 (envs_entails _ emp) => iEmpIntro: core.
Time
Hint Extern 0 (envs_entails _ (_ \226\137\161 _)) =>
  (rewrite envs_entails_eq; apply bi.internal_eq_refl): core.
Time
Hint Extern 0 (envs_entails _ (big_opL _ _ _)) =>
  (rewrite envs_entails_eq; apply big_sepL_nil'): core.
Time
Hint Extern 0 (envs_entails _ (big_sepL2 _ _ _)) =>
  (rewrite envs_entails_eq; apply big_sepL2_nil'): core.
Time
Hint Extern 0 (envs_entails _ (big_opM _ _ _)) =>
  (rewrite envs_entails_eq; apply big_sepM_empty'): core.
Time
Hint Extern 0 (envs_entails _ (big_sepM2 _ _ _)) =>
  (rewrite envs_entails_eq; apply big_sepM2_empty'): core.
Time
Hint Extern 0 (envs_entails _ (big_opS _ _ _)) =>
  (rewrite envs_entails_eq; apply big_sepS_empty'): core.
Time
Hint Extern 0 (envs_entails _ (big_opMS _ _ _)) =>
  (rewrite envs_entails_eq; apply big_sepMS_empty'): core.
Time Hint Extern 0 (envs_entails _ (\226\136\128 _, _)) => iIntros: core.
Time Hint Extern 0 (envs_entails _ (_ \226\134\146 _)) => iIntros: core.
Time Hint Extern 0 (envs_entails _ (_ -\226\136\151 _)) => iIntros: core.
Time Hint Extern 0 (envs_entails _ (\226\136\128.. _, _)) => iIntros ( ? ): core.
Time Hint Extern 1 (envs_entails _ (_ \226\136\167 _)) => iSplit: core.
Time Hint Extern 1 (envs_entails _ (_ \226\136\151 _)) => iSplit: core.
Time Hint Extern 1 (envs_entails _ (\226\150\183 _)) => iNext: core.
Time Hint Extern 1 (envs_entails _ (\226\150\160 _)) => iAlways: core.
Time Hint Extern 1 (envs_entails _ (<pers> _)) => iAlways: core.
Time Hint Extern 1 (envs_entails _ (<affine> _)) => iAlways: core.
Time Hint Extern 1 (envs_entails _ (\226\150\161 _)) => iAlways: core.
Time Hint Extern 1 (envs_entails _ (\226\136\131 _, _)) => iExists _: core.
Time Hint Extern 1 (envs_entails _ (\226\136\131.. _, _)) => iExists _: core.
Time Hint Extern 1 (envs_entails _ (\226\151\135 _)) => iModIntro: core.
Time Hint Extern 1 (envs_entails _ (_ \226\136\168 _)) => iLeft: core.
Time Hint Extern 1 (envs_entails _ (_ \226\136\168 _)) => iRight: core.
Time Hint Extern 1 (envs_entails _ (|==> _)) => iModIntro: core.
Time Hint Extern 1 (envs_entails _ (<absorb> _)) => iModIntro: core.
Time Hint Extern 2 (envs_entails _ (|={_}=> _)) => iModIntro: core.
Time Hint Extern 2 (envs_entails _ (_ \226\136\151 _)) => (progress iFrame): iFrame.
