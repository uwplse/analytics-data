Time Ltac descend := repeat match goal with
                            | |- exists _, _ => eexists
                            end.
Time
Ltac
 especialize H :=
  match type of H with
  | forall x : ?T, _ =>
      let x := fresh x in
      evar ( x : T ); specialize (H x); subst x
  end.
Time #[local]
Ltac
 _especialize H :=
  lazymatch type of H with
  | forall x : ?T, _ =>
      let x := fresh x in
      lazymatch type of T with
      | Prop => unshelve (evar ( x : T ); specialize (H x); subst x)
      | _ => evar ( x : T ); specialize (H x); subst x
      end
  end.
Time
Ltac
 epose_proof H :=
  let H' := fresh in
  pose proof H as H'; repeat _especialize H'.
Time
Ltac
 eexists_t t :=
  match goal with
  | |- exists _ : ?T, _ => eexists (_ : T)
  | |- {_ : ?T | _} => eexists (_ : T)
  end.
Time
Ltac
 simpl_match :=
  let repl_match_goal d d' :=
   replace d with d';
    lazymatch goal with
    | |- context [ match d' with
                   | _ => _
                   end ] => fail
    | _ => idtac
    end
  in
  let repl_match_hyp H d d' :=
   replace d with d' in H;
    lazymatch type of H with
    | context [ match d' with
                | _ => _
                end ] => fail
    | _ => idtac
    end
  in
  match goal with
  | Heq:?d = ?d'
    |- context [ match ?d with
                 | _ => _
                 end ] => repl_match_goal d d'
  | Heq:?d' = ?d
    |- context [ match ?d with
                 | _ => _
                 end ] => repl_match_goal d d'
  | Heq:?d = ?d', H:context [ match ?d with
                              | _ => _
                              end ] |- _ => repl_match_hyp H d d'
  | Heq:?d' = ?d, H:context [ match ?d with
                              | _ => _
                              end ] |- _ => repl_match_hyp H d d'
  end.
Time
Ltac
 destruct_matches_in e :=
  lazymatch e with
  | context [ match ?d with
              | _ => _
              end ] => destruct_matches_in d
  | _ => destruct e eqn:?; intros
  end.
Time
Ltac
 destruct_all_matches :=
  repeat
   (try simpl_match;
     try
      match goal with
      | |- context [ match ?d with
                     | _ => _
                     end ] => destruct_matches_in d
      | H:context [ match ?d with
                    | _ => _
                    end ] |- _ => destruct_matches_in d
      end); subst; try congruence; auto.
Time
Ltac
 destruct_nongoal_matches :=
  repeat
   (try simpl_match;
     try
      match goal with
      | H:context [ match ?d with
                    | _ => _
                    end ] |- _ => destruct_matches_in d
      end); subst; try congruence; auto.
Time
Ltac
 destruct_goal_matches :=
  repeat
   (try simpl_match;
     match goal with
     | |- context [ match ?d with
                    | _ => _
                    end ] => destruct_matches_in d
     end); try congruence; auto.
Time Ltac exists_econstructor := eexists_t ltac:(econstructor); simpl.
Time
Ltac
 destruct_tuple :=
  match goal with
  | H:context [ let '(a, b) := ?p in _ ]
    |- _ => let a := fresh a in
            let b := fresh b in
            destruct p as [a b]
  | |- context [ let '(a, b) := ?p in _ ] =>
        let a := fresh a in
        let b := fresh b in
        destruct p as [a b]
  end.
Time Tactic Notation "destruct" "matches" "in" "*" := destruct_all_matches.
Time
Tactic Notation "destruct" "matches" "in" "*|-" := destruct_nongoal_matches.
Time Tactic Notation "destruct" "matches" := destruct_goal_matches.
