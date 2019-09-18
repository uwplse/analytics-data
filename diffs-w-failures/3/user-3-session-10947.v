Time From iris.bi Require Import bi telescopes.
Time From iris.proofmode Require Import base environments.
Time Declare Reduction
pm_eval := cbv[base.beq base.Pos_succ base.ascii_beq base.string_beq
              base.positive_beq base.ident_beq env_lookup env_lookup_delete
              env_delete env_app env_replace env_dom env_intuitionistic
              env_spatial env_counter env_spatial_is_nil envs_dom envs_lookup
              envs_lookup_delete envs_delete envs_snoc envs_app
              envs_simple_replace envs_replace envs_split envs_clear_spatial
              envs_clear_intuitionistic envs_incr_counter envs_split_go
              envs_split env_to_prop pm_option_bind pm_from_option
              pm_option_fun].
Time Ltac pm_eval t := eval pm_eval in t.
Time
Ltac
 pm_reduce :=
  match goal with
  | |- ?u => let v := pm_eval u in
             convert_concl_no_check v
  end.
Time Ltac pm_reflexivity := pm_reduce; exact eq_refl.
Time Declare Reduction
pm_prettify := cbn[tele_fold tele_bind tele_app bi_persistently_if
                  bi_affinely_if bi_absorbingly_if bi_intuitionistically_if
                  bi_wandM sbi_laterN bi_tforall bi_texist].
Time
Ltac
 pm_prettify :=
  match goal with
  | |- ?u => let v := eval pm_prettify in u in
             convert_concl_no_check v
  end.
