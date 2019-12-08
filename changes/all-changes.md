See the paper for details on the analysis.

TODO WIP organizing and linking and checking final numbers
TODO make the non-actionable TODOs that aren't in the paper into notes
TODO f / args granularity is innermost	
TODO look at timestamps
TODO revisit each one in detail to finalize, perhaps after writing a bunch
TODO below are more final ones. in each session, just keep the notes. same at user-level.
TODO final recount at the end, also. plus link to every diff
TODO CUT-DEF includes cutting fix etc

Totals:
- User 3: TODO
  * Structure: TODO
    ** Add: TODO
      *** Add Hyp: 1
        **** Add Hyp Fixpoint: 1
- User 5: TODO
  * Structure: TODO
    ** Add: TODO
      *** Add Hyp: 11
        **** Add Hyp Record: 10
        **** Add Hyp Theorem: 1
- User 7: TODO
  * Structure: TODO
    ** Add: TODO
      *** Add Hyp: 17
        **** Add Hyp Lemma: 17
- User 8: TODO
  * Structure: TODO
    ** Add: TODO
      *** Add Hyp: 3
        **** Add Hyp Lemma: 2
        **** Add Hyp Fact: 1
- Total: TODO
  * Structure: TODO
    ** Add: TODO
      *** Add Hyp: 32
        **** Add Hyp Record: 10
        **** Add Hyp Fixpoint: 1
        **** Add Hyp Theorem: 1
        **** Add Hyp Lemma: 19
        **** Add Hyp Fact: 1

# Structure

## Add

### Add Hyp

#### Add Hyp Record

##### User 5

1. [5.19.5-7.1](https://github.com/uwplse/analytics-data/compare/2894ba5928f7fe963c8a1d8d2b31fb5cd3858df7..49ad0ac21d49dac8454385945fdf5e2cfb9abf90): 
  * Record: `EpsilonLogic`
  * New hypothesis: `evalPlus`
  * Elapsed: 573.95 seconds (this change only)
2. [5.19.7-8.1](https://github.com/uwplse/analytics-data/commit/08436be993b76fa3b4f9e8673acc78fbb12d79d1#diff-86d76448a54765ff094f8c80cd8be3a0)
  * Record: `EpsilonLogic`
  * New hypothesis: `evalMinus`
  * Elapsed: 209.32 seconds (includes other changes)
3. [5.19.7-8.2](https://github.com/uwplse/analytics-data/commit/08436be993b76fa3b4f9e8673acc78fbb12d79d1#diff-86d76448a54765ff094f8c80cd8be3a0)
  * Record: `EpsilonLogic`
  * New hypothesis: `evalTimes`
  * Elapsed: 209.32 seconds (includes other changes)
4. [5.19.23-26.1](https://github.com/uwplse/analytics-data/compare/ff27a314a04df3b8ec56090bff68c3060923a658..a282a80381cd7c89faea21c63af3887fb2a86537)
  * Record: `EpsilonLogic`
  * New hypothesis: `evalBoolConst`
  * Elapsed: 51610.77 seconds (includes other changes, new day)
5. [5.19.23-26.2](https://github.com/uwplse/analytics-data/compare/ff27a314a04df3b8ec56090bff68c3060923a658..a282a80381cd7c89faea21c63af3887fb2a86537)
  * Record: `EpsilonLogic`
  * New hypothesis: `evalBoolInj`
  * Elapsed: 51610.77 seconds (includes other changes, new day)
6. [5.19.23-26.3](https://github.com/uwplse/analytics-data/compare/ff27a314a04df3b8ec56090bff68c3060923a658..a282a80381cd7c89faea21c63af3887fb2a86537)
  * Record: `EpsilonLogic`
  * New hypothesis: `evalIfTrue`
  * Elapsed: 51610.77 seconds (includes other changes, new day)
7. [5.19.23-26.4](https://github.com/uwplse/analytics-data/compare/ff27a314a04df3b8ec56090bff68c3060923a658..a282a80381cd7c89faea21c63af3887fb2a86537)
  * Record: `EpsilonLogic`
  * New hypothesis: `evalIfFalse`
  * Elapsed: 51610.77 seconds (includes other changes, new day)
8. [5.19.23-26.5](https://github.com/uwplse/analytics-data/compare/ff27a314a04df3b8ec56090bff68c3060923a658..a282a80381cd7c89faea21c63af3887fb2a86537)
  * Record: `EpsilonLogic`
  * New hypothesis: `evalAnd`
  * Elapsed: 51610.77 seconds (includes other changes, new day)
9. [5.19.23-26.6](https://github.com/uwplse/analytics-data/compare/ff27a314a04df3b8ec56090bff68c3060923a658..a282a80381cd7c89faea21c63af3887fb2a86537)
  * Record: `EpsilonLogic`
  * New hypothesis: `evalOr`
  * Elapsed: 51610.77 seconds (includes other changes, new day)
10. [5.19.23-26.6](https://github.com/uwplse/analytics-data/compare/ff27a314a04df3b8ec56090bff68c3060923a658..a282a80381cd7c89faea21c63af3887fb2a86537)
  * Record: `EpsilonLogic`
  * New hypothesis: `evalNot`
  * Elapsed: 51610.77 seconds (includes other changes, new day)

#### Add Hyp Fixpoint

##### User 3

1. [3.960.19-80.1](https://github.com/uwplse/analytics-data/compare/017188f46db98812ea1072f74a15f0855cba1ba7..01de6576ae7e6c27c0f8f89c66c3ae092b4ef3db)
  * Fixpoint: `nat_to_le`
  * New hypothesis: `base`
  * Elapsed: 838.01 seconds (includes other changes)

#### Add Hyp Theorem

##### User 5

1. [5.18.18-21.1](https://github.com/uwplse/analytics-data/compare/093afda7c7959f84066fec93d2ebcc22e444c125..6fd291dea99a852a4b3d8846dc7adf59bae64552)
  * Theorem: `simplify_correct`
  * New hypothesis: `env`
  * Elapsed: 103.37 seconds (includes other changes)

#### Add Hyp Lemma

##### User 7

1. [7.2.94.1](https://github.com/uwplse/analytics-data/commit/4eab31c6c25dc2a5fd06adeee23ba4e89cb60138)
  * Lemma: `sub_r_unite_pairs_l__inv`
  * New hypothesis: `InNF( t1)`
  * Elapsed: 31.84 seconds (includes other changes)
2. [7.2.94.2](https://github.com/uwplse/analytics-data/commit/4eab31c6c25dc2a5fd06adeee23ba4e89cb60138)
  * Lemma: `sub_r_unite_pairs_l__inv`
  * New hypothesis: `InNF( t2)`
  * Elapsed: 31.84 seconds (includes other changes)
3. [7.2.147-152.1](https://github.com/uwplse/analytics-data/compare/d43041752f886ac0bbfe15a6c4e64aeab9fc69ff..1df9382cec8e149ba1d3e648a1268e0b4a54ef97)
  * Lemma: `weird_trans`
  * New hypothesis: `t3 << t2`
  * Elapsed: 96.36 seconds (includes other changes)
4. [7.2.158.1](https://github.com/uwplse/analytics-data/commit/32cda79ad11a1f7032728b7b2afbba09e57f6f65#diff-4cfcc23dc186dc3f932da247458e2157) 
  * Lemma: `weird_trans`
  * New hypothesis: `InNF( t2)`
  * Elapsed: 47.22 seconds (this change and change in proof only)
5. [7.2.162-165.1](https://github.com/uwplse/analytics-data/compare/148f834338b149875f89d4694fed52572c0c7767..d08ef3ace72f4694186fc6124d7f30d3f78ad46d)
  * Lemma: `weird_trans`
  * New hypothesis: `InNF( tm1)`
  * Elapsed: 64035.19 seconds (includes other changes, new day)
6. [7.19.50.1](https://github.com/uwplse/analytics-data/commit/fccadfdbd27be36090b583374f9159365a6e31f7#diff-c026bd15c3ac7f69c8e584c4c3b4f091)
  * Lemma: `match_ty_i_k__match_le_k`
  * New hypothesis: `0 < k'`
  * Elapsed: 6.38 seconds (this change and change in proof only)
7. [7.19.177.1](https://github.com/uwplse/analytics-data/commit/823800755c9b01bf82d95df69f774f6c88fa27ae#diff-c026bd15c3ac7f69c8e584c4c3b4f091)
  * Lemma: `match_ty_i__inv_depth_stable`
  * New hypothesis: `inv_depth v <= k`
  * Elapsed: 29.06 seconds (these two changes and changes in proof only)
8. [7.19.177.2](https://github.com/uwplse/analytics-data/commit/823800755c9b01bf82d95df69f774f6c88fa27ae#diff-c026bd15c3ac7f69c8e584c4c3b4f091)
  * Lemma: `match_ty_i__inv_depth_stable`
  * New hypothesis: `inv_depth v <= k'`
  * Elapsed: 29.06 seconds (these two changes and changes in proof only)
9. [7.19.486.1](https://github.com/uwplse/analytics-data/commit/cd51e545523ca6bbeb7645bbad348c87f1dfb2ac#diff-c026bd15c3ac7f69c8e584c4c3b4f091)
  * Lemma: `sem_sub_k_i_nf__inv_depth_le`
  * New hypothesis: `| t | <= k`
  * Elapsed: 1.86 seconds (this change and change in proof only)
10. [7.19.515.1](https://github.com/uwplse/analytics-data/commit/3e1dd5223c3db2b6c5b6efb89e8c94bf00e7da0a#diff-c026bd15c3ac7f69c8e584c4c3b4f091)
  * Lemma: `sem_eq_k_i__inv_depth_eq`
  * New hypothesis: `| t' | <= k`
  * Elapsed: 89.19 seconds (includes another change in proof)
11. [7.61.4.1](https://github.com/uwplse/analytics-data/commit/9fde4dec58829ebbca18822b07b9899d59b72f4f#diff-6d02cae462d8dbc01ed1d267af5c2ebb)
  * Lemma: `pair_sem_sub_k__sub_d`
  * New hypothesis: `| TPair ta1 ta2 | <= k`
  * Elapsed: 159.42 seconds (includes another change in proof)
12. [7.101.44.1](https://github.com/uwplse/analytics-data/commit/5a745ff4f3eb01ddd4e7a33a5271ac6cf0b69621#diff-64b536c14253573f88165197c7b30b83)
  * Lemma: `not_sem_sub__eXrefX_reft`
  * New hypothesis: `k : nat`
  * Elapsed: 27.32 seconds (includes another change)
13. [7.145.22.1](https://github.com/uwplse/analytics-data/commit/f2edee6079b88bf925ad97c6b03469a1a7c34ba2#diff-5863cbc0cc1562fe4e8aca04c5bfbb93)
  * Lemma: `sem_sub_fresh_var__sem_sub_exist`
  * New hypothesis: `tx : ty`
  * Elapsed: 221.90 seconds (includes another change)
14. [7.184.15.1](https://github.com/uwplse/analytics-data/commit/79dd13e4c614575a5c85cd9f1d852fc97da3fb45#diff-e9ca8fa9dbcf98ebf7f20bcfcb129e75)
  * Lemma: `build_v_full`
  * New hypothesis: `fresh_in_ty X' t'`
  * Elapsed: 74.31 seconds (this change only)
15. [7.202.30-32.1](https://github.com/uwplse/analytics-data/compare/42620d0854559700f3899c60194ce026c9ca9e8c..3255e40af1c1ba213ec9eb75c5c0cef75c007777)
  * Lemma: `b_subst_wf_ty`
  * New hypothesis: `not_b_free_in_ty X t`
  * Elapsed: 135.75 seconds (includes other changes)
16. [7.215.2.1](https://github.com/uwplse/analytics-data/commit/b347dd18be61e43b79e3ee012bfeb9ddbefd3a55#diff-133a27d36ec7cfb34b2d3c9e7523505e)
  * Lemma: `build_v_full`
  * New hypothesis: `wf_ty tx`
  * Elapsed: 110.05 seconds (this change only)
17. [7.219.10.1](https://github.com/uwplse/analytics-data/commit/e19825ab07eac43966d1d49e1d2247597c636ed5#diff-01bc82921b15d2250ca7bf1bffb387a5)
  * Lemma: `build_v_full`
  * New hypothesis: `b_free_in_ty X t`
  * Elapsed: 125.36 seconds (includes other changes)

##### User 8

1. [8.79.293.1](https://github.com/uwplse/analytics-data/commit/1360be59258b4fd0499d32f974fbd61d02d64150#diff-3ae9cc05249c564523bb8a4f63e1e3af)
  * Lemma: `big_kron_append`
  * New hypothesis: `m <> 0`
  * Elapsed: 11 seconds (these two changes only)
2. [8.79.293.2](https://github.com/uwplse/analytics-data/commit/1360be59258b4fd0499d32f974fbd61d02d64150#diff-3ae9cc05249c564523bb8a4f63e1e3af)
  * Lemma: `big_kron_append`
  * New hypothesis: `n <> 0`
  * Elapsed: 11 seconds (these two changes only)

#### Add Hyp Fact

##### User 8

1. [8.34.0-4](https://github.com/uwplse/analytics-data/compare/083009f275aa72d9fda76a6acb60de0ccf79ceee..87fbf320436f56f623301f67f789c4700ce3cacc)
  * Lemma: `denote_compose`
  * New hypothesis: `\207\129` (encoded)
  * Elapsed: 78.24 seconds (includes other changes)

### Add Ctr

Totals: TODO 

#### Add Ctr Inductive

Totals: TODO

##### User 1

Total: TODO

1. [1.37.4.1](https://github.com/uwplse/analytics-data/commit/ae812a8bb8bc351d2a4ce08dc6ba319f42b1f4b8#diff-16df098de71249ca8d704f5f6b2583e5)
  * Inductive: `ST`
  * New hypothesis: `SBool` (constructor)
  * Elapsed:
2. [1.37.4.2](https://github.com/uwplse/analytics-data/commit/ae812a8bb8bc351d2a4ce08dc6ba319f42b1f4b8#diff-16df098de71249ca8d704f5f6b2583e5)
  * Inductive: `ST`
  * New hypothesis: `
  * Elapsed:


      *** 1.37.4-12 (ST)
      *** 1.37.26 (GT)
      *** 1.37.31 (GT)
      *** 1.37.52-56 (Alpha)
      *** 1.41.0-3 (Alpha)
      *** 1.41.3-8 (Alpha)
      *** 1.41.3-8 (Alpha)
      *** 1.41.8-10 (Alpha)
      *** 1.41.10-12 (Alpha)
      *** 1.41.12-19 (Alpha)
      *** 1.41.12-19 (Alpha)
      *** 1.41.12-19 (Alpha)
      *** 1.41.20 (Alpha)
      *** 2.5.0-68 (term)
      *** 3.936.1 (compile_mail_base)
      *** 5.18.7 (Term)
      *** 5.18.7 (Term)
      *** 5.18.7 (Term)
      *** 5.18.7 (Term)
      *** 5.19.19 (Term)
      *** 5.19.19 (Term)
      *** 5.19.19 (Term)
      *** 5.19.19 (Term)
      *** 5.19.19 (Term)
      *** 5.19.19 (Term)
      *** 5.27.1 (Term)
      *** 5.27.1 (Term)
      *** 5.27.1 (Term)
      *** 7.99.0 (ty)
      *** 7.99.0-3 (value_type)
      *** 7.109.10 (sub_d)
      *** 7.193.0 (ty)

### Add Arg

#### Add Arg Instance

Totals:
- User 11: 2
- Total: 2

##### User 11

Total: TODO

1. [11.16.0-6](https://github.com/uwplse/analytics-data/compare/1b62f2879a6dd313c3cd30b5a8ed29c5bd1ac900..f696716f604c89e079ace122bc5a3b61e30b318d)
  * Instance: `showAppE`
  * New hypothesis: `c` in case `App_Recv`
  * Elapsed: 704.32 seconds (includes other changes, likely a repair)
2. [11.16.0-6](https://github.com/uwplse/analytics-data/compare/1b62f2879a6dd313c3cd30b5a8ed29c5bd1ac900..f696716f604c89e079ace122bc5a3b61e30b318d)
  * Instance: `showAppE`
  * New hypothesis: `c` in case `App_Send	`
  * Elapsed: 704.32 seconds (includes other changes, likely a repair) 

#### etc

  * ARG (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 2, 10: 0, 11: 0, Total: 2)
    ** Thm+ (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 2, 10: 0, 11: 0, Total: 2)
      *** 8.34.0-4 (denote_compose)
      *** 8.34.0-4 (denote_compose)
  * BODY (1: 5, 2: 0, 3: 7, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 12)
    ** Ind+ (1: 3, 2: 0, 3: 0, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 3)
      *** 1.37.3 (ST)
      *** 1.37.25 (GT)
      *** 1.37.0-52 (Alpha)
    ** Def (1: 0, 2: 0, 3: 6, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 6)
      *** 3.5741.1 (nanb)
      *** 3.6414.4-29 (init)
      *** 3.6414.4-29 (get)
      *** 3.6414.4-29 (append)
      *** 3.6414.4-113 (reset)
      *** 3.6414.4-113 (recover)
    ** Fix+ (1: 2, 2: 0, 3: 1, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 3)
      *** 1.37.26 (Gamma)
      *** 1.41.94-114 (eq)
      *** 3.960.19-69 (nat_to_le)
  * CASE (1: 24, 2: 4, 3: 1, 5: 21, 7: 6, 8: 0, 10: 1, 11: 0, Total: 57)
    ** Def (1: 0, 2: 0, 3: 1, 5: 0, 7: 0, 8: 0, 10: 1, 11: 0, Total: 2)
      *** 3.806.1 (step_open)
      *** 10.10.13-15 (network_of_app)
    ** Fix+ (1: 24, 2: 4, 3: 0, 5: 21, 7: 6, 8: 0, 10: 0, 11: 0, Total: 55)
      *** 1.37.27 (Gamma)
      *** 1.37.28 (Gamma)
      *** 1.37.28-30 (Gamma)
      *** 1.37.30-44 (Gamma)
      *** 1.37.52-55 (Gamma)
      *** 1.41.94-114 (eq)
      *** 1.41.94-114 (eq)
      *** 1.41.94-114 (eq)
      *** 1.41.94-114 (eq)
      *** 1.41.94-114 (eq)
      *** 1.41.100 (size_gt)
      *** 1.41.112 (size_gt)
      *** 1.41.112 (size_gt)
      *** 1.41.114 (size_gt)
      *** 1.41.118 (size_gt)
      *** 1.41.114-129 (eq)
      *** 1.41.114-129 (eq)
      *** 1.41.114-129 (eq)
      *** 1.41.114-129 (eq)
      *** 1.41.114-129 (eq)
      *** 1.41.114-129 (eq)
      *** 1.41.114-129 (eq)
      *** 1.41.114-129 (eq)
      *** 1.41.141 (eq_fn)
      *** 2.5.0-2 (value)
      *** 2.5.44 (step)
      *** 2.5.71 (value)
      *** 2.5.78 (step)
      *** 5.18.13-15 (simplify)
      *** 5.18.13-15 (simplify)
      *** 5.18.13-15 (simplify)
      *** 5.18.13-15 (simplify)
      *** 5.19.26-28 (identity)
      *** 5.19.26-28 (identity)
      *** 5.19.26-28 (identity)
      *** 5.19.26-28 (identity)
      *** 5.19.26-28 (identity)
      *** 5.19.26-28 (identity)
      *** 5.19.9-36 (free_vars)
      *** 5.19.9-36 (free_vars)
      *** 5.19.9-36 (free_vars)
      *** 5.19.9-36 (free_vars)
      *** 5.19.9-36 (free_vars)
      *** 5.33.0-3 (identity)
      *** 5.33.0-3 (identity)
      *** 5.33.0-3 (identity)
      *** 5.35.0-3 (free_vars)
      *** 5.35.0-3 (free_vars)
      *** 5.35.0-3 (free_vars)
      *** 7.99.0 (subst)
      *** 7.99.0-5 (match_ty)
      *** 7.102.0-11 (match_ty)
      *** 7.104.40-42 (inv_depth)
      *** 7.193.0 (FV)
      *** 7.193.0 (FV)

## Del


- REMOVE (1: 0, 2: 0, 3: 2, 5: 6, 7: 11, 8: 4, 10: 0, 11: 0, Total: 23)
  * CONSTRUCTOR (1: 0, 2: 0, 3: 0, 5: 1, 7: 0, 8: 0, 10: 0, 11: 0, Total: 1)
    ** IND+ (1: 0, 2: 0, 3: 0, 5: 5, 7: 0, 8: 0, 10: 0, 11: 0)
      *** 5.19.25 (Term)
  * HYPO (1: 0, 2: 0, 3: 2, 5: 5, 7: 11, 8: 4, 10: 0, 11: 0, Total: 22)
    ** CONSTRUCTOR-HYPO (1: 0, 2: 0, 3: 0, 5: 4, 7: 0, 8: 0, 10: 0, 11: 0)
      *** IND+ (1: 0, 2: 0, 3: 0, 5: 4, 7: 0, 8: 0, 10: 0, 11: 0)) 
        **** 5.19.23-25 (EpsilonLogic)
        **** 5.19.23-25 (EpsilonLogic)
        **** 5.19.23-25 (EpsilonLogic)
        **** 5.19.26 (Term)
    ** LET-HYPO (1: 0, 2: 0, 3: 2, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0)  (TODO move these; lets are not hypotheses, they are cut/uncut)
      *** FIX+ (1: 0, 2: 0, 3: 2, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0)
        **** 3.960.146-149 (nat_to_le)
        **** 3.960.146-149 (nat_to_le)
    ** THM-HYPO (1: 0, 2: 0, 3: 0, 5: 1, 7: 11, 8: 4, 10: 0, 11: 0)
      *** THM+ (1: 0, 2: 0, 3: 0, 5: 1, 7: 11, 8: 4, 10: 0, 11: 0)
        **** 5.18.24-26 (simplify_correct)
        **** 7.2.147-152 (weird_trans)
        **** 7.2.147-152 (weird_trans)
        **** 7.2.147-152 (weird_trans)
        **** 7.19.53 (match_ty_i_k__match_le_k)
        **** 7.19.71 (match_ty_i__inv_depth_stable)
        **** 7.19.71 (match_ty_i__inv_depth_stable)
        **** 7.19.344 (sem_sub_k_i_pair__inv)
        **** 7.19.525 (sem_eq_k_i__inv_depth_eq)
        **** 7.19.676 (pair_sem_sub_k_i__sub_d)
        **** 7.19.679 (cname_sem_sub_k_i__sub_d)
        **** 7.202.23 (b_subst_wf_ty)
        **** 8.79.17 (big_kron_append)
        **** 8.79.17 (big_kron_append)
        **** 8.79.20 (big_kron_append)
        **** 8.79.20 (big_kron_append)

## Mov

- MOVE (1: 0, 2: 0, 3: 7, 5: 3, 7: 19, 8: 0, 10: 1, 11: 0, Total: 30)
  * CONSTRUCTOR (1: 0, 2: 0, 3: 0, 5: 1, 7: 1, 8: 0, 10: 0, 11: 0, Total: 2)
    ** IND+ (1: 0, 2: 0, 3: 0, 5: 1, 7: 1, 8: 0, 10: 0, 11: 0)
      *** 5.19.19 (Term)
      *** 7.93.12 (ty)
  * HYPO (1: 0, 2: 0, 3: 0, 5: 1, 7: 18, 8: 0, 10: 1, 11: 0, Total: 20)
    ** DEF (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 0, 10: 1, 11: 0, Total: 1)
      *** 10.10.5 (network_of_app)
     ** THM+ (1: 0, 2: 0, 3: 0, 5: 1, 7: 18, 8: 0, 10: 0, 11: 0, Total: 19)
       *** 5.18.22 (simplify_correct)
       *** 7.2.147-152 (weird_trans)
       *** 7.19.62 (match_ty_i__inv_depth_stable)
       *** 7.19.63 (match_ty_i__inv_depth_stable)
       *** 7.19.180 (match_ty_i__value_type)
       *** 7.19.623 (nf_sem_sub_i__sub_d)
       *** 7.19.697 (match_ty_i_nf)
       *** 7.19.700 (match_ty_i_nf')
       *** 7.56.2 (match_ty_value_type_k)
       *** 7.94.15 (match_ty__value_type_l)
       *** 7.104.46 (not__ref_t_match_ty_t)
       *** 7.104.50 (not__ref_t_match_ty_t)
       *** 7.104.93 (not_sem_eq__reft_t)
       *** 7.106.13 (match_ty__match_ge_world)
       *** 7.110.26 (match_ty__transitive_on_value_type)
       *** 7.145.27 (xxx)
       *** 7.153.14 (build_v)
       *** 7.159.31 (build_v_full)
       *** 7.176.27 (match_ty__subst_neq_permute)
  * CASE (1: 0, 2: 0, 3: 0, 5: 1, 7: 0, 8: 0, 10: 0, 11: 0, Total: 1)
    ** FIX+ (1: 0, 2: 0, 3: 0, 5: 1, 7: 0, 8: 0, 10: 0, 11: 0, Total: 1)
      *** 5.19.26-28 (identity)
  * ARGS (1: 0, 2: 0, 3: 7, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 7)
      *** FIX+ (1: 0, 2: 0, 3: 4, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 4)
        **** 3.960.176 (le_to_nat)
        **** 3.960.181 (le_to_nat)
        **** 3.960.184 (le_to_nat)
        **** 3.960.184 (le_to_nat)
      *** THM+ (1: 0, 2: 0, 3: 3, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 3)
        **** 3.5406.1 (proc_spec_rx)
        **** 3.11377.1 (mult_n_Sm)
        **** 3.11377.1 (mult_n_Sm)

# Content

Totals: TODO

## Pch

- PATCH (1: 2, 2: 2, 3: 16, 5: 2, 7: 7, 8: 0, 10: 6, 11: 4, Total: 39)
  * BODY (1: 1, 2: 0, 3: 3, 5: 2, 7: 4, 8: 0, 10: 0, 11: 1, Total: 11)
    ** IND+ (1: 0, 2: 0, 3: 0, 5: 2, 7: 0, 8: 0, 10: 0, 11: 0, Total: 2)
      *** RECORD-FIELD / CONSTRUCTOR-HYPO / TYPE / PROD / BODY / all (1: 0, 2: 0, 3: 0, 5: 2, 7: 0)
        **** 5.18.28 (EpsilonLogic)
        **** 5.18.28 (EpsilonLogic)
    ** BODY / all (1: 0, 2: 0, 3: 3, 5: 0, 7: 4, 8: 0, 10: 0, 11: 1, Total: 8)
      *** DEF (1: 0, 2: 0, 3: 3, 5: 0, 7: 3, 8: 0, 10: 0, 11: 1)
        **** 3.159.2 (absr)
        **** 3.2698.2 (nat64_to_le)
        **** 3.7199.65 (log_abstraction)
        **** 7.93.9 (vX)
        **** 7.93.11 (vY)
        **** 7.93.11 (vZ)
        **** 11.16.5-16 (kvs_state)
      *** FIX+ (1: 0, 2: 0, 3: 0, 5: 0, 7: 1, 8: 0, 10: 0, 11: 0)
        **** 7.99.0-5 (match_ty)
    ** MATCH-CASE-BODY / APP / F / FUN / BODY / all (1: 1, 2: 0, 3: 0, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 1)
      *** FIX+ 1: 1, 2: 0, 3: 0, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0)
        **** 1.37.50-52 (Gamma)
  * TYPE (1: 0, 2: 0, 3: 1, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 1) (TODO revisit or clarify this vs. body of thm)
    ** DEF (1: 0, 2: 0, 3: 1, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 1)
      *** 3.2698.2 (nat64_to_le)
  * HYPO (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 0, 10: 1, 11: 0, Total: 1)
    ** HYPO / TYPE / all (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 0, 10: 1, 11: 0, Total: 1)
      *** FIX+
        **** 10.10.13-15 (network_of_app)
  * CASE (1: 1, 2: 2, 3: 0, 5: 0, 7: 0, 8: 0, 10: 3, 11: 3, Total: 9)
    ** MATCH-CASE-BODY / all (1: 1, 2: 2, 3: 0, 5: 0, 7: 0, 8: 0, 10: 3, 11: 3, Total: 9)
      *** DEF (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 0, 10: 0, 11: 1, Total: 1)
        **** 11.16.18-20 (smi)
      *** FIX+ (1: 1, 2: 2, 3: 0, 5: 0, 7: 0, 8: 0, 10: 3, 11: 0, Total: 6)
        **** 1.37.44-46 (Gamma)
        **** 2.5.3-42 (value)
        **** 2.5.51-54 (step)
        **** 10.13.11 (fib')
        **** 10.15.4 (fib)
        **** 10.15.5 (fib)
      *** INSTANCE (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 0, 10: 0, 11: 2, Total: 2)
        **** 11.16.0-6 (showAppE)
        **** 11.16.0-6 (showAppE)
  * ARGS (1: 0, 2: 0, 3: 12, 5: 0, 7: 3, 8: 0, 10: 2, 11: 0, Total: 17)
     ** CASE-BODY / APP / ARGS / all (1: 0, 2: 0, 3: 1, 5: 0, 7: 0, 8: 0, 10: 2, 11: 0, Total: 3)
       *** FIX+ (1: 0, 2: 0, 3: 1, 5: 0, 7: 0, 8: 0, 10: 2, 11: 0)
         **** 3.960.160 (le_to_nat)
         **** 10.13.16 (fib')
         **** 10.15.5 (fib)
     ** HYPO / TYPE / APP / ARGS / all 
       *** THM+ (1: 0, 2: 0, 3: 11, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 11)
        **** 3.73.2 (proc_rspec_refine_rec)
        **** 3.73.8 (proc_rspec_crash_refines)
        **** 3.73.9 (proc_rspec_crash_refines_op)
        **** 3.73.9 (proc_rspec_crash_refines_op)
        **** 3.73.9 (proc_rspec_crash_refines_op)
        **** 3.73.14-16 (proc_rspec_recovery_refines_crash_step)
        **** 3.73.14-16 (proc_rspec_recovery_refines_crash_step)
        **** 3.73.14-16 (proc_rspec_recovery_refines_crash_step)
        **** 3.73.14-16 (proc_rspec_recovery_refines_crash_step)
        **** 3.73.18 (proc_hspec_init_ok)
        **** 3.314.19 (crash_step_simp)
     ** BODY / APP / ARGS / all (1: 0, 2: 0, 3: 0, 5: 0, 7: 3, 8: 0, 10: 0, 11: 0, Total: 3)
       *** THM+ (1: 0, 2: 0, 3: 0, 5: 0, 7: 3, 8: 0, 10: 0, 11: 0)
        **** 7.10.25 (sub_r__mk_nf_sub_r)
        **** 7.101.45 (not_sem_sub__eXrefX_reft)
        **** 7.132.15 (sem_sub_k_ref)

## Uch

- Unpatch (1: 0, 2: 2, 3: 2, 5: 0, 7: 2, 8: 4, 10: 0, 11: 0, Total: 10 / 4)
  * HYPO (Total: 0 / 0)
  * BODY (1: 0, 2: 0, 3: 1, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 1 / 1)
    ** BODY / all
      *** DEF (1: 0, 2: 0, 3: 1, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0)
        **** 3.2698.3 (nat64_from_le)
  * TYPE (Total: 0 / 0)
  * CONSTR (Total: 0 / 0)
  * CASE (1: 0, 2: 1, 3: 0, 5: 0, 7: 2, 8: 0, 10: 0, 11: 0, Total: 3 / 2)
      *** FIX+ (1: 0, 2: 1, 3: 0, 5: 0, 7: 2, 8: 0, 10: 0, 11: 0, Total: 3)
        **** 2.5.3 (value)
        **** 7.174.28 (subst) (TODO check)
        **** 7.193.0-2 (FFV)
  * ARG (1: 0, 2: 1, 3: 1, 5: 0, 7: 0, 8: 4, 10: 0, 11: 0, Total: 6 / 3)
    ** CASE-HYPO / APP / ARGS / all (1: 0, 2: 0, 3: 1, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 1)
      *** DEF (1: 0, 2: 1, 3: 0, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 1)
        **** 2.5.53 (oneArgCbvPrimitive)
    ** MATCH-CASE-BODY / APP / ARGS / all (1: 0, 2: 0, 3: 1, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 1)
      *** FIX+ (1: 0, 2: 0, 3: 1, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 1)
        **** 3.960.81-125 (nat_to_le)
    ** HYPO / TYPE / APP / ARG / all (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 2, 10: 0, 11: 0, Total: 2)
      *** THM+ (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 2, 10: 0, 11: 0, Total: 2)
        **** 8.65.68 (assert_init_at_id)
        **** 8.65.68 (assert_init_at_id)
    ** BODY / APP / ARG / all (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 2, 10: 0, 11: 0, Total: 2)
      *** THM+ (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 2, 10: 0, 11: 0, Total: 2)
        **** 8.79.109 (Anonymous Goal)
        **** 8.79.109 (Anonymous Goal)

## Cut

termination proofs (include note, update tables, maybe mention as dev. pattern or include as benchmark)
- 1. [1.41.96-114.1](https://github.com/uwplse/analytics-data/compare/5ab8e74f7562d7516417cb982c5b861e132b28a4..f623d1c924afb791f4fd27f7ffe078d078169cba)
- 3. [3.960.19-80.2](https://github.com/uwplse/analytics-data/compare/017188f46db98812ea1072f74a15f0855cba1ba7..01de6576ae7e6c27c0f8f89c66c3ae092b4ef3db)
  * Fixpoint: `nat_to_le`
  * New hypothesis: `base`
  * Elapsed: 838.01 seconds (includes other changes)
- 7.([162.16](https://github.com/uwplse/analytics-data/blob/0e28364f2663d4f3c51d7a5073fd21a70086ae11/diffs-annotated-with-times/7/user-7-session-162.v)-[174.31](https://github.com/uwplse/analytics-data/blob/206cfb585f090a4dfb75ef54ca8dfe886459d670/diffs-annotated-with-times/7/user-7-session-174.v)).1
  * Notes: Multiple sessions, must use [external diff](https://www.diffchecker.com/Dku5ZDB3)
  * Too complicated to classify all of it


- CUT (1: 2, 2: 3, 3: 8, 5: 0, 7: 3, 8: 0, 10: 1, 11: 0, Total: 16)
  * FUNCTION (1: 1, 2: 0, 3: 0, 5: 0, 7: 3, 8: 0, 10: 0, 11: 0, Total: 3)
    ** DEF (1: 1, 2: 0, 3: 0, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 1)
      *** BODY / APP / F / all (1: 1, 2: 0, 3: 0, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0)
        **** 1.41.130 (eq_fn)
    ** THM+ (7: 3, Total: 3)
      *** HYPO / TYPE/ APP / F / all (7: 1)
        **** 7.113.30 (not_fresh_in_union__inv)
      *** BODY / APP / F / all (7: 2)
        **** 7.113.30 (not_fresh_in_union__inv)
        **** 7.113.30 (not_fresh_in_union__inv)
  * ARGS (1: 1, 2: 1, 3: 8, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 10)
    ** DEF (1: 0, 2: 1, 3: 2, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 3)
       *** 2.5.53 (primitive)
       *** 3.7199.65 (log_abstraction)
       *** 3.7199.65 (log_abstraction)
    ** FIX+ (1: 1, 2: 0, 3: 4, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 5)
      *** HYPO / FIX-HYPO 
        **** HYPO / APP / ARGS (1: 1, 2: 0, 3: 0, 5: 0, 7: 0)
          ****** 1.41.96-102 (eq)
      *** LET / CASE-HYPO / APP / ARGS (3: 2)
        **** 3.960.125-141 (nat_to_le)
        **** 3.960.150 (nat_to_le)
      *** MATCH-CASE-BODY / APP / ARGS (3: 2)
        **** 3.960.81-125 (nat_to_le)
        **** 3.960.150 (nat_to_le)
    ** THM+ (3: 2, Total: 2)
        **** HYPO / TYPE / APP / ARGS / all (3: 3)
          ***** 3.7199.293 (log_length_ok_nil)
          ***** 3.7199.294 (log_abstraction_nil)
  * BODY (1: 0, 2: 2, 3: 0, 5: 0, 7: 0, 8: 0, 10: 1, 11: 0, Total: 3)
    ** DEF (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 0, 10: 1, 11: 0, Total: 1)
      *** MATCH-CASE-BODY / all (10: 1)
        **** 10.18-25 (network_of_app)
    ** FIX+ (1: 1, 2: 2, 3: 0, 5: 0, 7: 0, 8: 0, 10: 0, 11: 0, Total: 2)
      *** MATCH-CASE-BODY / all (1: 0, 2: 2, 3: 0, 5: 0, 7: 0)
        **** CASE-BODY / all (1: 0, 2: 2, 3: 0, 5: 0, 7: 0)
          ***** 2.5.3-42 (value)
          ***** 2.5.42-47 (step)

## Uut

- UNCUT (3: 2, 5: 3, Total: 5)
  * TYPE (5: 2)
    ** DEF (1: 0, 2: 0, 3: 0, 5: 1)
      *** top-level
        **** 5.18.6-9 (extendEnv)
      *** hypo type
        **** 5.18.6-9 (extendEnv)
  * HYPO (5: 1) (new hypo)
    ** DEF
      *** HYPO / all (1: 0, 2: 0, 3: 0, 5: 1)
        **** 5.18.6-9 (extendEnv)
  * ARG (3: 2)
    ** FIX+ (3: 2)
      *** MATCH-CASE-BODY (1: 0, 2: 0, 3: 2)
        **** MATCH-CASE-BODY / APP / ARGS (1: 0, 2: 0, 3: 2)
          ***** 3.960.146-149 (nat_to_le)
          ***** 3.960.146-149 (nat_to_le)

## Rpl

- REPLACE (1: 2, 3: 4, 5: 7, 7: 20, 8: 30, 10: 5, 11: 1, Total: 69)
 * HYPO (1: 1, 7: 5, Total: 6)
   ** Ind+ (1: 1, 7: 2)
    *** INDUCTIVE-CONSTRUCTOR / CONSTRUCTOR-HYPO / all (1: 1, 7: 2)
        **** 1.37.13 (ST)
        **** 7.93.7 (ty)
        **** 7.93.7 (ty)
   ** Fix+ (7: 3)
      *** FIX / HYPO / TYPE / all (7: 3)
        **** 7.174.0-14 (subst)
        **** 7.174.14-24 (subst)
        **** 7.174.25 (subst)
 * ARGS (3: 3, 5: 5, 7: 6, Total: 14)
   ** Ind+ (5: 4)
      *** RECORD-FIELD / CONSTRUCTOR-HYPO / TYPE / PROD / BODY / APP / ARGS / all (5: 4)
        **** 5.19.5 (EpsilonLogic)
        **** 5.19.23-26 (EpsilonLogic)
        **** 5.19.23-26 (EpsilonLogic)
        **** 5.19.23-26 (EpsilonLogic)
   ** Fix+ (3: 2)
      *** TYPE / APP / ARGS (3: 1)
        **** 3.960.16-69 (nat_to_le)
      *** MATCH-CASE-BODY / APP / ARGS / all (3: 1)
        **** 3.960.125-141 (nat_to_le)
   ** Thm+ (3: 1, 5: 1, 7: 6)
      *** HYPO / TYPE / APP / ARGS / all (7: 1)
        **** 7.202.2 (b_subst_neq__permute)
      *** BODY / APP / ARGS / all (3: 1, 5: 1, 7: 5)
        **** 3.11377.4 (mult_n_Sm)
        **** 5.19.29 (eval_eq_true_or_false)
        **** 7.19.38 (match_ty_i_k__match_le_k)
        **** 7.145.22 (sem_sub_fresh_var__sem_sub_exist)
        **** 7.174.45 (triv)
        **** 7.224.22 (build_v_full)
        **** 7.228.7 (build_v_full)
 * FUN (7: 2, 8: 30, Total: 32)
   ** DEF (8 : 2)
      *** BODY / APP / F / all (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 2)
        **** 8.37.10 (valid_ancillae)
        **** 8.125.230 (uniform)
   ** THM+ (7: 2, 8: 28)
      *** HYPO / TYPE / APP / F / all (1: 0, 2: 0, 3: 0, 5: 0, 7: 1, 8: 2)
        **** 7.19.668 (pair_sem_sub_k_i__sub_d
        **** 8.37.74 (valid_denote_true)
        **** 8.37.80 (valid_denote_false)
      *** BODY / APP / F / all (7: 1, 8: 26)
        **** 7.212.3 (free_union__inv)
        **** 8.2.133 (denote_ctrls_transpose)
        **** 8.14.60 (MOVE_list_aux_id)
        **** 8.14.62 (denote_pat_fresh_id)
        **** 8.31.112 (inSeq_id_l) (not same change)
        **** 8.31.112 (inSeq_id_l) (not same change)
        **** 8.37.74 (valid_denote_true)
        **** 8.37.80 (valid_denote_false)
        **** 8.40.25 (init0_spec)
        **** 8.40.38 (MOVE_spec)
        **** 8.40.48 (MOVE_spec_sep)
        **** 8.40.52 (CNOT_spec)
        **** 8.40.56 (XOR_spec)
        **** 8.65.174 (denote_box_id_circ)
        **** 8.79.4 (big_kron_append)
        **** 8.79.113 (Anonymous Goal)
        **** 8.79.308 (init_at_spec)
        **** 8.79.516 (compile_correct)
        **** 8.108.3 (denote_unitary_box_eq)
        **** 8.108.17 (denote_unitary_isometry_box_eq)
        **** 8.108.18 (denote_isometry_box_eq)
        **** 8.125.233 (even_bias)
        **** 8.160.6 (bra0_equiv)
        **** 8.160.6 (bra1_equiv)
        **** 8.160.6 (ket0_equiv)
        **** 8.160.6 (ket1_equiv)
        **** 8.160.0-6 (bra0ket0)
 * BODY (1: 1, 3: 1, 5: 2, 7: 7, 10: 4, 11: 1, Total: 16)
   ** DEF (3: 1, 7: 1, 10: 3, 11: 1)
      *** BODY / all (1: 0, 2: 0, 3: 1, 5: 0, 7: 1, 8: 0, 10: 1)
        **** 3.6414.104 (log_length_ok)
        **** 7.93.2 (varid)
        **** 10.18-25 (network_of_app_ta)
      *** MATCH-CASE-BODY / all (10: 2, 11: 1)
        **** 10.8.1 (nmi_of_smi)
        **** 10.9.1 (nmi_of_smi)
        **** 11.16.18-20 (smi)
   ** FIX+ (1: 1, 7: 3, 10: 1)
      *** BODY / all (10: 1)
        **** 10.15.5-13
      *** MATCH-CASE-BODY / all (1: 1, 7: 3)
        **** 1.37.47 (Gamma)
        **** 7.102.0-11 (match_ty)
        **** 7.174.0 (subst)
        **** 7.174.29-31 (subst)
   ** THM+ (5: 2, 7: 3)
      *** BODY / all (5: 2, 7: 3)
        **** 5.18.18-21 (simplify_correct)
        **** 5.18.24-26 (simplify_correct)
        **** 7.101.45-48 (sem_sub__refint_eXrefX)
        **** 7.2.162-165 (weird_trans)
        **** 7.19.112 (match_ty_i_eq__inv_depth_eq) (TODO check)
 * CASE (10: 1, Total: 1)
   ** DEF (10: 1)
      *** 10.18-25 (network_of_app_ta)

# Syntax

Totals: TODO

## Rnm

(needs recounting, like all of these...)
- RENAME (1: 1, 2: 1, 3: 6, 5: 3, 7: 68, 8: 1, 10: 2, 11: 0, Total: 78 / 7)
  * ID (1: 1, 2: 1, 3: 1, 5: 0, 7: 41, 8: 1, 10: 2, 11: 0, Total: 48 / 5) (???)
    ** IND+ (1: 0, 2: 0, 3: 0, 5: 0, 7: 2, 8: 0, 10: 0, 11: 0, Total: 2)
      *** 7.93.1 (tvar -> varid)
      *** CONSTRUCTOR (1: 0, 2: 0, 3: 0, 5: 0, 7: 1, 8: 0, 10: 0, 11: 0, Total: 1 / 1)
        **** 7.193.0 (ty)
    ** Def (1: 0, 2: 1, 3: 0, 5: 0, 7: 8, 8: 0, 10: 0, 11: 0, Total: 9)
      *** 2.5.53 (primitive -> oneArgCbvPrimitive)
      *** 7.93.2-6 (vx -> vX)
      *** 7.93.2-6 (vy -> vY)
      *** 7.93.2-6 (vz -> vZ)
      *** 7.93.2-6 (tx -> tX)
      *** 7.93.2-6 (ty -> tY)
      *** 7.99.9 (sem_eq_k -> sem_eq_w_k)
      *** 7.193.3 (ffree_in_ty -> f_free_in_ty)
      *** 7.193.3 (not_ffree_in_ty -> not_f_free_in_ty)
    ** FIX+ (1: 1, 2: 0, 3: 1, 5: 0, 7: 1, 8: 0, 10: 2, 11: 0, Total: 5)
      *** 1.41.130 (eq -> eq_fn)
      *** 3.960.323 (le_to_nat -> nat_from_le)
      *** 7.193.0-2 (FV -> FFV)
      *** 10.7.1-5 (match_event -> match_app_event)
      *** 10.15.16 (fib -> Fib)
    ** THM+ (1: 0, 2: 0, 3: 0, 5: 0, 7: 31, 8: 1, 10: 0, 11: 0, Total: 32)
      *** 7.2.124 (sub_r_unite_pairs_l__inv -> sub_r_unite_pairs_nf_l__inv)
      *** 7.9.0 (atom_sub_r_union__sub_r_component -> atom_sub_r_union__inv)
      *** 7.10.0 (24 (weird_trans -> sub_r_nf__trans)
      *** 7.10.24 (sub_r__mk_nf_sub_r1 -> sub_r__mk_nf_sub_r)
      *** 7.10.56 (sub_r_nf__trans -> sub_r_nf__trans2)
      *** 7.19.323 (value_sem_sub_k_union__value_sem_sub_k_component -> value_sem_sub_k_i_union__inv)
      *** 7.19.507 (match_ty_nf -> match_ty_i_nf)
      *** 7.19.530 (sem_sub_k_i_nf__inv_depth_le -> sem_sub_k_i_nf__inv_depth_le_1)
      *** 7.19.546 (sem_eq_k_i__inv_depth_eq -> sem_eq_k_i__inv_depth_eq_1)
      *** 7.19.638 (nf_sem_sub_i__sub_d -> TODO)
      *** 7.19.689 (match_ty__unite_pairs_pair -> match_ty_i__unite_pairs_pair)
      *** 7.30.22 (match_ty__value_type -> match_ty__value_type_l)
      *** 7.48.1 (sem_sub_k__sem_eq_k -> sem_sub_k_i__sem_eq_k_i)
      *** 7.50.1 (unite_pairs__preserves_sub_d1 -> unite_pairs__preserves_sub_d_l)
      *** 7.50.1 (unite_pairs__preserves_sub_d2 -> unite_pairs__preserves_sub_d_r)
      *** 7.88.0-64 (sem_sub_k_i_nf__inv_depth_le_1 -> sem_sub_k_i_nf__inv_depth_le_2)
      *** 7.91.3 (unite_pairs_of_nf__preserves_sub_r1 -> unite_pairs_of_nf__preserves_sub_r_l)
      *** 7.91.8 (sub_r__mk_nf_sub_r1 -> sub_r__mk_nf_sub_r_l)
      *** 7.98.25 (sem_sub__eunion__union_e -> sem_sub__eunion__unione)
      *** 7.98.50 (match_ty__reflexive -> match_ty_value_type__reflexive)
      *** 7.125.2 (match_ty_exists -> match_ty__exists_w_v)
      *** 7.145.24 (sem_sub_fresh_var__sem_sub_exist -> sem_sub_fresh_var__sem_sub_exist')
      *** 7.152.8 (sem_sub_k_exist_fresh_l -> sem_sub_exist_fresh_l)
      *** 7.194.6 (not_free_in_ty_pair__inv -> not_f_free_in_ty_pair__inv)
      *** 7.195.4 (match_ty_fbar__inv -> match_ty_bvar__inv)
      *** 7.196.1 (subst_pair -> b_subst_pair)
      *** 7.198.1 (b_subst_var_eq -> b_subst_bvar_eq)
      *** 7.202.40 (b_subst_wf_ty -> b_subst_not_b_free_in_ty)
      *** 7.212.6 (free_in_ty_pair__inv -> f_free_in_ty_pair__inv)
      *** 7.218.6 (f_subst_bvar_eq -> f_subst_bvar)
      *** 7.227.1 (not_f_free_in_ty_fvar_eq__inv -> not_f_free_in_ty_fvar__inv)
      *** 8.79.156 (new_morphism -> morphism_test)
  * BND (1: 0, 2: 0, 3: 3, 5: 3, 7: 7, 8: 0, 10: 0, 11: 0, Total: 13 / 3)
    ** IND+ (1: 0, 2: 0, 3: 0, 5: 1, 7: 0, 8: 0, 10: 0, 11: 0, Total: 1)
      *** RECORD-FIELD / CONSRUCTOR-HYPO / TYPE / PROD / HYPO / all (1: 0, 2: 0, 3: 0, 5: 1)
        **** 5.29.0-4 (EpsilonLogic)
    ** FIX+ (1: 0, 2: 0, 3: 2, 5: 0, 7: 4, 8: 0, 10: 0, 11: 0, Total: 6)
      *** FIX / HYPO / all (1: 0, 2: 0, 3: 2, 5: 0, 7: 4)
        **** 3.960.81-125 (nat_to_le)
        **** 3.960.160 (le_to_nat)
        **** 7.102.0-11 (match_ty)
        **** 7.102.0-11 (match_ty)
        **** 7.102.0-11 (match_ty)
        **** 7.102.0-11 (match_ty)
    ** THM+ (1: 0, 2: 0, 3: 1, 5: 0, 7: 3, 8: 0, 10: 0, 11: 0, Total: 4)
        ***** 3.10289.14 (proc_spec_rx)
        ***** 7.2.162-165 (weird_trans)
        ***** 7.2.162-165 (weird_trans)
        ***** 7.19.257 (match_ty_i__transitive_on_value_type)
    ** Axiom (1: 0, 2: 0, 3: 0, 5: 2, 7: 0, 8: 0, 10: 0, 11: 0, Total: 2)
      *** 5.18.5 (evalChoose)
      *** 5.18.5 (evalChoose)
  * CASE
  * ARG
  * CONSTANT (1: 0, 2: 0, 3: 2, 5: 0, 7: 15, 8: 0, 10: 0, 11: 0, Total: 17 / 1)
    ** Def (1: 0, 2: 0, 3: 0, 5: 0, 7: 4, 8: 0, 10: 0, 11: 0, Total: 4)
      *** BODY / APP / ARGS / all (1: 0, 2: 0, 3: 0, 5: 0, 7: 4)
        **** 7.93.2-6 (tX)
        **** 7.93.2-6 (tX)
        **** 7.93.2-6 (tY)
        **** 7.93.2-6 (tY)
    ** Fix+ (1: 0, 2: 0, 3: 0, 5: 0, 7: 1, 8: 0, 10: 0, 11: 0, Total: 1)
      *** MATCH-CASE / HYPO / APP / F / all (1: 0, 2: 0, 3: 0, 5: 0, 7: 1)
        **** 7.193.6-8 (match_ty)
    ** THM+ (1: 0, 2: 0, 3: 2, 5: 0, 7: 10, 8: 0, 10: 0, 11: 0, Total: 12)
      *** HYPO (1: 0, 2: 0, 3: 0, 5: 0, 7: 2)
        **** HYPO / APP / F / all (1: 0, 2: 0, 3: 0, 5: 0, 7: 2)
          ***** 7.194.6 (not_free_in_ty_pair__inv)
          ***** 7.212.6 (f_free_in_ty_pair__inv)
      *** BODY (1: 0, 2: 0, 3: 2, 5: 0, 7: 8)
        **** BODY / APP (1: 0, 2: 0, 3: 2, 5: 0, 7: 8)
          ***** BODY / APP / ARGS / all (1: 0, 2: 0, 3: 1, 5: 0, 7: 0)
            ****** 3.960.154 (nat_le_inverse)
          ***** BODY / APP / F / all (1: 0, 2: 0, 3: 1, 5: 0, 7: 8)
            ****** 3.960.323 (nat_le_inverse)
            ****** 7.194.6 (not_f_free_in_ty_pair__inv)
            ****** 7.194.6 (not_f_free_in_ty_pair__inv)
            ****** 7.198.1 (b_subst_bvar_eq)
            ****** 7.198.2 (b_subst_bvar_neq)
            ****** 7.198.2 (b_subst_bvar_neq)
            ****** 7.212.6 (f_free_in_ty_pair__inv)
            ****** 7.212.6 (f_free_in_ty_pair__inv)
            ****** 7.218.8 (b_subst_fvar)


## Qfy

- QUALIFY (1: 6, 2: 0, 3: 0, 5: 0, 8: 0, 10: 0, 11: 0, Total: 6 / 1)
  ** CONST (1: 6, 2: 0, 3: 0, 5: 0, 8: 0, 10: 0, 11: 0, Total: 6 / 1)
    ** DEF (1: 6, 2: 0, 3: 0, 5: 0, 8: 0, 10: 0, 11: 0)
      *** BODY / APP / F / all (1: 6, 2: 0, 3: 0, 5: 0)
        **** 1.37.13-19 (R)
        **** 1.37.13-19 (R)
        **** 1.37.19-21 (Gamma2)
        **** 1.37.19-21 (Gamma2)
        **** 1.37.21-24 (transitive_closure)
        **** 1.37.21-24 (transitive_closure)

## Ufy

- UNQUALIFY (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 1, 10: 0, 11: 0, Total: 1 / 1)
  ** CONST (1: 0, 2: 0, 3: 0, 5: 0, 7: 0, 8: 1, 10: 0, 11: 0, Total: 1 / 1)
    ** BODY / APP / F / ARGS / all (2: 0, 3: 0, 5: 0, 7: 0, 8: 1)
      *** 8.75.6 (_R'_)


