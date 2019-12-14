Here are the benchmarks from the paper for Q2. See [all-changes.md](./all-changes.md) for
the breakdown and classification of the changes that revealed the patterns for these
benchmarks. Please check the [README](../README.md) for notes about this data.

**Timestamps**: 
All times are in Pacific and come from the _raw_ data.
Please do not rely on timestamps in the _processed_ data in the 
linked commits.
As noted in the README,
intermediate timestamps are in general not yet correct in 
the processed data you see in the linked commits, as these
were added experimentally in response to reviewer feedback.
The start and end time for each benchmark as a whole are
the start time of the first session and the end time of the last session;
this sometimes includes changes unrelated to the benchmark.
More granular times, when discussed in the paper and in this document,
are also taken from the raw data.
I will run a reanalysis at some point after the camera-ready
and update the commits to point to the data with the correct
intermediate timestamps.

**Presentation**: The best way to present these will be to eventually have the analysis commit
each change using `--date` to mark the timestamp, so it is easy to see the user
editing multiple files at the same time. I will most likely get to this after
the talk due to time constraints, but feel free to submit a pull request if you
modify the analysis and do this in your own branch first.
We will need to fix the above timestamp issues in the analysis first.

**Proofs and New Terms**: Also note that the changes we detected in the Q2 analysis were changes in terms, not in proof
scripts. So I do not list changes in proofs explicitly in here.
I do sometimes discuss them when they are interesting.
Certain kinds of automation (say, proof repair tools) should of course
consider the proofs changed in these sessions.
Similarly, for the analysis, we looked only at changes to existing terms, considering new terms only as part of cutting
an intermediate definition or lemma for an existing term.
For the benchmarks, I discuss new definitions when they are interesting.
When using these benchmarks to drive tool development, we recommend
looking at the entire session for information relevant to measuring
the success of your particular tool.

# Incremental Development of Inductive Types

Success for these benchmarks means partial or complete automation of the 
manual steps the users took in the development of later definitions, theorems, and proofs,
in response to the earlier changes that the users made to inductive types.

Note that records in Coq are inductive types with a single constructor, the hypotheses
for which are the fields of the record. (Records are additionally equipped with automatically 
generated named projection functions for those fields, which simply eliminate over the record's only
constructor and return the appropriate hypothesis.)

## Benchmark 1

User [5](https://github.com/uwplse/analytics-data/tree/master/diffs-annotated-with-times/5), Sessions [18](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/5/user-5-session-18.v), [19](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/5/user-5-session-19.v), [27](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/5/user-5-session-27.v), [33](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/5/user-5-session-33.v), and [35](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/5/user-5-session-35.v).

* Start time: 2019-08-12 09:26:35.67
* Finish time: 2019-09-01 09:52:08.35.
* Relevant changes: 63

Note that all changes for User 5 show up as successes in the processed data due to the
user's use of a Custom UI that does not distinguish between these.

### 5.18 (start time: 2019-08-12 09:26:35.67, relevant changes: 10)

1. The user adds constructors `Int`, `Plus`, `Times`, and `Minus` to
the inductive type `Term` in [5.18.7.1-4](https://github.com/uwplse/analytics-data/commit/9ba76d98852bc05e691854948d1510fc911eea93#diff-173bdb1576f0b722cd01570dda7d0ef6).

2. The user adds cases corresponding to each of `Int`, `Plus`, `Times`, and `Minus`
to the definition `simplify` in [5.18.13-15.1-4](https://github.com/uwplse/analytics-data/compare/340cb9fb53a1454d5d72f450f2b8fd205591edd8..dbc37b8a35ba02e3b11ece041ba38ae8a214ead6).
The user starts with only `Int`, which must fail, then adds the others in
the next attempt.

3. In [5.18.28.1-2](https://github.com/uwplse/analytics-data/commit/428960451de13bf138d880371b268f9243bd0775#diff-173bdb1576f0b722cd01570dda7d0ef6),
the user modifies two fields of the record `EpsilonLogic`: `evalEqTrue` and `evalEqFalse`.

### 5.19 (start time: 2019-08-12 18:28:59.48, relevant changes: 44)

1. As seen in 5.([18.29](https://github.com/uwplse/analytics-data/blob/fbae602cf8eb85e5ff89195034fd80529d27e124/diffs-annotated-with-times/5/user-5-session-18.v)-[19.0](https://github.com/uwplse/analytics-data/blob/5e53d111a38bb3dd9bcb46ae675774eed053d970/diffs-annotated-with-times/5/user-5-session-19.v)).1-3 ([diff](https://www.diffchecker.com/ByDlZAJU)), the user starts
by renaming `simplify` to `identity` and `simplify_correct` to `identity_correct`. The user also adds a new field to `EpsilonLogic`. 

2. The user then continues to modify `EpsilonLogic` in [5.19.5.1](https://github.com/uwplse/analytics-data/commit/2894ba5928f7fe963c8a1d8d2b31fb5cd3858df7#diff-86d76448a54765ff094f8c80cd8be3a0),
this time starting with `evalChoose`.

3. The user extends `EpsilonLogic` with a new field `evalPlus` in
[5.19.5-7.1](https://github.com/uwplse/analytics-data/compare/2894ba5928f7fe963c8a1d8d2b31fb5cd3858df7..49ad0ac21d49dac8454385945fdf5e2cfb9abf90),
then with `evalMinus` and `evalTimes` in
[5.19.7-8.1-2](https://github.com/uwplse/analytics-data/commit/08436be993b76fa3b4f9e8673acc78fbb12d79d1#diff-86d76448a54765ff094f8c80cd8be3a0).

4. Next, the user makes the changes to `Term` seen in Figure 6 on the left.
This happens over several commits. First, in
[5.19.24.1-7](https://github.com/uwplse/analytics-data/commit/8fc49439bcfc887ee2493d9562bd212b2bd1a2bf#diff-86d76448a54765ff094f8c80cd8be3a0),
the user extends `Term` with constructors `Bool`, `And`, `Or`, `Not`, `Implies`,
and `If`. The user also moves the `Int` constructor down below `If`.

5. The user then removes the constructor `Implies` from `Term`
in [5.19.25.1](https://github.com/uwplse/analytics-data/commit/0e679efd22f7ae6447c8fc5641090a5427240602#diff-86d76448a54765ff094f8c80cd8be3a0).

6. To wrap up the change to `Term`, the user fixes a mistake in `Not` in
[5.19.26.1](https://github.com/uwplse/analytics-data/commit/a282a80381cd7c89faea21c63af3887fb2a86537). This is most likely due to
the attempt at extending `EpsilonLogic` in
[5.19.23-26.1-16](https://github.com/uwplse/analytics-data/compare/ff27a314a04df3b8ec56090bff68c3060923a658..a282a80381cd7c89faea21c63af3887fb2a86537)
with fields corresponding to each of the new constructors, and modifying
existing fields to use those constructors as well. This attempt
must have failed the first time around when `Not` expected two arguments.
These changes succeed on a new day.

7. The user next makes the changes to `identity` seen in Figure 6 on the right. In [5.19.26-28.1-6](https://github.com/uwplse/analytics-data/compare/a282a80381cd7c89faea21c63af3887fb2a86537..641426ca64c96b20b5fe1c450b95f4cd983616dc),
the user extends `identity` with cases corresponding to each of the new
constructors in `Term`.

8. In [5.19.29.1-2](https://github.com/uwplse/analytics-data/commit/88831cd564e0fa8685cf0d37a2941d105220dfd5#diff-86d76448a54765ff094f8c80cd8be3a0),
the user changes `vTrue` and `vFalse` (once fields of `EpsilonLogic`, now removed)
in `eval_eq_true_or_false` with applications of `Eval` to applications of the new constructor `Bool`
of `Term` to `true` and `false`, respectively. This is similar to the change
in `EpsilonLogic` after removing those fields.

9. Finally, in [5.19.9-36.1-5](https://github.com/uwplse/analytics-data/compare/40b88925739c1ffb7c130395cc57911521987a95..ada30a73e03268cf378ce10849f697b04e4ccd4d),
the user extends `free_vars` with new cases for each of the new `Term` constructors as well. The user then attempts some later proofs before
ending the session (typically closing the file in the IDE).

### 5.27 (start time: 2019-08-28 15:16:25.35, relevant changes: 3)

1. Weeks have passed. The user has modified `Term` to extend it with
new constructors `Bools`, `Ints`, and `In`, as we see in 5.([19.24](https://github.com/uwplse/analytics-data/blob/8fc49439bcfc887ee2493d9562bd212b2bd1a2bf/diffs-annotated-with-times/5/user-5-session-19.v)-[27.1](https://github.com/uwplse/analytics-data/blob/7e75933b596616de7a54470d99369a3d6a06df46/diffs-annotated-with-times/5/user-5-session-27.v)).1-3 ([diff](https://www.diffchecker.com/IjqbTjc7)).

### 5.33 (start time: 2019-09-01 08:51:13.15, relevant changes: 3)

1. A few days later, in [5.33.0-3.1-3](https://github.com/uwplse/analytics-data/compare/a338aa6c435dedb41665ab30fe17eb73020ad07f..ed89b37b72a4f7d8f463e64a21f1893344d39fdb),
the user extends `identity` with new cases for the new constructors in `Term`.
The user omits the `In` case the first time around.

### 5.35 (start time: 2019-09-01 09:19:56.08, relevant changes: 3)

1. Soon after, in [5.35.0-3.1-3](https://github.com/uwplse/analytics-data/compare/6cdd9e85eefb602ec4c576ced438d416788e4fc8..111a4ec95023e0004b7fbd1ff9b8a02aabcbfa44),
the user makes the analogous changes to `free_vars`.

2. The session ends at 2019-09-01 09:52:08.35.

## Benchmark 2

User [1](https://github.com/uwplse/analytics-data/tree/master/diffs-annotated-with-times/1), Sessions [37](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/1/user-1-session-37.v) and [41](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/1/user-1-session-41.v).

* Start time: 2019-09-04 22:23:40.27
* Finish time: 2019-09-06 16:17:16.94
* Relevant changes: 61

### 1.37 (start time: 2019-09-04 22:23:40.27, relevant changes: 26)

1. In [1.37.3.1-2](https://github.com/uwplse/analytics-data/commit/2b01e33c93ebd83ed086214ecbc1cff8a8356467#diff-16df098de71249ca8d704f5f6b2583e5),
the user starts by adding a body to the parameter `ST`, defining
it as an inductive type with a single new constructor `SInt`.

2. Next, in [1.37.4.1-2](https://github.com/uwplse/analytics-data/commit/ae812a8bb8bc351d2a4ce08dc6ba319f42b1f4b8#diff-16df098de71249ca8d704f5f6b2583e5),
the user adds constructors `SBool` and `SFun` to `ST`.
The user then adds `SRec` to `ST` in [1.37.4-12.1](https://github.com/uwplse/analytics-data/compare/ae812a8bb8bc351d2a4ce08dc6ba319f42b1f4b8..c2f34747fb2c2b5d196a3d1ed4383c36bbcd1eca).

3. The user changes `SRec` in [1.37.13.1](https://github.com/uwplse/analytics-data/commit/24fc093a48c5e3ca504f8de6c8783ca13bf4e657#diff-16df098de71249ca8d704f5f6b2583e5).

4. In [1.37.25.1-5](https://github.com/uwplse/analytics-data/commit/d489f81ca6435e054f557ea840d8ed8d697a3ad7#diff-16df098de71249ca8d704f5f6b2583e5),
the user fills in the parameter `GT` as a new inductive type with
constructors `GDyn`, `GInt`, `GBool`, and `GRec`.

5. The user then adds `GRow` to `GT` in [1.37.26.1-2](https://github.com/uwplse/analytics-data/commit/fae52f1fd4f7d69aeffb60135e8fd8f36f1b4972#diff-16df098de71249ca8d704f5f6b2583e5).
The user also fills in the empty `Gamma` as a fixpoint a case for `GDyn`
and a catch-all.

6. The user extends `Gamma` with case `GInt` in [1.37.27.1](https://github.com/uwplse/analytics-data/commit/469db2a6262f5bbda406616d5678d47abf52903b#diff-16df098de71249ca8d704f5f6b2583e5),
then adds `GFun` to `GT` and cases `GBool` and `GFun G_1 G_2` to `Gamma` in [1.37.28-31.1-3](https://github.com/uwplse/analytics-data/compare/4f603266268acc346008b0182f7e2505161cf36d..4b069ba7dffe536eec00715edd850154ae2da798).

7. In [1.37.31-44.1](https://github.com/uwplse/analytics-data/compare/4b069ba7dffe536eec00715edd850154ae2da798..98da87a629b43b113c59384cb11f677d9f98d4a3),
the user extends `Gamma` with a case `GRec` after several failed attempts.

8. The user then extends `Gamma` further with a case `(R, G)` in [1.37.44-46.1](https://github.com/uwplse/analytics-data/compare/98da87a629b43b113c59384cb11f677d9f98d4a3..6e1b9b31e980d59180965545db1f99204e4b55be)
and a case `(O, G)` in [1.37.47.1](https://github.com/uwplse/analytics-data/commit/932711dd88c8a8f754f68991bedb7b404db20966#diff-16df098de71249ca8d704f5f6b2583e5).

9. The user changes the `GRec` case of `Gamma` in [1.37.50-52.1-3](https://github.com/uwplse/analytics-data/compare/45cee1be2f8e356d2404fb5dcf86555a8a94015c..816d42cdfc703417b4c56cd5e9f0746cb9299ccf),
filling in a placeholder function. There, the user also turns parameter
`Alpha` into an inductive type with a single new constructor `alpha_int`.

10. The user fills in the placeholder case in [1.37.52-55.1](https://github.com/uwplse/analytics-data/compare/816d42cdfc703417b4c56cd5e9f0746cb9299ccf..de8a2de8bee7beede982c4dc078f3e1f2108a0e5),
with the new case `GRow l`, which is similar to `GRec`.

11. The changes in [1.37.52-56.1-2](https://github.com/uwplse/analytics-data/compare/816d42cdfc703417b4c56cd5e9f0746cb9299ccf..4e1231197af1fa075bbc499f312d6b0dce9d8a36)
also show the user adding constructors `alpha_bool` and `alpha_fun`
to `Alpha`. This concludes the session.

### 1.41 (start time: 2019-09-04 23:41:50.63, relevant changes: 35)

1. The next session begins the same day, soon after.
In [1.41.0-3.1](https://github.com/uwplse/analytics-data/compare/b19de98b8490a6213fd1321992270e2305130b5a..e5ce3d9f7c8cac489600cba7007991072480173e),
the user adds `alpha_rec_mt` to `Alpha`. This takes a few tries.

2. The user keeps extending `Alpha`. The user adds `alpha_rec_cons_req` and `alpha_row_mt` in [1.41.3-8.1-2](https://github.com/uwplse/analytics-data/compare/e5ce3d9f7c8cac489600cba7007991072480173e..eb54d11ffdc3f7bef168fe1101d196b47147baf8).
Then, in [1.41.8-10.1](https://github.com/uwplse/analytics-data/compare/eb54d11ffdc3f7bef168fe1101d196b47147baf8..9189529eea42091860aae41c468781a5ed8f74d2),
the user adds `alpha_rec_cons_none`, and in [1.41.10-12.1](https://github.com/uwplse/analytics-data/compare/9189529eea42091860aae41c468781a5ed8f74d2..2a5978c5934f503128572a2ca9f33822b3a4874e),
the user adds `alpha_rec_cons_opt`. Each of these takes a few tries.

3. In [1.41.12-19.1-4](https://github.com/uwplse/analytics-data/compare/2a5978c5934f503128572a2ca9f33822b3a4874e..680118ae10639c2703e80701133630aaadbe0127),
the user adds `alpha_row_cons_none`, `alpha_row_cons_req`,
`alpha_row_cons_opt`, and `alpha_row_cons_row_skip_hd` to `Alpha`.
The user adds `alpha_gdyn` in [1.41.20.1](https://github.com/uwplse/analytics-data/commit/056ed0a757d8f369864a1ebc5a70b158cbe615cc#diff-c25d7b9e6c43e8e83b60b58b9a5b880b).

4. In [1.41.94-96.1-5](https://github.com/uwplse/analytics-data/compare/0badc15f9d971f11bad5cdd81db8773a7810198c..5ab8e74f7562d7516417cb982c5b861e132b28a4),
the user adds five cases to `eq` corresponding to constructors of `GT`.

5. The user cuts `size_gt` from `eq` in [1.41.96-102.1](https://github.com/uwplse/analytics-data/compare/5ab8e74f7562d7516417cb982c5b861e132b28a4..f962ec51215ed327666a7600e129283572373660)
in order to prove termination for the once empty parameter `eq`
(see [1.41.96-114.1-2](https://github.com/uwplse/analytics-data/compare/5ab8e74f7562d7516417cb982c5b861e132b28a4..f623d1c924afb791f4fd27f7ffe078d078169cba)).
This involves several attempts.

6. [1.41.100.1](https://github.com/uwplse/analytics-data/commit/dd22f9a7e6f9e77c86510e909004893788cdc0f8#diff-c25d7b9e6c43e8e83b60b58b9a5b880b) shows the addition of a case for 
`GRow l` to `size_gt`. [1.41.112.1-2](https://github.com/uwplse/analytics-data/commit/be30f8cb1ca317a35b18163a4da65a10f6bc24a4#diff-c25d7b9e6c43e8e83b60b58b9a5b880b) show the addition of two new cases
to `size_gt`.

7. The user tweaks a case of `size_gt` in [1.41.114.1](https://github.com/uwplse/analytics-data/commit/f623d1c924afb791f4fd27f7ffe078d078169cba#diff-c25d7b9e6c43e8e83b60b58b9a5b880b), then several more in
[1.41.118.1-2](https://github.com/uwplse/analytics-data/commit/fe84fc62f991b24e1d18769979c2bfe53111879f#diff-c25d7b9e6c43e8e83b60b58b9a5b880b).

8. [1.41.114-129.1-9](https://github.com/uwplse/analytics-data/compare/f623d1c924afb791f4fd27f7ffe078d078169cba..1d11189e592b7650612d2243e2a01581a0da0ba0)
show the addition of many more cases to `eq`.

9. In [1.41.130.1](https://github.com/uwplse/analytics-data/commit/e848aa322cbe79ee8a2eba1bf51e7550cfbcd040#diff-c25d7b9e6c43e8e83b60b58b9a5b880b),
the user renames `eq` to `eq_fn`, then defines `eq` using `eq_fn`.

10. The user adds one more case to `eq_fn` in [1.41.141.1](https://github.com/uwplse/analytics-data/commit/de97aaa23825c81adb909116786e47fcca390057#diff-c25d7b9e6c43e8e83b60b58b9a5b880b).

11. The session ends at 2019-09-06 16:17:16.94.

# Repetitive Refactoring of Identifiers

Success for these benchmarks means partial or complete automation of the 
manual steps the users took in renaming related types, constructors, 
definitions, and theorems, as well as their occurrences in other terms.

## Benchmark 3

User [7](https://github.com/uwplse/analytics-data/tree/master/diffs-annotated-with-times/7), Session [93](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/7/user-7-session-93.v).

* Start time: 2019-08-19 08:27:15.72
* Finish time: 2019-08-19 08:53:45.00
* Relevant changes: 7

### 7.93 (start time: 2019-08-19 08:27:15.72, relevant changes: 7)

1. By the second change of this session, the user has
defined an inductive type `ty` (see [the state of the file before the relevant changes](https://github.com/uwplse/analytics-data/blob/80228aa9659f025bd5a270860b6f74a8e6c1b88d/diffs-annotated-with-times/7/user-7-session-93.v)). The user has also tried to define
a second definition `ty` with a different meaning. This definition
has failed.

2. In [7.93.2-6.1-5](https://github.com/uwplse/analytics-data/compare/80228aa9659f025bd5a270860b6f74a8e6c1b88d..c15f5fd243e37dc4f2a76aed4d96d5b181cf6d4e),
the user renames the second `ty` to `tY`. Rather than change only `ty`,
the user also renames `vx` to `vX`, `vy` to `vY`, `vz` to `vZ`, and `tx` to `tX`, all following the same convention. 

3. For the change to succeed, in [7.93.2-6.6-7](https://github.com/uwplse/analytics-data/compare/80228aa9659f025bd5a270860b6f74a8e6c1b88d..c15f5fd243e37dc4f2a76aed4d96d5b181cf6d4e),
the user changes `vx` to `vX` in the body of `tX`, and `vy` to `vY`
in the body of `tY`. In total, the 7 changes to these 5 terms
take four tries over less than two minutes (see raw data for timestamps
for now).

4. The rest of the development is unrelated to this refactoring.
The session ends at 2019-08-19 08:53:45.00.

## Benchmark 4

User [7](https://github.com/uwplse/analytics-data/tree/master/diffs-annotated-with-times/7), Sessions [193](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/7/user-7-session-193.v) and [198](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/7/user-7-session-198.v).

* Start time: 2019-09-03 08:47:45.05
* Finish time: 2019-09-03 09:35:34.64
* Relevant changes: 13

### 7.193 (start time: 2019-09-03 08:47:45.05, relevant changes: 9)

1. At the beginning of the session, as seen in
([174.59](https://github.com/uwplse/analytics-data/blob/a6d3d04212bc0d6d6148ef9e284bb93ae067deba/diffs-annotated-with-times/7/user-7-session-174.v)-[193.2](https://github.com/uwplse/analytics-data/blob/a746a4ce87b617ac8053c8c079c97ff656558690/diffs-annotated-with-times/7/user-7-session-193.v)).1-6 ([diff](https://www.diffchecker.com/5Dz6HAYW)),
the user splits the constructor `TVar` of `ty` into two constructors:
`TBVar` and `TFVar`. At the same time, the user splits the fixpoint
`FV` into two fixpoints: `FFV` and `FBV`, renaming `TVar` to `TFVar` and `TBVar`, respectively, and mapping the other case to empty.
The user also replaces occurrences of `TVar` with `TBVar` inside of definitions `tX` and `tY`.

2. In [7.193.3.1-2](https://github.com/uwplse/analytics-data/commit/556d1e6694bea362735634ef269a2fc3fed2c951#diff-d4b97524adb9b59c8860b3bf9df068d8),
the user renames `ffree_in_ty` to `f_free_in_ty` and `not_ffree_in_ty` to `not_f_free_in_ty`, respectively.
The user also defines `b_free_in_ty` and `not_b_free_in_ty` similarly.

3. In [7.193.6-8.1](https://github.com/uwplse/analytics-data/compare/fdb0cb1b0f0d823d0e724796ebe766533b05d2f0..2018b45a51ee1deb5c7605bd130f53a537e3e2db),
the user renames the `TVar` case of `match_ty` to `TFVar`.

4. All of the changes total in this session take the user less than twenty minutes. The next session starts about half an hour later.

### 7.198 (start time: 2019-09-03 09:34:22.85, relevant changes: 4)

1. In [7.198.1.1-2](https://github.com/uwplse/analytics-data/commit/3ff0f2f44584bc6eaa93d5c74d01423e5dc600fc#diff-401c5a145ce7c67fa6059e1209070785),
the user renames `b_subst_var_eq` -> `b_subst_bvar_eq`, and at the same time changes `TVar ` to `TBVar` in its body. The user attempts to define
`b_subst_bvar_neq` (possibly also a renaming, but we don't have access to an earlier version of this definiton), but this fails since the user
does not change `TVar` in its body yet.

2. The user gets around to renaming both occurrences of `TVar` to `TBVar` inside of `b_subst_bvar_neq` in
[7.198.2.1-2](https://github.com/uwplse/analytics-data/commit/f4c9a7de4083a963c915d4074c65207fafc64c07#diff-401c5a145ce7c67fa6059e1209070785).

3. The session ends soon after at 2019-09-03 09:35:34.64.

## Benchmark 5

User [1](https://github.com/uwplse/analytics-data/tree/master/diffs-annotated-with-times/1), Session [37](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/1/user-1-session-37.v).

* Start time: 2019-09-04 22:23:40.27
* Finish time: 2019-09-04 23:38:29.00
* Relevant changes: 6

### 1.37 (start time: 2019-09-04 22:23:40.27, relevant changes: 6)

1. The user sffd an import in this session, which is what triggers
the refactor. This change does not
fall under our classification, but you can see it
[here](https://github.com/uwplse/analytics-data/commit/adb39e31175d32bf97c3b4a7293f97e6665db73f#diff-16df098de71249ca8d704f5f6b2583e5).
Notably, after this change, `In` now refers to `List.In` as opposed
to `Ensembles.In`. The user thus qualifies all occurrences of
`Ensembles.In` in the file.

2. In [1.37.13-19.1-2](https://github.com/uwplse/analytics-data/compare/24fc093a48c5e3ca504f8de6c8783ca13bf4e657..aef548c723a530b64e738e78ab9d1349307c0a77),
the user qualifies `In` twice in the definition `R`.
The user misses one occurrence the first time around.
This takes about a minute.

3. The user then qualifies `In` twice in `Gamma2`, as seen in
[1.37.19-21.1-2](https://github.com/uwplse/analytics-data/compare/aef548c723a530b64e738e78ab9d1349307c0a77..4d53482ec9b1d8560f8a8dd3e443cc681dbfe6e9).
The user again misses one occurrence the first time around,
but this time is much faster to figure it out.
The whole change from start to finish takes about five seconds.

4. Finally, in [1.37.21-24.1-2](https://github.com/uwplse/analytics-data/compare/4d53482ec9b1d8560f8a8dd3e443cc681dbfe6e9..19bda960b9f552fe69a1e33e0e5a38ff33047a21),
the user qualifies `In` twice in `transitive_closure`.
The user again misses one occurrence the first time around,
and the whole change from start to finish takes about eight seconds.

5. The rest of the development is unrelated to this refactoring.
The session ends at 2019-09-04 23:38:29.00.

# Repetitive Repair of Specifications

## Benchmark 6

WIP.

## Benchmark 7

WIP.

# Interactive Discovery of Programs & Specifications

## Benchmark 8

WIP.

## Benchmark 9

WIP.

## Benchmark 10

WIP.

## Benchmark 11

WIP.

