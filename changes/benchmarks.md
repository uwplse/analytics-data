Here are the benchmarks from the paper for Q2. See [all-changes.md](./all-changes.md) for
the breakdown and classification of the changes that revealed the patterns for these
benchmarks. Please check the [README](../README.md) for notes about this data.

Also note that the changes we detected in the Q2 analysis were changes in terms, not in proof
scripts. So I do not list changes in proofs explicitly in here.
I do sometimes discuss them when they are interesting.
Certain kinds of automation (say, proof repair tools) should of course
consider the proofs changed in these sessions.
When using these benchmarks to drive tool development, we recommend
looking at the entire session for information relevant to measuring
the success of your particular tool.

The best way to present these will be to eventually have the analysis commit
each change using `--date` to mark the timestamp, so it is easy to see the user
editing multiple files at the same time. I will most likely get to this after
the talk due to time constraints, but feel free to submit a pull request if you
modify the analysis and do this in your own branch first. (You will need to
make sure you always get the correct timestamps from the raw data, which is not true
yet for some users; see the [README](../README.md) for more information.)

Times are in Pacific.

# Incremental Development of Inductive Types

Success for these benchmarks means partial or complete automation of the 
manual steps the users took in the development of later definitions, theorems, and proofs,
in response to the earlier changes that the users made to inductive types.

Note that records in Coq are inductive types with a single constructor, the fields
for which are hypotheses of that constructor.

## Benchmark 1

User [5](https://github.com/uwplse/analytics-data/tree/master/diffs-annotated-with-times/5), Sessions [18](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/5/user-5-session-18.v), [19](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/5/user-5-session-19.v), [27](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/5/user-5-session-27.v), [33](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/5/user-5-session-33.v), and [35](https://github.com/uwplse/analytics-data/blob/master/diffs-annotated-with-times/5/user-5-session-35.v).

* Start time: 2019-08-12 09:26:35.67
* Finish time: 2019-09-01 09:52:08.35.
* Relevant changes: 60

Note that all changes for User 5 show up as successes in the processed data due to the
user's use of a Custom UI that does not distinguish between these. Intermediate
timestamps for User 5 are correct.

### 5.18 (start time: 2019-08-12 09:26:35.67, relevant changes: 10)

1. The user adds constructors `Int`, `Plus`, `Times`, and `Minus` to
the inductive type `Term` in [5.18.7.1-4](https://github.com/uwplse/analytics-data/commit/9ba76d98852bc05e691854948d1510fc911eea93#diff-173bdb1576f0b722cd01570dda7d0ef6).

2. The user adds cases corresponding to each of `Int`, `Plus`, `Times`, and `Minus`
to the definition `simplify` in [5.18.13-15.1-4](https://github.com/uwplse/analytics-data/compare/340cb9fb53a1454d5d72f450f2b8fd205591edd8..dbc37b8a35ba02e3b11ece041ba38ae8a214ead6).
The user starts with only `Int`, which must fail, then adds the others in
the next attempt. All of this takes less than a minute.

3. In [5.18.28.1-2](https://github.com/uwplse/analytics-data/commit/428960451de13bf138d880371b268f9243bd0775#diff-173bdb1576f0b722cd01570dda7d0ef6),
the user modifies two fields of the record `EpsilonLogic`: `evalEqTrue` and `evalEqFalse`.

### 5.19 (start time: 2019-08-12 18:28:59.48, relevant changes: 41)

1. The user starts by continuing to modify `EpsilonLogic` in [5.19.5.1](https://github.com/uwplse/analytics-data/commit/2894ba5928f7fe963c8a1d8d2b31fb5cd3858df7#diff-86d76448a54765ff094f8c80cd8be3a0),
this time starting with `evalChoose`.

2. The user extends `EpsilonLogic` with a new field `evalPlus` in
[5.19.5-7.1](https://github.com/uwplse/analytics-data/compare/2894ba5928f7fe963c8a1d8d2b31fb5cd3858df7..49ad0ac21d49dac8454385945fdf5e2cfb9abf90),
then with `evalMinus` and `evalTimes` in
[5.19.7-8.1-2](https://github.com/uwplse/analytics-data/commit/08436be993b76fa3b4f9e8673acc78fbb12d79d1#diff-86d76448a54765ff094f8c80cd8be3a0).

3. Next, the user makes the changes to `Term` seen in Figure 6 on the left.
This happens over several commits. First, in
[5.19.24.1-7](https://github.com/uwplse/analytics-data/commit/8fc49439bcfc887ee2493d9562bd212b2bd1a2bf#diff-86d76448a54765ff094f8c80cd8be3a0),
the user extends `Term` with constructors `Bool`, `And`, `Or`, `Not`, `Implies`,
and `If`. The user also moves the `Int` constructor down below `Int`.

4. The user then removes the constructor `Implies` from `Term`
in [5.19.25.1](https://github.com/uwplse/analytics-data/commit/0e679efd22f7ae6447c8fc5641090a5427240602#diff-86d76448a54765ff094f8c80cd8be3a0).

5. To wrap up the change to `Term`, the user fixes a mistake in `Not` in
[5.19.26.1](https://github.com/uwplse/analytics-data/commit/a282a80381cd7c89faea21c63af3887fb2a86537). This is most likely due to
the attempt at extending `EpsilonLogic` in
[5.19.23-26.1-16](https://github.com/uwplse/analytics-data/compare/ff27a314a04df3b8ec56090bff68c3060923a658..a282a80381cd7c89faea21c63af3887fb2a86537)
with fields corresponding to each of the new constructors, and modifying
existing fields to use those constructors as well. This attempt
must have failed the first time around. These changes succeed on a new day.

6. The user next makes the changes to `identity` seen in Figure 6 on the right. In [5.19.26-28.1-6](https://github.com/uwplse/analytics-data/compare/a282a80381cd7c89faea21c63af3887fb2a86537..641426ca64c96b20b5fe1c450b95f4cd983616dc),
the user extends `identity` with cases corresponding to each of the new
constructors in `Term`.

7. In [5.19.29.1-2](https://github.com/uwplse/analytics-data/commit/88831cd564e0fa8685cf0d37a2941d105220dfd5#diff-86d76448a54765ff094f8c80cd8be3a0),
the user changes `vTrue` and `vFalse` (once fields of `EpsilonLogic`, now removed)
in `eval_eq_true_or_false` with applications of the new constructor `Bool`
of `Term` to `true` and `false`, respectively. This is similar to the change
in `EpsilonLogic` after removing those fields.

8. Finally, in [5.19.9-36.1-5](https://github.com/uwplse/analytics-data/compare/40b88925739c1ffb7c130395cc57911521987a95..ada30a73e03268cf378ce10849f697b04e4ccd4d),
the user extends `free_vars` with new cases for each of the new `Term` constructors as well. The user then attempts some later proofs before
ending the session (typically closing the file in the IDE).

### 5.27 (start time: 2019-08-28 15:16:25.35, relevant changes: 3)

1. Weeks have passed. The user has modified `Term` to extend it with
new constructors `Bools`, `Ints`, and `In`, as we see in 5.([19.24](https://github.com/uwplse/analytics-data/blob/8fc49439bcfc887ee2493d9562bd212b2bd1a2bf/diffs-annotated-with-times/5/user-5-session-19.v)-[27.1](https://github.com/uwplse/analytics-data/blob/7e75933b596616de7a54470d99369a3d6a06df46/diffs-annotated-with-times/5/user-5-session-27.v)).1-3 ([diff](https://www.diffchecker.com/IjqbTjc7)).

### 5.33 (start time: 2019-09-01 08:51:13.15, relevant changes: 3)

1. A few days later, in [5.33.0-3.1-3](https://github.com/uwplse/analytics-data/compare/a338aa6c435dedb41665ab30fe17eb73020ad07f..ed89b37b72a4f7d8f463e64a21f1893344d39fdb),
the user extends `identity` with new cases for the new constructors in `Term`.
This takes less than a minute but the user does omit the `In` case the first
time around.

### 5.35 (start time: 2019-09-01 09:19:56.08, relevant changes: 3)

1. Soon after, in [5.35.0-3.1-3](https://github.com/uwplse/analytics-data/compare/6cdd9e85eefb602ec4c576ced438d416788e4fc8..111a4ec95023e0004b7fbd1ff9b8a02aabcbfa44),
the user makes the analogous changes to `free_vars`.

2. The session ends at 2019-09-01 09:52:08.35.

## Benchmark 2

TODO WIP


