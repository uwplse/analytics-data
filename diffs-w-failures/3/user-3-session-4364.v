Time Class Default T :=
         default : T.
Time #[local]Ltac mkDefault := unfold Default; constructor; exact default.
Time Hint Extern 1 (Default _) => mkDefault: typeclass_instances.
Time #[local]Notation cache_default := _ (only parsing).
Time Instance unit_def : (Default unit) := cache_default.
Time Instance nat_def : (Default nat) := cache_default.
Time Instance list_def  A: (Default (list A)) := cache_default.
Time Instance option_def  A: (Default (option A)) := cache_default.
Time
Instance pair_def  A B (defA : Default A) (defB : Default B):
 (Default (A * B)) := cache_default.
