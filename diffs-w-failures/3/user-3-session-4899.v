Time From Perennial.Goose Require Import Machine.
Time Class HasGoZero (T : Type) :=
         zeroValue : T.
Time Arguments zeroValue T {_}.
Time Instance uint64_zero : (HasGoZero uint64) := 0.
Time Instance bool_zero : (HasGoZero bool) := false.
Time Instance string_zero : (HasGoZero string) := ""%string.
Time Section GoModel.
Time Context `{GoModel}.
Time #[global]Instance byte_zero : (HasGoZero byte) := byte0.
Time #[global]Instance ptr_zero  ty: (HasGoZero (Ptr ty)) := (nullptr _).
Time #[global]Instance file_zero : (HasGoZero File) := nilFile.
Time #[global]
Instance slice_zero  T: (HasGoZero (slice.t T)) := (slice.nil _).
Time End GoModel.
