Time From Transitions Require Import Relations.
Time From RecordUpdate Require Import RecordSet.
Time Generalizable Variables all.
Time
Definition _zoom `{Setter A C proj} T (r : relation C C T) :
  relation A A T := zoom proj (fun c => set proj (fun _ => c)) r.
Time Arguments _zoom {A} {C} proj {H} {T} r.
