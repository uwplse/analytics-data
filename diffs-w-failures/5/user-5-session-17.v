Require Import Analytical.Analytics.
Goal _ ~ (forall a b, a /\ b).
intro H.
specialize H with False False.
intuition.
Qed.
