def precedes (x y: α) (s: List α) : Prop := ∃ s1 s2, s = s1 ++ (x :: s2) /\ y ∈ (x :: s2)
