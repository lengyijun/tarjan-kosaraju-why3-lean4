import Mathlib.Tactic.Tauto

structure Rapport (x : V) (s : List V) where
  s1 : List V
  last : x ∈ s -> ∃ s2, s1 ++ x :: s2 = s

def split_once [DecidableEq V] (x : V) (s: List V) : Rapport x s := match s with
| [] => {
          s1 := []
          last := by tauto
        }
| y :: s => if dite : x = y then
              {
                s1 := []
                last := by tauto
              }
            else
              let ⟨s1, last⟩ := split_once x s
              {
                s1 := y :: s1
                last := by intros h
                           cases h
                           . tauto
                           . obtain ⟨s3, h⟩ := last (by tauto)
                             subst s
                             exists s3
              }
