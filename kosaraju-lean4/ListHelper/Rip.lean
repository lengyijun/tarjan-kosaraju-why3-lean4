import ListHelper.Basic
import Mathlib.Tactic.Tauto

structure Rapport (x : V) (s : List V) where
  s1 : List V
  s2 : List V
  combine : s1 ++ s2 = s
  last : x ∈ s -> is_last x s1

def rip [DecidableEq V] (x : V) (s: List V) : Rapport x s := match s with
| [] => {
          s1 := []
          s2 := []
          combine := by tauto
          last := by tauto
        }
| y :: s => if dite : x = y then
              {
                s1 := x :: []
                s2 := s
                combine := by subst y; tauto
                last := by tauto
              }
            else
              let ⟨s1, s2, combine, last⟩ := rip x s
              {
                s1 := y :: s1
                s2 := s2
                combine := by subst s; tauto
                last := by intros h
                           cases h
                           . tauto
                           . obtain ⟨s3, h⟩ := last (by tauto)
                             exists (y :: s3)
                             tauto
              }
