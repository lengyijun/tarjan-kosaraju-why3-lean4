import ListHelper.Basic
import Mathlib.Tactic.Tauto

def rip [DecidableEq V] (x : V) (s: List V) : (List V × List V) := match s with
| [] => ([], [])
| y :: s => if x = y then
              (x :: [], s)
            else
              let (s1, s2) := rip x s
              (y :: s1, s2)

theorem rip_is_last [DecidableEq α] (x : α) (s : List α) :
x ∈ s -> is_last x (rip x s).fst := by
induction s
. tauto
. simp [rip]
  intros
  split <;> simp
  . tauto
  . rename_i h _
    cases h
    . tauto
    . rename_i y s1 induction_step h₃ h₄
      obtain ⟨w, h⟩ := induction_step h₄
      exists (y :: w)
      rw [h]
      tauto

theorem rip_combine [DecidableEq α] (x : α) (s : List α) :
(rip x s).fst ++ (rip x s).snd = s := by
induction s
. tauto
. simp [rip]
  split <;> simp <;> assumption
