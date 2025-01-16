import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Mathlib.Tactic.Tauto

variable {α : Type*}

def rank [BEq α] [LawfulBEq α] (x : α) (s : List α) (max_int : Nat) : Nat :=
  match s with
  | List.nil => max_int
  | List.cons y s => if x == y && !(List.contains s x) then
                        s.length
                      else
                        rank x s max_int

theorem rank_range [BEq α] [LawfulBEq α] (s : List α) (x : α) (max_int : Nat) :
                  x ∈ s ->
                  rank x s max_int < s.length := by
induction s with intros h₂
| nil => cases h₂
| cons a b => simp [rank] at *; split
              . omega
              . simp_all
                cases h₂ <;> simp_all <;> omega
