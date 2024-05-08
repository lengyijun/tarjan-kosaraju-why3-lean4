import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto

def precedes (x y: α) (s: List α) : Prop := ∃ s1 s2, s = s1 ++ (x :: s2) /\ y ∈ (x :: s2)

@[simp]
theorem precedes_refl {x : α} {s : List α} : precedes x x (x :: s) := by
use []
use s
tauto

/-
@[simp]
theorem precedes_trival {x y: α} {s : List α} : y ∈ s -> precedes x y (x :: s) := by
intros
use []
use s
tauto
-/
