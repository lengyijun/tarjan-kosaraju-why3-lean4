import Mathlib.Data.Finset.Basic
open Finset

theorem pertinent
[BEq V] [LawfulBEq V] [DecidableEq V]
{sccs : List (Finset V)} :
∀ (init : Finset V),
List.foldl Union.union init sccs = init ∪ List.foldl Union.union ∅ sccs
:= by
induction sccs <;> simp
rename_i scc sccs induction_step
intros
rw [induction_step, induction_step scc]
simp

theorem union_helper
[BEq V] [LawfulBEq V] [DecidableEq V]
{x : V} {sccs : List (Finset V)} :
x ∈ List.foldl Union.union ∅ sccs ↔ (∃ cc, x ∈ cc /\ cc ∈ sccs) := by
induction sccs
. tauto
. simp
  rw [pertinent]
  simp
  rename_i h
  rw [h]
  constructor <;> intros h <;> cases h
  . tauto
  . rename_i h
    obtain ⟨cc, h⟩ := h
    use cc
    tauto
  . rename_i h
    obtain ⟨_, h⟩ := h
    cases h
    . rename_i h
      rw [<- h]
      tauto
    . tauto
