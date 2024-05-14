import Mathlib.Data.Finset.Basic
open Finset

theorem pertinent
[BEq V] [LawfulBEq V] [DecidableEq V]
{sccs : List (Finset V)} :
∀ (init : Finset V),
List.foldl (fun x x_1 => x ∪ x_1) init sccs = init ∪ List.foldl (fun x x_1 => x ∪ x_1) ∅ sccs
:= by
induction sccs
. simp
. intros init
  simp
  rename_i scc sccs induction_step
  rw [induction_step, induction_step scc]
  simp

theorem jiting
[BEq V] [LawfulBEq V] [DecidableEq V]
{x : V} {sccs : List (Finset V)} :
∀ (init : Finset V),
x ∈ List.foldl (fun x x_1 => x ∪ x_1) init sccs ↔ x ∈ init \/ x ∈ List.foldl (fun x x_1 => x ∪ x_1) ∅ sccs
:= by
induction sccs
. tauto
. intros init
  simp
  rename_i head tail induction_step
  have h₁ := induction_step (init ∪ head)
  have h₂ := induction_step head
  rw [h₁, h₂]
  simp
  tauto

theorem union_helper
[BEq V] [LawfulBEq V] [DecidableEq V]
{x : V} {sccs : List (Finset V)} :
x ∈ List.foldl (fun x x_1 => x ∪ x_1) ∅ sccs ↔ (∃ cc, x ∈ cc /\ cc ∈ sccs) := by
induction sccs
. tauto
. simp_all
  rename_i h
  rw [jiting, h]
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
