import Tarjan.Env
import Tarjan.Dfs

def tarjan [DirectedGraph V Graph]
           [BEq V] [LawfulBEq V] [DecidableEq V]
           (graph: Graph) : Trajectory Graph V graph :=
let e : Env V graph := {
  black := ∅
  gray := ∅
  stack := []
  sccs := []
  num := fun _ => -1
  num_clamp := by tauto
  num_1 := by tauto
  num_infty := by tauto
  valid_gray  := by tauto
  valid_black := by tauto
  disjoint_gb := by tauto
  color := by tauto
  stack_finset := by tauto
  simplelist_stack := by tauto
  decreasing_stack := by tauto
  wf_stack₂ := by tauto
  wf_stack₃ := by tauto
  sccs_in_black := by simp
                      intros _ x h h₁ _
                      specialize h₁ h
                      tauto
  sccs_disjoint := by simp
}
let ⟨n, e', p₁, p₃, p₄, p₅, p₆⟩ := dfs graph (DirectedGraph.vertices graph) e (by tauto) (by tauto)
have empty_gray  : e'.gray  = ∅ := by rw [← p₁.eq_gray]
have empty_stack : e'.stack = [] := by
  have h : e'.stack = [] \/ ∃ x xs, e'.stack = x :: xs := by cases e'.stack <;> tauto
  cases h with
  | inl h => tauto
  | inr h => obtain ⟨x, xs, h⟩ := h
             have h₁ := e'.wf_stack₃ x
             rw [h, empty_gray] at h₁
             tauto
have eq_black : ∀ x, x ∈ DirectedGraph.vertices graph ↔ x ∈ e'.black := by
  intros x
  constructor
  . specialize p₃ x
    rw [empty_gray] at p₃
    simp at p₃
    tauto
  . apply e'.valid_black
{
  sccs_o := e'.sccs
  p₂ := by intros cc
           rw [e'.sccs_in_black]
           constructor <;> intros h <;> simp_all
           . intros x hx
             obtain ⟨_, h, _⟩ := h
             apply h hx
           . obtain ⟨_, _, h⟩ := h
             exact h
  p₄ := e'.sccs_disjoint
  p₅ := by simp [num_of_reachable] at p₅
           have h := shrewd e'
           rw [empty_gray, empty_stack] at h
           simp at h
           intro x
           rw [eq_black, h, union_helper]
           tauto
}
