import Tarjan.Env
import Tarjan.Dfs
import Kosaraju.Basic

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
                      intros cc h h₁
                      sorry
  sccs_disjoint := by simp
}
let ⟨n, e', p₁, p₃, p₄, p₅, p₆⟩ := dfs graph (DirectedGraph.vertices graph) e (by tauto) (by tauto)
{
  sccs_o := e'.sccs
  p₂ := by sorry
  p₄ := e'.sccs_disjoint
  p₅ := by sorry
}
