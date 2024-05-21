import Graph.DirectedGraph
import Graph.Scc
import Kosaraju.Dfs1
import Kosaraju.Grail

def kosaraju [DirectedGraph V Graph]
             [BEq V] [LawfulBEq V] [DecidableEq V]
             (graph: Graph) : Trajectory Graph V graph :=
have h₃ := by
  simp [wff_stack_G1, wff_color, no_black_to_white]
  tauto
let ⟨(stack: List V), p₃, p₄, monotony⟩ := dfs1 graph (DirectedGraph.vertices graph) [] [] (by tauto) (by tauto) h₃

have a₁ := by
  rw [DirectedGraph.same_vertices]
  simp_all

have a₂ := by
  simp [wff_stack_G2, wff_stack_G1, wff_color, no_black_to_white] at *
  rw [DirectedGraph.same_vertices]
  simp_all
  obtain ⟨_, _, p₃⟩ := p₃
  intro x y hx hy h
  rw [DirectedGraph.transpose_transpose] at *
  apply p₃ <;> assumption

let ⟨blacks_o, sccs_o, p₁, p₂, p₃, p₄, p₅, _⟩ := iter2 (DirectedGraph.transpose V graph) stack [] [] a₁ a₂ (by simp_all) (by tauto) (by tauto)

have p₇ := by
  intros cc
  rw [p₂]
  constructor
  all_goals intros h
  all_goals apply And.intro
  any_goals apply And.intro
  any_goals rw [<- is_scc_transpose] at *
  any_goals tauto
  any_goals simp_all
  . simp [is_scc] at h
    obtain ⟨_, ⟨h, _⟩, _⟩ := h
    intros x x_in_cc
    specialize h x x x_in_cc x_in_cc
    obtain ⟨h, _⟩ := h
    have := reachable_valid _ _ _ h
    tauto
  . intros x x_in_cc
    apply a₁
    rw [DirectedGraph.same_vertices]
    obtain ⟨_, _, h⟩ := h
    apply h
    assumption

{
  sccs_o  := sccs_o
  p₂ := p₇
  p₄ := p₄
  p₅ := by intros v h
           apply p₅
           simp_all
           rename_i q
           apply q
           assumption
}
