import Graph.DirectedGraph
import Mathlib.Data.Matrix.Basic

-- t[i][j] = true : i -> j
structure AdjacencyTable (n : Nat) where
  t : Matrix (Fin n) (Fin n) Bool

noncomputable def AdjacencyTable.succ {n : ℕ} (graph : AdjacencyTable n) (node : Fin n) : List (Fin n) := List.filter (fun j => graph.t node j) ((Finset.univ : Finset (Fin n)).toList)

noncomputable def AdjacencyTable.vertices {n : ℕ} (_g: AdjacencyTable n) : List (Fin n) := (Finset.univ : Finset (Fin n)).toList

-- graph  : a -> b
-- result : b -> a
def AdjacencyTable.transpose {n : ℕ}(graph : AdjacencyTable n) : AdjacencyTable n := {
    t :=  graph.t.transpose
}

theorem transpose_transpose {n : ℕ}: ∀ (g : AdjacencyTable n), g.transpose.transpose = g := by
simp [AdjacencyTable.transpose]

theorem same_vertices {n : ℕ}: ∀ (g : AdjacencyTable n), g.transpose.vertices = g.vertices := by
 simp [AdjacencyTable.transpose, AdjacencyTable.vertices]

noncomputable instance {n : ℕ}: DirectedGraph (Fin n) (AdjacencyTable n) where
  vertices := AdjacencyTable.vertices
  edge g a b := g.t a b = True
  succ      := AdjacencyTable.succ
  transpose := AdjacencyTable.transpose
  transpose_transpose := transpose_transpose
  same_vertices := same_vertices
  reverse_edge :=  by simp [AdjacencyTable.transpose]
  edge_succ := by simp [AdjacencyTable.succ]
  valid_edge := by intros
                   unfold AdjacencyTable.vertices
                   simp
