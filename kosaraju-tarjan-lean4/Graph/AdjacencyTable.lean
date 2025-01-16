import Graph.DirectedGraph
import Mathlib.Data.Matrix.Basic

def shepherd (n : Nat) : List (Fin n) :=
  match n with
  | Nat.zero => List.nil
  | Nat.succ x => List.cons ⟨x, by simp⟩ (shepherd x)

theorem all_in_shepherd {n : Nat} (x : Fin n) : x ∈ shepherd n := by
  induction n with obtain ⟨val, is_lt⟩ := x
  | zero => contradiction
  | succ n =>
      have h₂ : val < n \/ val = n := by omega
      simp [shepherd]
      cases h₂ with
      | inl h₂ => right; use ⟨val, h₂⟩; constructor <;> tauto
      | inr h₂ => tauto

-- t[i][j] = true : i -> j
structure AdjacencyTable (n : Nat) where
  t : Matrix (Fin n) (Fin n) Bool

def AdjacencyTable.succ {n : ℕ}(graph : AdjacencyTable n) (node : Fin n) : List (Fin n) := List.filter (fun j => graph.t node j) (shepherd n)

def AdjacencyTable.vertices {n : ℕ}(_g: AdjacencyTable n) : List (Fin n) := shepherd n

-- graph  : a -> b
-- result : b -> a
def AdjacencyTable.transpose {n : ℕ}(graph : AdjacencyTable n) : AdjacencyTable n := {
    t :=  graph.t.transpose
}

theorem transpose_transpose {n : ℕ}: ∀ (g : AdjacencyTable n), g.transpose.transpose = g := by
simp [AdjacencyTable.transpose]

theorem same_vertices {n : ℕ}: ∀ (g : AdjacencyTable n), g.transpose.vertices = g.vertices := by
 simp [AdjacencyTable.transpose, AdjacencyTable.vertices]

instance {n : ℕ}: DirectedGraph (Fin n) (AdjacencyTable n) where
  vertices := AdjacencyTable.vertices
  edge g a b := g.t a b = True
  succ      := AdjacencyTable.succ
  transpose := AdjacencyTable.transpose
  transpose_transpose := transpose_transpose
  same_vertices := same_vertices
  reverse_edge :=  by simp [AdjacencyTable.transpose]
  edge_succ := by simp [AdjacencyTable.succ]
                  intros
                  apply all_in_shepherd
  valid_edge := by intros; constructor <;> apply all_in_shepherd
