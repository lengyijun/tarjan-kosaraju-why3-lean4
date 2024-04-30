import Kosaraju.DirectedGraph
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

def AdjacencyTable.succ (graph : AdjacencyTable n) (node : Fin n) : List (Fin n) := List.filter (fun j => graph.t node j) (shepherd n)

def AdjacencyTable.all_nodes (_g: AdjacencyTable n) : List (Fin n) := shepherd n

-- graph  : a -> b
-- result : b -> a
def AdjacencyTable.transpose (graph : AdjacencyTable n) : AdjacencyTable n := {
    t :=  graph.t.transpose
}

theorem transpose_transpose : ∀ (g : AdjacencyTable n), g.transpose.transpose = g := by
simp [AdjacencyTable.transpose]

theorem same_nodes : ∀ (g : AdjacencyTable n), g.transpose.all_nodes = g.all_nodes := by
 simp [AdjacencyTable.transpose, AdjacencyTable.all_nodes]

instance : DirectedGraph (Fin n) (AdjacencyTable n) where
  all_nodes := AdjacencyTable.all_nodes
  edge g a b := g.t a b = True
  succ      := AdjacencyTable.succ
  transpose := AdjacencyTable.transpose
  transpose_transpose := transpose_transpose
  same_nodes := same_nodes
  reverse_edge :=  by simp [AdjacencyTable.transpose]
  edge_succ := by simp [AdjacencyTable.succ]
                  intros
                  constructor <;> intro h₂
                  . rw [List.mem_filter] at h₂
                    tauto
                  . rw [List.mem_filter]; constructor
                    . apply all_in_shepherd
                    . exact h₂
  valid_edge := by intros; constructor <;> apply all_in_shepherd
