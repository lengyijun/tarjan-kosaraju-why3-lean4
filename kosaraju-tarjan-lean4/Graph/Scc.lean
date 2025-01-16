import Graph.DirectedGraph

def in_same_scc {V Graph : Type*}
                [DirectedGraph V Graph]
                [BEq V] [LawfulBEq V]
                (g : Graph)
                (a b : V)
                : Prop := reachable g a b /\ reachable g b a

theorem same_scc_trans {V Graph : Type*}
                       [DirectedGraph V Graph]
                       [BEq V] [LawfulBEq V]
                       (g : Graph)
                       (x y z : V) :
in_same_scc g x y -> in_same_scc g y z -> in_same_scc g x z := by
simp [in_same_scc]
intros
constructor
all_goals apply reachable_trans
all_goals assumption

def is_subscc {V Graph : Type*}
              [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V]
              (g : Graph)
              (s : Finset V) : Prop :=
    ∀ x y, x ∈ s -> y ∈ s -> in_same_scc g x y

def is_scc {V Graph : Type*}
           [DirectedGraph V Graph]
           [BEq V] [LawfulBEq V]
           (g : Graph)
           (s : Finset V) : Prop :=
    is_subscc g s /\ (∀ s', s ⊆ s' -> is_subscc g s' -> s' ⊆ s)

theorem in_same_scc_transpose {V Graph : Type*}
                              [DirectedGraph V Graph]
                              [BEq V] [LawfulBEq V]
                              (g : Graph)
                              (a b : V) :
in_same_scc (DirectedGraph.transpose V g) a b <-> in_same_scc g a b := by
simp [in_same_scc]
repeat rw [reachable_transpose]
tauto

theorem is_subscc_transpose {V Graph : Type*}
                            [DirectedGraph V Graph]
                            [BEq V] [LawfulBEq V]
                            (g : Graph)
                            (cc : Finset V) :
is_subscc g cc <-> is_subscc (DirectedGraph.transpose V g) cc := by
simp [is_subscc]
constructor
all_goals intros h x y
all_goals specialize h x y
all_goals rw [in_same_scc_transpose] at *
all_goals tauto

private theorem is_scc_transpose_inner {V Graph : Type*}
                                       [DirectedGraph V Graph]
                                       [BEq V] [LawfulBEq V]
                                       (g : Graph)
                                       (cc : Finset V) :
is_scc g cc -> is_scc (DirectedGraph.transpose V g) cc := by
simp [is_scc]
intros
rw [<- is_subscc_transpose]
simp_all
intros
rw [<- is_subscc_transpose] at *
tauto

theorem is_scc_transpose  {V Graph : Type*}
                          [DirectedGraph V Graph]
                          [BEq V] [LawfulBEq V]
                          (g : Graph)
                          (cc : Finset V) :
is_scc g cc <-> is_scc (DirectedGraph.transpose V g) cc := by
constructor
. exact is_scc_transpose_inner g cc
. intros h
  have h := is_scc_transpose_inner _ _ h
  rw [DirectedGraph.transpose_transpose] at h
  assumption

theorem scc_max {V Graph : Type*}
                [DirectedGraph V Graph]
                [BEq V] [LawfulBEq V] [DecidableEq V]
                (g : Graph)
                (x y : V) (cc : Finset V)
                (h₁ : is_scc g cc)
                (h₃ : x ∈ cc)
                (h₄ : in_same_scc g x y) : y ∈ cc := by
simp [is_scc] at *
obtain ⟨h₁, h₂⟩ := h₁

have h₅ : ∀ z ∈ cc, in_same_scc g z y := by
  intros z h₅
  specialize h₁ x z h₃ h₅
  apply same_scc_trans <;> try assumption
  simp [in_same_scc] at *; tauto

have : is_subscc g (insert y cc) := by
  intros a b h₆ h₇
  simp_all
  cases h₇ <;> cases h₆ <;> try tauto
  all_goals subst y
  . subst b
    specialize h₅ x h₃
    obtain ⟨h₅, _ ⟩ := h₅
    have := reachable_valid _ _ _ h₅
    constructor
    all_goals right
    all_goals simp_all
  . apply h₅; assumption
  . specialize h₅ b
    simp [in_same_scc] at *
    simp_all

apply h₂ (insert y cc) <;> simp_all


theorem disjoint_scc {V Graph : Type*}
                     [DirectedGraph V Graph]
                     [BEq V] [LawfulBEq V] [DecidableEq V]
                     (g : Graph)
                     (cc1 cc2 : Finset V)
                     (h₁ : Nonempty (cc1 ∩ cc2 : Finset V))
                     (h₂ : is_scc g cc1)
                     (h₄ : is_scc g cc2) :
                     cc1 = cc2 := by
obtain ⟨x, h₁⟩ := h₁
apply Finset.Subset.antisymm
all_goals intros y h₉
all_goals have h₈ : x = y \/ ¬ x = y := by tauto
all_goals cases h₈
any_goals simp_all
all_goals apply scc_max g x y
any_goals assumption
any_goals tauto
. obtain ⟨h₂, _⟩ := h₂
  apply h₂ <;> tauto
. obtain ⟨h₄, _⟩ := h₄
  apply h₄ <;> tauto

theorem scc_navel {V Graph : Type*}
                  [DirectedGraph V Graph]
                  [BEq V] [LawfulBEq V] [DecidableEq V]
                  {g : Graph}
                  {cc : Finset V}
                  (x : V)
                  (h₂ : ∀ y ∈ cc, reachable g y x)
                  (h₁ : ∀ y ∈ cc, reachable g x y) :
is_subscc g cc := by
intros a b ha hb
constructor
. apply reachable_trans g a x b
  . apply h₂ ; assumption
  . apply h₁ ; assumption
. apply reachable_trans g b x a
  . apply h₂ ; assumption
  . apply h₁ ; assumption

structure Trajectory {Graph : Type*}
                     (V : Type*)
                     [DirectedGraph V Graph]
                     [BEq V] [LawfulBEq V] [DecidableEq V]
                     (graph: Graph)
where
  sccs_o  : List (Finset V)
  p₂ : ∀ cc, cc ∈ sccs_o ↔ Nonempty cc /\ is_scc graph cc /\ ∀ x ∈ cc, x ∈ DirectedGraph.vertices graph
  p₄ : ∀ cc₁ ∈ sccs_o, ∀ cc₂ ∈ sccs_o, cc₁ = cc₂ \/ cc₁ ∩ cc₂ = Finset.empty
  p₅ : ∀ v ∈ DirectedGraph.vertices graph, ∃ cc, v ∈ cc /\ cc ∈ sccs_o
