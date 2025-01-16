import Graph.DirectedGraph
import Graph.Scc
import Graph.ReachableBefore
import ListHelper.Rank
import Mathlib.Tactic.Tauto
import Init.Data.List.Lemmas

structure Funnel {V Graph: Type*}
                 [DirectedGraph V Graph] [BEq V] [LawfulBEq V]
                 (graph: Graph)
                 (roots black_stack grays : List V)
where
  stack : List V
  p₁ : wff_color graph stack grays
  p₂ : roots ⊆ stack ++ grays
  monotony: ∃ s', stack = s' ++ black_stack /\ access_from_set graph roots s'

def dfs2 {V Graph: Type*}
         [instance_graph : DirectedGraph V Graph] [BEq V] [LawfulBEq V]
         (graph: Graph)
         (roots black_stack grays : List V)
         (h₁: roots ⊆ DirectedGraph.vertices graph)
         (h₂: grays ⊆ DirectedGraph.vertices graph)
         (h₃: wff_color graph black_stack grays)
         : Funnel graph roots black_stack grays := match roots with
| List.nil => {
  stack := black_stack
  p₁ := h₃
  p₂ := by tauto
  monotony := by use []; tauto
}
| List.cons x roots =>
  if h₅ : List.contains black_stack x || List.contains grays x then
    let h₄ := by simp_all
    let ⟨stack, p₃, p₄, monotony⟩ := dfs2 graph roots black_stack grays h₄ h₂ h₃
    {
       stack := stack
       p₁ := p₃
       p₂ := by simp [Subset, List.Subset]
                simp_all
                constructor
                . cases h₅
                  . obtain ⟨s', h₁, _⟩ := monotony
                    subst stack
                    simp_all
                  . tauto
                . intros a h₆
                  specialize p₄ h₆
                  simp_all
       monotony := by obtain ⟨s', h₆, h₇⟩ := monotony
                      use s'
                      subst stack
                      constructor
                      . rfl
                      . simp [access_from_set] at *
                        simp_all
    }
  else
    let h₄ := by simp_all
    have h₅ := by simp [wff_color] at *
                  repeat any_goals apply And.intro
                  any_goals tauto
                  . simp_all
                    intros y h₁ h₂
                    subst y
                    tauto
                  . simp [no_black_to_white]
                    intros a b
                    obtain ⟨_, h₃, _, _⟩ := h₃
                    specialize h₃ a b
                    tauto
    have : grays.length < (instance_graph.vertices graph).length := by
      apply simplelist_size_2
      . tauto
      . simp [wff_color] at h₃
        tauto
      . use x
        constructor
        . tauto
        . rename_i h
          simp [*] at h
          intro g
          tauto
    let ⟨stack, p₃, p₄, monotony⟩ := dfs2 graph (DirectedGraph.succ graph x) black_stack (List.cons x grays) (by apply succ_valid; tauto) h₄ h₅
    have h₇ : ¬ x ∈ stack := by
      simp [ wff_color] at *
      obtain ⟨p₅, _, _⟩ := p₃
      intros h₁
      specialize p₅ _ h₁
      tauto
    have h₈: no_black_to_white graph (List.cons x stack) grays := by
      simp [no_black_to_white]
      intros a b a2b h₈
      cases h₈ with
      | inl h₈ => subst a
                  rw [<- DirectedGraph.edge_succ] at a2b
                  specialize p₄ a2b
                  rw [List.mem_append_eq] at p₄
                  cases p₄ <;> simp_all; tauto
      | inr h₈ => obtain ⟨p₅, p₈, ⟨p₇, p₉⟩⟩ := p₃
                  specialize p₈ a b a2b h₈
                  cases p₈ <;> simp_all; tauto
    have g₉: no_edge_out_of graph black_stack (List.cons x stack) := by
      intros s1 h a b h₂ h₆ h₄
      simp [wff_color, reachable_before_same_scc] at h₃
      obtain ⟨_, ⟨h₃, _⟩⟩ := h₃
      specialize h₃ _ _ h₄ h₂
      cases h₃
      . obtain ⟨s', _, _⟩ := monotony
        subst stack
        simp [wff_color, reachable_before_same_scc] at p₃
        casesm* _ ∧ _
        have h : x :: s' ++ black_stack = s1 ++ black_stack := by tauto
        have h := List.append_inj_left' h rfl
        subst s1
        cases h₆ <;> try tauto
        rename_i g _ _ _ _ _ _
        specialize g b (by tauto)
        tauto
      . have h₆: List.Nodup (List.cons x stack) := by
          rw [List.nodup_cons]
          constructor <;> try assumption
          simp [wff_color, reachable_before_same_scc] at *
          tauto
        unfold List.Nodup at h₆
        rw [h] at h₆
        rw [List.pairwise_append] at h₆
        obtain ⟨_, _, h₆⟩ := h₆
        apply h₆ b (by assumption) b (by assumption) rfl
    have g₉: no_path_out_of_in graph black_stack (List.cons x stack) := by
      apply no_edge_out_of_no_path_out_of_in ; assumption
    have h₆ := by
       simp [wff_color, reachable_before_same_scc] at p₃
       simp [wff_color, reachable_before_same_scc]
       simp_all
    let ⟨stack, p₃, p₄, monotony⟩ := dfs2 graph roots (List.cons x stack) grays (by tauto) (by tauto) h₆
    {
      stack := stack
      p₁ := p₃
      p₂ := by obtain ⟨s', _, _⟩ := monotony
               subst stack
               intros a h
               cases h
               . repeat rw [List.mem_append_eq]
                 tauto
               . tauto
      monotony := by obtain ⟨s₁, _, h₁⟩ := monotony
                     subst stack
                     obtain ⟨s₂, _, h₂⟩ := monotony
                     subst stack
                     use (s₁ ++ List.cons x s₂)
                     constructor
                     . simp_all
                     . intros a h
                       rw [List.mem_append_eq] at h
                       cases h with
                       | inl h => specialize h₁ _ h
                                  obtain ⟨y, h, g⟩ := h₁
                                  use y
                                  tauto
                       | inr h => use x
                                  cases h
                                  . tauto
                                  . rename_i h
                                    specialize h₂ a h
                                    obtain ⟨y, h₂, h₃⟩ := h₂
                                    rw [DirectedGraph.edge_succ] at h₂
                                    constructor
                                    . tauto
                                    . cases h₃ with
                                      | inl h₃ => obtain ⟨l, h₃⟩ := h₃
                                                  left
                                                  use (List.cons y l)
                                                  tauto
                                      | inr h₃ => cases h₃
                                                  subst a
                                                  tauto
    }
termination_by let v : List V := DirectedGraph.vertices graph
               (v.length - grays.length, roots)
