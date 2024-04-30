import Kosaraju.DirectedGraph
import Std.Data.List.Lemmas

open Rank

set_option maxHeartbeats 500000

structure Brigade [DirectedGraph V Graph] [BEq V] [LawfulBEq V]
                  (graph: Graph)
                  (roots black_stack grays : List V)
where
  stack : List V
  p₁ : wff_stack_G1 graph stack grays
  p₂ : roots ⊆ stack ++ grays
  monotony: ∃ s', stack = s' ++ black_stack /\ access_from_set graph roots s'

def dfs1 [DirectedGraph V Graph] [BEq V] [LawfulBEq V]
         (graph: Graph)
         (roots black_stack grays : List V)
         (h₁: roots ⊆ DirectedGraph.all_nodes graph)
         (h₂: grays ⊆ DirectedGraph.all_nodes graph)
         (h₃: wff_stack_G1 graph black_stack grays)
         : Brigade graph roots black_stack grays := match roots with
| List.nil => {
  stack := black_stack
  p₁ := by assumption
  p₂ := by tauto
  monotony := by use []; tauto
}
| List.cons x roots =>
  if h₅ : List.contains black_stack x || List.contains grays x then
    have h₄ := by simp_all
    let ⟨stack, p₃, p₄, monotony⟩ := dfs1 graph roots black_stack grays h₄ h₂ h₃
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
    have h₅ := by simp [wff_stack_G1] at *
                  constructor
                  . simp [wff_color] at *
                    constructor <;> simp_all
                    . intros y h₁ h₂
                      subst y
                      apply h₅
                      tauto
                    . constructor
                      . simp [no_black_to_white]
                        intros a b
                        obtain ⟨⟨_, ⟨h₃, _⟩⟩, _⟩ := h₃
                        specialize h₃ a b
                        tauto
                      . rw [simplelist_tl]
                        tauto
                  . tauto
    let v : List V := (DirectedGraph.all_nodes graph)
    let termination_proof: grays.length < v.length := by
      apply simplelist_size_2
      . tauto
      . simp [wff_stack_G1, wff_color] at h₃
        tauto
      . use x
        constructor
        . tauto
        . rename_i h
          simp [*] at h
          intro g
          apply h
          tauto
    let ⟨stack, p₃, p₄, monotony⟩ := dfs1 graph (DirectedGraph.succ graph x) black_stack (List.cons x grays) (by apply succ_valid; tauto) h₄ h₅
    have h₇ : ¬ x ∈ stack := by
      simp [wff_stack_G1, wff_color] at *
      obtain ⟨⟨p₅, _, _⟩, _, _⟩ := p₃
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
      | inr h₈ => obtain ⟨⟨p₅, p₈, ⟨p₇, p₉⟩⟩, p₆, p₃⟩ := p₃
                  specialize p₈ a b a2b h₈
                  cases p₈ <;> simp_all; tauto
    have g₉: no_edge_out_of graph black_stack (List.cons x stack) := by
      intros s1 h a b h₂ h₆ h₄
      simp [wff_stack_G1, wff_color, reachable_before_same_scc] at h₃
      obtain ⟨⟨_, ⟨h₃, _⟩⟩, _⟩ := h₃
      specialize h₃ _ _ h₄ h₂
      cases h₃
      . have h₆: simplelist (List.cons x stack) := by
          rw [simplelist_tl]
          constructor <;> try assumption
          simp [wff_stack_G1, wff_color, reachable_before_same_scc] at *
          tauto
        specialize h₆ b
        rw [h, num_occ_concat] at h₆
        rw [mem_num_occ] at *
        omega
      . obtain ⟨s', _, _⟩ := monotony
        subst stack
        simp [wff_stack_G1, wff_color, reachable_before_same_scc] at p₃
        obtain ⟨⟨p₃, _⟩, _⟩ := p₃
        apply p₃ b
        . have h : x :: s' ++ black_stack = s1 ++ black_stack := by tauto
          have h := List.append_inj_left' h rfl
          subst s1
          cases h₆ <;> try tauto
          rename_i g _ _ _ _ _ _ __ _ h₆
          simp at g
          exfalso
          apply g
          tauto
        . tauto
    have g₉: no_path_out_of_in graph black_stack (List.cons x stack) := by
      apply no_edge_out_of_no_path_out_of_in ; assumption
    have h₆ := by
       simp [wff_stack_G1, wff_color, reachable_before_same_scc] at p₃
       simp [wff_stack_G1, wff_color, reachable_before_same_scc]
       obtain ⟨⟨p₅, p₈, ⟨p₇, p₉⟩⟩, p₆, p₃⟩ := p₃
       rw [simplelist_tl] at *
       simp_all
       constructor
       any_goals constructor
       . intros a h₃ h₄
         apply p₅ <;> tauto
       . apply h₁
         tauto
       . intros x₁ y h h₉ h₇
         cases h <;> cases h₉ <;> cases h₇
         . subst y x₁
           simp [in_same_scc]
           tauto
         . subst y x₁
           simp [in_same_scc]
           tauto
         . subst x₁
           rename_i h₇
           obtain ⟨l, _, _, h₇⟩ := h₇
           specialize h₇ x (by tauto)
           simp [rank] at h₇
           split at h₇ <;> split at h₇ <;> simp_all; try tauto
           revert h₇
           obtain v : List V := DirectedGraph.all_nodes graph
           have : rank y stack (List.length v) < List.length stack := by apply rank_range; assumption
           omega
         . rename_i h
           obtain ⟨_, _⟩ := h
           subst x₁ y
           simp [in_same_scc]
           tauto
         . rename_i h₇
           obtain ⟨s', _, h₉⟩ := monotony
           subst stack y
           obtain ⟨l, _, _, h₇⟩ := h₇
           constructor <;> tauto
           left
           rename_i g₁ _ _
           rw [List.mem_append_eq] at g₁
           cases g₁ with
           | inl g₁ => specialize h₉ _ g₁
                       obtain ⟨y, h₈, h₉⟩ := h₉
                       cases h₉ with
                       | inl h₉ => obtain ⟨l, h₉⟩ := h₉
                                   rw [DirectedGraph.edge_succ] at h₈
                                   use (List.cons y l)
                                   constructor <;> assumption
                       | inr h₉ => cases h₉
                                   subst x₁
                                   rw [DirectedGraph.edge_succ] at h₈
                                   tauto
           | inr g₁ => exfalso
                       apply g₉ x₁ x l (List.cons x s') <;> tauto
         . rename_i h
           obtain ⟨_, _⟩ := h
           subst x₁ y
           simp [in_same_scc]
           tauto
         . apply p₃ <;> try assumption
           apply reachable_before_shrink _ _ _ x
           . constructor
             . assumption
           . assumption
         . rename_i h
           obtain ⟨_, _⟩ := h
           subst x₁
           simp [in_same_scc]
           tauto
    let ⟨stack, p₃, p₄, monotony⟩ := dfs1 graph roots (List.cons x stack) grays (by tauto) (by tauto) h₆
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
termination_by let v : List V := DirectedGraph.all_nodes graph
               (v.length - grays.length, roots)
