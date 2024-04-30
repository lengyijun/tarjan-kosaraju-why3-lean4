import Kosaraju.Dfs2
import Kosaraju.DirectedGraph
import Mathlib.Data.Finset.Basic
import Std.Data.List.Lemmas

open Rank
open Finset
open Finset List

set_option maxHeartbeats 0

structure Pillar [DirectedGraph Node Graph] [BEq Node] [LawfulBEq Node]
                 [DecidableEq Node]
                 (graph: Graph)
                 (stack blacks_i: List Node)
                 (sccs_i : List (Finset Node))
where
  blacks_o : List Node
  sccs_o   : List (Finset Node)
  p₁ : wff_stack_G2 graph blacks_o List.nil List.nil
  p₂ : ∀ cc, cc ∈ sccs_o ↔ Nonempty cc /\ is_scc graph cc /\ ∀ x, x ∈ cc -> x ∈ blacks_o
  p₃ : ∀ x, x ∈ blacks_o ↔ x ∈ stack \/ x ∈ blacks_i
  p₄ : ∀ cc₁ cc₂, cc₁ ∈ sccs_o → cc₂ ∈ sccs_o → cc₁ = cc₂ \/ cc₁ ∩ cc₂ = Finset.empty
  p₅ : ∀ v, v ∈ stack -> ∃ cc, v ∈ cc /\ cc ∈ sccs_o
  p₆ : sccs_i ⊆ sccs_o

def iter2 [DirectedGraph Node Graph] [BEq Node] [LawfulBEq Node]
          [DecidableEq Node]
         (graph: Graph)
         (stack blacks: List Node)
         (sccs : List (Finset Node))
         (a₁ : let v : List Node := DirectedGraph.all_nodes graph
               v.filter (fun x => !blacks.contains x) ⊆ stack)
         (a₂ : wff_stack_G2 graph blacks List.nil stack)
         (a₃ : ∀ cc, cc ∈ sccs ↔ Nonempty cc /\ is_scc graph cc /\ ∀ x, x ∈ cc → x ∈ blacks)
         (a₄ : ∀ cc₁ cc₂, cc₁ ∈ sccs → cc₂ ∈ sccs → cc₁ = cc₂ \/ cc₁ ∩ cc₂ = Finset.empty)
         (a₅ : ∀ v, v ∈ blacks -> ∃ cc, v ∈ cc /\ cc ∈ sccs)
         : Pillar graph stack blacks sccs := match stack with
| List.nil =>
{
  blacks_o := blacks
  sccs_o := sccs
  p₁ := a₂
  p₂ := a₃
  p₃ := by tauto
  p₄ := a₄
  p₅ := by tauto
  p₆ := by tauto
}
| List.cons x stack =>
  if dite : blacks.contains x then
    have h₁ := by intros _ b h
                  specialize a₁ h
                  cases a₁ <;> try assumption
                  rw [List.mem_filter] at h
                  simp_all
    have h₂ := by simp [wff_stack_G2, simplelist_tl] at *
                  simp_all
                  intros y z h₁ h₂ h₃
                  have ⟨_, a₆, a₇, a₈⟩:= a₂
                  apply a₈ y z (by tauto) (by tauto)
                  apply reachable_before_extension <;> assumption
    let ⟨blacks_o, sccs_o, p₁, p₂, p₃, p₄, p₅, p₆⟩ := iter2 graph stack blacks sccs h₁ h₂ a₃ a₄ a₅
    {
      blacks_o := blacks_o
      sccs_o := sccs_o
      p₁ := p₁
      p₂ := p₂
      p₃ := by intros y
               constructor <;> simp_all <;> try tauto
               intros h₁
               cases h₁ with try tauto
               | inl h₁ => cases h₁ <;> try tauto
                           subst y
                           right
                           assumption
      p₄ := p₄
      p₅ := by intros v h₁
               cases h₁ <;> try tauto
               specialize a₅ x
               simp_all
               obtain ⟨cc, a₅⟩ := a₅
               use cc
               constructor <;> simp_all
      p₆ := p₆
    }
  else
    have h₁ := by simp [wff_stack_G2] at *
                  tauto
    have h₂ := by simp [wff_stack_G2] at *
                  tauto
    let ⟨b₁, p₃, p₄, monotony⟩ := dfs2 graph (List.cons x List.nil) blacks List.nil h₁ (by tauto) h₂
    let cc₁ := b₁.filter (fun x => !blacks.contains x) |> toFinset
    have assert₁ : ∀ y, y ∈ cc₁ → y ∈ (List.cons x stack) := by
      intro y h₃
      apply a₁
      obtain ⟨s', _, h₄⟩ := monotony
      subst b₁
      rw [mem_toFinset, List.mem_filter, mem_em] at *
      simp_all
      specialize h₄ y (by tauto)
      simp_all
      have : x ∈ DirectedGraph.all_nodes graph /\ y ∈ DirectedGraph.all_nodes graph := by
        apply reachable_valid
        assumption
      tauto
    have assert₂ : x ∈ cc₁ := by
      rw [mem_toFinset, List.mem_filter] at *
      simp_all

    have em : ∀ y, y ∈ DirectedGraph.all_nodes graph ->
                   y ∈ blacks \/ y ∈ (x :: stack) := by
      intros y h
      have g: y ∈ blacks \/ ¬ y ∈ blacks := by tauto
      cases g <;> try tauto
      right
      apply a₁
      rw [List.mem_filter]
      simp_all

    have mascot : ∀ a b l, path graph a l b → a ∈ blacks → b ∈ blacks := by
      intros _ _ _ h
      obtain ⟨_, h₂, _⟩ := h₂
      induction h <;> intros h
      . rename_i b c h₅
        specialize h₂ b c h₅ h
        tauto
      . rename_i b c _ _ h₆ _ induction_step
        apply induction_step
        specialize h₂ b c
        simp_all

    have assert₃: ∀ y, y ∈ cc₁ -> reachable_before (DirectedGraph.transpose Node graph) y x (x :: stack) := by
      intros y h₃
      obtain ⟨s', _, h₄⟩ := monotony
      subst b₁
      specialize h₄ y
      rw [mem_toFinset, List.mem_filter, mem_em] at *
      simp_all
      have : y ∈ s' := by tauto
      simp_all
      cases h₄ with
      | inl h₄ => obtain ⟨l, h₄⟩ := h₄
                  have := path_valid graph _ _ _ h₄
                  left
                  use l.reverse
                  have M : y :: l ⊆ x :: stack := by
                    intros z h
                    cases h
                    . have g := em y (by tauto)
                      cases g with
                      | inl g => tauto
                      | inr g => simp_all
                    . rename_i h
                      have g : z ∈ l := by tauto
                      have g := List.append_of_mem g
                      obtain ⟨l₁, l₂, g⟩ := g
                      subst l
                      have g₁ := path_decomposition _ _ _ _ _ _ h₄
                      have g := em z (by tauto)
                      cases g <;> try simp_all
                      exfalso
                      apply h₃
                      apply mascot <;> tauto
                  repeat any_goals apply And.intro
                  . apply reverse_path
                    assumption
                  . intros z h
                    apply M
                    cases h
                    . tauto
                    . rename_i h
                      have : z ∈ l.reverse := by tauto
                      have : z ∈ l := by rw [<- List.mem_reverse]; assumption
                      tauto
                  . intros z h
                    simp [wff_stack_G2, simplelist_tl] at a₂
                    simp [rank]
                    split <;> split <;> try tauto
                    all_goals simp_all
                    rename_i h₁ h₂
                    obtain v : List Node := DirectedGraph.all_nodes (DirectedGraph.transpose Node graph)
                    have : rank z stack (List.length v) < List.length stack := by
                      apply rank_range; try assumption
                      have ⟨h₃, h₄⟩ := M
                      cases h <;> cases h₃
                      . subst z x
                        tauto
                      . subst y
                        tauto
                      . rename_i h₅ h₆
                        specialize h₄ h₅
                        cases h₄ <;> try assumption
                        tauto
                      . rename_i h₅ h₆
                        specialize h₄ h₅
                        cases h₄ <;> try assumption
                        tauto
                    omega
      | inr h₄ => cases h₄
                  subst y
                  right
                  tauto

    have assert₄ : ∀ y, y ∈ cc₁ → in_same_scc graph y x := by
      intros y h
      specialize assert₃ y h
      specialize assert₁ _ h
      rw [mem_toFinset, List.mem_filter] at *
      obtain ⟨s', _, h₄⟩ := monotony
      simp_all
      specialize h₄ y (by tauto)
      subst b₁
      simp_all
      simp [wff_stack_G2, reachable_before_same_scc] at *
      obtain ⟨_, _, _, a₂⟩:= a₂
      specialize a₂ y x
      rw [in_same_scc_transpose] at a₂
      apply a₂ <;> try tauto

    have assert₄ : is_subscc graph cc₁ := by
      intros y z hy hz
      simp_all
      have := assert₄ _ hy
      have := assert₄ _ hz
      apply same_scc_trans
      . assumption
      . simp [in_same_scc] at *
        simp_all

    have assert₅ : ∀ y, in_same_scc graph y x -> y ∈ cc₁ := by
      intros y h
      rw [mem_toFinset, List.mem_filter]
      obtain ⟨h₁, h₂⟩ := h
      cases h₁ <;> cases h₂ <;> try simp_all
      all_goals rename_i h₁ h₂
      all_goals obtain ⟨lyx, h₁⟩ := h₁
      . obtain ⟨lxy, h₂⟩ := h₂
        simp [wff_color] at p₃
        obtain ⟨p₃, _⟩ := p₃
        constructor
        . have h : y ∈ b₁ \/ ¬ y ∈ b₁ := by tauto
          cases h <;> try assumption
          exfalso
          apply no_black_to_white_no_path graph b₁ p₃ <;> assumption
        . intros h
          apply dite
          apply mascot <;> assumption
      . subst y
        simp_all

    have assert₆ : is_scc graph cc₁ := by
      constructor <;> try assumption
      intros _ h h₁ y h₂
      apply assert₅
      apply h₁ <;> try assumption
      apply h; assumption

    have h₁ := by
      obtain ⟨s', _, h₄⟩ := monotony
      subst b₁
      intros _ y
      specialize @a₁ y
      rw [mem_toFinset, List.mem_filter] at *
      intros h
      obtain ⟨h₅, h₆⟩ := h
      simp_all
      cases (em y (by tauto)) with
      | inl _ => tauto
      | inr h => cases h with
                 | inl h => subst y
                            tauto
                 | inr h => assumption

    have h₂ := by simp [wff_stack_G2, simplelist_tl] at *
                  simp_all
                  intros y z h₁ h₂ h₃
                  have ⟨_, a₆, _, a₈⟩:= a₂
                  apply a₈ y z (by tauto) (by tauto)
                  apply reachable_before_extension <;> assumption

    have h₃ := by
      obtain ⟨s', _, h₄⟩ := monotony
      subst b₁
      intros cc
      have h₆ := a₃ cc
      constructor <;> intros h
      . cases h <;> simp_all
        . constructor
          . use x
          . intros z
            rw [mem_toFinset, List.mem_filter] at *
            simp_all
            intros
            tauto
        . rename_i h
          have h₆ : cc ∈ sccs := by tauto
          simp_all
      . obtain ⟨_, _, h⟩ := h
        have h₇ : ∃ y, y ∈ cc := by simp_all
        obtain ⟨y, h₇⟩ := h₇
        specialize h y h₇
        rw [mem_em] at h
        have h₈ : y ∈ blacks \/ ¬ y ∈ blacks := by tauto
        cases h₈
        . simp_all
          right
          obtain ⟨cc₂, ⟨h₁, h₂, h₃, h₄⟩⟩ := a₅ y (by assumption)
          have : cc = cc₂ := by
            apply disjoint_scc graph <;> try assumption
            use y
            simp_all
          subst cc₂
          exact h₄
        . cases h <;> try tauto
          have : y ∈ cc₁ := by
            rw [mem_toFinset, List.mem_filter] at *
            simp_all
          simp_all; left
          apply disjoint_scc graph <;> try assumption
          use y
          simp_all

    have h₄ := by
      have : ∀ cc, cc ∈ sccs → cc₁ ∩ cc = ∅ := by
        intros cc h₅
        rw [eq_empty_iff_forall_not_mem]
        intros z h₆
        simp [*] at h₆
        obtain ⟨h₆, h₇⟩ := h₆
        rw [a₃] at h₅
        obtain ⟨_, _, _⟩ := h₅
        rw [mem_toFinset, List.mem_filter] at *
        simp_all

      intros cc₃ cc₄ h₅ h₆
      have := a₄ cc₃ cc₄
      cases h₅ <;> cases h₆ <;> try tauto
      right
      rw [inter_comm]
      tauto

    have h₅ := by
      intros z h
      obtain ⟨s', _, _⟩ := monotony
      subst b₁
      rw [mem_em] at h
      have h₈ : z ∈ blacks \/ ¬ z ∈ blacks := by tauto
      cases h₈ with
      | inl h₈ => specialize a₅ _ h₈
                  tauto
      | inr h₈ => cases h with
                  | inl h => use cc₁
                             constructor
                             . rw [mem_toFinset, List.mem_filter, mem_em] at *
                               simp_all
                             . tauto
                  | inr h => tauto

    let ⟨blacks_o, sccs_o, p₁, p₂, p₃, p₄, p₅, p₆⟩ := iter2 graph stack b₁ (cc₁ :: sccs) h₁ h₂ h₃ h₄ h₅
    {
      blacks_o := blacks_o
      sccs_o := sccs_o
      p₁ := p₁
      p₂ := p₂
      p₃ := by intros z
               rw [p₃]
               obtain ⟨s', _, _⟩ := monotony
               subst b₁
               rw [mem_em]
               constructor
               all_goals intros h
               all_goals cases h
               all_goals rename_i h
               any_goals tauto
               all_goals cases h
               all_goals rename_i h
               any_goals tauto
               . have h : z ∈ blacks \/ ¬ z ∈ blacks := by tauto
                 cases h <;> try tauto
                 left
                 apply assert₁
                 rw [mem_toFinset, List.mem_filter, mem_em] at *
                 simp_all
               . rw [mem_toFinset, List.mem_filter, mem_em] at *
                 obtain ⟨h, _⟩ := assert₂
                 cases h <;> tauto
      p₄ := p₄
      p₅ := by intros v h
               cases h
               . use cc₁
                 simp_all
               . apply p₅ v
                 tauto
      p₆ := by intros cc _
               apply p₆
               tauto
    }
