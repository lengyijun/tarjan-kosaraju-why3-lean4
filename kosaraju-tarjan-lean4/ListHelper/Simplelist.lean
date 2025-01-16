import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Data.List.Pairwise
import Mathlib.Tactic.Tauto

variable {α : Type*}

theorem simplelist_size_2 [BEq α] [LawfulBEq α] :
∀ (l₁ l₂: List α), l₁ ⊆ l₂ -> List.Nodup l₁ -> (∃ b, b ∈ l₂ /\ ¬ b ∈ l₁) -> l₁.length < l₂.length := by
intros l₁
induction l₁
. simp_all
  intros l₂ _ x
  rw [List.length_pos]
  intro
  subst l₂
  tauto
. intros l₂ h₁ h₂ h₃
  simp_all
  obtain ⟨h₁, h₄⟩ := h₁
  rename_i c l₁ induction_step
  have h₅: ∃ l₃ l₄, l₂ = l₃ ++ List.cons c l₄ := by apply List.append_of_mem; assumption
  obtain ⟨l₃, l₄, h₅⟩ := h₅
  subst l₂
  have : l₁ ⊆ l₃ ++ l₄ := by
    simp [Subset, List.Subset]
    intros x h₆
    specialize h₄ h₆
    simp_all
    cases h₄ with
    | inl _ => tauto
    | inr h₃ => cases h₃
                . subst x
                  tauto
                . tauto
  obtain ⟨b, h₃, h₉⟩ := h₃
  specialize induction_step (l₃ ++ l₄)
  simp_all
  have : b ∈ l₃ \/ b ∈ l₄ := by cases h₃ <;> tauto
  specialize induction_step b
  have : ¬ b ∈ l₁ := by intro h; tauto
  simp_all
  omega

theorem simplelist_uniq [BEq α] [LawfulBEq α] {x : α} :
∀ l₁ l₃ l₂ l₄: List α,
l₁ ++ x :: l₂ = l₃ ++ x :: l₄ ->
List.Nodup (l₁ ++ x :: l₂) ->
l₁ = l₃ /\ l₂ = l₄ := by
intro l₁
induction l₁
intro l₃
induction l₃
all_goals simp
all_goals intros l₂ l₄ h h₁ h₃
any_goals subst x
any_goals subst l₂
all_goals rename_i y _ _
. intros _
  apply h₃
  simp
. match l₂ with
  | [] => simp at h₁
          obtain ⟨h₁, _⟩ := h₁
          subst y
          intros _
          tauto
  | z :: l₂ =>  simp at h₁
                obtain ⟨h₁, h₅⟩ := h₁
                subst z
                rename_i l₁ induction_step _
                intros _ _ h₆
                specialize induction_step _ _ _ h₅ h₆
                simp_all
