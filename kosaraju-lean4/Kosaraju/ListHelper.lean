import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Mathlib.Tactic.Tauto

theorem mem_em {c : α} {cs : List α} (ds : List α) : c ∈ cs ++ ds <-> c ∈ cs \/ c ∈ ds := by
induction cs <;> simp_all
constructor <;> intros h <;> cases h <;> tauto

namespace Rank
def rank [BEq α] [LawfulBEq α] (x : α) (s : List α) (max_int : Nat) : Nat :=
  match s with
  | List.nil => max_int
  | List.cons y s => if x == y && !(List.contains s x) then
                        s.length
                      else
                        rank x s max_int

theorem rank_range [BEq α] [LawfulBEq α] (s : List α) (x : α) (max_int : Nat) :
                  x ∈ s ->
                  rank x s max_int < s.length := by
induction s with intros h₂
| nil => cases h₂
| cons a b => simp [rank] at *; split
              . omega
              . simp_all
                cases h₂ <;> simp_all <;> omega

end Rank

def num_occ [BEq α] [LawfulBEq α] (x : α) (s : List α) : Nat :=
match s with
| List.nil => 0
| List.cons y s => if x == y then
                    Nat.succ (num_occ x s)
                  else
                    num_occ x s

@[simp] theorem num_occ_concat [BEq α] [LawfulBEq α] :
 ∀ (x : α) l₁ l₂, num_occ x (l₁ ++ l₂) = num_occ x l₁ + num_occ x l₂ := by
intro x l₁
induction l₁ <;> simp [num_occ] ; split <;> simp_all
omega

theorem mem_num_occ [BEq α] [LawfulBEq α] :
 ∀ (x : α) l, x ∈ l ↔ num_occ x l > 0 := by
intros x l
induction l <;> simp [num_occ] ; split <;> simp_all

theorem mem_num_occ_0 [BEq α] [LawfulBEq α] :
 ∀ (x : α) l, ¬ x ∈ l ↔ num_occ x l = 0 := by
intros x l
induction l <;> simp [num_occ] ; split <;> simp_all

def simplelist [BEq α] [LawfulBEq α] (s : List α) : Prop :=
∀ x, num_occ x s <= 1

theorem simplelist_tl [BEq α] [LawfulBEq α] :
 ∀ (x : α) l, simplelist (List.cons x l) ↔ simplelist l /\ ¬ x ∈ l
:= by
simp [simplelist, num_occ]
intros x s1
constructor
. intros h₁
  constructor
  . intros y
    specialize h₁ y
    split at h₁ <;> omega
  . specialize h₁ x
    split at h₁
    . revert h₁
      induction s1
      . simp_all
      . simp [num_occ]
        split <;> simp_all
        omega
    . simp_all
. intros h₁ y
  split <;> simp_all
  subst y
  obtain ⟨_, h₁⟩ := h₁
  rw [mem_num_occ_0] at h₁
  omega

theorem simplelist_size [BEq α] [LawfulBEq α] :
∀ (l₁ l₂: List α), l₁ ⊆ l₂ -> simplelist l₁ -> l₁.length ≤ l₂.length := by
intros l₁
induction l₁
. simp_all
. intros l₂ h₁ h₂
  rename_i a l₁ induction_step
  rw [simplelist_tl] at h₂
  simp_all
  obtain ⟨h₁, h₃⟩ := h₁
  have h₄: ∃ l₃ l₄, l₂ = l₃ ++ List.cons a l₄ := by apply List.append_of_mem; assumption
  obtain ⟨l₃, l₄, h₄⟩ := h₄
  subst l₂
  specialize induction_step (l₃ ++ l₄)
  have : l₁ ⊆ l₃ ++ l₄ := by
    simp [Subset, List.Subset]
    intros x h₆
    specialize h₃ h₆
    simp_all
    cases h₃ with
    | inl _ => tauto
    | inr h₃ => cases h₃
                . subst x
                  tauto
                . tauto
  simp_all
  omega

theorem simplelist_size_2 [BEq α] [LawfulBEq α] :
∀ (l₁ l₂: List α), l₁ ⊆ l₂ -> simplelist l₁ -> (∃ b, b ∈ l₂ /\ ¬ b ∈ l₁) -> l₁.length < l₂.length := by
intros l₁
induction l₁
. simp_all
  intros l₂ _ x h
  rw [List.length_pos]
  intro
  subst l₂
  cases h
. intros l₂ h₁ h₂ h₃
  simp_all
  obtain ⟨h₁, h₄⟩ := h₁
  rename_i c l₁ induction_step
  have h₅: ∃ l₃ l₄, l₂ = l₃ ++ List.cons c l₄ := by apply List.append_of_mem; assumption
  obtain ⟨l₃, l₄, h₅⟩ := h₅
  subst l₂
  rw [simplelist_tl] at h₂
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
  have : ¬ b ∈ l₁ := by intro h; apply h₉; tauto
  simp_all
  omega
