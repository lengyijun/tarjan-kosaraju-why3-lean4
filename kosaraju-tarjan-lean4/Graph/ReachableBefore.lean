import Graph.DirectedGraph
import Graph.Scc
import ListHelper.Rank

def reachable_before [DirectedGraph V Graph]
                     [BEq V] [LawfulBEq V]
                     (g : Graph)
                     (x y: V) (s: List V) : Prop :=
  let v : List V := DirectedGraph.vertices g
  let max_int : Nat := v.length
  (∃ l, path g x l y /\
       let xl := List.cons x l
       xl ⊆ s /\
       (∀ z, z ∈ xl -> rank z s max_int <= rank y s max_int))
  \/
  (x = y /\ x ∈ s)

def reachable_before_same_scc [DirectedGraph V Graph]
                              [BEq V] [LawfulBEq V]
                              (g : Graph)
                              (s: List V) : Prop :=
   ∀ x y, x ∈ s -> y ∈ s -> reachable_before g x y s -> in_same_scc g x y


def wff_stack_G1 [DirectedGraph V Graph]
                 [BEq V] [LawfulBEq V]
                 (g : Graph)
                 (blacks grays: List V) :=
    wff_color g blacks grays
    /\ blacks ⊆ (DirectedGraph.vertices g)
    /\ reachable_before_same_scc g blacks

def wff_stack_G2 [DirectedGraph V Graph]
                 [BEq V] [LawfulBEq V]
                 (g : Graph)
                 (blacks grays s: List V) :=
    wff_color g blacks grays
    /\ simplelist s
    /\ s ⊆ DirectedGraph.vertices g
    /\ reachable_before_same_scc (DirectedGraph.transpose V g) s

theorem reachable_before_shrink [DirectedGraph V Graph]
                                [BEq V] [LawfulBEq V]
                                (g : Graph) :
∀ (x y z: V) s, reachable_before g x y (List.cons z s) -> y ∈ s -> reachable_before g x y s := by
  simp [reachable_before, rank]
  intros x y z s h₁ h₂
  cases h₁ with
  | inl h₁ =>
    obtain ⟨lxy, h₁, ⟨h₃, h₆⟩, h₄, h₅⟩ := h₁
    left
    use lxy
    split at h₄ <;> split at h₄ <;> simp_all
    . rename_i h₆
      obtain ⟨h₆, _⟩ := h₆
      subst z
      revert h₄
      obtain v : List V := DirectedGraph.vertices g
      have : rank y s (List.length v) < List.length s := by apply rank_range; assumption
      omega
    . constructor
      any_goals constructor
      . simp [Subset, List.Subset] at *
        cases h₃ <;> simp_all
      . simp [Subset, List.Subset]
        intros a h₉
        cases h₆ h₉
        . cases h₃
          . simp_all
          . specialize h₅ z h₉
            split at h₅ <;> simp_all
            revert h₅
            obtain v : List V := DirectedGraph.vertices g
            have : rank y s (List.length v) < List.length s := by apply rank_range; assumption
            omega
        . assumption
      . intros a h₇
        specialize h₅ a h₇
        split at h₅ <;> simp_all
        revert h₅
        obtain v : List V := DirectedGraph.vertices g
        have : rank y s (List.length v) < List.length s := by apply rank_range; assumption
        omega
  | inr h₁ => obtain ⟨_, h₁⟩ := h₁
              subst y
              tauto


theorem reachable_before_extension [DirectedGraph V Graph]
                                   [BEq V] [LawfulBEq V]
                                   (g : Graph) :
  ∀ (x y z: V) s, x ∈ s -> y ∈ s -> reachable_before g x y s -> reachable_before g x y (List.cons z s) := by
  intros x y z s _ h₂
  simp [reachable_before, rank]
  intros h₁
  cases h₁ with
  | inl h₁ =>
      obtain ⟨lxy, h₁, ⟨h₂, h₃⟩, h₄⟩ := h₁
      left
      use lxy
      constructor <;> try constructor
      . assumption
      . simp [Subset, List.Subset] at *
        simp_all
      . split <;> split <;> simp_all
        . intros a _
          split <;> simp_all
          rename_i h₉ h₆
          obtain ⟨ h₆, h₈⟩ := h₆
          subst a
          specialize h₃ h₉
          tauto
  | inr h₁ => obtain ⟨_, _⟩ := h₁
              subst y
              tauto

theorem no_edge_out_of_cons [DirectedGraph V Graph]
                            [BEq V] [LawfulBEq V]
                            (g : Graph)
                            (s1 s2: List V) (x : V) :
                        no_edge_out_of g s1 s2 ->
                        (∀ z, z ∈ s1 -> DirectedGraph.edge g z x -> False) ->
                        no_edge_out_of g s1 (List.cons x s2) := by
    simp [no_edge_out_of]
    intros h₁ h₂ s5 h₃ a b h₄ h₅ h₆
    cases s5 with simp_all
    | cons a5 s5 => obtain ⟨h₃, h₇⟩ := h₃
                    subst a5 s2
                    specialize h₁ a b h₄
                    cases h₅ <;> simp_all

theorem path_cross_sets [DirectedGraph V Graph]
                        [BEq V] [LawfulBEq V]
                        (g : Graph) :
   ∀ l (x y : V) s1 s2 ,
   -- simplelist (s1 ++ s2) ->
   y ∈ s2 ->
   x ∈ s1 ->
   path g y l x ->
   l ⊆ (s1 ++ s2) ->
   ∃ (y' x' : V), y' ∈ s2 /\ x' ∈ s1 /\ DirectedGraph.edge g y' x' := by
   intro l
   induction l <;> intros x y s1 s2 h₁ h₂ h₃ h₄ <;> cases h₃
   . use y
     use x
   . rename_i b bs induction_step h₅ h₆
     have : b ∈ (s1 ++ s2) := by apply h₄; simp_all
     have h₈ : b ∈ s1 \/ b ∈ s2 := by rw [<- List.mem_append_eq]; simp_all
     cases h₈
     . use y
       use b
     . apply induction_step x b <;> try assumption
       . simp [Subset, List.Subset]
         intros
         rw [<- List.mem_append_eq]
         apply h₄
         simp_all

theorem no_edge_out_of_no_path_out_of_in [DirectedGraph V Graph]
                                        [BEq V] [LawfulBEq V]
                                        (g : Graph) :
    ∀ (s1 s2 : List V),
   --  simplelist s2 ->
    no_edge_out_of g s1 s2 -> no_path_out_of_in g s1 s2 := by
simp [no_edge_out_of, no_path_out_of_in]
intros s2 s3 h₁ x y l s1 h₂ h₃ h₄ h₅ h₆
subst s3
specialize h₁ s1
simp_all
have h₇ := path_cross_sets g l y x s1 s2 h₃ h₄ h₅ h₆
obtain ⟨x, y, h₂, h₃, h₄⟩ := h₇
apply h₁ x y h₂ h₃ h₄


theorem no_black_to_white_no_path [DirectedGraph V Graph]
                                [BEq V] [LawfulBEq V]
                                (g : Graph) :
∀ (b : List V),
no_black_to_white g b List.nil ->
∀ l x y, x ∈ b -> ¬ y ∈ b -> path g x l y -> False := by
simp [no_black_to_white]
intros b h₁ l
induction l <;> intros x y h₂ h₃ h₄ <;> cases h₄
. tauto
. rename_i z zs induction_step h₄ h₅
  have h₆ : z ∈ b \/ ¬ z ∈ b := by tauto
  cases h₆ <;> tauto

theorem no_black_to_white_in_the_middle [DirectedGraph V Graph]
                                        [BEq V] [LawfulBEq V]
                                        (g : Graph) :
∀ (b b' : List V), no_black_to_white g b  List.nil ->
                      no_black_to_white g b' List.nil ->
                      b ⊆ b' ->
                      paths_in_set g (List.filter (fun x => !b.contains x) b') := by
simp [paths_in_set]
intros b b' h₁ h₂ _ x l y h₄ h₅ h₆ z h₇
rw [List.mem_filter] at *
simp_all
have h₈ := List.append_of_mem h₇
obtain ⟨l₁, l₂, h₈⟩:= h₈
subst l
have ⟨h₈, h₉⟩ := path_decomposition g x z y l₁ l₂ h₆
have g₁ : z ∈ b' \/ ¬ z ∈ b' := by tauto
have g₂ : z ∈ b  \/ ¬ z ∈ b  := by tauto
obtain ⟨h₄, _⟩ := h₄
obtain ⟨_, h₇⟩ := h₅
cases g₁ <;> cases g₂ <;> constructor <;> try assumption
. intros g₃
  apply no_black_to_white_no_path g b h₁ l₂ z y g₃ h₇ h₉
. exfalso
  apply no_black_to_white_no_path g b' h₂ l₁ x z h₄ <;> assumption
. intros _
  apply no_black_to_white_no_path g b' h₂ l₁ x z h₄ <;> assumption
. exfalso
  apply no_black_to_white_no_path g b' h₂ l₁ x z h₄ <;> assumption


theorem wff_stack_white_extension [DirectedGraph V Graph]
                                  [BEq V] [LawfulBEq V]
                                  (g : Graph) :
∀ grey grey' (s s': List V),
  wff_stack_G1 g s grey ->
  wff_stack_G1 g (s' ++ s) grey'  ->
  grey ⊆ grey' ->
  ∀ x, x ∈ s' -> x ∈ s \/ x ∈ grey -> False := by
simp [wff_stack_G1, reachable_before_same_scc, wff_color]
intros grey _ s s' _ _ _ _ _ _ h₅ _ g₂ _ _ _ _ g₁ x _ g₄
cases g₄ with
| inl g₄ => specialize g₂ x
            rw [num_occ_concat] at g₂
            rw [mem_num_occ] at *
            simp_all
            omega
| inr g₄ => apply h₅ x
            . simp_all
            . apply g₁ g₄
