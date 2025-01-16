import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto
import ListHelper.Simplelist

-- finite directed graph
class DirectedGraph (V : Type*)(Graph : Type*) where
  vertices : Graph -> List V
  succ      : Graph -> V -> List V
  edge      : Graph -> V -> V -> Prop := fun g x y => y ∈ succ g x
  edge_succ : ∀ g a b, b ∈ succ g a <-> edge g a b
  valid_edge : ∀ (g: Graph) (a b: V), edge g a b -> a ∈ vertices g /\ b ∈ vertices g
  transpose : Graph -> Graph
  transpose_transpose : ∀ g, (g |> transpose |> transpose) = g
  same_vertices : ∀ g, (g |> transpose |> vertices) = (g |> vertices)
  reverse_edge :∀ g a b, edge g a b <-> edge (g |> transpose) b a

theorem succ_valid {V Graph : Type*} [DirectedGraph V Graph] (g : Graph) (a: V)
  (_ : a ∈ DirectedGraph.vertices g) :
  DirectedGraph.succ g a ⊆ DirectedGraph.vertices g := by
intro b h
rw [DirectedGraph.edge_succ] at *
have : a ∈ DirectedGraph.vertices g /\ b ∈ DirectedGraph.vertices g := by
  apply DirectedGraph.valid_edge
  assumption
tauto

inductive path {V Graph : Type*} [DirectedGraph V Graph] : Graph -> V -> List V -> V -> Prop
  | edge: ∀ (g: Graph) (a b: V), DirectedGraph.edge g a b -> path g a List.nil b
  | cons: ∀ (g: Graph) (a b c: V) (l: List V), DirectedGraph.edge g a b -> path g b l c -> path g a (List.cons b l) c

theorem path_trans {V Graph : Type*} [DirectedGraph V Graph] (g : Graph) (a b c: V) (lab lbc: List V)
        (h : path g a lab b) :
        path g b lbc c -> path g a (lab ++ List.cons b lbc) c := by
induction h
. simp; intros; constructor <;> assumption
. intros; simp_all; constructor <;> assumption

theorem path_decomposition {V Graph : Type*} [DirectedGraph V Graph] (g : Graph) (a b c: V) (lab lbc: List V) :
  path g a (lab ++ List.cons b lbc) c -> path g a lab b /\ path g b lbc c := by
revert a b c lbc
induction lab <;> simp_all <;> intros a b c lbc h <;> cases h
. tauto
. rename_i x xs induction_step h₂ h₃
  specialize induction_step x b c lbc h₃
  tauto

theorem reverse_path {V Graph : Type*} [DirectedGraph V Graph] (g : Graph) (a b : V) (l : List V)
        (h : path g a l b) : path (DirectedGraph.transpose V g) b l.reverse a := by
induction h <;> simp
. constructor; rw [<- DirectedGraph.reverse_edge]; assumption
. apply path_trans
  . assumption
  . constructor; rw [<- DirectedGraph.reverse_edge]; assumption

theorem path_valid {V Graph : Type*} [DirectedGraph V Graph] (g : Graph) (a b: V)(l : List V)
        (h : path g a l b) :
        a ∈ DirectedGraph.vertices g /\
        b ∈ DirectedGraph.vertices g /\
        l ⊆ DirectedGraph.vertices g
:= by
induction h <;> simp_all
. apply DirectedGraph.valid_edge
  assumption
. rename_i a b _ _ h _ _
  have : a ∈ DirectedGraph.vertices g /\ b ∈ DirectedGraph.vertices g := by
    apply DirectedGraph.valid_edge
    assumption
  tauto

def reachable {V Graph : Type*}
              [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V]
              (g : Graph)
              (a b : V)
                : Prop := (∃ l, path g a l b)
                          \/
                          (
                            let v : List V := DirectedGraph.vertices g
                            a = b /\ a ∈ v
                          )

theorem reachable_trans {V Graph : Type*}
                        [DirectedGraph V Graph]
                        [BEq V] [LawfulBEq V]
                        (g : Graph)
                        (x y z : V) :
reachable g x y -> reachable g y z -> reachable g x z := by
simp [reachable]
intros xy yz
cases xy <;> cases yz <;> try simp_all
all_goals rename_i h g
. left
  obtain ⟨lyz, _⟩ := g
  obtain ⟨lxy, _⟩ := h
  use (lxy ++ y :: lyz)
  apply path_trans <;> assumption
. right
  obtain ⟨_, _⟩ := g
  subst z
  assumption

theorem reachable_valid {V Graph : Type*}
                        [DirectedGraph V Graph]
                        [BEq V] [LawfulBEq V]
                        (g : Graph) (a b: V)
                        (h : reachable g a b) :
 a ∈ DirectedGraph.vertices g /\ b ∈ DirectedGraph.vertices g
:= by
cases h with
| inl h => obtain ⟨l, h⟩ := h
           have := path_valid g _ _ _ h
           tauto
| inr h => cases h
           subst a
           tauto


def no_black_to_white {V Graph Lv: Type*}
                      [DirectedGraph V Graph]
                      [BEq V] [LawfulBEq V]
                      [Membership V Lv]
                      (g : Graph)
                      (blacks grays: Lv) : Prop :=
    ∀ a b, DirectedGraph.edge g a b -> a ∈ blacks -> b ∈ grays \/ b ∈ blacks

def access_from_set {V Graph : Type*}
                    [DirectedGraph V Graph]
                    [BEq V] [LawfulBEq V]
                    (g : Graph)
                    (roots b: List V) : Prop :=
∀ z ∈ b, ∃ x ∈ roots, reachable g x z

def access_to {V Graph : Type*}
              [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V]
              (graph : Graph)(s: Finset V) (y: V) : Prop :=
∀ x ∈ s, reachable graph x y

def wff_color {V Graph : Type*}
              [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V]
              (g : Graph)
              (blacks grays: List V) : Prop :=
              (∀ x, x ∈ blacks -> x ∈ grays -> False) /\
              no_black_to_white g blacks grays /\
              List.Nodup blacks /\
              List.Nodup grays


def no_edge_out_of {V Graph : Type*}
                   [DirectedGraph V Graph]
                   [BEq V] [LawfulBEq V]
                   (g : Graph)
                   (s3 s1: List V) : Prop :=
    ∀ s2, s1 = s2 ++ s3 -> ∀ x y, x ∈ s3 -> y ∈ s2 -> DirectedGraph.edge g x y -> False

def no_path_out_of_in {V Graph : Type*}
                      [DirectedGraph V Graph]
                      [BEq V] [LawfulBEq V]
                      (g : Graph)
                      (s3 s1: List V) : Prop :=
    ∀ x y l s2, s1 = s2 ++ s3 -> x ∈ s3 -> y ∈ s2 -> path g x l y -> l ⊆ s1 -> False

def paths_in_set {V Graph : Type*}
                 [DirectedGraph V Graph]
                 [BEq V] [LawfulBEq V]
                 (g : Graph)
                 (cc: List V) : Prop :=
    ∀ x l y, x ∈ cc -> y ∈ cc -> path g x l y -> l ⊆ cc

theorem reachable_transpose {V Graph : Type*}
                            [DirectedGraph V Graph]
                            [BEq V] [LawfulBEq V]
                            (g : Graph)
                            (a b : V) :
reachable (DirectedGraph.transpose V g) a b <-> reachable g b a := by
simp [reachable]
rw [DirectedGraph.same_vertices]
constructor <;> intros h
all_goals cases h
all_goals rename_i h
any_goals simp_all
. left
  obtain ⟨l, h⟩ := h
  use l.reverse
  have h := reverse_path _ _ _ _ h
  rw [DirectedGraph.transpose_transpose] at h
  assumption
. obtain ⟨_, _⟩ := h
  subst a
  tauto
. left
  obtain ⟨l, h⟩ := h
  use l.reverse
  have h := reverse_path _ _ _ _ h
  assumption
. obtain ⟨_, _⟩ := h
  subst a
  tauto
