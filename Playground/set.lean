import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Tauto

-- #print Set -- Set α とは、 α → Propのこと Typeが何かよくわからないけど.
example {α : Type} : Set α = (α → Prop) := by rfl

variable {α : Type} (A B C : Set α)

theorem inter_subset_left : A ∩ B ⊆ A := by
  intro x hx
  exact hx.left
-- #print inter_subset_left -- ∀ {α : Type} (A B : Set α), A ∩ B ⊆ A

-- #check funext
-- Sortが最上概念？
-- Sort 0: Prop
-- Sort 1: Type 0
-- Sort 2: Type 1
-- Type Theory未履修だからよくわからない

theorem inter_comm : A ∩ B = B ∩ A := by
  -- 2つの集合(関数 α → Prop)が等しいとは
  -- 任意の入力xに対してその結果が等しいことであるという公理を使う
  ext x
  constructor -- ⇒ と ⇐ に分解してそれぞれ証明すればよくする
  · intro h
    -- h.rightは x ∈ B という証明
    -- h.right ∧ h.leftという命題ではなく、証明を提出する必要がある
    -- およそゲンツェンのIntroductionのことをconstructorと呼んでいて
    exact And.intro h.right h.left -- と、andを使った証明を導入できる
  · intro h
    exact ⟨h.right, h.left⟩ -- \ + < で召喚できる記号はいい感じのconstructorを自動で適用するための構文

theorem my_subset_trans : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro h1 h2 x hA
  have hB := h1 hA
  exact h2 hB

theorem inter_subset_union : A ∩ B ⊆ A ∪ B := by
  intro x hx
  have hA := hx.left
  exact Or.inl hA

theorem union_subset : A ⊆ C → B ⊆ C → A ∪ B ⊆ C := by
  intro h1 h2 x hx
  cases hx with
  | inl hA =>
    exact h1 hA
  | inr hB =>
    exact h2 hB

theorem subset_inter : C ⊆ A → C ⊆ B → C ⊆ A ∩ B := by
  intro h1 h2 x hC
  constructor
  · exact h1 hC
  · exact h2 hC

theorem union_comm : A ∪ B = B ∪ A := by
  ext x
  constructor
  · intro h
    cases h with
    | inl hA => exact Or.inr hA
    | inr hB => exact Or.inl hB
  · intro h
    cases h with
    | inl hB => exact Or.inr hB
    | inr hA => exact Or.inl hA

theorem empty_subset : ∅ ⊆ A := by
  intro x hE -- x ∈ ∅ は矛盾(False)
  exact False.elim hE

theorem diff_subset : A \ B ⊆ A := by
  intro x hx
  exact hx.left

theorem subset_antisymmetry : A ⊆ B → B ⊆ A → A = B := by
  intro h1 h2
  ext x
  constructor
  · intro hA
    exact h1 hA
  · intro hB
    exact h2 hB

theorem inter_assoc : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  constructor
  · intro h1
    have hA := h1.left.left
    have hB := h1.left.right
    have hC := h1.right
    have BC := And.intro hB hC
    exact And.intro hA BC
  · intro ⟨hA, ⟨hB, hC⟩⟩ -- ⟨ ⟩ はなんだかスゴイ
    exact ⟨⟨hA, hB⟩, hC⟩

theorem inter_union_distrib_1 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · intro ⟨hA, hBC⟩
    cases hBC with
    | inl hB =>
        have AB := And.intro hA hB
        exact Or.inl AB
    | inr hC =>
        have AC := And.intro hA hC
        exact Or.inr AC
  · intro h
    cases h with
    | inl hAB =>
      have hA := hAB.left
      have hB := hAB.right
      constructor
      · exact hA
      · exact Or.inl hB
    | inr hAC =>
      have hA := hAC.left
      have hC := hAC.right
      constructor
      · exact hA
      · exact Or.inr hC
-- #print Set.inter_union_distrib_left
-- 標準ライブラリでは inf_sup_left を使って1発で証明している
-- inf_sup_leftの定義は未知の記号すぎるので見なかったことにする

theorem inter_union_distrib_2 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · rintro ⟨hA, hB | hC⟩
    · exact Or.inl ⟨hA, hB⟩
    · exact Or.inr ⟨hA, hC⟩
  · rintro (⟨hA, hB⟩ | ⟨hA, hC⟩)
    · exact ⟨hA, Or.inl hB⟩
    · exact ⟨hA, Or.inr hC⟩
-- rintroは便利かもしれないが、上の愚直な証明をはじめに考えないとこれは絶対書ける気がしない

-- Tautoとかいうチートを使う
theorem inter_union_distrib_3 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  -- 集合の ∩ と ∪ を、論理の ∧ と ∨ に翻訳する (simpもまだよく分かってない)
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto -- 基本的な命題論理だけの恒真を自動で探索して証明する
-- 初心者なので使いたくない。依存公理としてここでは本来不要なClassical.choiceが紛れ込むし


theorem union_inter_distrib_1 : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  · intro h
    cases h with
    | inl hA =>
      constructor
      · exact Or.inl hA
      · exact Or.inl hA
    | inr hBC =>
      have hB := hBC.left
      have hC := hBC.right
      constructor
      · exact Or.inr hB
      · exact Or.inr hC
  · intro ⟨hAB, hAC⟩
    cases hAB with
    | inl hA =>
      exact Or.inl hA
    | inr hB =>
      cases hAC with
      | inl hA => exact Or.inl hA
      | inr hC => exact Or.inr ⟨hB, hC⟩
