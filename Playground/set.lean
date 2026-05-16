import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Tauto

-- #print Set -- Set α とは、 α → Propのこと Typeが何かよくわからないけど.
example {α : Type} : Set α = (α → Prop) := by rfl

variable {α : Type} (A B C D E F : Set α)

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

-------------------------
-- 補集合、差集合、ドモルガン
-------------------------

theorem diff_subset_compl : A \ B ⊆ Bᶜ := by
  intro x hx
  have NB := hx.right
  exact NB

theorem compl_union_subset : (A ∪ B)ᶜ ⊆ Aᶜ ∩ Bᶜ := by
  intro x hx
  -- hxを明示的に論理記号に翻訳する
  change (x ∈ A ∨ x ∈ B) -> False at hx
  -- infoviewでの表示形式が変わるだけ
  constructor
  · intro hA
    have hAorB : x ∈ A ∨ x ∈ B := Or.inl hA
    -- 型（右側: x ∈ B）を明示しないとコンパイラが迷子になる
    exact hx hAorB
  · intro hB
    exact hx (Or.inr hB)
    -- 直接やるなら明示する必要がない

theorem subset_compl_union : Aᶜ ∩ Bᶜ ⊆ (A ∪ B)ᶜ := by
  intro x ⟨notA, notB⟩
  -- ゴールの形を論理記号に翻訳する
  change x ∈ (A ∪ B) → False
  change (x ∈ A ∨ x ∈ B) → False
  -- ってかゴールに → が残ってるんだからまだintroできるじゃん
  intro h
  cases h with
  | inl hA => exact notA hA
  | inr hB => exact notB hB

theorem demorgan_union : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  constructor
  -- すでにある定理はapplyで適用する
  · apply compl_union_subset A B
  · apply subset_compl_union A B
theorem demorgan_union_2 : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  -- 要素xを取り出さず、見かけ上集合レベルのまま適用する
  apply Set.Subset.antisymm
  -- まあ裏で直ちにextを使っているのでどっちでも賢さは同じ
  · exact compl_union_subset A B
  · exact subset_compl_union A B


theorem compl_inter_subset : Aᶜ ∪ Bᶜ ⊆ (A ∩ B)ᶜ := by
  intro x hx ⟨hA, hB⟩
  cases hx with
  | inl hNotA => exact hNotA hA
  | inr hNotB => exact hNotB hB

theorem subset_compl_inter : (A ∩ B)ᶜ ⊆ Aᶜ ∪ Bᶜ := by
  intro x hx
  change (x ∈ A ∧ x ∈ B) → False at hx
  change (x ∈ A → False) ∨ (x ∈ B → False)
  by_cases hA : x ∈ A
  · -- hAとhxで、x ∈ B → Falseを作れそうだから先に
    apply Or.inr
    intro hB
    exact hx ⟨hA, hB⟩
  · exact Or.inl hA

theorem demorgan_intersection : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  constructor
  · apply subset_compl_inter
  · apply compl_inter_subset

----------
-- ルベーグ可測集合が共通部分で閉じている証明の中で使うやつ
----------
example : (A \ (E ∩ F)) ∩ E = (A ∩ E) \ F := by
  ext x
  constructor
  · intro ⟨⟨hA, hNotEF⟩,  hE⟩
    constructor
    · exact And.intro hA hE
    · intro hF
      have hEF := And.intro hE hF
      exact hNotEF hEF
  · intro ⟨⟨hA, hE⟩, hNotF⟩
    constructor
    · constructor
      · exact hA
      · intro hEF
        exact hNotF hEF.right
    · exact hE
/-
手書きの証明では、 x ∈ A \ (E ∩ F) ∩ E から代数的に同値変形という計算を
していって、最終的に x ∈ (A ∩ E) \ F までが同値で結ばれることを証明とするが
上のLean的証明は推移規則に従った木構造を構成することで証明としている
これを自然演繹というらしい。
手書きでは共通部分のドモルガンを使ったから排中律依存だけど、自然演繹を使うと
実は不要であることがわかった
calcを使うと手書きの証明と同じようにできる。明らかな変形はtautoして示す。
-/
example : x ∈ (A \ (E ∩ F)) ∩ E ↔ x ∈ (A ∩ E) \ F := by
  calc
    x ∈ (A \ (E ∩ F)) ∩ E
      ↔ (x ∈ A ∧ ¬(x ∈ E ∧ x ∈ F)) ∧ x ∈ E := by rfl
    -- ドモルガンを使う
    _ ↔ (x ∈ A ∧ (¬ x ∈ E ∨ ¬ x ∈ F)) ∧ x ∈ E := by rw [not_and_or]
    -- 順番を変える（結合・交換則）
    _ ↔ (x ∈ A ∧ x ∈ E) ∧ (¬ x ∈ E ∨ ¬ x ∈ F) := by tauto
    -- 分配法則と矛盾 (E ∧ ¬E) の除去
    _ ↔ x ∈ A ∧ x ∈ E ∧ ¬ x ∈ F := by tauto
    -- Leanは∧を右結合で評価するが、右辺に合わないので結合の順番を変える
    _ ↔ (x ∈ A ∧ x ∈ E) ∧ ¬ x ∈ F := by tauto
    _ ↔ x ∈ (A ∩ E) \ F := by rfl
-- このように手書きと同じようにできるけど
-- InfoViewが無意味で証明支援されている感じがしない
---
example : (A \ (E ∩ F)) \ E = A \ E := by
  ext x
  constructor
  · intro ⟨⟨hA, hNotEF⟩, hNotE⟩
    exact And.intro hA hNotE
  · intro ⟨hA, hNotE⟩
    constructor
    · constructor
      · exact hA
      · intro hEF
        exact hNotE hEF.left
    · exact hNotE
-- これを手書きと同じようにするために、吸収律を作っておく
theorem my_absorption (P Q : Prop) : P ∧ (P ∨ Q) ↔ P := by
  constructor
  · intro h
    exact h.left
  · intro hP
    constructor
    · exact hP
    · exact Or.inl hP
example (P Q : Prop) : P ∧ (P ∨ Q) ↔ P :=
  Iff.intro
    (fun h => h.left)
    (fun hP => And.intro hP (Or.inl hP))
-- ⟨ ⟩ を使えば1行でもかける！
example (P Q : Prop) : P ∧ (P ∨ Q) ↔ P :=
  ⟨fun h => h.left, fun hP => ⟨hP, Or.inl hP⟩⟩
example : x ∈ (A \ (E ∩ F)) \ E ↔ x ∈ A \ E := by
  calc
    x ∈ (A \ (E ∩ F)) \ E
      ↔ (x ∈ A ∧ ¬(x ∈ E ∧ x ∈ F)) ∧ ¬x ∈ E := by rfl
    _ ↔ (x ∈ A ∧ (¬x ∈ E ∨ ¬x ∈ F)) ∧ ¬x ∈ E := by rw [not_and_or]
    _ ↔ x ∈ A ∧ ¬x ∈ E ∧ (¬x ∈ E ∨ ¬x ∈ F) := by tauto
    -- 吸収律もTautoで行けるけど明示的にしたい
    _ ↔  x ∈ A ∧ ¬x ∈ E := by rw [my_absorption]
    _ ↔ x ∈ A \ E := by rfl
