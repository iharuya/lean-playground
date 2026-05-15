variable (φ ψ χ : Prop)

theorem currying : (φ ∧ ψ → χ) → (φ → ψ → χ) := by
  intro h
  intro phi
  intro psi
  have both := And.intro phi psi
  exact h both

theorem uncurrying : (φ → ψ → χ) → (φ ∧ ψ → χ) := by
  intro h
  intro both
  have phi := And.left both
  have psi := And.right both
  exact h phi psi

theorem my_and_comm : (φ ∧ ψ) → (ψ ∧ φ) := by
  intro both
  have phi := And.left both
  have psi := And.right both
  exact And.intro psi phi

theorem and_implies_or : (φ ∧ ψ) → (φ ∨ ψ) := by
  intro h
  exact Or.inl h.left

theorem or_weakning : (φ → ψ) → (φ → ψ ∨ χ) := by
  intro h
  intro phi
  have psi := h phi
  exact Or.inl psi

theorem my_or_comm : (φ ∨ ψ) → (ψ ∨ φ) := by
  intro h
  cases h with
  | inl phi =>
    exact Or.inr phi
  | inr psi =>
    exact Or.inl psi

theorem distribution_of_implication : (φ → ψ ∧ χ) → ((φ → ψ) ∧ (φ → χ)) := by
  intro h
  -- ゴールが ∧ なら constructor で割る
  constructor
  · intro phi
    have both := h phi
    exact both.left
  . intro psi
    have both := h psi
    exact both.right
