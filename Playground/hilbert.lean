variable (φ ψ χ: Prop)

theorem jakka: φ → (ψ → φ) := by
  intro phi
  intro psi
  exact phi

theorem jakka_raw:  φ → (ψ → φ) :=
  fun phi _ => phi

theorem ganni_no_bunpai: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)) := by
  intro h1
  intro h2
  intro phi
  apply h1 -- φとψそれぞれのcaseを証明すればよくなる
  exact phi
  apply h2
  exact phi

theorem ganni_no_bunpai_raw: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)) :=
  fun h1 h2 phi => h1 phi (h2 phi)

theorem taigu_gyaku: (¬ψ → ¬φ) → (φ → ψ) := by
  intro h1
  intro phi
  by_cases h: ψ
  .
    exact h
  .
    have nphi := h1 h
    have fls := nphi phi
    exact False.elim fls
