import Mathlib

open Finset Function

def range' (n : ℕ) : Finset ℕ := Ioc 0 n

noncomputable def upperBoundOny (n : ℕ) := ⌈(n ^ (1/3 : ℝ) : ℝ)⌉₊

noncomputable def upperBoundOnz (n : ℕ) := ⌈(n ^ (1/100 : ℝ) : ℝ)⌉₊

noncomputable def generalizedCountOfSquares (n : ℕ) (f₁ f₂ : ℕ → ℝ) : ℝ :=
  ∑ x ∈ range' n,
  ∑ y ∈ range' (upperBoundOny n),
  ∑ z ∈ range' (upperBoundOnz n), (f₁ x) * (f₂ (x + (y + z)^2))

noncomputable def countOfSquares (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  generalizedCountOfSquares n f f

def Finset.containsSquareDifference (S : Finset ℕ) : Prop :=
  ∃ d : {d : ℕ // d > 0}, ∃ a ∈ S, a + d ^ 2 ∈ S

noncomputable def Finset.indicator {α : Type} [DecidableEq α] (S : Finset α) : α → ℝ :=
  S.toSet.indicator (const α 1)

lemma non_zero_countOfSquares_implies_squareDifference (n : ℕ) (S : Finset ℕ)
     : countOfSquares n S.indicator ≠ 0 → S.containsSquareDifference := by
  contrapose!
  intro squareDifferenceFree

  unfold containsSquareDifference at squareDifferenceFree
  push_neg at squareDifferenceFree
  unfold countOfSquares generalizedCountOfSquares range'

  apply sum_eq_zero
  intros x _
  apply sum_eq_zero
  intros y hy
  apply sum_eq_zero
  intros z hz

  by_cases (x ∈ S)
  case neg xNotInS =>
    unfold indicator
    simp
    left
    exact xNotInS
  case pos xInS =>
    unfold indicator
    simp
    right
    simp at hy
    simp at hz
    have ypz_pos : 0 < y + z := by omega
    exact (squareDifferenceFree ⟨ y + z, ypz_pos ⟩ x xInS)

noncomputable def maxOfGeneralizedCountOfSquares (n₁ n₂ n₃ : ℕ) :=
  n₁ * (upperBoundOny n₂) * (upperBoundOnz n₃)
noncomputable def maxOfCountOfSquares (n : ℕ) := maxOfGeneralizedCountOfSquares n n n
noncomputable def almostN (n : ℕ) := n - (upperBoundOny n + upperBoundOnz n)^2
noncomputable def almostMaxOfCountOfSquares (n : ℕ) :=
  maxOfGeneralizedCountOfSquares (almostN n) n n

lemma uniform_δ_indicator_at_least_sqr_δ_density_of_countOfSquares_minus_error
    {n : ℕ} {δ : ℝ} (δ_in_unit_interval : 0 ≤ δ ∧ δ ≤ 1)
    (n_is_large : (upperBoundOny n + upperBoundOnz n)^2 < n) :
    δ ^ 2 * (almostMaxOfCountOfSquares n) ≤ countOfSquares n (δ • (range' n).indicator) := by

  let innerTerm (x : ℕ) :=
    ∑ y ∈ range' (upperBoundOny n),
      ∑ z ∈ range' (upperBoundOnz n),
        if x + (y + z) ^ 2 ≤ n then δ * δ else 0

  let almost_n := almostN n
  suffices reduction :
      countOfSquares n (δ • (range' n).indicator) ≥ ∑ x ∈ range' almost_n, innerTerm x by

    suffices another_reduction :
        δ ^ 2 * (almostMaxOfCountOfSquares n) = ∑ x ∈ range' almost_n, innerTerm x by
      apply Eq.trans_le another_reduction
      simp_rw [← ge_iff_le]
      exact reduction

    simp [innerTerm]
    rw [← sum_product' (s := range' almost_n)]
    rw [← sum_product' (s := (range' almost_n ×ˢ range' (upperBoundOny n))), sum_ite_of_true]
    · simp
      ring_nf
      simp_rw [mul_assoc]
      simp
      left
      norm_cast
      simp [range', almostMaxOfCountOfSquares, maxOfGeneralizedCountOfSquares]
      ring_nf
    · intros xs hxs
      simp at hxs
      set x := xs.1.1
      set y := xs.1.2
      set z := xs.2
      dsimp [range'] at hxs
      simp only [mem_Ioc] at hxs
      let xnneg := hxs.1.1.1
      let hx := hxs.1.1.2
      let hy := hxs.1.2.2
      let hz := hxs.2.2

      calc x + (y + z)^2
        _ ≤ almost_n + (y + z)^2 := by omega
        _ ≤ almost_n + (upperBoundOny n + z)^2 := by
          simp
          apply Nat.pow_le_pow_of_le_left
          omega
        _ ≤ almost_n + (upperBoundOny n + upperBoundOnz n)^2 := by
          simp
          apply Nat.pow_le_pow_of_le_left
          omega

      simp [almost_n, upperBoundOny, upperBoundOnz, almostN]
      simp [upperBoundOny, upperBoundOnz] at n_is_large
      omega

  dsimp [almostMaxOfCountOfSquares, countOfSquares, generalizedCountOfSquares, indicator]
  dsimp [Set.indicator, const]
  simp only [mul_assoc, ite_mul]
  simp
  simp_rw [← ge_iff_le]
  dsimp [innerTerm]

  have innerTerm_nneg : ∀ (x : ℕ), 0 ≤ innerTerm x := by
    intro x
    dsimp [innerTerm]
    apply sum_nonneg
    intro _ _
    apply sum_nonneg
    intro _ _
    apply ite_nonneg (mul_self_nonneg δ)
    rfl

  have range'_subset {m n : ℕ} (m_le_n : m ≤ n) : (range' m) ⊆ (range' n) := by
    dsimp [range']
    apply Ioc_subset_Ioc_right
    assumption

  have almost_n_le_n : almost_n ≤ n := by
    dsimp [almost_n, almostN]
    omega

  rw [ge_iff_le]
  -- apply sum_le_sum_of_subset_of_nonneg (range'_subset almost_n_le_n) ?_
  sorry

-- approach should be the following: do cases. if we have not many fewer than
-- expected square differences in S, then we are done. otherwise, we can go to a
-- denser subset by the density increment argument and we show that recursively
-- calling furstenberg_sarkozy terminates because δ increases and is at most one

noncomputable def unitInterval' := (Set.Ioc (0 : ℝ) (1 : ℝ))

theorem furstenberg_sarkozy :
    ∀ δ ∈ unitInterval', ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∀ S ⊆ (range' n), δ * n ≤ S.card →
    S.containsSquareDifference :=
  sorry
