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
    simp only [const_one, mul_eq_zero, Set.indicator_apply_eq_zero, mem_coe, Pi.one_apply,
      one_ne_zero, imp_false]
    left
    exact xNotInS
  case pos xInS =>
    unfold indicator
    simp only [const_one, mul_eq_zero, Set.indicator_apply_eq_zero, mem_coe, Pi.one_apply,
      one_ne_zero, imp_false]
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
    {n : ℕ} {δ : ℝ}
    (n_is_large : (upperBoundOny n + upperBoundOnz n)^2 ≤ n) :
    δ ^ 2 * (almostMaxOfCountOfSquares n) ≤ countOfSquares n (δ • (range' n).indicator) := by
  simp only [countOfSquares, generalizedCountOfSquares, range', indicator,
              Pi.smul_apply, smul_eq_mul, coe_Ioc]
  have almost_sub : Ioc 0 (almostN n) ⊆ Ioc 0 n := by
    simp only [almostN, Ioc_subset_Ioc_right, Nat.sub_le]
  refine le_trans (le_of_eq ?_) (sum_le_sum_of_subset_of_nonneg almost_sub ?_)
  · rw [sum_eq_card_nsmul]
    rotate_left
    · intro a ha
      rw [sum_eq_card_nsmul]
      intro y hy
      rw [sum_eq_card_nsmul (b := δ * δ)]
      intro z hz
      have cond : a + (y + z) ^ 2 ∈ Set.Ioc 0 n := by
        simp only [mem_Ioc, Set.mem_Ioc, add_pos_iff] at ha hy hz ⊢
        refine ⟨Or.inl ha.1, ?_⟩
        dsimp only [almostN] at ha
        have hyz : (y + z) ^ 2 ≤ (upperBoundOny n + upperBoundOnz n) ^ 2 := by
          nlinarith only [hy.2, hz.2]
        simpa only [tsub_add_cancel_of_le n_is_large] using add_le_add ha.2 hyz
      have ha : a ∈ Set.Ioc 0 n := by simpa only [mem_Ioc] using almost_sub ha
      rw [Set.indicator_of_mem ha _, Set.indicator_of_mem cond _]
      simp only [const_apply, mul_one]
    · simp only [almostMaxOfCountOfSquares, maxOfGeneralizedCountOfSquares,
        Nat.cast_mul, Nat.card_Ioc, tsub_zero]
      ring
  · intro a _ _
    apply sum_nonneg
    intro y _
    apply sum_nonneg
    intro z _
    ring_nf
    refine mul_nonneg (mul_nonneg (sq_nonneg δ) ?_) ?_ <;>
      exact Set.indicator_nonneg (by simp) _

lemma uniform_δ_indicator_at_most_sqr_δ_density_of_countOfSquares
    (n : ℕ) (δ : ℝ) :
    countOfSquares n (δ • (range' n).indicator) ≤ δ ^ 2 * (maxOfCountOfSquares n) := by
  simp only [countOfSquares, maxOfCountOfSquares, maxOfGeneralizedCountOfSquares,
              generalizedCountOfSquares, indicator, range', coe_Ioc, const_one,
              Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Set.indicator, Set.mem_Ioc,
              Pi.one_apply, mul_ite, mul_one, mul_zero, add_pos_iff, ite_mul, zero_mul,
              ←ite_and]
  apply le_trans
  · apply sum_le_card_nsmul
    intro x hx
    simp only [mem_Ioc] at hx
    simp only [hx, true_or, true_and, and_self, and_true]
    apply sum_le_card_nsmul
    intro y _
    apply sum_le_card_nsmul
    intro z _
    apply ite_le_sup (δ * δ) 0
  · simp only [Nat.card_Ioc, tsub_zero, nsmul_eq_mul]
    ring_nf
    norm_cast
    apply le_of_eq
    simp only [Nat.cast_mul, mul_eq_mul_left_iff, sup_eq_left, mul_eq_zero, Nat.cast_eq_zero]
    left
    exact sq_nonneg δ

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
