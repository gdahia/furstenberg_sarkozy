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

lemma sum_indicator_supset_le_card' {α β : Type} [DecidableEq α] [DecidableEq β]
    (S : Finset α) {T : Finset β} {f : β → α} (hf : Set.InjOn f (f ⁻¹' S)) :
    ∑ x ∈ T, S.indicator (f x) ≤ #S := by
  simp only [indicator, Set.indicator, mem_coe, const_apply]
  apply le_trans
  · apply sum_le_sum
    · intro x hx
      apply le_of_eq
      apply ite_congr (c := x ∈ S.preimage f hf)
      · simp only [Finset.mem_preimage, mem_coe]
      · intro
        rfl
      · intro
        rfl
  rw [sum_ite_mem]
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.cast_le]
  have T_inter_pre_S_subset_pre_S : T ∩ S.preimage f hf ⊆ S.preimage f hf := by simp only [inter_subset_right]
  apply le_trans
  · apply card_le_card T_inter_pre_S_subset_pre_S
  · apply card_le_card_of_injOn
    · simp only [mem_preimage]
      intro _ hfS
      exact hfS
    · simp only [coe_preimage]
      assumption

lemma sum_indicator_supset_le_card {α : Type} [DecidableEq α] {S T : Finset α} :
    ∑ x ∈ T, S.indicator x ≤ #S := by
  apply sum_indicator_supset_le_card'
  simp only [Set.preimage_id', Set.InjOn, mem_coe, imp_self, implies_true]

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
    simp only [mem_Ioc] at hy
    simp only [mem_Ioc] at hz
    have ypz_pos : 0 < y + z := by omega
    exact (squareDifferenceFree ⟨ y + z, ypz_pos ⟩ x xInS)

lemma uniform_indicator_vs_uniform_indicator_upper_bound (n : ℕ) (δ : ℝ) :
    countOfSquares n (δ • (range' n).indicator) ≤ δ ^ 2 * n * (upperBoundOny n) * (upperBoundOnz n) := by

  simp only [countOfSquares, generalizedCountOfSquares, indicator, range',
    coe_Ioc, const_one, Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Set.indicator,
    Set.mem_Ioc, Pi.one_apply, mul_ite, mul_one, mul_zero, add_pos_iff, ite_mul,
    zero_mul, ←ite_and]

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

noncomputable def unitInterval' := (Set.Ioc (0 : ℝ) (1 : ℝ))

lemma dense_set_vs_uniform_indicator_upper_bound {n : ℕ} {δ : ℝ} {S : Finset ℕ}
    (δ_is_density : δ ∈ unitInterval') (S_is_dense : #S = δ * n) :
    generalizedCountOfSquares n S.indicator (δ • (range' n).indicator) ≤
    δ ^ 2 * n * (upperBoundOny n) * (upperBoundOnz n) := by

  simp only [generalizedCountOfSquares]

  rw [sum_comm]
  apply le_trans
  · apply sum_le_card_nsmul
    intro y hy
    rw [sum_comm]
    apply sum_le_card_nsmul
    intro z hz
    apply sum_le_sum
    · intro x hx
      apply mul_le_mul_of_nonneg_left
      · simp only [indicator, range', coe_Ioc, const_one, Pi.smul_apply, Set.indicator,
          Set.mem_Ioc, add_pos_iff, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
        apply le_trans
        · apply ite_le_sup δ 0
        · simp only [sup_le_iff]
          constructor
          · exact le_rfl
          · simp only [unitInterval'] at δ_is_density
            exact δ_is_density.1.le
      · simp only [indicator, Set.indicator, mem_coe, const_apply]
        positivity
  · simp only [range', Nat.card_Ioc, tsub_zero, nsmul_eq_mul]
    rw [← mul_assoc, mul_comm, mul_assoc]
    refine mul_le_mul ?_ le_rfl (by positivity) (by positivity)
    rw [← sum_mul, mul_comm]
    apply le_trans (mul_le_mul_of_nonneg_left sum_indicator_supset_le_card δ_is_density.1.le)
    rw [S_is_dense]
    nlinarith

lemma uniform_indicator_vs_dense_set_upper_bound {n : ℕ} {δ : ℝ} {S : Finset ℕ}
    (δ_is_density : δ ∈ unitInterval') (S_is_dense : #S = δ * n) :
    generalizedCountOfSquares n (δ • (range' n).indicator) S.indicator ≤
    δ ^ 2 * n * (upperBoundOny n) * (upperBoundOnz n) := by

  simp only [generalizedCountOfSquares]

  rw [sum_comm]
  apply le_trans
  · apply sum_le_card_nsmul
    intro y hy
    rw [sum_comm]
    apply sum_le_card_nsmul
    intro z hz

    have bound_on_uniform_indicator :
        ∀ x ∈ range' n, ((δ • (range' n).indicator) x) * S.indicator (x + (y + z)^2) ≤ δ * S.indicator (x + (y + z)^2) := by
      intro x hx
      gcongr
      · simp only [indicator, Set.indicator, mem_coe, const_apply]
        positivity
      · simp_all only [range', mem_Ioc, indicator, coe_Ioc, const_one, Pi.smul_apply, Set.mem_Ioc,
          and_self, Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one, le_refl]

    apply le_trans (sum_le_sum bound_on_uniform_indicator)
    · rw [← mul_sum, mul_le_mul_left]
      · apply sum_indicator_supset_le_card'
        · simp only [Set.InjOn, Set.mem_preimage, mem_coe, add_left_inj, imp_self, implies_true]
      · simp only [unitInterval', Set.mem_Ioc] at δ_is_density
        exact δ_is_density.1
  · simp only [range', Nat.card_Ioc, tsub_zero, S_is_dense, nsmul_eq_mul]
    nlinarith


-- approach should be the following: do cases. if we have not many fewer than
-- expected square differences in S, then we are done. otherwise, we can go to a
-- denser subset by the density increment argument and we show that recursively
-- calling furstenberg_sarkozy terminates because δ increases and is at most one

theorem furstenberg_sarkozy :
    ∀ δ ∈ unitInterval', ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∀ S ⊆ (range' n), δ * n ≤ #S →
    S.containsSquareDifference :=
  sorry
