import Mathlib

open Finset

def mrange (n : ℕ) := map ⟨fun x => x + 1, add_left_injective 1⟩ (range n)

noncomputable def upperBoundOnr (n : ℕ) := ⌈(n ^ (1/4 : ℝ) : ℝ)⌉₊

noncomputable def upperBoundOnh (n : ℕ) := ⌈(n ^ (1/100 : ℝ) : ℝ)⌉₊

noncomputable def generalizedCountOfSquares (n : ℕ) (f₁ f₂ : ℕ → ℝ) : ℝ :=
  ∑ x ∈ (mrange n),
  ∑ r ∈ mrange (upperBoundOnr n),
  ∑ h ∈ mrange (upperBoundOnh n), (f₁ x) * (f₂ (x + (r + h)^2))

noncomputable def countOfSquares (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  generalizedCountOfSquares n f f

def containsSquareDifference (S : Finset ℕ) : Prop := ∃ d : ℕ, ∃ a ∈ S, a + d ^ 2 ∈ S

def id' {α : Type} (x : ℝ) : α → ℝ := fun _ => x
def Finset.indicator {α : Type} [DecidableEq α] (S : Finset α) : α → ℝ :=
  S.piecewise (id' 1) (id' 0)

lemma non_zero_countOfSquares_implies_squareDifference (n : ℕ) (S : Finset ℕ)
     : countOfSquares n S.indicator ≠ 0 → containsSquareDifference S := by
  contrapose!
  intro squareDifferenceFree

  unfold containsSquareDifference at squareDifferenceFree
  push_neg at squareDifferenceFree
  unfold countOfSquares generalizedCountOfSquares

  apply sum_eq_zero
  intros x _
  apply sum_eq_zero
  intros r _
  apply sum_eq_zero
  intros h _

  by_cases (x ∈ S)
  case neg xNotInS =>
    unfold indicator
    simp
    left
    exact if_neg xNotInS
  case pos xInS =>
    unfold indicator
    simp
    right
    exact if_neg (squareDifferenceFree (r + h) x xInS)

noncomputable def almostN (n : ℕ) := n - (upperBoundOnr n + upperBoundOnh n)^2
noncomputable def almostMaxCountOfSquares (n : ℕ) :=
  (almostN n) * (upperBoundOnr n) * (upperBoundOnh n)

lemma uniform_δ_indicator_at_least_sqr_δ_density_of_countOfSquares_minus_error
    {n : ℕ} {δ : ℝ} (δ_in_unit_interval : 0 ≤ δ ∧ δ ≤ 1)
    (n_is_large : (upperBoundOnr n + upperBoundOnh n)^2 < n) :
    δ ^ 2 * (almostMaxCountOfSquares n) ≤ countOfSquares n (δ • (mrange n).indicator) := by
  dsimp [almostMaxCountOfSquares, countOfSquares, generalizedCountOfSquares, indicator]
  dsimp [piecewise, id']
  simp only [mul_assoc, ite_mul]
  simp
  unfold mrange
  simp
  rw [← ge_iff_le]

  let almost_n := n - (upperBoundOnr n + upperBoundOnh n)^2
  have can_go_to_subset {f : ℕ → ℕ} (fpos : ∀ (x : ℕ), 0 ≤ f x) :
      (∑ x ∈ range n, f x ≥ ∑ x ∈ range almost_n, f x) := by
    apply sum_le_sum_of_subset_of_nonneg ?_ fun i a a ↦ fpos i
    simp
    omega

  let innerTerm (x : ℕ) :=
    ∑ r ∈ range (upperBoundOnr n),
      ∑ h ∈ range (upperBoundOnh n),
        if ∃ a < n, a + 1 = x + 1 + (r + 1 + (h + 1)) ^ 2 then δ * δ else 0

  have innerTerm_pos : ∀ (x : ℕ), 0 ≤ innerTerm x := by
    intro x
    dsimp [innerTerm]
    apply sum_nonneg
    intro _ _
    apply sum_nonneg
    intro _ _
    apply ite_nonneg (mul_self_nonneg δ)
    rfl

  have to_subset : (∑ x ∈ range n, innerTerm x) ≥ (∑ x ∈ range almost_n, innerTerm x) := by
    apply sum_le_sum_of_subset_of_nonneg ?_ fun i a a ↦ innerTerm_pos i
    simp
    omega

  convert to_subset using 1
  dsimp [innerTerm, almost_n]

  have eq_in_innerTerm : ∀ x ∈ range almost_n, ∀ r ∈ range (upperBoundOnr n), ∀ h ∈ range (upperBoundOnh n),
      ∃ a < n, a + 1 = x + 1 + (r + 1 + (h + 1)) ^ 2 := by
    intros x hx r hr h hh
    use (x + (r + h + 2)^2)
    constructor
    · dsimp [almost_n, upperBoundOnr, upperBoundOnh] at *
      simp only [mem_range] at *
      calc x + (r + h + 2)^2
        _ ≤ x + (upperBoundOnr n + h + 1)^2 := by
          simp
          have : (r + h + 2) ≤ (upperBoundOnr n + h + 1) := by
            dsimp [upperBoundOnr]
            omega
          calc (r + h + 2)^2
            _ = (r + h + 2) * (r + h + 2) := pow_two (r + h + 2)
            _ ≤ (upperBoundOnr n + h + 1) * (r + h + 2) := by simp; omega
            _ ≤ (upperBoundOnr n + h + 1) * (upperBoundOnr n + h + 1) := by simp; omega
            _ = (upperBoundOnr n + h + 1) ^ 2 := by rw [pow_two]
        _ ≤ x + (upperBoundOnr n + upperBoundOnh n)^2 := by
          simp
          have : (upperBoundOnr n + h + 1) ≤ (upperBoundOnr n + upperBoundOnh n) := by
            dsimp [upperBoundOnh]
            omega
          calc (upperBoundOnr n + h + 1)^2
            _ = (upperBoundOnr n + h + 1) * (upperBoundOnr n + h + 1) := by rw [pow_two]
            _ ≤ (upperBoundOnr n + upperBoundOnh n) * (upperBoundOnr n + h + 1) := by simp; omega
            _ ≤ (upperBoundOnr n + upperBoundOnh n) * (upperBoundOnr n + upperBoundOnh n) :=
              Nat.mul_le_mul_left (upperBoundOnr n + upperBoundOnh n) (by omega)
            _ = (upperBoundOnr n + upperBoundOnh n) ^ 2 := by rw [pow_two]
        _ < n - (upperBoundOnr n + upperBoundOnh n)^2 + (upperBoundOnr n + upperBoundOnh n)^2 := by
          simp
          dsimp [upperBoundOnr, upperBoundOnh]
          exact hx
        _ = n := by
          dsimp [upperBoundOnr, upperBoundOnh]
          omega
    · linarith

  -- apply sum_eq_card_nsmul
  sorry

-- approach should be the following: do cases. if we have not many fewer than
-- expected square differences in S, then we are done. otherwise, we can go to a
-- denser subset by the density increment argument and we show that recursively
-- calling furstenberg_sarkozy terminates because δ increases and is at most one

theorem furstenberg_sarkozy :
    ∀ δ : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, ∀ S ⊆ (range n),
    n ≥ n₀ ∧ S.card ≥ δ * n → ∃ d : ℕ, ∃ a ∈ S, a + d ^ 2 ∈ S :=
  sorry
