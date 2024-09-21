import Mathlib

open Finset

def generalDensityOfSquares (n : ℕ) (f₁ f₂ : ℕ → unitInterval) : ℝ :=
  ∑ x ∈ (range n), ∑ r ∈ (range (n ^ (1/3))), ∑ h ∈ (range (n ^ (1/100))),
  (f₁ x) * (f₂ (x + (r + h)^2))

def densityOfSquares (n : ℕ) (f : ℕ → unitInterval) : ℝ :=
  generalDensityOfSquares n f f

def containsSquareDifference (S : Finset ℕ) : Prop := ∃ d : ℕ, ∃ a ∈ S, a + d ^ 2 ∈ S

def one {α : Type} : α → unitInterval := 1
def zero {α : Type} : α → unitInterval := 0
def Finset.indicator {α : Type} [DecidableEq α] (S : Finset α) : α → unitInterval :=
  S.piecewise one zero

lemma zero_density_if_set_is_square_difference_free (n : ℕ) (S : Finset ℕ)
    (squareDifferenceFree : ¬ containsSquareDifference S) :
    densityOfSquares n S.indicator = 0 := by

  unfold containsSquareDifference at squareDifferenceFree
  push_neg at squareDifferenceFree
  unfold densityOfSquares generalDensityOfSquares

  refine Finset.sum_eq_zero ?_
  intros x _
  refine Finset.sum_eq_zero ?_
  intros r _
  refine Finset.sum_eq_zero ?_
  intros h _

  by_cases (x ∈ S)
  case neg xNotInS =>
    unfold indicator
    rw [mul_eq_zero]
    left
    norm_num
    exact if_neg xNotInS
  case pos xInS =>
    unfold indicator
    rw [mul_eq_zero]
    right
    simp
    exact if_neg (squareDifferenceFree (r + h) x xInS)

theorem furstenberg_sarkozy :
    ∀ α : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, ∀ S ⊆ (range n),
    n ≥ n₀ ∧ S.card ≥ α * n → ∃ d : ℕ, ∃ a ∈ S, a + d ^ 2 ∈ S :=
  sorry
