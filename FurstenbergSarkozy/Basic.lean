import Mathlib

open Finset

noncomputable def generalizedCountOfSquares (n : ℕ) (f₁ f₂ : ℕ → unitInterval) : ℝ :=
  ∑ x ∈ (range n),
  ∑ r ∈ range (⌈(n ^ (1/3 : ℝ) : ℝ)⌉₊),
  ∑ h ∈ range (⌈(n ^ (1/100 : ℝ) : ℝ)⌉₊), (f₁ x) * (f₂ (x + (r + h)^2))

noncomputable def countOfSquares (n : ℕ) (f : ℕ → unitInterval) : ℝ :=
  generalizedCountOfSquares n f f

def containsSquareDifference (S : Finset ℕ) : Prop := ∃ d : ℕ, ∃ a ∈ S, a + d ^ 2 ∈ S

def id' {α : Type} (x : unitInterval) : α → unitInterval := fun _ => x
def Finset.indicator {α : Type} [DecidableEq α] (S : Finset α) : α → unitInterval :=
  S.piecewise (id' 1) (id' 0)

lemma square_difference_free_set_has_zero_countOfSquares (n : ℕ) (S : Finset ℕ)
    (squareDifferenceFree : ¬ containsSquareDifference S) :
    countOfSquares n S.indicator = 0 := by

  unfold containsSquareDifference at squareDifferenceFree
  push_neg at squareDifferenceFree
  unfold countOfSquares generalizedCountOfSquares

  refine sum_eq_zero ?_
  intros x _
  refine sum_eq_zero ?_
  intros r _
  refine sum_eq_zero ?_
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

theorem furstenberg_sarkozy :
    ∀ α : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, ∀ S ⊆ (range n),
    n ≥ n₀ ∧ S.card ≥ α * n → ∃ d : ℕ, ∃ a ∈ S, a + d ^ 2 ∈ S :=
  sorry
