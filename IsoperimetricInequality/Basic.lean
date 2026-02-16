import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Real
open scoped BigOperators Topology

noncomputable section

-- The Fourier coefficients
variable (a : ℕ → ℝ) (b : ℕ → ℝ)

-- The classical Fourier series as a function of x
def fourierSeries (x : ℝ) : ℝ :=
    (1/2) * a 0 + ∑' n : ℕ+, (a n * cos (n * x) + b n * sin (n * x))

-- The sum part of fourier series
def fourierSum (x : ℝ) : ℝ :=
    ∑' n : ℕ+, (a n * cos (n * x) + b n * sin (n * x))

-- f(x) = a₀/2 + S(x) where is S is the sum
lemma fourierSeries_eq (x : ℝ) :
  fourierSeries a b x = (1/2) * a 0 + fourierSum a b x := by rfl 

-- The expansion of [f(x)]² 
theorem fourierSeries_sq (x : ℝ) : by 
  sorry 


end
