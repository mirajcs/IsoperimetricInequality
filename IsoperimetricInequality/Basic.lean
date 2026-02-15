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


end
