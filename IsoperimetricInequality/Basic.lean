import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

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
lemma fourierSeries_sq (x : ℝ) :  
  --(hsum : Summable fun n : ℕ+ => (a n * cos (n * x) + b n * sin (n * x))) : 
  (fourierSeries a b x)^2 = (a 0)^2 / 4 + 
  a 0 * (∑' n : ℕ+ , (a n * cos (n * x) + b n * sin (n * x))) + 
  (∑' n : ℕ+ , (a n * cos (n * x) + b n * sin (n * x)))^2 := by 
unfold fourierSeries 
ring

-- simplifying the expansion of square term
lemma expand_sqare (x : ℝ)
    (hc : Summable fun n : ℕ+ => a n * cos (n * x))
    (hs : Summable fun n : ℕ+ => b n * sin (n * x)) :
    (∑' n : ℕ+, (a n * cos (n * x) + b n * sin (n * x)))^2 =
    (∑' n : ℕ+, a n * cos (n * x))^2 +
    2 * (∑' n : ℕ+, a n * cos (n * x)) * (∑' n : ℕ+, b n * sin (n * x)) +
    (∑' n : ℕ+, b n * sin (n * x))^2 := by
  rw [hc.tsum_add hs]
  ring

-- Expanding the square of the sine sum into a double sum
-- (∑ bₙ sin(nx))² = ∑ₙ ∑ₘ bₙ bₘ sin(nx) sin(mx)
lemma expand_sin_sq (x : ℝ)
    (hs : Summable fun n : ℕ+ => b n * sin (n * x))
    -- The product family (n,m) ↦ bₙ sin(nx) · bₘ sin(mx) is summable
    (hprod : Summable fun z : ℕ+ × ℕ+ =>
      (b z.1 * sin (z.1 * x)) * (b z.2 * sin (z.2 * x)))
    -- Each inner sum is summable (needed for converting paired → iterated tsum)
    (hinner : ∀ n : ℕ+, Summable fun m : ℕ+ =>
      (b n * sin (n * x)) * (b m * sin (m * x))) :
    (∑' n : ℕ+, b n * sin (n * x))^2 =
    ∑' n : ℕ+, ∑' m : ℕ+, b n * b m * sin (n * x) * sin (m * x) := by
  -- Step 1: Rewrite x² as x * x
  rw [sq]
  -- Step 2: Product of tsums → tsum over pairs
  rw [hs.tsum_mul_tsum hs hprod]
  -- Step 3: Paired tsum → iterated tsum
  rw [hprod.tsum_prod' hinner]
  -- Step 4: Show the terms match pointwise
  congr 1; ext n; congr 1; ext m
  ring

-- Expanding the square of the sine sum into a double sum
-- (∑ aₙ cos(nx))² = ∑ₙ ∑ₘ aₙ aₘ cos(nx) cos(mx)
lemma expand_cos_sq (x : ℝ)
    (hs1 : Summable fun n : ℕ+ => a n * cos (n * x))
    -- The product family (n,m) ↦ aₙ cos(nx) · aₘ cos(mx) is summable
    (hprod1 : Summable fun z : ℕ+ × ℕ+ =>
      (a z.1 * cos (z.1 * x)) * (a z.2 * cos (z.2 * x)))
    -- Each inner sum is summable (needed for converting paired → iterated tsum)
    (hinner : ∀ n : ℕ+, Summable fun m : ℕ+ =>
      (a n * cos (n * x)) * (a m * cos (m * x))) :
    (∑' n : ℕ+, a n * cos (n * x))^2 =
    ∑' n : ℕ+, ∑' m : ℕ+, a n * a m * cos (n * x) * cos (m * x) := by
  -- Step 1: Rewrite x² as x * x
  rw [sq]
  -- Step 2: Product of tsums → tsum over pairs
  rw [hs1.tsum_mul_tsum hs1 hprod1]
  -- Step 3: Paired tsum → iterated tsum
  rw [hprod1.tsum_prod' hinner]
  -- Step 4: Show the terms match pointwise
  congr 1; ext n; congr 1; ext m
  ring





end
