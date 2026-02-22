import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

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
lemma expand_square (x : ℝ)
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


-- Fourier series square fully expanded (step by step)
theorem fourier_series_sq_expanded (x : ℝ)
    (hc : Summable fun n : ℕ+ => a n * cos (n * x))
    (hs : Summable fun n : ℕ+ => b n * sin (n * x))
    (hprod_cos : Summable fun z : ℕ+ × ℕ+ =>
      (a z.1 * cos (z.1 * x)) * (a z.2 * cos (z.2 * x)))
    (hinner_cos : ∀ n : ℕ+, Summable fun m : ℕ+ =>
      (a n * cos (n * x)) * (a m * cos (m * x)))
    (hprod_sin : Summable fun z : ℕ+ × ℕ+ =>
      (b z.1 * sin (z.1 * x)) * (b z.2 * sin (z.2 * x)))
    (hinner_sin : ∀ n : ℕ+, Summable fun m : ℕ+ =>
      (b n * sin (n * x)) * (b m * sin (m * x))) :
    (fourierSeries a b x)^2 = (a 0)^2 / 4 +
    a 0 * (∑' n : ℕ+, (a n * cos (n * x) + b n * sin (n * x))) +
    ((∑' n : ℕ+, ∑' m : ℕ+, a n * a m * cos (n * x) * cos (m * x)) +
    2 * (∑' n : ℕ+, a n * cos (n * x)) * (∑' n : ℕ+, b n * sin (n * x)) +
    (∑' n : ℕ+, ∑' m : ℕ+, b n * b m * sin (n * x) * sin (m * x))) := by
  -- Step 1: Expand (a₀/2 + S)² into a₀²/4 + a₀·S + S²
  rw [fourierSeries_sq]
  -- Step 2: Expand S² into C² + 2·C·S_sin + S_sin²
  rw [expand_square a b x hc hs]
  -- Step 3: Expand C² into double sum
  rw [expand_cos_sq a x hc hprod_cos hinner_cos]
  -- Step 4: Expand S_sin² into double sum
  rw [expand_sin_sq b x hs hprod_sin hinner_sin]

/--
Taking the integration
-/
-- Integration of the constant term
lemma integration_of_const :
    ∫ _x in (-π)..π, (1 / 4) * (a 0)^2 = (1 / 2) * (a 0)^2 * π := by
  rw [intervalIntegral.integral_const]
  simp [smul_eq_mul]
  ring

-- ∫_{-π}^{π} cos(n·x) dx = 0 for any n : ℕ+
private lemma integral_cos_pnat (n : ℕ+) :
    ∫ x in (-π)..π, cos ((n : ℝ) * x) = 0 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast n.pos.ne'
  have h_sin : sin ((n : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (n : ℕ)
  have key : (n : ℝ) * ∫ x in (-π)..π, cos ((n : ℝ) * x) = 0 := by
    rw [intervalIntegral.mul_integral_comp_mul_left, integral_cos]
    simp [mul_neg, sin_neg, h_sin]
  exact (mul_eq_zero.mp key).resolve_left hn

-- ∫_{-π}^{π} sin(n·x) dx = 0 for any n : ℕ+
private lemma integral_sin_pnat (n : ℕ+) :
    ∫ x in (-π)..π, sin ((n : ℝ) * x) = 0 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast n.pos.ne'
  have key : (n : ℝ) * ∫ x in (-π)..π, sin ((n : ℝ) * x) = 0 := by
    rw [intervalIntegral.mul_integral_comp_mul_left, integral_sin]
    simp [mul_neg, cos_neg]
  exact (mul_eq_zero.mp key).resolve_left hn

-- ∫_{-π}^{π} (aₙcos(nx) + bₙsin(nx)) dx = 0 for each n : ℕ+ (orthogonality)
private lemma integral_fourierTerm (n : ℕ+) :
    ∫ x in (-π)..π, (a n * cos ((n : ℝ) * x) + b n * sin ((n : ℝ) * x)) = 0 := by
  have hc : Continuous (fun x => a n * cos ((n : ℝ) * x)) :=
    continuous_const.mul (continuous_cos.comp (continuous_const.mul continuous_id))
  have hs : Continuous (fun x => b n * sin ((n : ℝ) * x)) :=
    continuous_const.mul (continuous_sin.comp (continuous_const.mul continuous_id))
  rw [intervalIntegral.integral_add (hc.intervalIntegrable (-π) π) (hs.intervalIntegrable (-π) π),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cos_pnat n, integral_sin_pnat n, mul_zero, mul_zero, add_zero]

-- The cross term a₀ · fourierSum integrates to zero over [-π, π]:
-- ∫_{-π}^{π} a₀ · (∑_{n≥1} aₙcos(nx) + bₙsin(nx)) dx = 0
lemma integration_of_cos_sin
    (hF_int : ∀ n : ℕ+, IntervalIntegrable
      (fun x => a n * cos ((n : ℕ+) * x) + b n * sin ((n : ℕ+) * x))
      MeasureTheory.volume (-π) π)
    (hF_sum : Summable (fun n : ℕ+ =>
      ∫ x in (-π)..π, ‖a n * cos ((n : ℕ+) * x) + b n * sin ((n : ℕ+) * x)‖)) :
    ∫ x in (-π)..π, a 0 * fourierSum a b x = 0 := by
  -- Factor out the constant a 0
  rw [intervalIntegral.integral_const_mul]
  -- It suffices to show ∫ fourierSum = 0
  suffices h : ∫ x in (-π)..π, fourierSum a b x = 0 by simp [h]
  simp only [fourierSum]
  -- Interchange ∫ and ∑' (by summability of norms via dominated convergence)
  have hswap : ∫ x in (-π)..π,
        ∑' n : ℕ+, (a n * cos ((n : ℕ+) * x) + b n * sin ((n : ℕ+) * x)) =
        ∑' n : ℕ+, ∫ x in (-π)..π,
          (a n * cos ((n : ℕ+) * x) + b n * sin ((n : ℕ+) * x)) := by
    have h_le : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
    -- Convert interval integrals to restricted integrals over Ioc (-π) π
    simp_rw [intervalIntegral.integral_of_le h_le]
    symm
    -- Apply integral_tsum_of_summable_integral_norm with μ = volume.restrict (Ioc (-π) π)
    apply MeasureTheory.integral_tsum_of_summable_integral_norm
    · intro n; exact (hF_int n).1
    · simp_rw [← intervalIntegral.integral_of_le h_le]; exact hF_sum
  rw [hswap]
  -- Each term integrates to zero by orthogonality of trig functions
  simp_rw [integral_fourierTerm a b, tsum_zero]

-- ∫_(-π) ^π cos (nx) cos (mx) dx = 0 for n ≠ m
lemma integration_cos_cos_zero (n m : ℕ+) (h : n ≠ m) :
    ∫ x in (-π)..π, cos (n  * x) * cos (m * x) = 0 := by
  -- (n-m) ≠ 0 in ℝ
  have hnm_ne : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  -- sin((n-m)π) = 0  (integer multiple of π)
  have hnm_sin : sin (((n : ℝ) - m) * π) = 0 := by
    rw [sub_mul, sin_sub]
    have h1 : sin ((n : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (n : ℕ)
    have h2 : sin ((m : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (m : ℕ)
    simp [h1, h2]
  -- ∫ cos((n-m)x) = 0
  have int_nm : ∫ x in (-π)..π, cos (((n : ℝ) - m) * x) = 0 := by
    have key : ((n : ℝ) - m) * ∫ x in (-π)..π, cos (((n : ℝ) - m) * x) = 0 := by
      rw [intervalIntegral.mul_integral_comp_mul_left, integral_cos]
      simp [mul_neg, sin_neg, hnm_sin]
    exact (mul_eq_zero.mp key).resolve_left hnm_ne
  -- ∫ cos((n+m)x) = 0  (n+m : ℕ+ so use integral_cos_pnat)
  have int_np : ∫ x in (-π)..π, cos (((n : ℝ) + m) * x) = 0 := by
    have h_cast : ((n : ℝ) + m) = ((n + m : ℕ+) : ℝ) := by push_cast; ring
    rw [h_cast]; exact integral_cos_pnat (n + m)
  -- Product-to-sum: cos(nx)cos(mx) = ½cos((n-m)x) + ½cos((n+m)x)
  have prod_sum : ∀ x : ℝ, cos ((n : ℝ) * x) * cos ((m : ℝ) * x) =
      (1/2) * cos (((n : ℝ) - m) * x) + (1/2) * cos (((n : ℝ) + m) * x) := fun x => by
    have h1 := cos_sub ((n : ℝ) * x) ((m : ℝ) * x)
    have h2 := cos_add ((n : ℝ) * x) ((m : ℝ) * x)
    simp only [← sub_mul, ← add_mul] at h1 h2
    linarith
  simp_rw [prod_sum]
  have hc1 : IntervalIntegrable (fun x => (1/2 : ℝ) * cos (((n : ℝ) - m) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  have hc2 : IntervalIntegrable (fun x => (1/2 : ℝ) * cos (((n : ℝ) + m) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add hc1 hc2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      int_nm, int_np]; simp

-- ∫_(-π) ^π sin (nx) sin (mx) dx = 0 for n ≠ m
lemma integration_sin_sin_zero (n m : ℕ+) (h : n ≠ m) :
    ∫ x in (-π)..π, sin (n  * x) * sin (m * x) = 0 := by
  -- (n-m) ≠ 0 in ℝ
  have hnm_ne : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  -- sin((n-m)π) = 0  (integer multiple of π)
  have hnm_sin : sin (((n : ℝ) - m) * π) = 0 := by
    rw [sub_mul, sin_sub]
    have h1 : sin ((n : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (n : ℕ)
    have h2 : sin ((m : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (m : ℕ)
    simp [h1, h2]
  -- sin((n+m)x) = 0 (integer multiple of π)
  have hnm1_sin : sin (((n : ℝ) + m) * π) = 0 := by
    rw [add_mul, sin_add]
    have h1 : sin ((n : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (n : ℕ)
    have h2 : sin ((m : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (m : ℕ)
    simp [h1, h2]
  -- ∫ cos((n-m)x) = 0
  have int_nm : ∫ x in (-π)..π, cos (((n : ℝ) - m) * x) = 0 := by
    have key : ((n : ℝ) - m) * ∫ x in (-π)..π, cos (((n : ℝ) - m) * x) = 0 := by
      rw [intervalIntegral.mul_integral_comp_mul_left, integral_cos]
      simp [mul_neg, sin_neg, hnm_sin]
    exact (mul_eq_zero.mp key).resolve_left hnm_ne
  -- ∫ cos((n+m)x) = 0  (n+m : ℕ+ so use integral_cos_pnat)
  have int_np : ∫ x in (-π)..π, cos (((n : ℝ) + m) * x) = 0 := by
    have h_cast : ((n : ℝ) + m) = ((n + m : ℕ+) : ℝ) := by push_cast; ring
    rw [h_cast]; exact integral_cos_pnat (n + m)
  -- Product-to-sum: sin(nx)sin(mx) = ½cos((n-m)x) - ½cos((n+m)x)
  have prod_sum : ∀ x : ℝ, sin ((n : ℝ) * x) * sin ((m : ℝ) * x) =
      (1/2) * cos (((n : ℝ) - m) * x) - (1/2) * cos (((n : ℝ) + m) * x) := fun x => by
    have h1 := cos_sub ((n : ℝ) * x) ((m : ℝ) * x)
    have h2 := cos_add ((n : ℝ) * x) ((m : ℝ) * x)
    simp only [← sub_mul, ← add_mul] at h1 h2
    linarith
  simp_rw [prod_sum]
  have hc1 : IntervalIntegrable (fun x => (1/2 : ℝ) * cos (((n : ℝ) - m) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  have hc2 : IntervalIntegrable (fun x => (1/2 : ℝ) * cos (((n : ℝ) + m) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_sub hc1 hc2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      int_nm, int_np]; simp

--∫ _(-π) ^ π cos (nx)sin (mx) dx = 0
lemma integration_sin_cos_zero (n m : ℕ+) (h : n ≠ m) :
    ∫ x in (-π)..π, cos (n * x) * sin (m * x) = 0 := by
  have hnm_ne : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  -- ∫ sin((n-m)x) = 0
  have int_sin_nm : ∫ x in (-π)..π, sin (((n : ℝ) - m) * x) = 0 := by
    have key : ((n : ℝ) - m) * ∫ x in (-π)..π, sin (((n : ℝ) - m) * x) = 0 := by
      rw [intervalIntegral.mul_integral_comp_mul_left, integral_sin]
      simp [mul_neg, cos_neg]
    exact (mul_eq_zero.mp key).resolve_left hnm_ne
  -- ∫ sin((n+m)x) = 0
  have int_sin_np : ∫ x in (-π)..π, sin (((n : ℝ) + m) * x) = 0 := by
    have h_cast : ((n : ℝ) + m) = ((n + m : ℕ+) : ℝ) := by push_cast; ring
    rw [h_cast]; exact integral_sin_pnat (n + m)
  -- Product-to-sum: cos(nx)sin(mx) = ½sin((n+m)x) - ½sin((n-m)x)
  have prod_sum : ∀ x : ℝ, cos ((n : ℝ) * x) * sin ((m : ℝ) * x) =
      (1/2) * sin (((n : ℝ) + m) * x) - (1/2) * sin (((n : ℝ) - m) * x) := fun x => by
    have h1 := sin_add ((n : ℝ) * x) ((m : ℝ) * x)
    have h2 := sin_sub ((n : ℝ) * x) ((m : ℝ) * x)
    simp only [← add_mul, ← sub_mul] at h1 h2
    linarith
  simp_rw [prod_sum]
  have hc1 : IntervalIntegrable (fun x => (1/2 : ℝ) * sin (((n : ℝ) + m) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  have hc2 : IntervalIntegrable (fun x => (1/2 : ℝ) * sin (((n : ℝ) - m) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_sub hc1 hc2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      int_sin_np, int_sin_nm]; simp

--∫ _(-π)^π cos(nx)cos(mx) dx = π for n = m
lemma integration_cos_cos_pi (n m : ℕ+) (h : n = m) :
    ∫ x in (-π)..π, cos (n * x) * cos (m * x) = π := by
  subst h
  -- cos^2(nx) = ½(1 + cos(2nx))
  have half_angle : ∀ x : ℝ,  cos ((n : ℝ) * x) * cos ((n : ℝ) * x) =
      1/2 + (1/2) * cos ((2 * (n : ℝ)) * x) := fun x => by
    have h := cos_sq ((n : ℝ) * x)
    rw [sq, show 2 * ((n : ℝ) * x) = 2 * (n : ℝ) * x from by ring] at h
    linarith
  simp_rw [half_angle]
  -- ∫ cos(2nx) = 0 since 2n : ℕ+
  have int_cos2n : ∫ x in (-π)..π, (1/2 : ℝ) * cos ((2 * (n : ℝ)) * x) = 0 := by
    have h_cast : 2 * (n : ℝ) = ((2 * n : ℕ+) : ℝ) := by push_cast; ring
    rw [intervalIntegral.integral_const_mul, h_cast, integral_cos_pnat]
    simp
  have hc1 : IntervalIntegrable (fun _ => (1/2 : ℝ)) MeasureTheory.volume (-π) π :=
    intervalIntegrable_const
  have hc2 : IntervalIntegrable (fun x => (1/2 : ℝ) * cos ((2 * (n : ℝ)) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add hc1 hc2, intervalIntegral.integral_const, int_cos2n]
  simp only [smul_eq_mul, sub_neg_eq_add, add_zero]
  linarith


--∫ _(-π)^π sin(nx)sin(mx) dx = π for n = m
lemma integration_sin_sin_pi (n m : ℕ+) (h : n = m) :
    ∫ x in (-π)..π, sin (n * x) * sin (m * x) = π := by
  subst h
  -- sin(nx)sin(nx) = ½(1 - cos(2nx))
  have half_angle : ∀ x : ℝ, sin ((n : ℝ) * x) * sin ((n : ℝ) * x) =
      1/2 - (1/2) * cos ((2 * (n : ℝ)) * x) := fun x => by
    have h1 := sin_sq_add_cos_sq ((n : ℝ) * x)
    have h2 := cos_sq ((n : ℝ) * x)
    rw [show 2 * ((n : ℝ) * x) = 2 * (n : ℝ) * x from by ring] at h2
    rw [← sq]
    linarith
  simp_rw [half_angle]
  -- ∫ cos(2nx) = 0 since 2n : ℕ+
  have int_cos2n : ∫ x in (-π)..π, (1/2 : ℝ) * cos ((2 * (n : ℝ)) * x) = 0 := by
    have h_cast : 2 * (n : ℝ) = ((2 * n : ℕ+) : ℝ) := by push_cast; ring
    rw [intervalIntegral.integral_const_mul, h_cast, integral_cos_pnat]
    simp
  have hc1 : IntervalIntegrable (fun _ => (1/2 : ℝ)) MeasureTheory.volume (-π) π :=
    intervalIntegrable_const
  have hc2 : IntervalIntegrable (fun x => (1/2 : ℝ) * cos ((2 * (n : ℝ)) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_sub hc1 hc2, intervalIntegral.integral_const, int_cos2n]
  simp only [smul_eq_mul, sub_neg_eq_add, sub_zero]
  linarith

theorem Parsevals_thm
    -- Integrability of a₀·S(x) over [-π, π]
    (hfS_int : IntervalIntegrable (fun x => a 0 * fourierSum a b x)
      MeasureTheory.volume (-π) π)
    -- Integrability of S(x)² over [-π, π]
    (hfSq_int : IntervalIntegrable (fun x => (fourierSum a b x)^2)
      MeasureTheory.volume (-π) π)
    -- Each Fourier term is integrable
    (hF_int : ∀ n : ℕ+, IntervalIntegrable
      (fun x => a n * cos ((n : ℕ+) * x) + b n * sin ((n : ℕ+) * x))
      MeasureTheory.volume (-π) π)
    -- L¹ summability (for integral/sum interchange in cross term)
    (hF_sum : Summable (fun n : ℕ+ =>
      ∫ x in (-π)..π, ‖a n * cos ((n : ℕ+) * x) + b n * sin ((n : ℕ+) * x)‖))
    -- ∫ S(x)² = π · ∑ₙ (aₙ² + bₙ²)  (orthogonality of the Fourier basis)
    (h_int_sq : ∫ x in (-π)..π, (fourierSum a b x)^2 =
      π * ∑' n : ℕ+, ((a n)^2 + (b n)^2)) :
    (1/π) * ∫ x in (-π)..π, (fourierSeries a b x)^2 =
    (1/2) * (a 0)^2 + ∑' n : ℕ+, ((a n)^2 + (b n)^2) := by
  -- Step 1: pointwise expand f(x)² = (a₀/2)² + a₀·S(x) + S(x)²
  have hpt : ∀ x : ℝ, (fourierSeries a b x)^2 =
      (1/4 : ℝ) * (a 0)^2 + a 0 * fourierSum a b x + (fourierSum a b x)^2 := fun x => by
    simp only [fourierSeries_eq]; ring
  simp_rw [hpt]
  -- Step 2: establish integrability of the sub-expressions
  have h_const_int : IntervalIntegrable (fun _ : ℝ => (1 / 4 : ℝ) * (a 0) ^ 2)
      MeasureTheory.volume (-π) π := intervalIntegrable_const
  have h_sum_int : IntervalIntegrable
      (fun x => (1 / 4 : ℝ) * (a 0) ^ 2 + a 0 * fourierSum a b x)
      MeasureTheory.volume (-π) π := h_const_int.add hfS_int
  -- Step 3: split the integral linearly into three pieces
  rw [intervalIntegral.integral_add h_sum_int hfSq_int,
      intervalIntegral.integral_add h_const_int hfS_int]
  -- Step 3: evaluate each piece
  --   ∫ (1/4)·a₀²  = (1/2)·a₀²·π   (integration_of_const)
  --   ∫ a₀·S(x)    = 0              (orthogonality, integration_of_cos_sin)
  --   ∫ S(x)²      = π·∑ₙ(aₙ²+bₙ²) (h_int_sq)
  rw [integration_of_const, integration_of_cos_sin a b hF_int hF_sum, h_int_sq]
  -- Step 4: arithmetic — (1/π)·((1/2)·a₀²·π + 0 + π·∑…) = (1/2)·a₀² + ∑…
  simp only [add_zero]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  

end
