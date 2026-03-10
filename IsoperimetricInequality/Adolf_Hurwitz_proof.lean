import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


/-- A simple closed C¹ curve in ℝⁿ, parametrized over [0, 1]. -/
structure SimpleClosedC1Curve (n : ℕ) where
  /-- The parametrization map. -/
  curve : ℝ → EuclideanSpace ℝ (Fin n)
  /-- The curve is continuous. -/
  continuous : Continuous curve
  /-- The curve is C¹: a derivative exists at every point. -/
  has_deriv : ∀ t : ℝ, ∃ f : EuclideanSpace ℝ (Fin n), HasDerivAt curve f t
  /-- The curve is closed: its endpoints coincide. -/
  closed : curve 0 = curve 1
  /-- The curve is 1-periodic. -/
  periodic : ∀ t : ℝ, curve (t + 1) = curve t
  /-- The curve is simple: injective on the open interval (0, 1). -/
  simple : ∀ t s : ℝ, t ∈ Set.Ioo 0 1 → s ∈ Set.Ioo 0 1 → curve t = curve s → t = s

/-- The arc length of `γ` over the interval `[a, b]`. -/
noncomputable def arcLength {n : ℕ} (γ : SimpleClosedC1Curve n) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ.curve t‖

/-- The total perimeter of `γ`: arc length over one period `[0, 1]`. -/
noncomputable def perimeter {n : ℕ} (γ : SimpleClosedC1Curve n) : ℝ :=
  arcLength γ 0 1

/-- A curve is arc-length parametrized if its speed is constant and equal to its perimeter.
    This means γ traverses equal arc lengths in equal parameter intervals. -/
def IsArcLengthParametrized {n : ℕ} (γ : SimpleClosedC1Curve n) : Prop :=
  ∀ t : ℝ, ‖deriv γ.curve t‖ = perimeter γ

/-- The x-coordinate of a planar curve at parameter `s`. -/
noncomputable def xCoord (γ : SimpleClosedC1Curve 2) (s : ℝ) : ℝ :=
  γ.curve s 0

/-- The y-coordinate of a planar curve at parameter `s`. -/
noncomputable def yCoord (γ : SimpleClosedC1Curve 2) (s : ℝ) : ℝ :=
  γ.curve s 1
