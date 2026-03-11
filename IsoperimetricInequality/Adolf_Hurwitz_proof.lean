import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring


/-- A simple closed C¹ curve in ℝⁿ, parametrized over [0, L] where L is the arc length. -/
structure SimpleClosedC1Curve (n : ℕ) where
  /-- The parametrization map. -/
  curve : ℝ → EuclideanSpace ℝ (Fin n)
  /-- The period (arc length) of the curve. -/
  length : ℝ
  /-- The period is positive. -/
  length_pos : 0 < length
  /-- The curve is continuous. -/
  continuous : Continuous curve
  /-- The curve is C¹: a derivative exists at every point. -/
  has_deriv : ∀ t : ℝ, ∃ f : EuclideanSpace ℝ (Fin n), HasDerivAt curve f t
  /-- The curve is closed: its endpoints coincide. -/
  closed : curve 0 = curve length
  /-- The curve is L-periodic. -/
  periodic : ∀ t : ℝ, curve (t + length) = curve t
  /-- The curve is simple: injective on the open interval (0, L). -/
  simple : ∀ t s : ℝ, t ∈ Set.Ioo 0 length → s ∈ Set.Ioo 0 length → curve t = curve s → t = s

/-- The arc length of `γ` over the interval `[a, b]`. -/
noncomputable def arcLength {n : ℕ} (γ : SimpleClosedC1Curve n) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ.curve t‖

/-- The total perimeter of `γ`: arc length over one period `[0, L]`. -/
noncomputable def perimeter {n : ℕ} (γ : SimpleClosedC1Curve n) : ℝ :=
  arcLength γ 0 γ.length

/-- A curve is arc-length parametrized if it has unit speed.
    Since the parameter runs over [0, L], this means ‖γ'(t)‖ = 1 everywhere. -/
def IsArcLengthParametrized {n : ℕ} (γ : SimpleClosedC1Curve n) : Prop :=
  ∀ t : ℝ, ‖deriv γ.curve t‖ = 1

/-- The x-coordinate of a planar curve at parameter `s`. -/
noncomputable def xCoord (γ : SimpleClosedC1Curve 2) (s : ℝ) : ℝ :=
  γ.curve s 0

/-- The y-coordinate of a planar curve at parameter `s`. -/
noncomputable def yCoord (γ : SimpleClosedC1Curve 2) (s : ℝ) : ℝ :=
  γ.curve s 1

/-- Reparametrized x-coordinate: f(θ) = x(Lθ/(2π)) for θ ∈ [0, 2π] -/
noncomputable def fParm (γ : SimpleClosedC1Curve 2) (θ : ℝ) : ℝ :=
  xCoord γ (γ.length * θ / (2 * Real.pi))

/-- Reparametrized y-coordinate: g(θ) = y(Lθ/(2π)) for θ ∈ [0, 2π] -/
noncomputable def gParm (γ : SimpleClosedC1Curve 2) (θ : ℝ) : ℝ :=
  yCoord γ (γ.length * θ / (2 * Real.pi))

/-- fParm and gPram are 2π-periodic. -/
lemma fParm_periodic (γ : SimpleClosedC1Curve 2) (θ : ℝ) :
    fParm γ (θ + 2 * Real.pi) = fParm γ θ := by
  simp only [fParm, xCoord]
  have h : γ.length * (θ + 2 * Real.pi) / (2 * Real.pi) =
           γ.length * θ / (2 * Real.pi) + γ.length := by
    field_simp
  rw [h, γ.periodic]

lemma gParm_periodic (γ : SimpleClosedC1Curve 2) (θ : ℝ) : 
    gParm γ (θ + 2 * Real.pi) = gParm γ θ := by
      simp only [gParm, yCoord]
      have h : γ.length * (θ + 2 * Real.pi) / (2 * Real.pi) = 
               γ.length * θ / (2 * Real.pi) + γ.length := by 
                field_simp 
      rw [h, γ.periodic]


/-- The x-coordinate function is differentiable; its derivative at `t` is the 0th component
    of the curve's velocity vector at `t`. -/
lemma xCoord_hasDerivAt (γ : SimpleClosedC1Curve 2) (t : ℝ) :
    HasDerivAt (xCoord γ) ((γ.has_deriv t).choose 0) t := by
  set f := (γ.has_deriv t).choose
  have hf := (γ.has_deriv t).choose_spec
  have hFD : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin 2) => v 0)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0) (γ.curve t) :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (γ.curve t) 0
  have hcomp := HasFDerivAt.comp_hasDerivAt t hFD hf
  convert hcomp using 1

/-- The y-coordinate function is differentiable; its derivative at `t` is the 1st component
    of the curve's velocity vector at `t`. -/
lemma yCoord_hasDerivAt (γ : SimpleClosedC1Curve 2) (t : ℝ) :
    HasDerivAt (yCoord γ) ((γ.has_deriv t).choose 1) t := by
  set f := (γ.has_deriv t).choose
  have hf := (γ.has_deriv t).choose_spec
  have hFD : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin 2) => v 1)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1) (γ.curve t) :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (γ.curve t) 1
  have hcomp := HasFDerivAt.comp_hasDerivAt t hFD hf
  convert hcomp using 1

/-- The derivative of fParm by the chain rule:
    (fParm γ)'(θ) = (xCoord γ)'(γ.length · θ / (2π)) · γ.length / (2π) -/
lemma fParm_deriv (γ : SimpleClosedC1Curve 2) (θ : ℝ) :
    deriv (fParm γ) θ =
      deriv (xCoord γ) (γ.length * θ / (2 * Real.pi)) * (γ.length / (2 * Real.pi)) := by
  have hx := (xCoord_hasDerivAt γ (γ.length * θ / (2 * Real.pi))).differentiableAt
  have hinner : HasDerivAt (fun t => γ.length * t / (2 * Real.pi)) (γ.length / (2 * Real.pi)) θ :=
  by
    have heq : (fun t : ℝ => γ.length * t / (2 * Real.pi)) =
               fun t => t * (γ.length / (2 * Real.pi)) := by
      ext t; rw [mul_comm, mul_div_assoc]
    rw [heq]
    have hid : HasDerivAt (fun t : ℝ => t) 1 θ := hasDerivAt_id θ
    have h := HasDerivAt.mul_const hid (γ.length / (2 * Real.pi))
    simpa using h
  have hg : HasDerivAt (xCoord γ) (deriv (xCoord γ) (γ.length * θ / (2 * Real.pi)))
      (γ.length * θ / (2 * Real.pi)) := hx.hasDerivAt
  have hcomp : HasDerivAt (xCoord γ ∘ fun t => γ.length * t / (2 * Real.pi))
      (deriv (xCoord γ) (γ.length * θ / (2 * Real.pi)) * (γ.length / (2 * Real.pi))) θ :=
    HasDerivAt.comp θ hg hinner
  exact HasDerivAt.deriv hcomp

lemma gParm_deriv (γ : SimpleClosedC1Curve 2) (θ : ℝ) :
    deriv (gParm γ) θ =
      deriv (yCoord γ) (γ.length * θ / (2 * Real.pi)) * (γ.length / (2 * Real.pi)) := by
  have hy := (yCoord_hasDerivAt γ (γ.length * θ / (2 * Real.pi))).differentiableAt
  have hinner :
  HasDerivAt (fun t => γ.length * t / (2 * Real.pi)) (γ.length / (2 * Real.pi)) θ := by
    have heq : (fun t : ℝ => γ.length * t / (2 * Real.pi)) =
               fun t => t * (γ.length / (2 * Real.pi)) := by
      ext t; rw [mul_comm, mul_div_assoc]
    rw [heq]
    have hid : HasDerivAt (fun t : ℝ => t) 1 θ := hasDerivAt_id θ
    have h := HasDerivAt.mul_const hid (γ.length / (2 * Real.pi))
    simpa using h
  have hg : HasDerivAt (yCoord γ) (deriv (yCoord γ) (γ.length * θ / (2 * Real.pi)))
      (γ.length * θ / (2 * Real.pi)) := hy.hasDerivAt
  have hcomp : HasDerivAt (yCoord γ ∘ fun t => γ.length * t / (2 * Real.pi))
      (deriv (yCoord γ) (γ.length * θ / (2 * Real.pi)) * (γ.length / (2 * Real.pi))) θ :=
    HasDerivAt.comp θ hg hinner
  exact HasDerivAt.deriv hcomp

/-- The sum of squared derivatives of the reparametrized coordinates equals the sum of squared
    derivatives of the original coordinates, scaled by `(L / 2π)²`. -/
lemma fParm_gParm_deriv_sq_sum (γ : SimpleClosedC1Curve 2) (θ : ℝ) :
    deriv (fParm γ) θ ^ 2 + deriv (gParm γ) θ ^ 2 =
      (deriv (xCoord γ) (γ.length * θ / (2 * Real.pi)) ^ 2 +
       deriv (yCoord γ) (γ.length * θ / (2 * Real.pi)) ^ 2) *
      (γ.length / (2 * Real.pi)) ^ 2 := by
  rw [fParm_deriv, gParm_deriv]
  ring

