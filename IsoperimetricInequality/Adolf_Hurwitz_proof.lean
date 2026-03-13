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

/-- gParm and fParm are 2π-periodic. -/
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

/-- The derivative of gParm by the chain rule:
    (gParm γ)'(θ) = (yCoord γ)'(γ.length · θ / (2π)) · γ.length / (2π) -/
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

/-- Under arc-length parametrization, the sum of squares of coordinate derivatives equals 1,
    because the speed ‖γ'(t)‖ = 1 and the two components square-sum to the squared norm. -/
lemma due_to_arc_length_parametrization (γ : SimpleClosedC1Curve 2)
    (h : IsArcLengthParametrized γ) (θ : ℝ) :
    deriv (xCoord γ) (γ.length * θ / (2 * Real.pi)) ^ 2 +
    deriv (yCoord γ) (γ.length * θ / (2 * Real.pi)) ^ 2 = 1 := by
  set t := γ.length * θ / (2 * Real.pi)
  have hxd := (xCoord_hasDerivAt γ t).deriv
  have hyd := (yCoord_hasDerivAt γ t).deriv
  have hchoose : deriv γ.curve t = (γ.has_deriv t).choose :=
    (γ.has_deriv t).choose_spec.deriv
  have hnorm : ‖(γ.has_deriv t).choose‖ = 1 := by rw [← hchoose]; exact h t
  rw [hxd, hyd]
  have hsq : (γ.has_deriv t).choose 0 ^ 2 + (γ.has_deriv t).choose 1 ^ 2 =
      ‖(γ.has_deriv t).choose‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  rw [hsq, hnorm, one_pow]

/-- Under arc-length parametrization, the sum of squared derivatives of the reparametrized
    coordinates is the constant `(L / 2π)²`. -/
lemma fParm_gParm_deriv_eq_sum_const (γ : SimpleClosedC1Curve 2)
    (h : IsArcLengthParametrized γ) (θ : ℝ) :
    deriv (fParm γ) θ ^ 2 + deriv (gParm γ) θ ^ 2 = (γ.length / (2 * Real.pi)) ^ 2 := by
  rw [fParm_gParm_deriv_sq_sum]
  rw [due_to_arc_length_parametrization γ h]
  ring


/-- The signed area enclosed by `γ` between parameters `a` and `b`,
    computed via the shoelace formula: 1/2 ∫ (x · y' - y · x') dt. -/
noncomputable def area (γ : SimpleClosedC1Curve 2)
  (a b : ℝ) : ℝ := 
  (1/2)*∫ t in a..b, (γ.curve t 0 * deriv γ.curve t 1 - γ.curve t 1 * deriv γ.curve t 0)


/-- x'(s) = (2π/L) f'(θ), where θ = 2π·s/L -/
lemma xPrime_s (γ : SimpleClosedC1Curve 2) (s : ℝ) :
    deriv (xCoord γ) s =
      (2 * Real.pi) / γ.length * deriv (fParm γ) (2 * Real.pi * s / γ.length) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hL : (0 : ℝ) < γ.length := γ.length_pos
  have h := fParm_deriv γ (2 * Real.pi * s / γ.length)
  have hsimp : γ.length * (2 * Real.pi * s / γ.length) / (2 * Real.pi) = s := by
    field_simp
  rw [hsimp] at h
  rw [h]
  field_simp [hL.ne', hpi.ne']

/-- y'(s) = (2π/L) g'(θ), where θ = 2π·s/L -/ 
lemma yPrime_s (γ : SimpleClosedC1Curve 2) (s : ℝ) : 
    deriv (yCoord γ) s = 
      (2 * Real.pi) / γ.length * deriv (gParm γ) (2 * Real.pi * s / γ.length) := by 
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity 
    have hL : (0 : ℝ) < γ.length := γ.length_pos 
    have h := gParm_deriv γ (2 * Real.pi * s / γ.length)
    have hsimp : γ.length * (2 * Real.pi * s / γ.length) / (2 * Real.pi) = s := by 
      field_simp
    rw [hsimp] at h 
    rw [h]
    field_simp [hL.ne', hpi.ne']

/-- area = (1/2)∫₀²π f(θ)g'(θ) - g(θ)f'(θ) dθ -/
lemma area_parametrized (γ : SimpleClosedC1Curve 2) (s : ℝ) :
    area γ 0 γ.length =
      (1 / 2) * ∫ t in (0 : ℝ)..(2 * Real.pi),
        fParm γ t * deriv (gParm γ) t - gParm γ t * deriv (fParm γ) t := by
  unfold area 
  have hL : (0 : ℝ) < γ.length := γ.length_pos 
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have key : (1/2) * ∫ s in (0 : ℝ)..γ.length, 
    (xCoord γ s * deriv (yCoord γ) s - yCoord γ s * deriv (xCoord γ) s) = 
    (1/2) * ∫ t in (0 : ℝ)..(2*Real.pi), 
    fParm γ t * deriv (gParm γ) t - gParm γ t * deriv (fParm γ) t := by 
      have xeq : ∀ s, xCoord γ s = fParm γ (2 * Real.pi * s / γ.length) := fun s ↦ by
        simp only [fParm, xCoord]
        have heq : γ.length * (2 * Real.pi * s / γ.length) / (2 * Real.pi) = s := by
         field_simp [hL.ne']
        rw [heq]
      have yeq : ∀ s, yCoord γ s = gParm γ (2 * Real.pi * s / γ.length) := fun s ↦ by 
        simp only [gParm, yCoord]
        have heq : γ.length * (2 * Real.pi * s / γ.length) / (2 * Real.pi) = s := by 
          field_simp [hL.ne']
        rw [heq]
      simp_rw [xeq, yeq, xPrime_s, yPrime_s] 

      have hπL_ne : γ.length ≠ 0 := hL.ne'
      have h2π_ne : (2 : ℝ) * Real.pi ≠ 0 := hpi.ne'
      have hscale : (2 * Real.pi / γ.length) ≠ 0 := div_ne_zero h2π_ne hπL_ne
      -- factor (2π/L) out of each integrand term
      have factor : ∀ s : ℝ,
          fParm γ (2 * Real.pi * s / γ.length) *
            (2 * Real.pi / γ.length * deriv (gParm γ) (2 * Real.pi * s / γ.length)) -
          gParm γ (2 * Real.pi * s / γ.length) *
            (2 * Real.pi / γ.length * deriv (fParm γ) (2 * Real.pi * s / γ.length)) =
          (2 * Real.pi / γ.length) *
            (fParm γ (2 * Real.pi / γ.length * s) * deriv (gParm γ) (2 * Real.pi / γ.length * s) -
             gParm γ (2 * Real.pi / γ.length * s) * deriv (fParm γ) (2 * Real.pi / γ.length * s)) :=
        fun s => by rw [show 2 * Real.pi * s / γ.length = 
        2 * Real.pi / γ.length * s from by ring]; ring
      congr 1
      simp_rw [factor, intervalIntegral.integral_const_mul]
      -- use smul_integral_comp_mul_left with named args to pin down f exactly
      have key3 := intervalIntegral.smul_integral_comp_mul_left
        (f := fun t : ℝ => fParm γ t * deriv (gParm γ) t - gParm γ t * deriv (fParm γ) t)
        (a := (0 : ℝ)) (b := γ.length) (2 * Real.pi / γ.length)
      rw [mul_zero, show (2 * Real.pi / γ.length) * γ.length = 2 * Real.pi from by
        field_simp] at key3
      exact key3
  -- connect the outer goal (uses .ofLp and deriv γ.curve) to key (uses xCoord/yCoord)
  have hxd : ∀ t : ℝ, deriv (xCoord γ) t = (deriv γ.curve t) 0 := fun t => by
    rw [(xCoord_hasDerivAt γ t).deriv, (γ.has_deriv t).choose_spec.deriv]
  have hyd : ∀ t : ℝ, deriv (yCoord γ) t = (deriv γ.curve t) 1 := fun t => by
    rw [(yCoord_hasDerivAt γ t).deriv, (γ.has_deriv t).choose_spec.deriv]
  have eq1 : (1/2) * ∫ t in (0:ℝ)..γ.length,
      ((γ.curve t).ofLp 0 * (deriv γ.curve t).ofLp 1 -
       (γ.curve t).ofLp 1 * (deriv γ.curve t).ofLp 0) =
    (1/2) * ∫ s in (0:ℝ)..γ.length,
      (xCoord γ s * deriv (yCoord γ) s - yCoord γ s * deriv (xCoord γ) s) := by
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only [xCoord, yCoord, hxd, hyd]
  rw [eq1]
  exact key
