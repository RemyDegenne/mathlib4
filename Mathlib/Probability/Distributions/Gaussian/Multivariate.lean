/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Moments.CovarianceBilinDual
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order

/-!
# Multivariate Gaussian distributions

## Main definitions

## Main statements

-/

@[expose] public section

open EMetric Set
open scoped ENNReal NNReal MatrixOrder


open MeasureTheory ProbabilityTheory Filter Matrix NormedSpace WithLp
open scoped ENNReal NNReal Topology RealInnerProductSpace

section InnerProductSpace

open scoped InnerProductSpace

theorem OrthonormalBasis.norm_sq_eq_sum_sq_inner_right {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ⟪b i, x⟫_ℝ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right]
  simp

theorem OrthonormalBasis.norm_sq_eq_sum_sq_inner_left {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ⟪x, b i⟫_ℝ ^ 2 := by
  simp_rw [b.norm_sq_eq_sum_sq_inner_right, real_inner_comm]

theorem EuclideanSpace.real_norm_sq_eq {n : Type*} [Fintype n] (x : EuclideanSpace ℝ n) :
    ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  congr with i; simp

theorem OrthonormalBasis.norm_dual {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) (L : StrongDual ℝ E) :
    ‖L‖ ^ 2 = ∑ i, L (b i) ^ 2 := by
  have := Module.Basis.finiteDimensional_of_finite b.toBasis
  simp_rw [← (InnerProductSpace.toDual ℝ E).symm.norm_map, b.norm_sq_eq_sum_sq_inner_left,
    InnerProductSpace.toDual_symm_apply]

@[simp]
lemma LinearIsometryEquiv.coe_coe_eq_coe {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F) :
    ⇑f.toLinearIsometry.toContinuousLinearMap = ⇑f := rfl

end InnerProductSpace

namespace ProbabilityTheory

section iIndepFun

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)}

variable [∀ i, IsProbabilityMeasure (μ i)]

lemma variance_pi {X : Π i, Ω i → ℝ} (h : ∀ i, MemLp (X i) 2 (μ i)) :
    Var[∑ i, fun ω ↦ X i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i] := by
  rw [IndepFun.variance_sum]
  · congr with i
    change Var[(X i) ∘ (fun ω ↦ ω i); Measure.pi μ] = _
    rw [← variance_map, (measurePreserving_eval _ i).map_eq]
    · rw [(measurePreserving_eval _ i).map_eq]
      exact (h i).aestronglyMeasurable.aemeasurable
    · exact Measurable.aemeasurable (by fun_prop)
  · exact fun i _ ↦ (h i).comp_measurePreserving (measurePreserving_eval _ i)
  · exact fun i _ j _ hij ↦
      (iIndepFun_pi fun i ↦ (h i).aestronglyMeasurable.aemeasurable).indepFun hij

end iIndepFun

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  {d : ℕ}

variable (E) in
/-- Standard Gaussian distribution on `E`. -/
noncomputable
def stdGaussian : Measure E :=
  (Measure.pi (fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 1)).map
    (fun x ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i)

variable [BorelSpace E]

instance isProbabilityMeasure_stdGaussian : IsProbabilityMeasure (stdGaussian E) :=
    Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

@[simp]
lemma integral_id_stdGaussian : ∫ x, x ∂(stdGaussian E) = 0 := by
  rw [stdGaussian, integral_map _ (by fun_prop)]
  swap; · exact (Finset.measurable_sum _ (by fun_prop)).aemeasurable
  rw [integral_finset_sum]
  swap
  · refine fun i _ ↦ Integrable.smul_const ?_ _
    convert integrable_comp_eval (i := i) (f := id) ?_
    · infer_instance
    · rw [← memLp_one_iff_integrable]
      exact memLp_id_gaussianReal 1
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have : (∫ (a : Fin (Module.finrank ℝ E) → ℝ), a i ∂Measure.pi fun x ↦ gaussianReal 0 1)
      = ∫ x, x ∂gaussianReal 0 1 := by
    convert integral_comp_eval (i := i) aestronglyMeasurable_id
    all_goals infer_instance
  simp [integral_smul_const, this]

lemma isCentered_stdGaussian : ∀ L : StrongDual ℝ E, (stdGaussian E)[L] = 0 := by
  intro L
  rw [L.integral_comp_id_comm, integral_id_stdGaussian, map_zero]
  rw [stdGaussian, integrable_map_measure]
  · rw [Function.id_comp]
    exact integrable_finset_sum _ fun i _ ↦ Integrable.smul_const
      (integrable_comp_eval (f := id) IsGaussian.integrable_id) _
  · exact aestronglyMeasurable_id
  · exact Measurable.aemeasurable (by fun_prop)

lemma variance_dual_stdGaussian (L : StrongDual ℝ E) : Var[L; stdGaussian E] = ‖L‖ ^ 2 := by
  rw [stdGaussian, variance_map]
  · have : L ∘ (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i) =
        ∑ i, (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ L (stdOrthonormalBasis ℝ E i) * x i) := by
      ext x; simp [mul_comm]
    rw [this, variance_pi]
    · change ∑ i, Var[fun x ↦ _ * (id x); gaussianReal 0 1] = _
      simp_rw [variance_const_mul, variance_id_gaussianReal, (stdOrthonormalBasis ℝ E).norm_dual]
      simp
    · exact fun i ↦ IsGaussian.memLp_two_id.const_mul _
  · exact L.continuous.aemeasurable
  · exact Measurable.aemeasurable (by fun_prop)

lemma charFun_stdGaussian (t : E) : charFun (stdGaussian E) t = Complex.exp (- ‖t‖ ^ 2 / 2) := by
  rw [charFun_apply, stdGaussian, integral_map]
  · simp_rw [sum_inner, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum,
      integral_fintype_prod_eq_prod
        (f := fun i x ↦ Complex.exp (⟪x • stdOrthonormalBasis ℝ E i, t⟫ * Complex.I)),
      real_inner_smul_left, mul_comm _ (⟪_, _⟫), Complex.ofReal_mul, ← charFun_apply_real,
      charFun_gaussianReal]
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one, one_mul,
      zero_sub]
    simp_rw [← Complex.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, ← Complex.ofReal_pow,
      ← Complex.ofReal_sum, ← (stdOrthonormalBasis ℝ E).norm_sq_eq_sum_sq_inner_right, neg_div]
  · exact Measurable.aemeasurable (by fun_prop)
  · exact Measurable.aestronglyMeasurable (by fun_prop)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma isSymm_inner : LinearMap.IsSymm (innerₗ E) where
  eq x y := by simp only [innerₗ_apply_apply, RingHom.id_apply]; rw [real_inner_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma isNonneg_inner : LinearMap.IsNonneg (innerₗ E) where
  nonneg x := by simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma isPosSemidef_inner : LinearMap.IsPosSemidef (innerₗ E) where
  isSymm := isSymm_inner
  isNonneg := isNonneg_inner

instance isGaussian_stdGaussian : IsGaussian (stdGaussian E) := by
  refine isGaussian_iff_gaussian_charFun.2 ⟨0, innerSL ℝ, ?_, ?_⟩
  · rw [LinearMap.BilinForm.isPosSemidef_iff]
    exact isPosSemidef_inner
  · simp only [charFun_stdGaussian, neg_div, inner_zero_right, Complex.ofReal_zero, zero_mul,
      zero_sub]
    congr!
    rw [innerSL_apply_apply]
    simp

lemma charFunDual_stdGaussian (L : StrongDual ℝ E) :
    charFunDual (stdGaussian E) L = Complex.exp (- ‖L‖ ^ 2 / 2) := by
  rw [IsGaussian.charFunDual_eq, integral_complex_ofReal, isCentered_stdGaussian,
    variance_dual_stdGaussian]
  simp [neg_div]

lemma covarianceBilin_stdGaussian :
    covarianceBilin (stdGaussian E) = innerSL ℝ := by
  refine gaussian_charFun_congr 0 _ ?_ (fun t ↦ ?_) |>.2.symm
  · rw [LinearMap.BilinForm.isPosSemidef_iff]
    exact isPosSemidef_inner
  · simp only [charFun_stdGaussian, neg_div, inner_zero_right, Complex.ofReal_zero, zero_mul,
      zero_sub]
    congr!
    rw [innerSL_apply_apply]
    simp

lemma stdGaussian_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] (f : E ≃ₗᵢ[ℝ] F) :
    haveI := f.finiteDimensional; (stdGaussian E).map f = stdGaussian F := by
  have := f.finiteDimensional
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [← f.coe_coe_eq_coe, charFunDual_map, charFunDual_stdGaussian,
    L.opNorm_comp_linearIsometryEquiv]

lemma pi_eq_stdGaussian {n : Type*} [Fintype n] :
    (Measure.pi (fun _ ↦ gaussianReal 0 1)).map (toLp 2) = stdGaussian (EuclideanSpace ℝ n) := by
  -- This instance is not found automatically, probably a defeq issue between
  -- `n → ℝ` and `EuclideanSpace ℝ n`.
  have : IsFiniteMeasure (Measure.pi fun _ : n ↦ gaussianReal 0 1) := inferInstance
  apply Measure.ext_of_charFun (E := EuclideanSpace ℝ n)
  ext t
  simp_rw [charFun_stdGaussian, charFun_pi, charFun_gaussianReal, ← Complex.exp_sum,
    ← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq]
  simp [Finset.sum_div, neg_div]

lemma stdGaussian_eq_pi_map_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    stdGaussian E = (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map
      (fun x ↦ ∑ i, x i • b i) := by
  have : (fun (x : ι → ℝ) ↦ ∑ i, x i • b i) =
      ⇑((EuclideanSpace.basisFun ι ℝ).equiv b (Equiv.refl ι)) ∘ (toLp 2) := by
    simp_rw [← b.equiv_apply_euclideanSpace]
    rfl
  rw [this, ← Measure.map_map, pi_eq_stdGaussian, stdGaussian_map]
  all_goals fun_prop

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multivariate Gaussian measure on `EuclideanSpace ℝ ι` with mean `μ` and covariance
matrix `S`. -/
noncomputable
def multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  (stdGaussian (EuclideanSpace ℝ ι)).map (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)

@[simp]
lemma multivariateGaussian_zero_one :
    multivariateGaussian 0 (1 : Matrix ι ι ℝ) = stdGaussian (EuclideanSpace ℝ ι) := by
  simp [multivariateGaussian]

variable {μ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} {hS : S.PosSemidef}

instance isGaussian_multivariateGaussian : IsGaussian (multivariateGaussian μ S) := by
  have h : (fun x ↦ μ + x) ∘ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))) =
    (fun x ↦ μ + (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) x) := rfl
  simp only [multivariateGaussian]
  rw [← h, ← Measure.map_map (measurable_const_add μ) (by measurability)]
  infer_instance

@[simp]
lemma integral_id_multivariateGaussian : ∫ x, x ∂(multivariateGaussian μ S) = μ := by
  rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop),
    integral_add (integrable_const _), integral_const]
  · simp [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id]
  · exact IsGaussian.integrable_id.comp_measurable (by fun_prop)

end ProbabilityTheory
