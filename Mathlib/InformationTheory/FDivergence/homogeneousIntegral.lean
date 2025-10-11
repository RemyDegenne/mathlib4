/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib

/-!
# HomogeneousIntegral

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}

lemma toReal_rnDeriv_comp [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (κ : Kernel α β) [IsFiniteKernel κ] :
    (fun ab ↦ ((∂(κ ∘ₘ μ)/∂(κ ∘ₘ ν)) ab.2).toReal)
      =ᵐ[ν ⊗ₘ κ] (ν ⊗ₘ κ)[fun ab ↦ ((∂μ/∂ν) ab.1).toReal | mβ.comap Prod.snd] := by
  sorry -- proved in TestingLowerBounds

end ProbabilityTheory

namespace InformationTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {μ ν : Measure 𝓧}

/-- A function which is homogeneous of degree 1 in the pair of arguments and convex.
TODO: we might want to add lsc. -/
structure SymmFDivFun where
  toFun : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞
  mul' : ∀ {a b c : ℝ≥0∞}, toFun (c * a) (c * b) = c * toFun a b
  convex' : ConvexOn ℝ≥0 Set.univ (fun p : ℝ≥0∞ × ℝ≥0∞ ↦ toFun p.1 p.2)

-- example : `f a b = a * log(a / b)` is a `SymmFDivFun`

namespace SymmFDivFun

attribute [coe] toFun

instance instCoeFun : CoeFun SymmFDivFun fun _ => ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ := ⟨toFun⟩

initialize_simps_projections SymmFDivFun (toFun → apply)

@[ext] lemma ext {f g : SymmFDivFun} (h : ∀ x y, f.toFun x y = g.toFun x y) : f = g :=
  (SymmFDivFun.mk.injEq ..).mpr (funext fun x ↦ funext (h x))

lemma mul (f : SymmFDivFun) (a b c : ℝ≥0∞) : f (c * a) (c * b) = c * f a b := f.mul'

lemma convex (f : SymmFDivFun) : ConvexOn ℝ≥0 Set.univ (fun p : ℝ≥0∞ × ℝ≥0∞ ↦ f p.1 p.2) :=
  f.convex'

lemma eq_mul_one_left (f : SymmFDivFun) (a b : ℝ≥0∞) (h_pos : 0 < a) (h_fin : a ≠ ∞) :
    f a b = a * f 1 (b / a) := by
  calc f a b = f (a * 1) (a * (b / a)) := by rw [mul_one, ENNReal.mul_div_cancel h_pos.ne' h_fin]
  _ = a * f 1 (b / a) := by rw [f.mul]

lemma eq_mul_one_right (f : SymmFDivFun) (a b : ℝ≥0∞) (h_pos : 0 < b) (h_fin : b ≠ ∞) :
    f a b = b * f (a / b) 1 := by
  calc f a b = f (b * (a / b)) (b * 1) := by rw [mul_one, ENNReal.mul_div_cancel h_pos.ne' h_fin]
  _ = b * f (a / b) 1 := by rw [f.mul]

end SymmFDivFun

noncomputable
def todoIntegral (f : SymmFDivFun) (μ ν : Measure 𝓧) : ℝ≥0∞ :=
  ∫⁻ x, f ((∂μ/∂(μ + ν)) x) ((∂ν/∂(μ + ν)) x) ∂(μ + ν)

lemma toIntegral_comp_le (f : SymmFDivFun)
    (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (κ : Kernel 𝓧 𝓨) [IsFiniteKernel κ] :
    todoIntegral f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ todoIntegral f μ ν := by
  rw [todoIntegral, todoIntegral]
  calc ∫⁻ y, f ((∂κ ∘ₘ μ/∂(κ ∘ₘ μ + κ ∘ₘ ν)) y) ((∂κ ∘ₘ ν/∂(κ ∘ₘ μ + κ ∘ₘ ν)) y) ∂(κ ∘ₘ μ + κ ∘ₘ ν)
  _ = ∫⁻ y, f ((∂κ ∘ₘ μ/∂(κ ∘ₘ (μ + ν))) y) ((∂κ ∘ₘ ν/∂(κ ∘ₘ (μ + ν))) y) ∂(κ ∘ₘ (μ + ν)) := by
    sorry
  _ = ∫⁻ xy, f ((∂κ ∘ₘ μ/∂(κ ∘ₘ (μ + ν))) xy.2) ((∂κ ∘ₘ ν/∂(κ ∘ₘ (μ + ν))) xy.2)
      ∂((μ + ν) ⊗ₘ κ) := by
    sorry
  _ = ∫⁻ xy, f (.ofReal (((μ + ν) ⊗ₘ κ)[fun ab ↦ ((∂μ/∂(μ + ν)) ab.1).toReal|m𝓨.comap Prod.snd] xy))
      (.ofReal (((μ + ν) ⊗ₘ κ)[fun ab ↦ ((∂ν/∂(μ + ν)) ab.1).toReal|m𝓨.comap Prod.snd] xy))
      ∂((μ + ν) ⊗ₘ κ) := by
    -- todo: whould benefit from an ENNReal `condExp`
    have h1 := toReal_rnDeriv_comp (μ := μ) (ν := μ + ν)
      (Measure.AbsolutelyContinuous.rfl.add_right _) κ
    have h2 := toReal_rnDeriv_comp (μ := ν) (ν := μ + ν) ?_ κ
    swap; · rw [add_comm]; exact Measure.AbsolutelyContinuous.rfl.add_right _
    refine lintegral_congr_ae ?_
    -- need finiteness on top of h1 and h2
    sorry
  _ ≤ ∫⁻ x, f ((∂μ/∂(μ + ν)) x) ((∂ν/∂(μ + ν)) x) ∂(μ + ν) := sorry

end InformationTheory
