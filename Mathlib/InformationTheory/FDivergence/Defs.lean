/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.InformationTheory.FDivergence.DivFunction
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# f-divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

-/

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ ν : Measure 𝓧} {f g : DivFunction}

section Perspective

noncomputable
def perspective (f : DivFunction) (x u : ℝ≥0∞) : ℝ≥0∞ :=
  if u = 0 then limsup (fun y ↦ y * f (x / y)) (𝓝 0) else u * f (x / u)

end Perspective

section TODO

variable {Θ : Type*} {mΘ : MeasurableSpace Θ} [CountableOrCountablyGenerated Θ 𝓧]

noncomputable
def todo (f : (Θ → ℝ≥0∞) → ℝ≥0∞) (P : Kernel Θ 𝓧) (μ : Measure 𝓧) : ℝ≥0∞ :=
  ∫⁻ x, f (fun i ↦ Kernel.rnDeriv P (Kernel.const Θ μ) i x) ∂μ

end TODO

/-
`f : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞`
`f (a • x) (a • y) = a • f x y`
`f` l.s.c.
`f` convex

Consequences:
`f x y = x * f 1 (y / x)` if `x ≠ 0`
`f x y = y * f (x / y) 1` if `y ≠ 0`
-/

noncomputable
def fDiv' (f : DivFunction) (μ ν : Measure 𝓧) : ℝ≥0∞ :=
  ∫⁻ x, perspective f ((∂μ/∂(μ + ν)) x) ((∂ν/∂(μ + ν)) x) ∂(μ + ν)

/-- f-Divergence of two measures `μ, ν` for the divergence function `f`. -/
noncomputable
def fDiv (f : DivFunction) (μ ν : Measure 𝓧) : ℝ≥0∞ :=
  ∫⁻ x, f ((∂μ/∂ν) x) ∂ν + f.derivAtTop * μ.singularPart ν univ

section Zero

@[simp]
lemma fDiv_zero_divFunction (μ ν : Measure 𝓧) : fDiv 0 μ ν = 0 := by simp [fDiv]

@[simp]
lemma fDiv_zero_measure_left (ν : Measure 𝓧) : fDiv f 0 ν = f 0 * ν .univ := by
  have : (fun x ↦ f ((∂0/∂ν) x)) =ᵐ[ν] fun _ ↦ f 0 := by
    filter_upwards [ν.rnDeriv_zero] with x hx using by simp [hx]
  simp [fDiv, lintegral_congr_ae this]

@[simp]
lemma fDiv_zero_measure_right (μ : Measure 𝓧) : fDiv f μ 0 = f.derivAtTop * μ .univ := by
  simp [fDiv]

@[simp]
lemma fDiv_self (μ : Measure 𝓧) [SigmaFinite μ] : fDiv f μ μ = 0 := by
  have : (fun x ↦ f (μ.rnDeriv μ x)) =ᵐ[μ] 0 := by
    filter_upwards [μ.rnDeriv_self] with x hx using by simp [hx, f.one]
  simp [fDiv, lintegral_congr_ae this]

end Zero

section Congr

lemma fDiv_congr (hfg : f =ᵐ[ν.map (∂μ/∂ν)] g) (hfg' : f =ᶠ[atTop] g) :
    fDiv f μ ν = fDiv g μ ν := by
  have h : (fun a ↦ f ((∂μ/∂ν) a)) =ᶠ[ae ν] fun a ↦ g ((∂μ/∂ν) a) :=
    ae_of_ae_map (μ.measurable_rnDeriv ν).aemeasurable hfg
  rw [fDiv, DivFunction.derivAtTop_congr hfg', lintegral_congr_ae h]
  rfl

lemma fDiv_congr_measure {μ' ν' : Measure 𝓨}
    (h_eq : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∫⁻ x, f ((∂μ'/∂ν') x) ∂ν')
    (h_sing : μ.singularPart ν univ = μ'.singularPart ν' univ) :
    fDiv f μ ν = fDiv f μ' ν' := by
  rw [fDiv, fDiv, h_sing, h_eq]

end Congr

lemma fDiv_smul (c : ℝ≥0) (μ ν : Measure 𝓧) : fDiv (c • f) μ ν = c * fDiv f μ ν := by
  simp only [fDiv, DivFunction.smul_apply, DivFunction.derivAtTop_smul]
  rw [lintegral_const_mul _ DivFunction.measurable_comp_rnDeriv, mul_add, ← mul_assoc]

lemma fDiv_add (μ ν : Measure 𝓧) : fDiv (f + g) μ ν = fDiv f μ ν + fDiv g μ ν := by
  simp only [fDiv, DivFunction.add_apply, DivFunction.derivAtTop_add]
  rw [lintegral_add_left DivFunction.measurable_comp_rnDeriv]
  ring

end ProbabilityTheory
