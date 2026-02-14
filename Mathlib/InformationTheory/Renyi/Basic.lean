/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Rényi divergence


## Main definitions

*  `InformationTheory.renyiDiv`

## Main statements

*

-/

@[expose] public section

open Real MeasureTheory Set

open scoped ENNReal

namespace InformationTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ ν : Measure 𝓧}

noncomputable
def renyiDiv (α : ℝ≥0∞) (μ ν : Measure 𝓧) : ℝ≥0∞ :=
  if α = 1 then klDiv μ ν
  else if α = 0 then sorry
  else if α = ∞ then sorry
  else if α < 1 then (1 - α)⁻¹ * ⨅ (ξ : Measure 𝓧) (_ : IsProbabilityMeasure ξ),
    (α * klDiv ξ μ + (1 - α) * klDiv ξ ν)
  else sorry

end InformationTheory
