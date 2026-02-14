/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Mutual information


## Main definitions

* `InformationTheory.mutualInfo` : The mutual information of a measure `ρ` on `𝓧 × 𝓨` is the
  Kullback-Leibler divergence between `ρ` and the product of its marginals.

## Main statements

*

-/

@[expose] public section

open Real MeasureTheory Set

open scoped ENNReal

namespace InformationTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}

/-- The mutual information of a measure `ρ` on `𝓧 × 𝓨` is the Kullback-Leibler divergence between
`ρ` and the product of its marginals. -/
noncomputable
def mutualInfo (ρ : Measure (𝓧 × 𝓨)) : ℝ≥0∞ := klDiv ρ (ρ.fst.prod ρ.snd)

-- todo: do we need to restrict the infimum? or assume something on ρ?
lemma mutualInfo_eq_iInf_klDiv (ρ : Measure (𝓧 × 𝓨)) :
    mutualInfo ρ = ⨅ (ν : Measure 𝓨), klDiv ρ (ρ.fst.prod ν) := by
  sorry

end InformationTheory
