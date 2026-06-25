/-
Copyright (c) 2024 Yaël Dillies, Kin Yau James Wong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kin Yau James Wong, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Disintegration of measures and kernels

This file defines predicates for a kernel to "disintegrate" a measure or a kernel. This kernel is
also called the "conditional kernel" of the measure or kernel.

A measure `ρ : Measure (α × Ω)` is disintegrated by a kernel `ρCond : Kernel α Ω` if
`ρ.fst ⊗ₘ ρCond = ρ`.

A kernel `ρ : Kernel α (β × Ω)` is disintegrated by a kernel `κCond : Kernel (α × β) Ω` if
`κ.fst ⊗ₖ κCond = κ`.

## Main definitions

* `MeasureTheory.Measure.IsCondKernel ρ ρCond`: Predicate for the kernel `ρCond` to disintegrate the
  measure `ρ`.
* `ProbabilityTheory.Kernel.IsCondKernel κ κCond`: Predicate for the kernel `κ Cond` to disintegrate
  the kernel `κ`.

Further, if `κ` is an s-finite kernel from a countable `α` such that each measure `κ a` is
disintegrated by some kernel, then `κ` itself is disintegrated by a kernel, namely
`ProbabilityTheory.Kernel.condKernelCountable`.

## See also

`Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean` for a **construction** of
disintegrating kernels.
-/

@[expose] public section

open MeasureTheory Set Filter MeasurableSpace ProbabilityTheory
open scoped ENNReal MeasureTheory Topology

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mΩ : MeasurableSpace Ω}

/-!
### Disintegration of measures

This section provides a predicate for a kernel to disintegrate a measure.
-/

namespace MeasureTheory.Measure
variable {ρ : Measure (α × Ω)} {ρCond : Kernel α Ω}

/-- A kernel `ρCond` is a conditional kernel for a measure `ρ` if it disintegrates it in the sense
that `ρ.fst ⊗ₘ ρCond = ρ`. -/
structure IsCondKernel (ρ : Measure (α × Ω)) (ρCond : Kernel α Ω) : Prop where
  disintegrate : ρ.fst ⊗ₘ ρCond = ρ

lemma disintegrate (h_cond : ρ.IsCondKernel ρCond) : ρ.fst ⊗ₘ ρCond = ρ := h_cond.disintegrate

lemma IsCondKernel.isSFiniteKernel (h_cond : ρ.IsCondKernel ρCond) (hρ : ρ ≠ 0) :
    IsSFiniteKernel ρCond := by
  contrapose hρ; rwa [← h_cond.disintegrate, Measure.compProd_of_not_isSFiniteKernel]

class HasCondKernel (ρ : Measure (α × Ω)) : Prop where
  exists_condKernel : ∃ ρCond, ρ.IsCondKernel ρCond ∧ IsMarkovKernel ρCond

noncomputable
def condKernel (ρ : Measure (α × Ω)) [hρ : HasCondKernel ρ] : Kernel α Ω :=
  hρ.exists_condKernel.choose

lemma isCondKernel_condKernel (ρ : Measure (α × Ω)) [hρ : HasCondKernel ρ] :
    ρ.IsCondKernel (ρ.condKernel) := hρ.exists_condKernel.choose_spec.1

instance (ρ : Measure (α × Ω)) [hρ : HasCondKernel ρ] : IsMarkovKernel (ρ.condKernel) :=
  hρ.exists_condKernel.choose_spec.2

instance (μ : Measure α) [SFinite μ] (κ : Kernel α Ω) [IsMarkovKernel κ] :
    HasCondKernel (μ ⊗ₘ κ) where
  exists_condKernel := ⟨κ, ⟨by simp [Measure.fst_compProd]⟩, inferInstance⟩

variable [IsFiniteMeasure ρ]

/-- A conditional kernel is almost everywhere a probability measure. -/
lemma IsCondKernel.isProbabilityMeasure_ae (h_cond : ρ.IsCondKernel ρCond) :
    ∀ᵐ a ∂ρ.fst, IsProbabilityMeasure (ρCond a) := by
  have h := h_cond.disintegrate
  by_cases hρ0 : ρ = 0
  · simp [hρ0]
  have h_sfin : IsSFiniteKernel ρCond := IsCondKernel.isSFiniteKernel h_cond hρ0
  suffices ∀ᵐ a ∂ρ.fst, ρCond a Set.univ = 1 by
    convert! this with b
    exact ⟨fun _ ↦ measure_univ, fun h ↦ ⟨h⟩⟩
  suffices (∀ᵐ a ∂ρ.fst, ρCond a Set.univ ≤ 1)
      ∧ (∀ᵐ a ∂ρ.fst, 1 ≤ ρCond a Set.univ) by
    filter_upwards [this.1, this.2] with b h1 h2 using le_antisymm h1 h2
  have h_eq s (hs : MeasurableSet s) :
      ∫⁻ b, s.indicator (fun b ↦ ρCond b Set.univ) b ∂ρ.fst = ρ.fst s := by
    conv_rhs => rw [← h]
    rw [fst_compProd_apply _ _ hs]
  have h_meas : Measurable fun b ↦ ρCond b Set.univ := ρCond.measurable_coe MeasurableSet.univ
  constructor
  · rw [ae_le_const_iff_forall_gt_measure_zero]
    intro r hr
    let s := {b | r ≤ ρCond b Set.univ}
    have hs : MeasurableSet s := h_meas measurableSet_Ici
    have h_2_le : s.indicator (fun _ ↦ r) ≤ s.indicator (fun b ↦ (ρCond b) Set.univ) := by
      intro b
      by_cases hbs : b ∈ s
      · simpa [hbs]
      · simp [hbs]
    have : ∫⁻ b, s.indicator (fun _ ↦ r) b ∂ρ.fst ≤ ρ.fst s :=
      (lintegral_mono h_2_le).trans_eq (h_eq s hs)
    rw [lintegral_indicator_const hs] at this
    contrapose! this with h_ne_zero
    conv_lhs => rw [← one_mul (ρ.fst s)]
    gcongr
    finiteness
  · rw [ae_const_le_iff_forall_lt_measure_zero]
    intro r hr
    let s := {b | ρCond b Set.univ ≤ r}
    have hs : MeasurableSet s := h_meas measurableSet_Iic
    have h_2_le : s.indicator (fun b ↦ (ρCond b) Set.univ) ≤ s.indicator (fun _ ↦ r) := by
      intro b
      by_cases hbs : b ∈ s
      · simpa [hbs]
      · simp [hbs]
    have : ρ.fst s ≤ ∫⁻ b, s.indicator (fun _ ↦ r) b ∂ρ.fst :=
      (h_eq s hs).symm.trans_le (lintegral_mono h_2_le)
    rw [lintegral_indicator_const hs] at this
    contrapose! this with h_ne_zero
    conv_rhs => rw [← one_mul (ρ.fst s)]
    gcongr
    finiteness

lemma IsCondKernel.exists_isMarkovKernel [Nonempty Ω] (h_cond : ρ.IsCondKernel ρCond) :
    ∃ ρCond' : Kernel α Ω, ρ.IsCondKernel ρCond' ∧ IsMarkovKernel ρCond' := by
  obtain ⟨ω₀⟩ : Nonempty Ω := inferInstance
  by_cases hρ0 : ρ = 0
  · refine ⟨Kernel.const _ (Measure.dirac ω₀), ?_, inferInstance⟩
    constructor
    simp [hρ0]
  have : IsSFiniteKernel ρCond := IsCondKernel.isSFiniteKernel h_cond hρ0
  have h_ae := IsCondKernel.isProbabilityMeasure_ae h_cond
  have h_meas : Measurable fun b ↦ ρCond b Set.univ := ρCond.measurable_coe MeasurableSet.univ
  let s := {a | IsProbabilityMeasure (ρCond a)}
  have hs_eq : s = {a | ρCond a Set.univ = 1} := by
    unfold s
    ext a
    simp only [mem_setOf_eq]
    exact ⟨fun h ↦ by simp, fun h ↦ ⟨h⟩⟩
  have hs : MeasurableSet s := by rw [hs_eq]; exact h_meas (measurableSet_singleton _)
  classical
  let ρCond' : Kernel α Ω :=
    ⟨s.piecewise ρCond (fun _ ↦ Measure.dirac ω₀),
      Measurable.piecewise hs (by fun_prop) (by fun_prop)⟩
  have : IsMarkovKernel ρCond' := by
    unfold ρCond'
    refine ⟨fun a ↦ ?_⟩
    by_cases ha : a ∈ s
    · simp only [Kernel.coe_mk, ha, piecewise_eq_of_mem]
      simpa [s] using ha
    · simp only [Kernel.coe_mk, ha, not_false_eq_true, piecewise_eq_of_notMem]
      infer_instance
  have h_ae_eq : ρCond =ᵐ[ρ.fst] ρCond' := by
    filter_upwards [h_ae] with a ha
    simp only [Kernel.coe_mk, ρCond']
    rw [Set.piecewise_eq_of_mem s]
    simpa [s]
  refine ⟨ρCond', ?_, inferInstance⟩
  · constructor
    conv_rhs => rw [← h_cond.disintegrate]
    exact Measure.compProd_congr h_ae_eq.symm

lemma IsCondKernel.hasCondKernel [Nonempty Ω] (h_cond : ρ.IsCondKernel ρCond) : HasCondKernel ρ :=
  ⟨h_cond.exists_isMarkovKernel⟩

/-- Auxiliary lemma for `IsCondKernel.apply_of_ne_zero`. -/
private lemma IsCondKernel.apply_of_ne_zero_of_measurableSet [MeasurableSingletonClass α]
    (h_cond : ρ.IsCondKernel ρCond) {x : α}
    (hx : ρ.fst {x} ≠ 0) {s : Set Ω} (hs : MeasurableSet s) :
    ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  have := h_cond.isSFiniteKernel (by rintro rfl; simp at hx)
  nth_rewrite 2 [← h_cond.disintegrate]
  rw [Measure.compProd_apply (measurableSet_prod.mpr (Or.inl ⟨measurableSet_singleton x, hs⟩))]
  classical
  have (a : _) : ρCond a (Prod.mk a ⁻¹' {x} ×ˢ s) = ({x} : Set α).indicator (ρCond · s) a := by
    obtain rfl | hax := eq_or_ne a x
    · simp only [singleton_prod, mem_singleton_iff, indicator_of_mem]
      congr with y
      simp
    · simp only [singleton_prod, mem_singleton_iff, hax, not_false_eq_true, indicator_of_notMem]
      have : Prod.mk a ⁻¹' Prod.mk x '' s = ∅ := by ext y; simp [Ne.symm hax]
      simp only [this, measure_empty]
  simp_rw [this]
  rw [MeasureTheory.lintegral_indicator (measurableSet_singleton x)]
  simp only [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hx (measure_ne_top _ _), one_mul]

/-- If the singleton `{x}` has non-zero mass for `ρ.fst`, then for all `s : Set Ω`,
`ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s)` . -/
lemma IsCondKernel.apply_of_ne_zero [MeasurableSingletonClass α] (h_cond : ρ.IsCondKernel ρCond)
    {x : α} (hx : ρ.fst {x} ≠ 0) (s : Set Ω) : ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  have : ρCond x s = ((ρ.fst {x})⁻¹ • ρ).comap (fun (y : Ω) ↦ (x, y)) s := by
    congr 2 with s hs
    simp [IsCondKernel.apply_of_ne_zero_of_measurableSet h_cond hx hs,
      (measurableEmbedding_prodMk_left x).comap_apply, Set.singleton_prod]
  simp [this, (measurableEmbedding_prodMk_left x).comap_apply, Set.singleton_prod]

lemma IsCondKernel.isProbabilityMeasure [MeasurableSingletonClass α] (h_cond : ρ.IsCondKernel ρCond)
    {a : α} (ha : ρ.fst {a} ≠ 0) :
    IsProbabilityMeasure (ρCond a) := by
  constructor
  rw [IsCondKernel.apply_of_ne_zero h_cond ha, prod_univ, ← Measure.fst_apply
    (measurableSet_singleton _), ENNReal.inv_mul_cancel ha (measure_ne_top _ _)]

lemma IsCondKernel.isMarkovKernel [MeasurableSingletonClass α] (h_cond : ρ.IsCondKernel ρCond)
    (hρ : ∀ a, ρ.fst {a} ≠ 0) :
    IsMarkovKernel ρCond := ⟨fun _ ↦ h_cond.isProbabilityMeasure (hρ _)⟩

end MeasureTheory.Measure

/-!
### Disintegration of kernels

This section provides a predicate for a kernel to disintegrate a kernel. It also proves that if `κ`
is an s-finite kernel from a countable `α` such that each measure `κ a` is disintegrated by some
kernel, then `κ` itself is disintegrated by a kernel, namely
`ProbabilityTheory.Kernel.condKernelCountable`.
-/

namespace ProbabilityTheory.Kernel
variable {κ : Kernel α (β × Ω)} {κCond : Kernel (α × β) Ω}

/-! #### Predicate for a kernel to disintegrate a kernel -/

/-- A kernel `κCond` is a conditional kernel for a kernel `κ` if it disintegrates it in the sense
that `κ.fst ⊗ₖ κCond = κ`. -/
structure IsCondKernel (κ : Kernel α (β × Ω)) (κCond : Kernel (α × β) Ω) : Prop where
  protected disintegrate : κ.fst ⊗ₖ κCond = κ

lemma instIsCondKernel_zero (κCond : Kernel (α × β) Ω) : IsCondKernel 0 κCond where
  disintegrate := by simp

lemma disintegrate (h_cond : κ.IsCondKernel κCond) : κ.fst ⊗ₖ κCond = κ :=
  h_cond.disintegrate

class HasCondKernel (κ : Kernel α (β × Ω)) : Prop where
  exists_condKernel : ∃ κCond, κ.IsCondKernel κCond ∧ IsMarkovKernel κCond

noncomputable
def condKernel (κ : Kernel α (β × Ω)) [hκ : HasCondKernel κ] : Kernel (α × β) Ω :=
  hκ.exists_condKernel.choose

lemma isCondKernel_condKernel (κ : Kernel α (β × Ω)) [hκ : HasCondKernel κ] :
    κ.IsCondKernel (κ.condKernel) := hκ.exists_condKernel.choose_spec.1

instance (κ : Kernel α (β × Ω)) [hκ : HasCondKernel κ] : IsMarkovKernel (κ.condKernel) :=
  hκ.exists_condKernel.choose_spec.2

lemma isCondKernel_sectR (h_cond : κ.IsCondKernel κCond) (a : α) :
    (κ a).IsCondKernel (κCond.sectR a) := by
  constructor
  have h := disintegrate h_cond
  by_cases h_sfin1 : IsSFiniteKernel κ.fst
  swap; · rw [Kernel.compProd_of_not_isSFiniteKernel_left _ _ h_sfin1] at h; simp [h.symm]
  by_cases h_sfin2 : IsSFiniteKernel κCond
  swap; · rw [Kernel.compProd_of_not_isSFiniteKernel_right _ _ h_sfin2] at h; simp [h.symm]
  conv_rhs => rw [← disintegrate h_cond]
  rw [compProd_apply_eq_compProd_sectR, Kernel.fst_apply, Measure.fst]

instance [HasCondKernel κ] (a : α) : (κ a).HasCondKernel :=
  ⟨κ.condKernel.sectR a, isCondKernel_sectR (isCondKernel_condKernel κ) a, inferInstance⟩

lemma hasCondKernel_const (ρ : Measure (β × Ω)) [ρ.HasCondKernel] :
    (Kernel.const α ρ).HasCondKernel := by
  sorry

/-- A conditional kernel is almost everywhere a probability measure. -/
lemma IsCondKernel.isProbabilityMeasure_ae [IsFiniteKernel κ.fst] (h_cond : κ.IsCondKernel κCond)
    (a : α) :
    ∀ᵐ b ∂(κ.fst a), IsProbabilityMeasure (κCond (a, b)) := by
  have h_ae := (isCondKernel_sectR h_cond a).isProbabilityMeasure_ae
  have h_fst : κ.fst a = (κ a).fst := by simp [Kernel.fst_apply, Measure.fst]
  rw [h_fst]
  filter_upwards [h_ae] with b hb using hb

lemma IsCondKernel.exists_isMarkovKernel [Nonempty Ω] (h_cond : κ.IsCondKernel κCond) :
    ∃ κCond' : Kernel (α × β) Ω, κ.IsCondKernel κCond' ∧ IsMarkovKernel κCond' := by
  sorry

lemma IsCondKernel.hasCondKernel [Nonempty Ω] (h_cond : κ.IsCondKernel κCond) : HasCondKernel κ :=
  ⟨h_cond.exists_isMarkovKernel⟩

/-! #### Existence of a disintegrating kernel in a countable space -/

section Countable
variable [Countable α] (κCond : α → Kernel β Ω)

/-- Auxiliary definition for `ProbabilityTheory.Kernel.condKernel`.

A conditional kernel for `κ : Kernel α (β × Ω)` where `α` is countable and `Ω` is a measurable
space. -/
noncomputable def condKernelCountable (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y) :
    Kernel (α × β) Ω where
  toFun p := κCond p.1 p.2
  measurable' := by
    refine measurable_from_prod_countable_right' (fun a ↦ (κCond a).measurable) fun x y hx hy ↦ ?_
    simpa using DFunLike.congr (h_atom _ _ hy) rfl

lemma condKernelCountable_apply (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y)
    (p : α × β) : condKernelCountable κCond h_atom p = κCond p.1 p.2 := rfl

instance condKernelCountable.instIsMarkovKernel [∀ a, IsMarkovKernel (κCond a)]
     (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y) :
    IsMarkovKernel (condKernelCountable κCond h_atom) where
  isProbabilityMeasure p := (‹∀ a, IsMarkovKernel (κCond a)› p.1).isProbabilityMeasure p.2

lemma isCondKernel_condKernelCountable [∀ a, IsMarkovKernel (κCond a)]
    (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y) (κ : Kernel α (β × Ω))
    [IsSFiniteKernel κ] (h_cond : ∀ a, (κ a).IsCondKernel (κCond a)) :
    κ.IsCondKernel (condKernelCountable κCond h_atom) := by
  constructor
  ext a s hs
  conv_rhs => rw [← (h_cond a).disintegrate]
  simp_rw [compProd_apply hs, condKernelCountable_apply, Measure.compProd_apply hs]
  congr

end Countable
end ProbabilityTheory.Kernel
