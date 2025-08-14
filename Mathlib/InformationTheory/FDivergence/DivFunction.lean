/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Probability.Moments.Variance

/-!
# Divergence functions for f-divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

instance : OrderedSMul ℝ≥0 ℝ≥0∞ := by
  constructor
  · intro a b u hab hu
    simp_rw [ENNReal.smul_def, smul_eq_mul]
    rw [ENNReal.mul_lt_mul_left]
    · exact hab
    · simp [hu.ne']
    · exact ENNReal.coe_ne_top
  · intro a b u h_lt h_pos
    simp_rw [ENNReal.smul_def, smul_eq_mul] at h_lt
    rw [ENNReal.mul_lt_mul_left] at h_lt
    · exact h_lt
    · simp [h_pos.ne']
    · exact ENNReal.coe_ne_top

lemma ENNReal.tendsto_of_monotone {ι : Type*} [Preorder ι] {f : ι → ℝ≥0∞} (hf : Monotone f) :
    ∃ y, Tendsto f atTop (𝓝 y) :=
  ⟨_, tendsto_atTop_ciSup hf (OrderTop.bddAbove _)⟩

lemma ENNReal.tendsto_of_monotoneOn {ι : Type*} [SemilatticeSup ι] [Nonempty ι] {x : ι}
    {f : ι → ℝ≥0∞} (hf : MonotoneOn f (Ici x)) :
    ∃ y, Tendsto f atTop (𝓝 y) := by
  classical
  suffices ∃ y, Tendsto (fun z ↦ if x ≤ z then f z else f x) atTop (𝓝 y) by
    obtain ⟨y, hy⟩ := this
    refine ⟨y, ?_⟩
    refine (tendsto_congr' ?_).mp hy
    rw [EventuallyEq, eventually_atTop]
    exact ⟨x, fun z hz ↦ if_pos hz⟩
  refine ENNReal.tendsto_of_monotone (fun y z hyz ↦ ?_)
  split_ifs with hxy hxz hxz
  · exact hf hxy hxz hyz
  · exact absurd (hxy.trans hyz) hxz
  · exact hf le_rfl hxz hxz
  · exact le_rfl

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

structure DivFunction where
  toFun : ℝ≥0∞ → ℝ≥0∞
  one : toFun 1 = 0
  convexOn' : ConvexOn ℝ≥0 univ toFun
  continuous' : Continuous toFun

namespace DivFunction

attribute [coe] toFun

instance instCoeFun : CoeFun DivFunction fun _ ↦ ℝ≥0∞ → ℝ≥0∞ := ⟨toFun⟩

initialize_simps_projections DivFunction (toFun → apply)

@[ext] lemma ext {f g : DivFunction} (h : ∀ x, f x = g x) : f = g :=
  (DivFunction.mk.injEq ..).mpr (funext h)

section Def
variable (f : DivFunction)

@[simp] lemma apply_one : f 1 = 0 := f.one

lemma convexOn : ConvexOn ℝ≥0 univ f := f.convexOn'

lemma continuous : Continuous f := f.continuous'

lemma measurable : Measurable f := f.continuous.measurable

end Def

variable {f g : DivFunction}

lemma measurable_comp_rnDeriv : Measurable (fun x ↦ f (μ.rnDeriv ν x)) :=
  f.continuous.measurable.comp (Measure.measurable_rnDeriv _ _)

section Module

protected def zero : DivFunction where
  toFun := 0
  one := rfl
  convexOn' := convexOn_const _ convex_univ
  continuous' := continuous_const

protected noncomputable def add (f g : DivFunction) : DivFunction where
  toFun := fun x ↦ f x + g x
  one := by simp
  convexOn' := f.convexOn.add g.convexOn
  continuous' := f.continuous.add g.continuous

noncomputable
instance : AddZeroClass DivFunction where
  add := DivFunction.add
  zero := DivFunction.zero
  zero_add _ := ext fun _ ↦ zero_add _
  add_zero _ := ext fun _ ↦ add_zero _

@[simp] lemma zero_apply (x : ℝ≥0∞) : (0 : DivFunction) x = 0 := rfl

@[simp] lemma add_apply (f g : DivFunction) (x : ℝ≥0∞) : (f + g) x = f x + g x := rfl

noncomputable
instance : AddCommMonoid DivFunction where
  nsmul n f := nsmulRec n f
  add_assoc _ _ _ := ext fun _ ↦ add_assoc _ _ _
  add_comm _ _ := ext fun _ ↦ add_comm _ _
  __ := DivFunction.instAddZeroClass

noncomputable
instance : SMul ℝ≥0 DivFunction where
  smul c f := {
    toFun := fun x ↦ c * f x
    one := by simp
    convexOn' := f.convexOn.smul c.2
    continuous' := (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp f.continuous}

@[simp] lemma smul_apply (c : ℝ≥0) (f : DivFunction) (x : ℝ≥0∞) : (c • f) x = c * f x := rfl

noncomputable
instance : Module ℝ≥0 DivFunction where
  one_smul _ := ext fun _ ↦ one_mul _
  mul_smul _ _ _ := ext fun _ ↦ by simp [mul_assoc]
  smul_zero _ := ext fun _ ↦ mul_zero _
  smul_add _ _ _ := ext fun _ ↦ mul_add _ _ _
  add_smul _ _ _ := ext fun _ ↦ by simp [add_mul]
  zero_smul _ := ext fun _ ↦ zero_mul _

end Module

section EffectiveDomain

lemma eventually_ne_top_nhds_one (f : DivFunction) : ∀ᶠ a in 𝓝 1, f a ≠ ∞ := by
  suffices ∀ᶠ a in 𝓝 1, f a < 1 by
    filter_upwards [this] with x hx using ne_top_of_lt hx
  refine Tendsto.eventually_lt_const ?_ (f.continuous.tendsto 1)
  simp

/-- Lower bound of the effective domain of `f`. -/
noncomputable def xmin (f : DivFunction) : ℝ≥0∞ := sInf {x | f x ≠ ∞}
/-- Upper bound of the effective domain of `f`. -/
noncomputable def xmax (f : DivFunction) : ℝ≥0∞ := sSup {x | f x ≠ ∞}

lemma xmin_lt_one : f.xmin < 1 := by
  rw [xmin, sInf_lt_iff]
  suffices ∀ᶠ a in 𝓝 1, f a ≠ ⊤ by
    obtain ⟨a, ha_lt, ha⟩ := this.exists_lt
    exact ⟨a, ha, ha_lt⟩
  suffices ∀ᶠ a in 𝓝 1, f a < 1 by
    filter_upwards [this] with x hx using ne_top_of_lt hx
  refine Tendsto.eventually_lt_const ?_ (f.continuous.tendsto 1)
  simp

lemma xmin_lt_top : f.xmin < ∞ := lt_top_of_lt xmin_lt_one

lemma xmin_ne_top : f.xmin ≠ ∞ := xmin_lt_top.ne

lemma one_lt_xmax : 1 < f.xmax := by
  rw [xmax, lt_sSup_iff]
  obtain ⟨a, ha_gt, ha⟩ := f.eventually_ne_top_nhds_one.exists_gt
  exact ⟨a, ha, ha_gt⟩

lemma xmax_pos : 0 < f.xmax := zero_lt_one.trans one_lt_xmax

lemma xmin_lt_xmax : f.xmin < f.xmax := xmin_lt_one.trans one_lt_xmax

lemma eq_top_of_lt_xmin {x : ℝ≥0∞} (hx_lt : x < f.xmin) : f x = ∞ := by
  rw [xmin] at hx_lt
  by_contra h_eq
  exact not_le_of_gt hx_lt (sInf_le h_eq)

lemma eq_top_of_xmax_lt {x : ℝ≥0∞} (hx_gt : f.xmax < x) : f x = ∞ := by
  rw [xmax] at hx_gt
  by_contra h_eq
  exact not_le_of_gt hx_gt (le_sSup h_eq)

lemma lt_top_of_mem_Ioo {x : ℝ≥0∞} (hx : x ∈ Ioo f.xmin f.xmax) : f x < ∞ := by
  rw [mem_Ioo, xmin, sInf_lt_iff, xmax, lt_sSup_iff] at hx
  obtain ⟨a, ha, hax⟩ := hx.1
  obtain ⟨b, hb, hxb⟩ := hx.2
  calc f x
  _ ≤ max (f a) (f b) := by
    -- todo: should be ConvexOn.le_max_of_mem_Icc but that does not work with ℝ≥0∞
    have h := f.convexOn.2 (mem_univ a) (mem_univ b)
    obtain ⟨u, v, huv, rfl⟩ : ∃ (u : ℝ≥0) (v : ℝ≥0), u + v = 1 ∧ u • a + v • b = x := by
      have h_mem : x ∈ Icc a b := ⟨hax.le, hxb.le⟩
      have h_cvx : Convex ℝ≥0 (Icc a b) := convex_Icc _ _
      -- refine Convex.exists_mem_add_smul_eq
      sorry
    refine (h (zero_le u) (zero_le v) huv).trans ?_
    calc u • f a + v • f b
    _ ≤ u • max (f a) (f b) + v • max (f a) (f b) := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = (u + v) • max (f a) (f b) := by module
    _ = max (f a) (f b) := by simp [huv]
  _ < ∞ := by finiteness

lemma apply_xmin_eq_top (h : 0 < f.xmin) : f f.xmin = ∞ := by
  have h_tendsto : Tendsto f (𝓝[<] f.xmin) (𝓝 ∞) := by
    refine (tendsto_congr' ?_).mp tendsto_const_nhds
    exact eventually_nhdsWithin_of_forall fun x hx ↦ (eq_top_of_lt_xmin hx).symm
  have h_ne_bot : (𝓝[<] f.xmin).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Iio']
    · simp
    · exact ⟨0, h⟩
  refine tendsto_nhds_unique ?_ h_tendsto
  refine tendsto_nhdsWithin_of_tendsto_nhds ?_
  exact f.continuous.tendsto _

lemma apply_xmax_eq_top (h : f.xmax ≠ ∞) : f f.xmax = ∞ := by
  have h_tendsto : Tendsto f (𝓝[>] f.xmax) (𝓝 ∞) := by
    refine (tendsto_congr' ?_).mp tendsto_const_nhds
    exact eventually_nhdsWithin_of_forall fun x hx ↦ (eq_top_of_xmax_lt hx).symm
  have h_ne_bot : (𝓝[>] f.xmax).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ioi']
    · simp
    · exact ⟨⊤, h.lt_top⟩
  refine tendsto_nhds_unique ?_ h_tendsto
  refine tendsto_nhdsWithin_of_tendsto_nhds ?_
  exact f.continuous.tendsto _

end EffectiveDomain

section Real

protected noncomputable def real (f : DivFunction) : ℝ → ℝ := fun x ↦ (f (.ofReal x)).toReal

end Real

section DerivAtTop

lemma exists_tendsto_atTop (f : DivFunction) :
    ∃ l, Tendsto (fun x ↦ f x / (x - 1)) atTop (𝓝 l) := by
  refine ENNReal.tendsto_of_monotoneOn (x := 1) ?_
  sorry

/-- Limit of the derivative of the divergence function at infinity. -/
noncomputable
def derivAtTop (f : DivFunction) : ℝ≥0∞ := limsup (fun x ↦ f x / x) atTop

lemma tendsto_derivAtTop (f : DivFunction) :
    Tendsto (fun x ↦ f x / x) atTop (𝓝 f.derivAtTop) := by
  have h := exists_tendsto_atTop f
  sorry

@[simp]
lemma derivAtTop_zero : (0 : DivFunction).derivAtTop = 0 := by
  simp [derivAtTop, limsup_const, ENNReal.zero_div]

lemma derivAtTop_congr (h : f =ᶠ[atTop] g) : f.derivAtTop = g.derivAtTop := by
  refine limsup_congr ?_
  filter_upwards [h] with x hx
  rw [hx]

@[simp]
lemma derivAtTop_eq_zero_iff : f.derivAtTop = 0 ↔ ∀ x, 1 ≤ x → f x = 0 := by
  sorry

lemma derivAtTop_smul (c : ℝ≥0) (f : DivFunction) :
    (c • f).derivAtTop = c * f.derivAtTop := by
  by_cases hc : c = ∞
  · simp only [hc]
    by_cases h : f.derivAtTop = 0
    · simp only [h, mul_zero, derivAtTop_eq_zero_iff, smul_apply, mul_eq_zero, ENNReal.coe_eq_zero]
      simp only [derivAtTop_eq_zero_iff] at h
      exact fun x hx ↦ .inr (h x hx)
    simp only [ne_eq, h, not_false_eq_true, ENNReal.top_mul]
    simp only [derivAtTop_eq_zero_iff, not_forall] at h
    obtain ⟨x, hx, h⟩ := h
    sorry
  · simp only [derivAtTop, smul_apply, mul_div_assoc]
    rw [ENNReal.limsup_const_mul_of_ne_top hc]

lemma derivAtTop_add : (f + g).derivAtTop = f.derivAtTop + g.derivAtTop := by
  simp only [derivAtTop, add_apply, ENNReal.add_div]
  sorry

end DerivAtTop

end DivFunction

end ProbabilityTheory
