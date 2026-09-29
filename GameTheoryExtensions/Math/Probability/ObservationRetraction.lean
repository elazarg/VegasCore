/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.ConditionalNoise

/-! # Conditioning an observation-local expansion and retraction

An expansion can restore hidden aliases of a source state. If its observation
law depends only on the source observation, conditioning the expanded state
and then retracting gives the original source posterior. Only supported
states and a positive observed fiber enter the argument.
-/

noncomputable section

namespace PMF

open GameTheory.Math.Probability

variable {Source Native SourceInfo NativeInfo : Type*}

/-- Conditioning on an observation of a readout commutes with retaining that
readout. The positivity premise avoids the arbitrary empty-fiber fallback. -/
theorem map_conditional_readout {A B Info : Type*} (law : PMF A)
    (read : A → B) (observe : B → Info) (observed : Info)
    (present : observed ∈ (law.map (observe ∘ read)).support) :
    (fiberConditional law (observe ∘ read) observed).map read =
      fiberConditional (law.map read) observe observed := by
  classical
  obtain ⟨point, supported, equal⟩ := support_map .. ▸ present
  have originalMeets : ∃ a ∈ (observe ∘ read) ⁻¹' {observed}, a ∈ law.support :=
    ⟨point, equal, supported⟩
  have imageMeets : ∃ b ∈ observe ⁻¹' {observed}, b ∈ (law.map read).support := by
    refine ⟨read point, equal, ?_⟩
    rw [support_map]
    exact ⟨point, supported, rfl⟩
  rw [fiberConditional, dite_eq_left originalMeets, fiberConditional, dite_eq_left imageMeets]
  have massMap (μ : PMF A) (b : B) : (μ.map read) b = μ.toOuterMeasure (read ⁻¹' {b}) := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have normalizer : (law.map read).toOuterMeasure (observe ⁻¹' {observed}) =
      law.toOuterMeasure ((observe ∘ read) ⁻¹' {observed}) := by
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  ext value
  rw [massMap, toOuterMeasure_filter_apply, PMF.filter_apply, ← PMF.toOuterMeasure_apply,
    normalizer, div_eq_mul_inv]
  by_cases same : observe value = observed
  · have inside : value ∈ observe ⁻¹' {observed} := same
    have fiber : read ⁻¹' {value} ∩ (observe ∘ read) ⁻¹' {observed} = read ⁻¹' {value} := by
      ext point
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
      exact ⟨And.left, fun equal => ⟨equal, equal ▸ same⟩⟩
    rw [Set.indicator_of_mem inside, massMap, fiber]
  · have outside : value ∉ observe ⁻¹' {observed} := same
    have empty : read ⁻¹' {value} ∩ (observe ∘ read) ⁻¹' {observed} = ∅ := by
      ext point
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and, Function.comp_apply]
      intro projected matching
      exact same (projected ▸ matching)
    rw [Set.indicator_of_notMem outside, empty, MeasureTheory.measure_empty, zero_mul]

/-- Retraction after conditioning recovers the source posterior whenever the
expansion's observation law is constant on each supported source information
fiber. The expanded observation may contain additional random distinctions.
No independence between the source state and its prior is assumed. -/
theorem conditional_retraction (prior : PMF Source)
    (kernel : Source → PMF Native) (retract : Native → Source)
    (sourceObserve : Source → SourceInfo) (nativeObserve : Native → NativeInfo)
    (project : NativeInfo → SourceInfo)
    (commutes : ∀ a, sourceObserve (retract a) = project (nativeObserve a))
    (restores : ∀ s ∈ prior.support, ∀ a ∈ (kernel s).support, retract a = s)
    (locality : ∀ s ∈ prior.support, ∀ t ∈ prior.support,
      sourceObserve s = sourceObserve t →
        (kernel s).map nativeObserve = (kernel t).map nativeObserve)
    (observed : NativeInfo) (present : observed ∈ ((prior.bind kernel).map nativeObserve).support) :
    ((fiberConditional (prior.bind kernel) nativeObserve observed).map retract) =
      fiberConditional prior sourceObserve (project observed) := by
  classical
  let expanded := prior.bind kernel
  let read := fun a => (retract a, nativeObserve a)
  let information := fun pair : Source × NativeInfo => (sourceObserve pair.1, pair.2)
  let joint := prior.bind fun s =>
    ((kernel s).map nativeObserve).map fun signal => (s, signal)
  have jointLaw : expanded.map read = joint := by
    rw [map_bind]
    apply bind_congr_on_support _
    intro s supported
    rw [map_comp]
    apply map_congr_on_support _
    intro a member
    exact Prod.ext (restores s supported a member) rfl
  obtain ⟨a, aSupport, aView⟩ := support_map .. ▸ present
  obtain ⟨s, sSupport, member⟩ := Set.mem_iUnion₂.mp (support_bind .. ▸ aSupport)
  have sourceView : sourceObserve s = project observed := by
    rw [← restores s sSupport a member, commutes, aView]
  have noisePresent : ∃ s ∈ prior.support,
      sourceObserve s = project observed ∧ observed ∈ ((kernel s).map nativeObserve).support := by
    refine ⟨s, sSupport, sourceView, ?_⟩
    rw [support_map]
    exact ⟨a, member, aView⟩
  have augmentedPresent : (project observed, observed) ∈
      (expanded.map (information ∘ read)).support := by
    rw [support_map]
    refine ⟨a, aSupport, ?_⟩
    exact Prod.ext ((commutes a).trans (congrArg project aView)) aView
  have sameFiber : (information ∘ read) ⁻¹' {(project observed, observed)} =
      nativeObserve ⁻¹' {observed} := by
    ext value
    change (sourceObserve (retract value), nativeObserve value) =
      (project observed, observed) ↔ nativeObserve value = observed
    rw [commutes]
    exact ⟨fun equal => (Prod.mk.inj equal).2,
      fun equal => Prod.ext (congrArg project equal) equal⟩
  have conditional : fiberConditional expanded (information ∘ read) (project observed, observed) =
      fiberConditional expanded nativeObserve observed := by
    unfold fiberConditional
    rw [sameFiber]
  have projected := map_conditional_readout expanded read information
    (project observed, observed) augmentedPresent
  rw [conditional, jointLaw] at projected
  have final := conditional_kernel_of_fiber prior sourceObserve
    (fun s => (kernel s).map nativeObserve) locality (project observed) observed noisePresent
  change ((fiberConditional joint information (project observed,
      observed)).map Prod.fst) = _ at final
  rw [← projected, map_comp] at final
  exact final

/-- If a transition determines its new observation from the old state,
conditioning can be performed before that transition. All transition laws
remain unchanged; only the prior is conditioned. -/
theorem conditional_bind_of_observation {Info : Type*} (prior : PMF Source)
    (kernel : Source → PMF Native) (before : Source → Info) (after : Native → Info)
    (determines : ∀ s ∈ prior.support, ∀ a ∈ (kernel s).support, after a = before s)
    (observed : Info) (present : observed ∈ (prior.map before).support) :
    fiberConditional (prior.bind kernel) after observed =
      (fiberConditional prior before observed).bind kernel := by
  classical
  have observations : (prior.bind kernel).map after = prior.map before := by
    rw [map_bind, ← PMF.bind_pure_comp]
    apply bind_congr_on_support _
    intro s supported
    calc
      (kernel s).map after = (kernel s).map (fun _ => before s) := by
        apply map_congr_on_support _
        exact determines s supported
      _ = PMF.pure (before s) := PMF.map_const _ _
  obtain ⟨s, sSupported, sView⟩ := (PMF.mem_support_map_iff _ _ _).mp present
  have oldMeets : ∃ s ∈ before ⁻¹' {observed}, s ∈ prior.support :=
    ⟨s, sView, sSupported⟩
  have newPresent : observed ∈ ((prior.bind kernel).map after).support := by
    rwa [observations]
  obtain ⟨a, aSupported, aView⟩ := (PMF.mem_support_map_iff _ _ _).mp newPresent
  have newMeets : ∃ a ∈ after ⁻¹' {observed}, a ∈ (prior.bind kernel).support :=
    ⟨a, aView, aSupported⟩
  have mass : (prior.bind kernel).toOuterMeasure (after ⁻¹' {observed}) =
      prior.toOuterMeasure (before ⁻¹' {observed}) := by
    rw [← PMF.toOuterMeasure_map_apply, observations, PMF.toOuterMeasure_map_apply]
  rw [fiberConditional, dite_eq_left newMeets, fiberConditional, dite_eq_left oldMeets]
  ext value
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, mass, PMF.bind_apply]
  by_cases matched : after value = observed
  · rw [Set.indicator_of_mem (show value ∈ after ⁻¹' {observed} from matched), PMF.bind_apply,
      ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro s
    rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply]
    by_cases supported : s ∈ prior.support
    · by_cases possible : value ∈ (kernel s).support
      · have view : s ∈ before ⁻¹' {observed} :=
          (determines s supported value possible).symm.trans matched
        rw [Set.indicator_of_mem view]
        ring
      · rw [(PMF.apply_eq_zero_iff _ _).mpr possible]
        simp
    · have zero := (PMF.apply_eq_zero_iff _ _).mpr supported
      simp [Set.indicator, zero]
  · rw [Set.indicator_of_notMem (show value ∉ after ⁻¹' {observed} from matched), zero_mul]
    symm
    apply ENNReal.tsum_eq_zero.mpr
    intro s
    rw [PMF.filter_apply]
    by_cases view : s ∈ before ⁻¹' {observed}
    · by_cases supported : s ∈ prior.support
      · have impossible : value ∉ (kernel s).support := fun possible =>
          matched ((determines s supported value possible).trans view)
        rw [(PMF.apply_eq_zero_iff _ _).mpr impossible, mul_zero]
      · rw [Set.indicator_of_mem view, (PMF.apply_eq_zero_iff _ _).mpr supported]
        simp
    · rw [Set.indicator_of_notMem view]
      simp

/-- Once the finer observation is made, an earlier observation determined by
it does not further change the posterior. The support condition also handles
the total conditioning operator's unused empty-fiber fallback. -/
theorem conditional_fiber_after_projection {A Info Coarse : Type*} (law : PMF A)
    (observe : A → Info) (project : Info → Coarse) (coarse : Coarse) (observed : Info)
    (present : observed ∈ ((fiberConditional law (project ∘ observe) coarse).map observe).support) :
    fiberConditional (fiberConditional law (project ∘ observe) coarse) observe observed =
      fiberConditional law observe observed := by
  classical
  by_cases coarseMeets : ∃ a ∈ (project ∘ observe) ⁻¹' {coarse}, a ∈ law.support
  · have coarseLaw : fiberConditional law (project ∘ observe) coarse =
        law.filter ((project ∘ observe) ⁻¹' {coarse}) coarseMeets := by
      rw [fiberConditional, dite_eq_left coarseMeets]
    rw [coarseLaw] at present ⊢
    obtain ⟨a, aSupported, aView⟩ := (PMF.mem_support_map_iff _ _ _).mp present
    have aOriginal := ((PMF.mem_support_filter_iff _).mp aSupported).2
    have aCoarse := ((PMF.mem_support_filter_iff _).mp aSupported).1
    have projected : project observed = coarse := by
      change project (observe a) = coarse at aCoarse
      rwa [aView] at aCoarse
    have fineMeets : ∃ a ∈ observe ⁻¹' {observed}, a ∈ law.support :=
      ⟨a, aView, aOriginal⟩
    have nestedMeets : ∃ a ∈ observe ⁻¹' {observed},
        a ∈ (law.filter ((project ∘ observe) ⁻¹' {coarse}) coarseMeets).support :=
      ⟨a, aView, aSupported⟩
    rw [fiberConditional, dite_eq_left nestedMeets, fiberConditional, dite_eq_left fineMeets]
    exact filter_filter_of_subset law _ _ coarseMeets nestedMeets fun value member => by
      change project (observe value) = coarse
      rw [show observe value = observed from member, projected]
  · have coarseLaw : fiberConditional law (project ∘ observe) coarse = law := by
      rw [fiberConditional, dite_eq_right coarseMeets]
    rw [coarseLaw]

end PMF
