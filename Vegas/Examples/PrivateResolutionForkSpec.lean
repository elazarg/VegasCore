/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkProtectedInclusion
import Vegas.Game.AsyncServiceSpec

/-! # The actual bounded asynchronous resolution-fork service

The finite message alphabet contains both Boolean values and Alice's singleton
value. Initialized candidate coverage is derived from the actual compiled
initial law. The service uses the fixed public scheduler and its all-raw
contract, rather than a supplied service-identification assumption.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

open Classical in
def baseBounds : MessageBounds nativeGraph :=
  ⟨4, {⟨.bool, false⟩, ⟨.bool, true⟩, ⟨unitPayload, unitValue⟩}⟩

def bounds : MessageBounds nativeGraph :=
  baseBounds.withInitialValues ((setup.initialLaw.map setup.eventInputs).map State.initial)

theorem bindingValues : bounds.CoversBindingValues := by
  intro event
  change Fin 4 at event
  fin_cases event <;> trivial

theorem initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state := by
  intro state supported
  rw [initialLaw_eq_inputs] at supported
  obtain ⟨input, present, rfl⟩ := PMF.support_map .. ▸ supported
  apply baseBounds.candidateValues_initial (setup.initialLaw.map setup.eventInputs) _ input present
  rw [PMF.support_map]
  exact setup.initialLaw_support_finite.image _

/-- This is the concrete service used by the native fork, with every required
finite-support, coverage, timing and all-raw service field proved. -/
def service : AsyncServiceSpec Player simpleExpr where
  setup := setup
  leaks := leaks
  bounds := bounds
  values := bindingValues
  initialValues := initialValues
  capacity := by change 4 ≤ 4; rfl
  horizon := horizon
  scheduler := scheduler
  delay := delay
  bound := bound
  contract := contract
  timely := timely
  initialFinite := inferInstance
  leaksFinite := ⟨by intro who pending; simp [leaks]⟩
  schedulerFinite := by
    intro past view
    unfold scheduler
    split
    · exact (Set.Finite.union (by simp) (by simp)).subset
        (support_mix_subset _ _ _ _ _)
    · split
      · exact (Set.Finite.union (by simp) (by simp)).subset
          (support_mix_subset _ _ _ _ _)
      · simp

end Vegas.PrivateResolutionFork
