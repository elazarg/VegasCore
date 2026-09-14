/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedTermination
import VegasTests.PendingOutcome

/-! # Nullable resolution of an actual compiled checked source

The runtime uses the four rules emitted by the checked core compiler. Both
missing commitments resolve without private registrations, and the public
result agrees with a legal written-source execution choosing `none` twice.
This is a concrete settlement test, not a general strategic correspondence.
-/

namespace VegasTests.SealedResolution

open Interaction Vegas Vegas.EventGraph VegasTests.PendingSource VegasTests.PendingExecution
open VegasTests.PendingOutcome

private def runtime : Interaction.SealedResolution PendingSource.Player Value :=
  ⟨PendingExecution.program, none, 2⟩

private theorem compilation : SealedCompilation source (.option .bool) :=
  ⟨sealedFragment⟩

theorem uses_compiled_source : runtime.program = sealedFragment.compile := rfl

private def resolved := runtime.tick (runtime.tick runtime.initial)

theorem missing_commits_publish_source_nulls :
    resolved.visible.timeouts = [0, 1] ∧
      resolved.visible.events = [.opened 2 none, .opened 3 none] ∧
      resolved.service.lookup (0, 0) = none ∧
      resolved.service.lookup (1, 1) = none ∧
      runtime.complete resolved.visible = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

noncomputable section

/-- The four-node compiled fixture terminates after twelve rounds even with an
empty roster and zero wire-service slots, under arbitrary policies. -/
theorem arbitrary_policies_complete_without_service
    (players : PendingSource.Player → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈
      (runtime.roundDriver.runRounds [] 0 players environment 12
        (MessageApplication.PolicyExecution.initial _
          (MessageApplication.State.initial _ runtime.initial))).support) :
    runtime.complete next.native.application.visible = true := by
  exact compilation.supported.resolvingRuntime_runRounds_complete none 2 [] 0
    players environment 12 (by decide) next hnext

/-- Competing candidates, malformed traffic, and arbitrary service decisions
cannot prevent clock-driven completion of the compiled four-node program. -/
theorem arbitrary_candidate_policies_complete
    (principals : List PendingSource.Player) (serviceSlots : Nat)
    (players : PendingSource.Player → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.WirePolicy)
    (next : runtime.candidateApplication.PolicyExecution)
    (hnext : next ∈
      (runtime.candidateRoundDriver.runRounds principals serviceSlots players environment 12
        (MessageApplication.PolicyExecution.initial _
          (MessageApplication.State.initial _ runtime.candidateInitial))).support) :
    runtime.complete next.native.application.visible = true := by
  exact compilation.supported.candidateRuntime_runRounds_complete none 2 principals serviceSlots
    players environment 12 (by decide) next hnext

end

theorem resolved_public_values_have_source_execution :
    ∃ terminalEnv : VEnv simpleExpr compiled.terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := compiled.terminalCtx, env := terminalEnv, cont := .ret compiled.sourcePayoffs } ∧
      resolved.visible.published? 2 = some (terminalEnv.get (.there .here)) ∧
      resolved.visible.published? 3 = some (terminalEnv.get .here) := by
  obtain ⟨terminalEnv, hsource, _, hfields⟩ := honestRun_source none none false
  refine ⟨terminalEnv, hsource, ?_, ?_⟩
  · have hfield := hfields (.there .here)
    have hstored : Store.getAs (expected none none).store
        (compiled.terminalState.fieldOf (.there .here)) (.option .bool) = some none := by
      rfl
    rw [hstored] at hfield
    exact hfield
  · have hfield := hfields .here
    have hstored : Store.getAs (expected none none).store
        (compiled.terminalState.fieldOf .here) (.option .bool) = some none := by
      rfl
    rw [hstored] at hfield
    exact hfield

end VegasTests.SealedResolution

/-- info: 'VegasTests.SealedResolution.resolved_public_values_have_source_execution'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedResolution.resolved_public_values_have_source_execution
