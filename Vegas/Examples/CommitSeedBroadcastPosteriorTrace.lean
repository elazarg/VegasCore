/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastCountedSeedTrace
import Vegas.Examples.CommitSeedBroadcastInitialResponses
import Interaction.ReactiveSchedulerSeedSupport
import Interaction.ReactiveSchedulerSeedContinuation
import Interaction.ReactiveRoundOccupation

/-! # Retained original posterior seeds realize each native menu control -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem menu_original_posterior_trace (menu : app.ResponseMenu) (current : app.Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some current))
    (seed : Seeds)
    (supported : seed ∈ (implementation.posterior current.execution.environmentRecall).support) :
    seed ∈ nativeSeedLaw.support ∧
      Nonempty ((menu.protocol initial horizon (family seed)).Trace (some current)) := by
  obtain ⟨accounted, reached⟩ := menu.roundSupported_uniform initial horizon scheduler trace
  cases active : current.actor with
  | none =>
      rw [active] at reached
      have initialized : current.execution ∈ (app.runRounds scheduler menu.uniformResponses
          current.execution.environmentRecall.length initialExecution).support := by
        simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind,
          initialExecution] using reached
      obtain ⟨originalSupport, originalReached⟩ :=
        app.schedulerMixture_run_of_posterior_support nativeSeedLaw family menu.uniformResponses
          current.execution.environmentRecall.length initialState current.execution seed
            initialized supported
      have rounds : current.execution ∈ (app.roundsFrom initial (family seed)
          menu.uniformResponses current.execution.environmentRecall.length).support := by
        simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind,
          initialExecution] using originalReached
      obtain ⟨fixed⟩ := menu.trace_roundsFrom initial horizon (family seed)
        menu.uniformResponses (fun who past view action member =>
          (menu.uniformResponses_support who past view action).mp member)
        current.execution.environmentRecall.length (by omega) current.execution rounds
      have distance : horizon - current.execution.environmentRecall.length =
          current.remaining := by omega
      rw [distance] at fixed
      have shape : current = (⟨current.remaining, none, current.execution⟩ : app.Control) := by
        cases current with
        | mk remaining acting execution =>
            change acting = none at active
            cases active
            rfl
      rw [← shape] at fixed
      exact ⟨originalSupport, ⟨fixed⟩⟩
  | some owner =>
      rw [active] at reached
      obtain ⟨count, before, command, position, beforeReached, selected, actor, moved⟩ := reached
      have initialized : before ∈ (app.runRounds scheduler menu.uniformResponses count
          initialExecution).support := by
        simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind,
          initialExecution] using beforeReached
      obtain ⟨originalSupport, original, originalReached, originalSelected, originalMoved⟩ :=
        app.schedulerMixture_decision_of_posterior_support nativeSeedLaw family
          menu.uniformResponses count initialState before current.execution command seed initialized
            selected moved
            supported
      have rounds : original ∈ (app.roundsFrom initial (family seed) menu.uniformResponses
          count).support := by
        simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind,
          initialExecution] using originalReached
      obtain ⟨beforeTrace⟩ := menu.trace_roundsFrom initial horizon (family seed)
        menu.uniformResponses (fun who past view action member =>
          (menu.uniformResponses_support who past view action).mp member)
        count (by omega) original rounds
      have distance : horizon - count = current.remaining + 1 := by omega
      rw [distance] at beforeTrace
      obtain ⟨fixed⟩ := menu.trace_environment initial horizon (family seed) current.remaining
        original current.execution command beforeTrace originalSelected originalMoved
      rw [actor] at fixed
      have shape : current =
          (⟨current.remaining, some owner, current.execution⟩ : app.Control) := by
        cases current with
        | mk remaining acting execution =>
            change acting = some owner at active
            cases active
            rfl
      rw [← shape] at fixed
      exact ⟨originalSupport, ⟨fixed⟩⟩

end Vegas.Examples.CommitSeedBroadcast
