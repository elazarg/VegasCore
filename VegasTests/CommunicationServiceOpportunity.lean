/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationNative
import Vegas.Pending.ReactiveServiceOpportunity

/-! # A dependent response remains available after arbitrary earlier behavior

Instantiate recurring reactive service on the actual deferred-guard graph.
After any number of epochs with arbitrary player policies, malformed calls,
omissions, partial observations and network reactions, a newly activated final
guess event has a timely owner visit in the next epoch, or is completed before
that visit. This is a checked service opportunity, not SE-preservation or a
claim that a prescribed packet wins competing inclusion.
-/

noncomputable section

namespace VegasTests.CommunicationServiceOpportunity

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open SequentialValidation

theorem newly_ready_guess_has_owner_opportunity
    (leaks : MessageNetwork.ObservationRule Bool (WitnessedPacket nativeGraph))
    (networkTurns : Nat)
    (players : Bool → (nativeRuntime.reactiveApplication leaks).Policy)
    (network : nativeRuntime.NetworkPolicy leaks) (bit : Bool) (epochs : Nat)
    (execution middle next : (nativeRuntime.reactiveApplication leaks).Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionEpochs leaks
      (ServiceOrder.increasing nativeGraph) networkTurns players network epochs
        (.initial (nativeRuntime.reactiveApplication leaks) (nativeStart bit))).support)
    (absent : execution.application.activatedAt guessEvent = none)
    (ready : middle.application.config.cut.Ready guessEvent)
    (first : middle ∈ (nativeRuntime.runInteractionPlan leaks players network
      (interactionEpoch (ServiceOrder.increasing nativeGraph) networkTurns) execution).support)
    (second : next ∈ (nativeRuntime.runInteractionPlan leaks players network
      (interactionEpoch (ServiceOrder.increasing nativeGraph) networkTurns) middle).support) :
    ∃ before after prior responded,
      interactionEpoch (ServiceOrder.increasing nativeGraph) networkTurns =
        before ++ .player true :: after ∧
      prior ∈ (nativeRuntime.runInteractionPlan leaks players network before middle).support ∧
      responded ∈
        (nativeRuntime.interactionStep leaks players network (.player true) prior).support ∧
      next ∈ (nativeRuntime.runInteractionPlan leaks players network after responded).support ∧
      (guessEvent ∈ prior.application.config.cut.completed ∨
        (prior.application.config.cut.Ready guessEvent ∧
          prior.application.WithinDeadline nativeRuntime guessEvent)) := by
  have invariant := (nativeRuntime.runInteractionEpochs_facts leaks
    (sourceSetup.eventInputs (initialState bit)) (ServiceOrder.increasing nativeGraph) networkTurns
    players network epochs _ execution (State.initial_invariant _) reached).invariant
  have feasible : nativeRuntime.ServiceFeasible := by
    intro event
    change 2 ≤ 10
    decide
  exact nativeRuntime.interactionEpoch_new_activation_opportunity feasible leaks
    (sourceSetup.eventInputs (initialState bit)) (ServiceOrder.increasing nativeGraph) networkTurns
    players network execution middle next invariant guessEvent true rfl absent ready first second

end VegasTests.CommunicationServiceOpportunity
