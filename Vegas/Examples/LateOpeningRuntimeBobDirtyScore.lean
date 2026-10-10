/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingTransport
import Vegas.Examples.LateOpeningRuntimeBobDirtyPayoff
import Vegas.Examples.LateOpeningRuntimeBobSuccessPayoff

/-! # Receiver score ceilings after a sunk native audit charge

Every fixed raw response selects its actual typed binding through protected
native service. Against arbitrary later policies, its receiver payoff is bounded
by that binding's score less the already incurred full receiver charge.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobDirtyScore

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeBobBindingService LateOpeningRuntimeBobDirtyPrefix
  LateOpeningRuntimeBobBindingTransport
  LateOpeningRuntimeBobSuccessPayoff
  LateOpeningRuntimeBobBindingOmission LateOpeningRuntimeUtility

theorem dirty_continuation_payoff_le_score (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (dirty : ¬ SilentRecall execution) (publishedBit : Bool)
    (publishedAlice : execution.application.config.store (.inr aliceEvent) =
      some (.success publishedBit : PublicationResult Bool))
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob response)).support)
    (reward forfeit : ℝ) (forfeitNonnegative : 0 ≤ forfeit) (deposit : Player → ℝ) :
    LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit (some ⟨0, none, final⟩) bob ≤
        bindingScore (originalLabel execution)
          ((servicedBinding execution response).application.config.store (.inr bobBindEvent)) -
            deposit bob := by
  have rawTrace := rawMenu.toRawTrace _ _ _ trace
  obtain ⟨bit, label, binding, publication, bitEq, labelEq, finalReachable,
    bound, published, readout⟩ := continuation_readout weight nonnegative execution
      rawTrace publishedBit publishedAlice response players final reached
  have splitReach := reached
  change final ∈ ((app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
    (execution.respond app bob response)).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 13)).support
    at splitReach
  rw [servicedBinding_round weight nonnegative execution trace response players,
    PMF.pure_bind] at splitReach
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 execution bob response rawTrace
  obtain ⟨servicedTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 13 _
    (servicedBinding execution response) respondedTrace
    (by rw [servicedBinding_round weight nonnegative execution trace response players]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  change serviceSourceReadout setup .sequential deadline leaks (some ⟨0, none, final⟩) =
    some (terminalStateOf bit label (.success publishedBit) binding publication) at readout
  rw [dirty_binding_payoff_eq_base_sub_deposit weight nonnegative reward forfeit deposit
    execution trace ready dirty response players final reached,
    nativeBaseUtility_of_readout reward forfeit _ _ readout bob]
  apply sub_le_sub_right
  rw [labelEq]
  cases publication with
  | failure =>
      rw [sourceUtility_bob_failure]
      exact (neg_nonpos.mpr forfeitNonnegative).trans (bindingScore_nonnegative label _)
  | success answer =>
      have finalBinding := bob_success_from_binding final.application _ finalReachable answer
        published
      have selected : (servicedBinding execution response).application.config.store
          (.inr bobBindEvent) = some (.success answer) := by
        cases immediate : (servicedBinding execution response).application.config.store
            (.inr bobBindEvent) with
        | none =>
            have failed := omitted_binding_expires weight nonnegative players _ final
              servicedTrace immediate splitReach
            rw [finalBinding] at failed
            cases failed
        | some result =>
            have retained := (ReactiveApplication.Invariant.policyInvariant app
              (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
                (.inr bobBindEvent) result) players).runRounds
                  (LateOpeningRuntimeService.scheduler weight nonnegative) 13 _ final immediate
                    splitReach
            exact congrArg some (Option.some.inj (retained.symm.trans finalBinding))
      rw [selected]
      exact le_of_eq (sourceUtility_bob_after_alice_success reward forfeit bit label
        publishedBit binding answer)

end Vegas.Examples.LateOpeningRuntimeBobDirtyScore
