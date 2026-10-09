/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingOmission
import Vegas.Examples.LateOpeningRuntimeBobAnswerPayoff

/-! # Every raw binding continuation is bounded by its selected answer

An immediate successful binding fixes the final answer. An unusable accepted
binding or an omitted binding cannot produce a successful final publication.
Nonnegative forfeits and audit collateral therefore bound every raw suffix by
the logical score of the immediate typed binding result. Neither the current
response nor later policies are required to have canonical packet syntax.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobRawPayoff

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeUtility LateOpeningRuntimeBobBindingInformation
  LateOpeningRuntimeBobAnswerPayoff LateOpeningRuntimeBobRawBinding
  LateOpeningRuntimeBobBindingOmission

/-- The payoff ceiling selected by the actual immediate typed binding. -/
def bindingScore (bit : Bool) : Option (PublicationResult Answer) → ℝ
  | some (.success answer) => if answer.val = (if bit then 5 else 4) then 1 else 0
  | _ => 0

theorem bindingScore_nonnegative (bit : Bool) (result : Option (PublicationResult Answer)) :
    0 ≤ bindingScore bit result := by
  cases result with
  | none => exact le_rfl
  | some result =>
      cases result with
      | failure => exact le_rfl
      | success answer =>
          change 0 ≤ if answer.val = (if bit then 5 else 4) then (1 : ℝ) else 0
          split_ifs <;> norm_num

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- The actual terminal decoder preserves the initialized bit and Alice's
already public failure through every unrestricted raw continuation. -/
theorem continuation_readout (decision : DecisionHistory weight nonnegative)
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (decision.execution.respond app bob response)).support) :
    ∃ bit label binding publication,
      originalBit decision.execution = bit ∧
      EventGraph.Config.Reachable (graph := nativeGraph)
        (setup.eventInputs (sourceInitial bit label)) final.application.config ∧
      final.application.config.store (.inr bobBindEvent) = some binding ∧
      final.application.config.store (.inr bobRevealEvent) = some publication ∧
      serviceSourceReadout setup .sequential deadline leaks (app.finished final) =
        some (terminalStateOf bit label .failure binding publication) := by
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨14, some bob, decision.execution⟩ decision.trace
  have invariant := LateOpeningRuntimeService.runtime.reactiveStateInvariant leaks
    (setup.eventInputs (sourceInitial bit label))
  have after := (ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (invariant.respond decision.execution bob response valid) reached
  have failedInvariant := LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
    (.inr aliceEvent) (.failure : PublicationResult Bool)
  have aliceAfter := (ReactiveApplication.Invariant.policyInvariant app failedInvariant
    players).runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (failedInvariant.respond decision.execution bob response decision.failed) reached
  obtain ⟨responded⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 decision.execution bob response
      decision.trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 14 _ final responded reached
  have complete := (contract weight nonnegative).completes ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
  obtain ⟨binding, bound⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal complete (.inr bobBindEvent))
  obtain ⟨publication, published⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal complete (.inr bobRevealEvent))
  refine ⟨bit, label, binding, publication,
    originalBit_initialized decision.execution bit label valid, after.reachable, bound,
      published, ?_⟩
  change (if final.application.config.cut.Terminal then
    decodeState? (terminalRefs program) final.application.config.store else none) = _
  rw [ite_eq_left complete]
  exact decode_terminalStateOf final.application bit label .failure binding publication
    after.reachable.inputs_eq aliceAfter bound published

/-- A fixed raw response cannot earn more than the logical score of its
actual immediate binding, against any later raw player policies. -/
theorem continuation_payoff_le_score (decision : DecisionHistory weight nonnegative)
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (decision.execution.respond app bob response)).support)
    (reward forfeit : ℝ) (forfeitNonnegative : 0 ≤ forfeit) (deposit : Player → ℝ)
    (depositNonnegative : 0 ≤ deposit bob)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) :
    LateOpeningRuntimeNash.payoff reward forfeit sample deposit (app.finished final) bob ≤
      bindingScore (originalBit decision.execution)
        ((serviced decision.execution response).application.config.store (.inr bobBindEvent)) := by
  obtain ⟨bit, label, binding, publication, bitEq, finalReachable, bound, published, readout⟩ :=
    continuation_readout weight nonnegative decision response players final reached
  have splitReach := reached
  rw [continuation_split weight nonnegative _ decision.trace decision.quiet] at splitReach
  obtain ⟨servicedTrace⟩ := serviced_trace weight nonnegative _ decision.trace decision.quiet
    response
  have deduction : 0 ≤ TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks sample) (app.finished final) bob *
        deposit bob := mul_nonneg (TerminalAudit.charge_mem_Icc _ _ _ _).1 depositNonnegative
  have baseUpper : LateOpeningRuntimeNash.payoff reward forfeit sample deposit
      (app.finished final) bob ≤ sourceUtility reward forfeit
        (terminalStateOf bit label .failure binding publication) bob := by
    unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
    rw [nativeBaseUtility_of_readout reward forfeit _ _ readout bob]
    exact sub_le_self _ deduction
  rw [bitEq]
  cases publication with
  | failure =>
      rw [sourceUtility_bob_failure] at baseUpper
      have lower := bindingScore_nonnegative bit
        ((serviced decision.execution response).application.config.store (.inr bobBindEvent))
      linarith
  | success answer =>
      have finalBinding := bob_success_from_binding final.application _ finalReachable answer
        published
      have selected : (serviced decision.execution response).application.config.store
          (.inr bobBindEvent) = some (.success answer) := by
        cases immediate : (serviced decision.execution response).application.config.store
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
            have same := Option.some.inj (retained.symm.trans finalBinding)
            exact congrArg some same
      rw [selected]
      change _ ≤ if answer.val = (if bit then 5 else 4) then 1 else 0
      rw [sourceUtility_bob_after_alice_failure] at baseUpper
      exact baseUpper

end Vegas.Examples.LateOpeningRuntimeBobRawPayoff
