/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingOmission
import Vegas.Examples.LateOpeningRuntimeBobSuccessInformation
import Vegas.Examples.LateOpeningRuntimeBobSafeContinuation

/-! # Actual answer scores after successful Alice publication

A ready timely first binding with silent earlier Bob responses can settle
any fixed answer with zero Bob charge. Every raw current response and raw
suffix is bounded by the score of its actual immediate typed binding. The
label used in that score is the immutable initialized private input; no
posterior distribution or restriction on pending packet contents is assumed.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobSuccessPayoff

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeUtility LateOpeningRuntimeBobSuccessInformation
  LateOpeningRuntimeBobSafeContinuation
  LateOpeningRuntimeBobBindingOmission
open LateOpeningRuntimeBobRawBinding
  (serviced continuation_split serviced_trace)

/-- Alice's immutable initialized private label, read only for describing
hidden-history payoffs rather than selecting an observable runtime action. -/
def originalLabel (execution : app.Execution) : Fin 3 :=
  let label : Label := execution.application.config.inputs labelInput
  ⟨label.val.toNat, by
    have lower := label.property.1
    have upper := label.property.2
    omega⟩

theorem originalLabel_initialized (execution : app.Execution) (bit : Bool) (label : Fin 3)
    (valid : EventGraphRuntime.State.Invariant (graph := nativeGraph)
      (setup.eventInputs (sourceInitial bit label)) execution.application) :
    originalLabel execution = label := by
  apply Fin.ext
  change (execution.application.config.inputs labelInput).val.toNat = label.val
  rw [valid.reachable.inputs_eq]
  exact Int.toNat_natCast label.val

def answerScore (label : Fin 3) (answer : Answer) : ℝ :=
  if answer.val = 0 then 2 / 5
  else if answer.val = (label.val : Int) + 1 then 1 else 0

/-- The ceiling selected by the actual immediate successful typed binding. -/
def bindingScore (label : Fin 3) : Option (PublicationResult Answer) → ℝ
  | some (.success answer) => answerScore label answer
  | _ => 0

theorem bindingScore_nonnegative (label : Fin 3) (result : Option (PublicationResult Answer)) :
    0 ≤ bindingScore label result := by
  cases result with
  | none => exact le_rfl
  | some result =>
      cases result with
      | failure => exact le_rfl
      | success answer =>
          change 0 ≤ if answer.val = 0 then (2 / 5 : ℝ)
            else if answer.val = (label.val : Int) + 1 then 1 else 0
          split_ifs <;> norm_num

theorem bindingScore_abs_le_one (label : Fin 3)
    (result : Option (PublicationResult Answer)) : |bindingScore label result| ≤ 1 := by
  cases result with
  | none => norm_num [bindingScore]
  | some result =>
      cases result with
      | failure => norm_num [bindingScore]
      | success answer =>
          change |if answer.val = 0 then (2 / 5 : ℝ)
            else if answer.val = (label.val : Int) + 1 then 1 else 0| ≤ 1
          split_ifs <;> norm_num

theorem sourceUtility_bob_after_alice_success (reward forfeit : ℝ) (bit : Bool)
    (label : Fin 3) (publishedBit : Bool) (binding : PublicationResult Answer) (answer : Answer) :
    sourceUtility reward forfeit
      (terminalStateOf bit label (.success publishedBit) binding (.success answer)) bob =
        answerScore label answer := by
  rw [sourceUtility_bob, parameterOutcome_terminalStateOf]
  change answerScore label answer - 0 = _
  simp

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- Terminal decoding retains the actual immutable label and successful
public Alice bit through every unrestricted raw continuation. -/
theorem continuation_readout (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (publishedBit : Bool)
    (publishedAlice : execution.application.config.store (.inr aliceEvent) =
      some (.success publishedBit : PublicationResult Bool))
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob response)).support) :
    ∃ bit label binding publication,
      publishedBit = bit ∧ originalLabel execution = label ∧
      EventGraph.Config.Reachable (graph := nativeGraph)
        (setup.eventInputs (sourceInitial bit label)) final.application.config ∧
      final.application.config.store (.inr bobBindEvent) = some binding ∧
      final.application.config.store (.inr bobRevealEvent) = some publication ∧
      serviceSourceReadout setup .sequential deadline leaks (app.finished final) =
        some (terminalStateOf bit label (.success publishedBit) binding publication) := by
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨14, some bob, execution⟩ trace
  have invariant := LateOpeningRuntimeService.runtime.reactiveStateInvariant leaks
    (setup.eventInputs (sourceInitial bit label))
  have after := (ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (invariant.respond execution bob response valid) reached
  have publicationInvariant := LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
    (.inr aliceEvent) (.success publishedBit : PublicationResult Bool)
  have aliceAfter := (ReactiveApplication.Invariant.policyInvariant app publicationInvariant
    players).runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (publicationInvariant.respond execution bob response publishedAlice) reached
  obtain ⟨responded⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 execution bob response
      trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 14 _ final responded reached
  have complete := (contract weight nonnegative).completes ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
  obtain ⟨binding, bound⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal complete (.inr bobBindEvent))
  obtain ⟨publication, published⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal complete (.inr bobRevealEvent))
  refine ⟨bit, label, binding, publication,
    alice_success_from_initialized_bit execution.application bit label valid
      publishedBit publishedAlice, originalLabel_initialized execution bit label valid,
    after.reachable, bound,
      published, ?_⟩
  change (if final.application.config.cut.Terminal then
    decodeState? (terminalRefs program) final.application.config.store else none) = _
  rw [ite_eq_left complete]
  exact decode_terminalStateOf final.application bit label (.success publishedBit) binding
    publication after.reachable.inputs_eq aliceAfter bound published

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
      bindingScore (originalLabel decision.execution)
        ((serviced decision.execution response).application.config.store (.inr bobBindEvent)) := by
  obtain ⟨bit, label, binding, publication, bitEq, labelEq, finalReachable,
    bound, published, readout⟩ :=
    continuation_readout weight nonnegative decision.execution decision.trace decision.bit
      decision.published response players final reached
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
        (terminalStateOf bit label (.success decision.bit) binding publication) bob := by
    unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
    rw [nativeBaseUtility_of_readout reward forfeit _ _ readout bob]
    exact sub_le_self _ deduction
  rw [labelEq]
  cases publication with
  | failure =>
      rw [sourceUtility_bob_failure] at baseUpper
      have lower := bindingScore_nonnegative label
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
      change _ ≤ answerScore label answer
      rw [sourceUtility_bob_after_alice_success] at baseUpper
      exact baseUpper


/-- Each fixed answer is attained by a genuine whole policy, with arbitrary
future Alice responses and no assumed distribution of the private label. -/
theorem answer_continuation_payoff
    (decision : DecisionHistory weight nonnegative) (answer : Answer)
    (players : Player → app.Policy) (bobPolicy : players bob = answerPolicy answer)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14
        (decision.execution.respond app bob
          (LateOpeningRuntimeBobSuffix.binding answer))).support) :
    LateOpeningRuntimeNash.payoff reward forfeit sample deposit (app.finished final) bob =
      answerScore (originalLabel decision.execution) answer := by
  obtain ⟨successful, clear⟩ := answer_continuation_clean weight nonnegative answer players
    bobPolicy decision.execution final decision.trace decision.quiet decision.ready decision.timely
      sample authentic reached
  obtain ⟨bit, label, binding, publication, bitEq, labelEq, reachable, bound, published, readout⟩ :=
    continuation_readout weight nonnegative decision.execution decision.trace decision.bit
      decision.published (LateOpeningRuntimeBobSuffix.binding answer)
      players final reached
  have same : publication = PublicationResult.success answer :=
    Option.some.inj (published.symm.trans successful)
  subst publication
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  rw [clear, zero_mul, sub_zero, nativeBaseUtility_of_readout reward forfeit _ _ readout bob,
    sourceUtility_bob_after_alice_success, labelEq]

end Vegas.Examples.LateOpeningRuntimeBobSuccessPayoff
