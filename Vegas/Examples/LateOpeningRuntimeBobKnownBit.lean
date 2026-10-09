/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingDecision
import Vegas.Pending.ReactiveAssociationEvidence
import Interaction.ReactiveResponseEvaluation

/-! # Authentic bit knowledge and optimal native continuations

An opening certificate together with its public accepted association identifies
Alice's immutable initial bit throughout an actual receiver information class.
The result uses the complete bounded raw game, including off-path histories;
the assessment belief need not satisfy a separately assumed posterior formula.

After Alice's publication fails, a canonical commitment and complete opening
of the known correct bit attain payoff one. Every raw audited continuation is
bounded above by one. Sequential rationality therefore saturates that bound.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobKnownBit

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeUtility LateOpeningRuntimeBobBindingInformation
  LateOpeningRuntimeBobBindingDecision LateOpeningRuntimeBobAnswerPayoff
  LateOpeningRuntimeEarlyBobSafeMenu

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- A concrete observable certificate and its public graph association. -/
def ObservesBit (view : app.PlayerView) (bit : Bool) : Prop :=
  LateOpeningRuntimeService.runtime.bindingEvidenceObserved leaks view
    ⟨alice, .bool, aliceBinding, bit⟩

private theorem initial_law_eq :
    (setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)) = initial := by
  rw [PMF.map_comp]
  rfl

/-- Actual certificate soundness and binding provenance determine the stored
initial bit; an unaccepted plaintext claim supplies no such fact. -/
theorem originalBit_of_observed (decision : DecisionHistory weight nonnegative)
    (bit : Bool) (observed : ObservesBit (decision.execution.observe app bob) bit) :
    originalBit decision.execution = bit := by
  have trace : (app.protocol ((setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)))
      LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ).Trace (some ⟨14, some bob, decision.execution⟩) := by
    rw [initial_law_eq]
    exact decision.trace
  have valid := LateOpeningRuntimeService.runtime.reactiveBindingInvariant_history leaks
    (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  have sound := (LateOpeningRuntimeService.runtime.packetEvidence leaks).history_sound initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      decision.trace
  have stored := LateOpeningRuntimeService.runtime.observed_bindingEvidence_valid leaks
    decision.execution bob valid sound ⟨alice, .bool, aliceBinding, bit⟩ observed
  change aliceBinding.get? decision.execution.application.config.store = some (.success bit)
    at stored
  unfold originalBit
  rw [stored]

variable
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)

/-- Knowledge ranges over every actual compatible raw history, independently
of whether an assessment assigns it positive belief. -/
theorem originalBit_of_information (bit : Bool)
    (observed : ObservesBit (decision.execution.observe app bob) bit)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    originalBit (decisionOfInformation weight nonnegative site representative decision current
      history).execution = bit := by
  have same := (decisionOfInformation_spec weight nonnegative site representative decision current
    history).2.2
  apply originalBit_of_observed weight nonnegative _ bit
  unfold ObservesBit at observed ⊢
  rwa [← same]

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

/-- The bound holds for every protocol state and every audit kernel. A
nonnegative deduction cannot raise Bob's bounded gross payoff. -/
theorem payoff_le_one (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (state : app.ProtocolState) :
    LateOpeningRuntimeNash.payoff reward forfeit sample deposit state bob ≤ 1 := by
  have baseUpper : nativeBaseUtility reward forfeit state bob ≤ 1 := by
    unfold nativeBaseUtility serviceBaseUtility
    cases decoded : serviceSourceReadout setup .sequential deadline leaks state with
    | none => norm_num
    | some terminal =>
        exact (sourceUtility_bob_bounds forfeitNonnegative reward terminal).2
  have deduction : 0 ≤ TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks sample) state bob * deposit bob :=
    mul_nonneg (TerminalAudit.charge_mem_Icc _ _ _ _).1 depositNonnegative
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  linarith

include representative decision current in
/-- The actual whole-policy correct guess attains the maximal payoff under
any belief over this certificate-bearing native information class. -/
theorem correct_guess_context_value (bit : Bool)
    (observed : ObservesBit (decision.execution.observe app bob) bit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative (bitGuess bit)) = 1 := by
  rw [answer_context_value weight nonnegative site representative decision current]
  calc
    _ = expect (assessment.belief bob site) (fun _ => (1 : ℝ)) := by
      apply expect_congr_on_support
      intro history _
      rw [originalBit_of_information weight nonnegative site representative decision current
        bit observed history]
      simp [bitGuess]
    _ = 1 := expect_constant _ _

include representative decision current in
/-- Sequential rationality attains the raw upper bound once an authentic
certificate identifies the failed publication's immutable initial bit. -/
theorem rational_context_value_eq_one (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob) (bit : Bool)
    (observed : ObservesBit (decision.execution.observe app bob) bit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) = 1 := by
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight nonnegative site reward forfeit deposit assessment
      (assessment.strategy bob))
    (fun alternative _ => context_integrable weight nonnegative site reward forfeit deposit
      assessment alternative)).mp rational
  have lower := comparison (answerFinitePolicy weight nonnegative (bitGuess bit)) (Set.mem_univ _)
  rw [correct_guess_context_value weight nonnegative site representative decision current
    reward forfeit deposit bit observed assessment] at lower
  have upper : (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) ≤ 1 :=
    expect_le_const _ _ (context_integrable weight nonnegative site reward forfeit deposit
      assessment (assessment.strategy bob)) 1
      (fun history _ => payoff_le_one reward forfeit deposit forfeitNonnegative
        depositNonnegative (fun actual => PMF.pure actual) history.state)
  exact le_antisymm upper lower

include representative decision current in
/-- Saturation holds at each supported complete native continuation history,
which is stronger than merely having optimal expected payoff. -/
theorem rational_supported_payoff_eq_one (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob) (bit : Bool)
    (observed : ObservesBit (decision.execution.observe app bob) bit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ∀ final ∈ ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (assessment.strategy bob)).support,
      LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit final.state bob = 1 := by
  apply expect_eq_const_of_le_on_support _ _ 1
    (context_integrable weight nonnegative site reward forfeit deposit assessment
      (assessment.strategy bob))
    (fun history _ => payoff_le_one reward forfeit deposit forfeitNonnegative
      depositNonnegative (fun actual => PMF.pure actual) history.state)
  exact rational_context_value_eq_one weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositNonnegative bit observed assessment rational

/-- The complete physical continuation of the incumbent native profile,
averaged over the actual assessment information class. -/
def incumbentFinalLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    PMF app.Execution :=
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  (assessment.belief bob site).bind fun history =>
    (app.invoke players bob
      (decisionOfInformation weight nonnegative site representative decision current
        history).execution).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 14)

theorem incumbent_context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (assessment.strategy bob)).map History.state =
    (incumbentFinalLaw weight nonnegative site representative decision current assessment).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, incumbentFinalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  have valid := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  simp only [Profile.update, Function.update_eq_self]
  calc
    _ = app.finish initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)
        (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
        history.1.state :=
      rawMenu.run_eq_finish initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy 53 history.1
          (by rw [valid.1]; change 29 ≤ 53; decide)
    _ = _ := by rw [valid.1]; rfl

include representative decision current in
theorem rational_physical_payoff_eq_one (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob) (bit : Bool)
    (observed : ObservesBit (decision.execution.observe app bob) bit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ∀ final ∈ (incumbentFinalLaw weight nonnegative site representative decision current
      assessment).support,
      LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) bob = 1 := by
  intro final supported
  have mapped : app.finished final ∈
      (((context weight nonnegative site reward forfeit deposit assessment).outcome
        (assessment.strategy bob)).map History.state).support := by
    rw [incumbent_context_outcome_law weight nonnegative site representative decision current]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
  obtain ⟨history, historySupported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp mapped
  rw [← same]
  exact rational_supported_payoff_eq_one weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositNonnegative bit observed assessment rational
      history historySupported

omit site representative decision current in
/-- A payoff-one actual continuation from a failed publication must publish
the certified correct bit and incur zero full audit charge. Its terminal
readout and initialized hidden input are derived from the legal raw trace. -/
theorem payoff_one_correct_publication (forfeitNonnegative : 0 ≤ forfeit)
    (depositPositive : 0 < deposit bob) (decision : DecisionHistory weight nonnegative)
    (bit : Bool) (observed : ObservesBit (decision.execution.observe app bob) bit)
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (decision.execution.respond app bob response)).support)
    (payoffOne : LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit (app.finished final) bob = 1) :
    final.application.config.store (.inr bobRevealEvent) = some (.success (bitGuess bit)) ∧
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
          (app.finished final) bob = 0 := by
  obtain ⟨initialBit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime
    leaks LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨14, some bob, decision.execution⟩ decision.trace
  have bitEq := (originalBit_initialized decision.execution initialBit label valid).symm.trans
    (originalBit_of_observed weight nonnegative decision bit observed)
  subst initialBit
  have invariant := LateOpeningRuntimeService.runtime.reactiveStateInvariant leaks
    (setup.eventInputs (sourceInitial bit label))
  have finalValid := (ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (invariant.respond decision.execution bob response valid) reached
  have failedInvariant := LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
    (.inr aliceEvent) (.failure : PublicationResult Bool)
  have finalFailed := (ReactiveApplication.Invariant.policyInvariant app failedInvariant
    players).runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (failedInvariant.respond decision.execution bob response decision.failed) reached
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 decision.execution bob response
      decision.trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 14 _ final respondedTrace
      reached
  have completed := (contract weight nonnegative).completes ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
  obtain ⟨binding, bindingStored⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal completed (.inr bobBindEvent))
  obtain ⟨answer, answerStored⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal completed (.inr bobRevealEvent))
  have decoded := decode_terminalStateOf final.application bit label .failure binding answer
    finalValid.reachable.inputs_eq finalFailed bindingStored answerStored
  have readout : serviceSourceReadout setup .sequential deadline leaks (app.finished final) =
      some (terminalStateOf bit label .failure binding answer) := by
    change (if final.application.config.cut.Terminal then
      decodeState? (terminalRefs program) final.application.config.store else none) = _
    rw [ite_eq_left completed]
    exact decoded
  have deduction := mul_nonneg
    (TerminalAudit.charge_mem_Icc (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
      (app.finished final) bob).1 depositPositive.le
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility at payoffOne
  rw [nativeBaseUtility_of_readout reward forfeit _ _ readout bob] at payoffOne
  cases answer with
  | failure =>
      rw [sourceUtility_bob_failure] at payoffOne
      linarith
  | success answer =>
      rw [sourceUtility_bob_after_alice_failure] at payoffOne
      have correct : answer.val = (if bit then 5 else 4) := by
        by_contra wrong
        rw [ite_eq_right wrong] at payoffOne
        linarith
      have same : answer = bitGuess bit := Subtype.ext correct
      subst answer
      rw [ite_eq_left correct] at payoffOne
      refine ⟨answerStored, ?_⟩
      nlinarith

include representative decision current in
/-- Every supported actual physical continuation publishes the correct bit
and has zero full audit charge at a rational certificate-bearing class. -/
theorem rational_correct_publication (forfeitNonnegative : 0 ≤ forfeit)
    (depositPositive : 0 < deposit bob) (bit : Bool)
    (observed : ObservesBit (decision.execution.observe app bob) bit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ∀ final ∈ (incumbentFinalLaw weight nonnegative site representative decision current
      assessment).support,
      final.application.config.store (.inr bobRevealEvent) = some (.success (bitGuess bit)) ∧
        TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
          (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
            (app.finished final) bob = 0 := by
  intro final supported
  have payoffOne := rational_physical_payoff_eq_one weight nonnegative site representative decision
    current reward forfeit deposit forfeitNonnegative depositPositive.le bit observed assessment
      rational final supported
  unfold incumbentFinalLaw at supported
  obtain ⟨history, _, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨responded, responseSupported, reached⟩ := (PMF.mem_support_bind_iff _ _ _).mp rest
  obtain ⟨response, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp responseSupported
  subst responded
  let recovered := decisionOfInformation weight nonnegative site representative decision current
    history
  apply payoff_one_correct_publication weight nonnegative reward forfeit deposit forfeitNonnegative
    depositPositive recovered bit ?_ response _ final reached payoffOne
  unfold ObservesBit at observed ⊢
  rw [← (decisionOfInformation_spec weight nonnegative site representative decision current
    history).2.2]
  exact observed

include representative decision current in
/-- The conclusion follows from sequential rationality in the owning native
game, without a separate local-context or posterior premise. -/
theorem sequentially_rational_context_value_eq_one (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob) (bit : Bool)
    (observed : ObservesBit (decision.execution.observe app bob) bit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) = 1 := by
  apply rational_context_value_eq_one weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositNonnegative bit observed assessment
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact localRational

include representative decision current in
/-- Every actual sequentially rational assessment publishes the certified
correct bit without full audit charge on each supported physical continuation. -/
theorem sequentially_rational_correct_publication (forfeitNonnegative : 0 ≤ forfeit)
    (depositPositive : 0 < deposit bob) (bit : Bool)
    (observed : ObservesBit (decision.execution.observe app bob) bit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    ∀ final ∈ (incumbentFinalLaw weight nonnegative site representative decision current
      assessment).support,
      final.application.config.store (.inr bobRevealEvent) = some (.success (bitGuess bit)) ∧
        TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
          (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
            (app.finished final) bob = 0 := by
  apply rational_correct_publication weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositPositive bit observed assessment
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact localRational

include representative decision current in
/-- The same physical conclusion applies to every native sequential
equilibrium, including this class after an earlier publication deviation. -/
theorem equilibrium_correct_publication (forfeitNonnegative : 0 ≤ forfeit)
    (depositPositive : 0 < deposit bob) (bit : Bool)
    (observed : ObservesBit (decision.execution.observe app bob) bit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    ∀ final ∈ (incumbentFinalLaw weight nonnegative site representative decision current
      assessment).support,
      final.application.config.store (.inr bobRevealEvent) = some (.success (bitGuess bit)) ∧
        TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
          (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
            (app.finished final) bob = 0 :=
  sequentially_rational_correct_publication weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositPositive bit observed assessment equilibrium.1

end Vegas.Examples.LateOpeningRuntimeBobKnownBit
