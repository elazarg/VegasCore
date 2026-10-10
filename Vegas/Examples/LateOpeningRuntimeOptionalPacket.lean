/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeOptionalRationality
import Vegas.Examples.LateOpeningRuntimeBobFinalAuditObservation
import Interaction.ReactiveReceiptIdentity
import Interaction.ReactiveTrafficContinuation

/-! # Optional native response normalization on the entire information class

A sent packet receives its permanent receipt immediately. One supported clean
terminal continuation therefore certifies the effect of that current packet;
equal complete Bob information transports that effect to every compatible
hidden history. The raw submission's private representation remains arbitrary.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeOptionalPacket

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeOptionalOpening LateOpeningRuntimeOptionalInformation
  LateOpeningRuntimeOptionalIncentive LateOpeningRuntimeOptionalDecision
  LateOpeningRuntimeOptionalRationality
open LateOpeningRuntimeBobFinalObservation (serviced)
open LateOpeningRuntimeBobResponseState (responseState)
open LateOpeningRuntimeBobFinalAuditObservation
  (auditKey keyCharge fullCharge fullCharge_eq_keyCharge)
open LateOpeningRuntimeBobBindingDecision (context)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def emittedMessage (execution : app.Execution) (material : app.Submission) :
    Message Player app.Payload :=
  ⟨(bob, execution.network.nextSerial bob),
    app.packet (app.submit execution.application bob material) bob
      (execution.network.known bob) material⟩

theorem continuation_split (decision : DecisionHistory weight nonnegative)
    (material : app.Submission) (players : Player → app.Policy) :
    continuation weight nonnegative decision ⟨some material⟩ players =
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 11
      (serviced decision.execution ⟨some material⟩) := by
  change (app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
    (decision.execution.respond app bob ⟨some material⟩)).bind _ = _
  rw [LateOpeningRuntimeBobFinalObservation.serviced_round weight nonnegative 12
    decision.execution decision.trace ⟨some material⟩ players, PMF.pure_bind]

theorem permitted_of_clear (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (message : Message Player app.Payload) (present : message ∈ control.execution.network.inputs)
    (owner : message.sender = bob) (clear : fullCharge control.execution = 0) :
    (LateOpeningRuntimeService.runtime.settledRecord leaks control.execution).permits message =
      true := by
  classical
  have zero : keyCharge (auditKey control.execution) = 0 := by
    rw [← fullCharge_eq_keyCharge weight nonnegative control trace]
    exact clear
  by_contra forbidden
  have denied := Bool.eq_false_iff.mpr forbidden
  have violation : ∃ packet ∈ control.execution.network.inputs.filter
      (fun packet => packet.sender = bob),
      (⟨control.execution.application.publicView, control.execution.receipts⟩ :
        SettledRecord nativeGraph).permits packet = false :=
    ⟨message, List.mem_filter.mpr ⟨present, by simpa using owner⟩, denied⟩
  unfold keyCharge auditKey at zero
  split at zero <;> norm_num at zero

theorem permitted_terminal_accepts (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control)) (message : Message Player app.Payload)
    (permitted : (LateOpeningRuntimeService.runtime.settledRecord leaks control.execution).permits
      message = true) : (message.id, true) ∈ control.execution.receipts := by
  let record := LateOpeningRuntimeService.runtime.settledRecord leaks control.execution
  have permission := (record.permits_eq_true_iff message).mp permitted
  cases named : message.payload.call.event? nativeGraph with
  | none => simp only [SettledRecord.Permits, named] at permission
  | some event =>
      simp only [SettledRecord.Permits, named] at permission
      rcases permission with unfinished | settled
      · have complete := LateOpeningRuntimeService.completes weight nonnegative control trace
          terminal
        have member : event ∈ control.execution.application.config.cut.completed := by
          rw [complete]
          exact Finset.mem_univ _
        exact (unfinished
          ((control.execution.application.config.history_exact event).mpr member)).elim
      · exact settled.1

theorem immediate_publication_of_clear (decision : DecisionHistory weight nonnegative)
    (material : app.Submission) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (continuation weight nonnegative decision ⟨some material⟩ players).support)
    (published : final.application.config.store (.inr bobRevealEvent) =
      some (.success decision.answer)) (clear : fullCharge final = 0) :
    (serviced decision.execution ⟨some material⟩).application.config.store
      (.inr bobRevealEvent) = some (.success decision.answer) := by
  let submitted := decision.execution.respond app bob ⟨some material⟩
  let first := serviced decision.execution ⟨some material⟩
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 12 decision.execution bob
      ⟨some material⟩ decision.trace
  obtain ⟨firstTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 11 submitted first
      respondedTrace (by
        rw [LateOpeningRuntimeBobFinalObservation.serviced_round weight nonnegative 12
    decision.execution decision.trace ⟨some material⟩ players]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have suffix := reached
  rw [continuation_split weight nonnegative decision material players] at suffix
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 11 first final firstTrace
      suffix
  have submittedMessage : emittedMessage decision.execution material ∈ submitted.network.inputs :=
    by
      simp [submitted, ReactiveApplication.Execution.respond, MessageNetwork.submit, emittedMessage]
  have inputs := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) respondedTrace
  change (app.executionTraffic submitted).map ReactiveApplication.TrafficRecord.envelope =
    submitted.network.inputs at inputs
  rw [← inputs, List.mem_map] at submittedMessage
  obtain ⟨traffic, trafficPresent, envelopeEq⟩ := submittedMessage
  have finalTraffic := (app.executionTraffic_runRounds (LateOpeningRuntimeService.scheduler
    weight nonnegative) players 12 submitted final reached).subset trafficPresent
  have finalInputs := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) finalTrace
  change (app.executionTraffic final).map ReactiveApplication.TrafficRecord.envelope =
    final.network.inputs at finalInputs
  have finalMessage : emittedMessage decision.execution material ∈ final.network.inputs := by
    rw [← finalInputs]
    exact List.mem_map.mpr ⟨traffic, finalTraffic, envelopeEq⟩
  have permission := permitted_of_clear weight nonnegative ⟨0, none, final⟩ finalTrace
    (emittedMessage decision.execution material) finalMessage rfl clear
  have accepted := permitted_terminal_accepts weight nonnegative ⟨0, none, final⟩ finalTrace
    ⟨rfl, rfl⟩ (emittedMessage decision.execution material) permission
  have serials := app.serialsBeforeNext_history (LateOpeningRuntimeService.scheduler
    weight nonnegative) initial LateOpeningRuntimeService.horizon decision.trace
  have lookup : submitted.network.lookup (emittedMessage decision.execution material).id =
      some (emittedMessage decision.execution material) :=
    serials.lookup_submit bob
      (app.packet (app.submit decision.execution.application bob material) bob
        (decision.execution.network.known bob) material)
  have handled : ∃ next, app.handle submitted.application
      (emittedMessage decision.execution material) = some next := by
    cases result : app.handle submitted.application
        (emittedMessage decision.execution material) with
    | some next => exact ⟨next, rfl⟩
    | none =>
        have rejected : ((emittedMessage decision.execution material).id, false) ∈ first.receipts :=
          by
          change ((emittedMessage decision.execution material).id, false) ∈
            (submitted.includePending app (emittedMessage decision.execution material).id).receipts
          unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
          simp [lookup, result]
        have retained := (app.receipt_policyInvariant players
          ((emittedMessage decision.execution material).id, false)).runRounds
            (LateOpeningRuntimeService.scheduler weight nonnegative) 11 first final rejected suffix
        exact (app.rejected_identifier_not_accepted initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) ⟨0, none, final⟩ finalTrace
          (emittedMessage decision.execution material).id retained accepted).elim
  obtain ⟨next, handled⟩ := handled
  have raw := reactiveHandle_call handled
  obtain ⟨event, _named, unfinished, complete⟩ := handle_completes
    LateOpeningRuntimeService.runtime submitted.application next
      ⟨(emittedMessage decision.execution material).id,
        (emittedMessage decision.execution material).payload.call⟩ raw
  have configSame := (LateOpeningRuntimeService.runtime.reactive_respond_application leaks
    decision.execution bob ⟨some material⟩).1
  have eventEq : event = bobRevealEvent := by
    change Fin 3 at event
    fin_cases event
    · have prior := decision.ready.2 (by decide : aliceEvent ∈
        nativeGraph.order.predecessors bobRevealEvent)
      apply False.elim
      apply unfinished
      rwa [configSame]
    · have prior := decision.ready.2 (by decide : bobBindEvent ∈
        nativeGraph.order.predecessors bobRevealEvent)
      apply False.elim
      apply unfinished
      rwa [configSame]
    · rfl
  subst event
  have physical : first.application = next := by
    change (submitted.includePending app
      (emittedMessage decision.execution material).id).application = next
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    simp only [lookup, handled, Option.getD_some]
  have available : (first.application.config.outputs bobRevealEvent).isSome := by
    rw [physical]
    exact (next.config.output_available bobRevealEvent).mpr complete
  change (first.application.config.store (.inr bobRevealEvent)).isSome = true at available
  obtain ⟨result, stored⟩ := Option.isSome_iff_exists.mp available
  have retained := (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobRevealEvent) result)
      players).runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) 11 first final
        stored suffix
  exact stored.trans (retained.symm.trans published)

theorem immediate_publication_same_information
    (first second : DecisionHistory weight nonnegative)
    (sameRecall : first.execution.recall bob = second.execution.recall bob)
    (sameView : first.execution.observe app bob = second.execution.observe app bob)
    (material : app.Submission) :
    (serviced first.execution ⟨some material⟩).application.config.store (.inr bobRevealEvent) =
      (serviced second.execution ⟨some material⟩).application.config.store
        (.inr bobRevealEvent) := by
  rw [LateOpeningRuntimeBobFinalObservation.serviced_physical weight nonnegative 12
    first.execution first.trace ⟨some material⟩,
    LateOpeningRuntimeBobFinalObservation.serviced_physical weight nonnegative 12
    second.execution second.trace ⟨some material⟩]
  have views := LateOpeningRuntimeBobResponseState.responseState_same_view
    first.execution second.execution
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) first.trace)
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) second.trace)
    sameRecall sameView ⟨some material⟩
  have stores : nativeGraph.playerStore bob
      (responseState first.execution ⟨some material⟩).config.store =
      nativeGraph.playerStore bob
        (responseState second.execution ⟨some material⟩).config.store :=
    congrArg (fun view : PlayerView nativeGraph => view.observation.store) views
  have visible : nativeGraph.fieldVisibleTo bob (.inr bobRevealEvent) := by decide
  simpa only [nativeGraph.playerStore_of_visible bob _ _ visible] using
    congrFun stores (.inr bobRevealEvent)

variable
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨12, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem rational_supported_response (forfeitPositive : 0 < forfeit)
    (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support) :
    response.transmission = none ∨
      (serviced (decisionOfInformation weight nonnegative site representative decision current
        history).execution response).application.config.store (.inr bobRevealEvent) =
          some (.success decision.answer) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact Or.inl rfl
  | some material =>
      obtain ⟨believedHistory, believed⟩ := (assessment.belief bob site).support_nonempty
      let recovered := decisionOfInformation weight nonnegative site representative decision current
        believedHistory
      let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
      obtain ⟨final, reached⟩ :=
        (continuation weight nonnegative recovered ⟨some material⟩ players).support_nonempty
      obtain ⟨published, clear⟩ := rational_supported_clean_settlement weight nonnegative site
        representative decision current reward forfeit deposit forfeitPositive depositPositive
          assessment rational ⟨some material⟩ supported believedHistory believed final reached
      have compatible := decisionOfInformation_spec weight nonnegative site representative decision
        current believedHistory
      have published' : final.application.config.store (.inr bobRevealEvent) =
          some (.success recovered.answer) := by rwa [compatible.2.2.2] at published
      have immediate := immediate_publication_of_clear weight nonnegative recovered material players
        final reached published' clear
      have other := decisionOfInformation_spec weight nonnegative site representative decision
        current history
      have same := immediate_publication_same_information weight nonnegative recovered
        (decisionOfInformation weight nonnegative site representative decision current history)
          (compatible.2.1.symm.trans other.2.1)
          (compatible.2.2.1.symm.trans other.2.2.1) material
      exact Or.inr (same.symm.trans (immediate.trans
        (congrArg (fun answer => some (PublicationResult.success answer)) compatible.2.2.2.symm)))

theorem sequentially_rational_supported_response (forfeitPositive : 0 < forfeit)
    (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support) :
    response.transmission = none ∨
      (serviced (decisionOfInformation weight nonnegative site representative decision current
        history).execution response).application.config.store (.inr bobRevealEvent) =
          some (.success decision.answer) := by
  apply rational_supported_response weight nonnegative site representative decision current reward
    forfeit deposit forfeitPositive depositPositive assessment _ history response supported
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact localRational

theorem equilibrium_supported_response (forfeitPositive : 0 < forfeit)
    (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support) :
    response.transmission = none ∨
      (serviced (decisionOfInformation weight nonnegative site representative decision current
        history).execution response).application.config.store (.inr bobRevealEvent) =
          some (.success decision.answer) :=
  sequentially_rational_supported_response weight nonnegative site representative decision current
    reward forfeit deposit forfeitPositive depositPositive assessment equilibrium.1 history response
      supported

end Vegas.Examples.LateOpeningRuntimeOptionalPacket
