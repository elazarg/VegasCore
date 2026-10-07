/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRiskSlots
import Vegas.Game.SourceServiceOwnerSettled

/-! # Actual packet facts at a clear risk-menu prefix

Persistent clarity forces the owner's earlier responses to be canonical and
every owned submission to pass its protection gate. This derives fresh,
conforming, unique calls from the actual legal prefix, including silent
deferrals. Protected inclusion then preserves their actual pending or accepted
content. Foreign owners may take every legal expanded raw response.

Current opportunity clarity is not needed for earlier packet facts. These
lemmas assert neither zero audit charge nor an equilibrium comparison.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

private theorem clearCanonicalResponse_packetFacts
    (bounds : MessageBounds (serviceGraph setup mode)) (bound :
        (serviceGraph setup mode).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {middle : (serviceApplication setup mode deadline leaks).Execution} {who : Player}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining, some who, middle⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks middle who)
    (slots : CanonicalSlotsUsed setup leaks middle who)
    (calls : OwnFreshCalls setup leaks bound middle who)
    (conform : FreshCallsConform setup leaks middle who)
    (once : OneCallPerEvent setup leaks middle who)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (member : response ∈ bounds.clearActions (serviceRuntime setup mode deadline) leaks who
      (middle.recall who) (middle.observe (serviceApplication setup mode deadline leaks) who))
    (clear : (serviceRuntime setup mode deadline).persistentServiceRisk leaks bound who
      ((middle.respond (serviceApplication setup mode deadline leaks) who response).recall who)
      ((middle.respond (serviceApplication setup mode deadline leaks) who response).observe
        (serviceApplication setup mode deadline leaks) who) = false) :
    OwnFreshCalls setup leaks bound (middle.respond
        (serviceApplication setup mode deadline leaks) who response) who ∧
      FreshCallsConform setup leaks (middle.respond
          (serviceApplication setup mode deadline leaks) who response) who ∧
      OneCallPerEvent setup leaks (middle.respond
          (serviceApplication setup mode deadline leaks) who response) who := by
  let app := serviceApplication setup mode deadline leaks
  apply ownerCallFacts_respond middle who response calls conform once
  · exact bounds.clearActions_firstSubmission
      (serviceRuntime setup mode deadline) leaks who _ _ response member
  · intro material submitted
    rcases bounds.clearActions_cases (serviceRuntime setup mode deadline) leaks who _ _ response
        member with member | ⟨_, conformant⟩
    · obtain ⟨event, action, turn, _, _, timely, unrecorded, _, decided⟩ :=
        bounds.canonicalActions_submission
            (serviceRuntime setup mode deadline) leaks who _ _ response member material
          submitted
      have fresh := canonicalSlot_fresh_of_used trace who atTurn slots event turn unrecorded
      exact canonicalServiceDecision_freshServiceEnvelope trace event turn timely fresh action
        material (by rw [← decided]; exact submitted)
    · obtain ⟨other, sent, _, fresh⟩ := conformantResponse_actual trace who response conformant
      rw [submitted] at sent
      cases Option.some.inj sent
      exact fresh
  · intro event submitted
    have owned : (serviceGraph setup mode).actor? event = some who := by
      rcases bounds.clearActions_cases (serviceRuntime setup mode deadline) leaks who _ _
          response member with member | ⟨_, conformant⟩
      · exact (bounds.canonical_submitted_event
          (serviceRuntime setup mode deadline) leaks who _ _ response member
          event submitted).2.1
      · obtain ⟨named, submittedNamed, _, owned, _⟩ :=
          conformantResponse_turn trace who response conformant
        rw [submitted, Option.some.injEq] at submittedNamed
        subst named
        exact owned
    obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
    let entry : app.PlayerEntry := ⟨middle.observe app who, response, emitted⟩
    have entryMember : entry ∈ (middle.respond app who response).recall who := by
      rw [recalled]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have submittedClear :=
        ((serviceRuntime setup mode deadline).persistentServiceRisk_clear_iff leaks bound who
      _ _).mp clear |>.1.2
    exact ((serviceRuntime setup mode deadline).recalledSubmissionRisk_clear_iff leaks bound who
        _).mp submittedClear
      entry entryMember rfl event submitted owned

/-- Any owner policy covered by the risk menu has actual protected, conforming,
unique calls and sound packet content whenever its persistent risk is clear.
Foreign policies need no coverage premise. -/
theorem riskPacketFacts_roundsFrom
    (bounds : MessageBounds (serviceGraph setup mode)) (bound :
        (serviceGraph setup mode).EventId → Nat)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler
      delay bound)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    (covered : ∀ past view response, response ∈ (players who past view).support →
      response ∈ bounds.riskActions (serviceRuntime setup mode deadline) leaks bound who past view)
    (count : Nat) (within : count ≤ horizon) (execution :
        (serviceApplication setup mode deadline leaks).Execution)
    (reached : execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
        (serviceInitialLaw setup mode) scheduler
      players count).support)
    (clear : (serviceRuntime setup mode deadline).persistentServiceRisk leaks bound who
        (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) = false) :
    OwnFreshCalls setup leaks bound execution who ∧
      FreshCallsConform setup leaks execution who ∧ OneCallPerEvent setup leaks execution who ∧
      ∀ message, message.sender = who → Emitted setup leaks execution message →
        SettledGood setup leaks execution message := by
  let app := serviceApplication setup mode deadline leaks
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro entry present
        cases present
      · intro entry present
        cases present
      · intro entry present
        cases present
      · intro message _ emitted
        simp only [Emitted, ReactiveApplication.Execution.initial, MessageNetwork.empty] at emitted
        cases emitted
  | succ count ih =>
      rw [app.roundsFrom_succ (serviceInitialLaw setup mode) scheduler players count] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom
          (serviceInitialLaw setup mode) horizon scheduler players count
        (by omega) prior priorMem
      rw [show horizon - count = (horizon - (count + 1)) + 1 by omega] at trace
      obtain ⟨command, selected, middle, observed, effect⟩ := round_cases setup leaks moved
      have clearMiddle :
          (serviceRuntime setup mode deadline).persistentServiceRisk leaks bound who
              (middle.recall who)
          (middle.observe app who) = false := by
        rcases effect with ⟨_, rfl⟩ | ⟨responder, _, response, _, rfl⟩
        · exact clear
        · exact (serviceRuntime setup mode deadline).persistentServiceRisk_clear_before_respond
            leaks bound middle
            responder who response clear
      have clearPrior :=
          (serviceRuntime setup mode deadline).persistentServiceRisk_clear_before_environment
              leaks bound
        who clearMiddle observed
      obtain ⟨calls, conform, once, good⟩ := ih (by omega) prior priorMem clearPrior
      obtain ⟨atTurn, slots⟩ := riskCanonicalSlots_roundsFrom bounds bound scheduler players who
        covered count prior priorMem clearPrior
      obtain ⟨middleTrace⟩ := app.raw_trace_environment
          (serviceInitialLaw setup mode) horizon scheduler
        (horizon - (count + 1)) prior middle command trace selected observed
      have recallEq := app.environmentStep_recall prior middle command observed
      have callsMiddle : OwnFreshCalls setup leaks bound middle who := by
        unfold OwnFreshCalls
        rw [recallEq]
        exact calls
      have conformMiddle : FreshCallsConform setup leaks middle who := by
        unfold FreshCallsConform
        rw [recallEq]
        exact conform
      have onceMiddle : OneCallPerEvent setup leaks middle who := by
        unfold OneCallPerEvent
        rw [recallEq]
        exact once
      have goodMiddle : ∀ message, message.sender = who → Emitted setup leaks middle message →
          SettledGood setup leaks middle message := by
        intro message authored emitted
        have emittedBefore : Emitted setup leaks prior message := by
          unfold Emitted at emitted ⊢
          rw [← app.environmentStep_inputs prior middle command observed]
          exact emitted
        exact (good message authored emittedBefore).owner_environment contract.inclusion
          (settledFacts_history
              (serviceInitialLaw setup mode) horizon scheduler trace) observed middleTrace
          who callsMiddle conformMiddle onceMiddle authored emittedBefore
      rcases effect with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
      · exact ⟨callsMiddle, conformMiddle, onceMiddle, goodMiddle⟩
      · rw [active] at middleTrace
        by_cases same : responder = who
        · subst responder
          have member := covered _ _ response chosen
          have menuClear :=
              (serviceRuntime setup mode deadline).serviceRisk_clear_before_respond leaks bound
                  middle who
            response clear
          rw [bounds.riskActions_of_clear
              (serviceRuntime setup mode deadline) leaks bound who _ _ menuClear] at member
          have atMiddle : OwnSubmissionsAtTurn setup leaks middle who := by
            unfold OwnSubmissionsAtTurn
            rw [recallEq]
            exact atTurn
          have slotsMiddle := canonicalSlotsUsed_environment observed who slots
          obtain ⟨callsNext, conformNext, onceNext⟩ := clearCanonicalResponse_packetFacts bounds
            bound middleTrace atMiddle slotsMiddle callsMiddle conformMiddle onceMiddle response
            member clear
          refine ⟨callsNext, conformNext, onceNext, ?_⟩
          apply owner_good_response (settledFacts_history
              (serviceInitialLaw setup mode) horizon scheduler
            middleTrace) who who response goodMiddle
          intro _ material submitted
          let message : Message Player (WitnessedPacket (serviceGraph setup mode)) :=
            ⟨(who, middle.network.nextSerial who), app.packet (app.submit middle.application who
              material) who (middle.network.known who) material⟩
          let entry : app.PlayerEntry := ⟨middle.observe app who, response, some message⟩
          have entryMember : entry ∈ (middle.respond app who response).recall who := by
            cases response
            cases submitted
            rw [respond_submit_recall]
            exact List.mem_append_right _ (List.mem_singleton_self _)
          exact conformNext entry entryMember material message submitted rfl
        · have different : who ≠ responder := fun equal => same equal.symm
          have recallSame := app.respond_recall_other middle responder who different response
          refine ⟨?_, ?_, ?_, ?_⟩
          · unfold OwnFreshCalls
            rw [recallSame]
            exact callsMiddle
          · unfold FreshCallsConform
            rw [recallSame]
            exact conformMiddle
          · unfold OneCallPerEvent
            rw [recallSame]
            exact onceMiddle
          · apply owner_good_response (settledFacts_history
              (serviceInitialLaw setup mode) horizon scheduler
              middleTrace) who responder response goodMiddle
            intro equal
            exact (same equal).elim

/-- A legal risk-menu prefix supplies all owner packet facts from its actual
trace. Earlier silence is allowed, and only persistent owner clarity is needed. -/
theorem riskPacketFacts_history
    (bounds : MessageBounds (serviceGraph setup mode)) (bound :
        (serviceGraph setup mode).EventId → Nat)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler
      delay bound)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).protocol
        (serviceInitialLaw setup mode) horizon
      scheduler).Trace (some control))
    (who : Player)
    (clear : (serviceRuntime setup mode deadline).persistentServiceRisk leaks bound who
        (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) = false) :
    OwnFreshCalls setup leaks bound control.execution who ∧
      FreshCallsConform setup leaks control.execution who ∧
      OneCallPerEvent setup leaks control.execution who ∧
      ∀ message, message.sender = who → Emitted setup leaks control.execution message →
        SettledGood setup leaks control.execution message := by
  let app := serviceApplication setup mode deadline leaks
  let menu := bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound
  have covered : ∀ past view response,
      response ∈ (menu.uniformResponses who past view).support →
        response ∈ bounds.riskActions
            (serviceRuntime setup mode deadline) leaks bound who past view := by
    intro past view response supported
    exact (menu.uniformResponses_support who past view response).mp supported
  have supported := menu.roundSupported_uniform
      (serviceInitialLaw setup mode) horizon scheduler trace
  have rawTrace := menu.toRawTrace (serviceInitialLaw setup mode) horizon scheduler trace
  obtain ⟨remaining, actor, execution⟩ := control
  cases actor with
  | none =>
      have within : execution.environmentRecall.length ≤ horizon := by
        have lengths := supported.1
        change execution.environmentRecall.length + remaining = horizon at lengths
        omega
      exact riskPacketFacts_roundsFrom bounds bound contract menu.uniformResponses who covered
        execution.environmentRecall.length within execution supported.2 clear
  | some responder =>
      obtain ⟨lengthEq, count, prior, command, _, priorMem, _, active, moved⟩ := supported
      have clearPrior :=
          (serviceRuntime setup mode deadline).persistentServiceRisk_clear_before_environment
              leaks bound
        who clear moved
      obtain ⟨calls, conform, once, good⟩ := riskPacketFacts_roundsFrom bounds bound contract
        menu.uniformResponses who covered count (by omega) prior priorMem clearPrior
      have recallEq := app.environmentStep_recall prior execution command moved
      have callsNext : OwnFreshCalls setup leaks bound execution who := by
        unfold OwnFreshCalls
        rw [recallEq]
        exact calls
      have conformNext : FreshCallsConform setup leaks execution who := by
        unfold FreshCallsConform
        rw [recallEq]
        exact conform
      have onceNext : OneCallPerEvent setup leaks execution who := by
        unfold OneCallPerEvent
        rw [recallEq]
        exact once
      refine ⟨callsNext, conformNext, onceNext, ?_⟩
      intro message authored emitted
      have emittedBefore : Emitted setup leaks prior message := by
        unfold Emitted at emitted ⊢
        rw [← app.environmentStep_inputs prior execution command moved]
        exact emitted
      obtain ⟨priorTrace⟩ := app.raw_trace_roundsFrom
          (serviceInitialLaw setup mode) horizon scheduler
        menu.uniformResponses count (by omega) prior priorMem
      rw [← active] at rawTrace
      exact (good message authored emittedBefore).owner_environment contract.inclusion
        (settledFacts_history
            (serviceInitialLaw setup mode) horizon scheduler priorTrace) moved rawTrace who
        callsNext conformNext onceNext authored emittedBefore

end Vegas
