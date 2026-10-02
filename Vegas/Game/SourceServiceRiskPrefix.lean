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
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem clearCanonicalResponse_packetFacts
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    {middle : (application setup leaks).Execution} {who : Player}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, middle⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks middle who)
    (slots : CanonicalSlotsUsed setup leaks middle who)
    (calls : OwnFreshCalls setup leaks bound middle who)
    (conform : FreshCallsConform setup leaks middle who)
    (once : OneCallPerEvent setup leaks middle who)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.canonicalActions (runtime setup) leaks who
      (middle.recall who) (middle.observe (application setup leaks) who))
    (clear : (runtime setup).persistentServiceRisk leaks bound who
      ((middle.respond (application setup leaks) who response).recall who)
      ((middle.respond (application setup leaks) who response).observe
        (application setup leaks) who) = false) :
    OwnFreshCalls setup leaks bound (middle.respond (application setup leaks) who response) who ∧
      FreshCallsConform setup leaks (middle.respond (application setup leaks) who response) who ∧
      OneCallPerEvent setup leaks (middle.respond (application setup leaks) who response) who := by
  let app := application setup leaks
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      obtain ⟨_, recalled, _⟩ := respond_recall_self setup leaks middle who ⟨none⟩
      refine ⟨?_, ?_, ?_⟩
      · intro entry present material submits
        rw [recalled] at present
        rcases List.mem_append.mp present with old | new
        · exact calls entry old material submits
        · rw [List.mem_singleton] at new
          subst new
          cases submits
      · intro entry present material message submits emitted
        rw [recalled] at present
        rcases List.mem_append.mp present with old | new
        · exact conform entry old material message submits emitted
        · rw [List.mem_singleton] at new
          subst new
          cases submits
      · intro first firstMember second secondMember event firstMessage secondMessage
          firstEvent secondEvent firstEmitted secondEmitted
        rw [recalled] at firstMember secondMember
        rcases List.mem_append.mp firstMember with firstOld | firstNew
        · rcases List.mem_append.mp secondMember with secondOld | secondNew
          · exact once first firstOld second secondOld event _ _ firstEvent secondEvent
              firstEmitted secondEmitted
          · rw [List.mem_singleton] at secondNew
            subst secondNew
            cases secondEvent
        · rw [List.mem_singleton] at firstNew
          subst firstNew
          cases firstEvent
  | some material =>
      obtain ⟨event, action, turn, owned, _, timely, unrecorded, _, decided⟩ :=
        bounds.canonicalActions_submission (runtime setup) leaks who _ _ ⟨some material⟩ member
          material rfl
      have fresh := canonicalSlot_fresh_of_used trace who atTurn slots event turn unrecorded
      have packetConform := canonicalServiceDecision_freshServiceEnvelope trace event turn timely
        fresh action material (congrArg ReactiveApplication.Action.transmission decided.symm)
      let message : Message Player (WitnessedPacket (graph setup)) :=
        ⟨(who, middle.network.nextSerial who), app.packet (app.submit middle.application who
          material) who (middle.network.known who) material⟩
      let entry : app.PlayerEntry := ⟨middle.observe app who, ⟨some material⟩, some message⟩
      have recalled := respond_submit_recall middle who material
      have entryMember : entry ∈ (middle.respond app who ⟨some material⟩).recall who := by
        rw [recalled]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      obtain ⟨named, addressed, readyView, owner⟩ :=
        (runtime setup).freshServiceEnvelope_owned _ message packetConform
      have namedTurn : middle.application.publicView.ownTurn? who = some named :=
        ownTurn?_of_ready setup middle.application
          ((middle.application.publicView_eventReady named).mp readyView) owner
      have equal : named = event := Option.some.inj (namedTurn.symm.trans turn)
      subst equal
      have entryEvent : (runtime setup).submittedEvent? leaks entry.action = some named :=
        addressed
      have submittedClear := ((runtime setup).persistentServiceRisk_clear_iff leaks bound who
        _ _).mp clear |>.1.2
      have fits := ((runtime setup).recalledSubmissionRisk_clear_iff leaks bound who _).mp
        submittedClear entry entryMember rfl named entryEvent owned
      have absent : ∀ old ∈ middle.recall who,
          (runtime setup).submittedEvent? leaks old.action ≠ some named := by
        intro old oldMember oldEvent
        have recorded : (runtime setup).eventRecorded leaks (middle.recall who) named = true :=
          List.any_eq_true.mpr ⟨old, oldMember, decide_eq_true oldEvent⟩
        rw [unrecorded] at recorded
        cases recorded
      refine ⟨?_, ?_, ?_⟩
      · intro current present currentMaterial submits
        rw [recalled] at present
        rcases List.mem_append.mp present with old | new
        · exact calls current old currentMaterial submits
        · rw [List.mem_singleton] at new
          subst new
          exact ⟨named, message, rfl, rfl, addressed, entryEvent, fits⟩
      · intro current present currentMaterial currentMessage submits emitted
        rw [recalled] at present
        rcases List.mem_append.mp present with old | new
        · exact conform current old currentMaterial currentMessage submits emitted
        · rw [List.mem_singleton] at new
          subst new
          cases Option.some.inj emitted
          exact packetConform
      · intro first firstMember second secondMember shared firstMessage secondMessage
          firstEvent secondEvent firstEmitted secondEmitted
        rw [recalled] at firstMember secondMember
        rcases List.mem_append.mp firstMember with firstOld | firstNew <;>
          rcases List.mem_append.mp secondMember with secondOld | secondNew
        · exact once first firstOld second secondOld shared _ _ firstEvent secondEvent
            firstEmitted secondEmitted
        · rw [List.mem_singleton] at secondNew
          subst secondNew
          rw [entryEvent] at secondEvent
          cases Option.some.inj secondEvent
          exact (absent first firstOld firstEvent).elim
        · rw [List.mem_singleton] at firstNew
          subst firstNew
          rw [entryEvent] at firstEvent
          cases Option.some.inj firstEvent
          exact (absent second secondOld secondEvent).elim
        · rw [List.mem_singleton] at firstNew secondNew
          subst firstNew secondNew
          rw [firstEmitted] at secondEmitted
          rw [Option.some.inj secondEmitted]

/-- Any owner policy covered by the risk menu has actual protected, conforming,
unique calls and sound packet content whenever its persistent risk is clear.
Foreign policies need no coverage premise. -/
theorem riskPacketFacts_roundsFrom
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (covered : ∀ past view response, response ∈ (players who past view).support →
      response ∈ bounds.riskActions (runtime setup) leaks bound who past view)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (clear : (runtime setup).persistentServiceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false) :
    OwnFreshCalls setup leaks bound execution who ∧
      FreshCallsConform setup leaks execution who ∧ OneCallPerEvent setup leaks execution who ∧
      ∀ message, message.sender = who → Emitted setup leaks execution message →
        SettledGood setup leaks execution message := by
  let app := application setup leaks
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
      rw [app.roundsFrom_succ (initialLaw setup) scheduler players count] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players count
        (by omega) prior priorMem
      rw [show horizon - count = (horizon - (count + 1)) + 1 by omega] at trace
      obtain ⟨command, selected, middle, observed, effect⟩ := round_cases setup leaks moved
      have clearMiddle : (runtime setup).persistentServiceRisk leaks bound who (middle.recall who)
          (middle.observe app who) = false := by
        rcases effect with ⟨_, rfl⟩ | ⟨responder, _, response, _, rfl⟩
        · exact clear
        · exact (runtime setup).persistentServiceRisk_clear_before_respond leaks bound middle
            responder who response clear
      have clearPrior := (runtime setup).persistentServiceRisk_clear_before_environment leaks bound
        who clearMiddle observed
      obtain ⟨calls, conform, once, good⟩ := ih (by omega) prior priorMem clearPrior
      obtain ⟨atTurn, slots⟩ := riskCanonicalSlots_roundsFrom bounds bound scheduler players who
        covered count prior priorMem clearPrior
      obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
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
          (settledFacts_history (initialLaw setup) horizon scheduler trace) observed middleTrace
          who callsMiddle conformMiddle onceMiddle authored emittedBefore
      rcases effect with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
      · exact ⟨callsMiddle, conformMiddle, onceMiddle, goodMiddle⟩
      · rw [active] at middleTrace
        by_cases same : responder = who
        · subst responder
          have member := covered _ _ response chosen
          have menuClear := (runtime setup).serviceRisk_clear_before_respond leaks bound middle who
            response clear
          rw [bounds.riskActions_of_clear (runtime setup) leaks bound who _ _ menuClear] at member
          have atMiddle : OwnSubmissionsAtTurn setup leaks middle who := by
            unfold OwnSubmissionsAtTurn
            rw [recallEq]
            exact atTurn
          have slotsMiddle := canonicalSlotsUsed_environment observed who slots
          obtain ⟨callsNext, conformNext, onceNext⟩ := clearCanonicalResponse_packetFacts bounds
            bound middleTrace atMiddle slotsMiddle callsMiddle conformMiddle onceMiddle response
            member clear
          refine ⟨callsNext, conformNext, onceNext, ?_⟩
          apply owner_good_response (settledFacts_history (initialLaw setup) horizon scheduler
            middleTrace) who who response goodMiddle
          intro _ material submitted
          let message : Message Player (WitnessedPacket (graph setup)) :=
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
          · apply owner_good_response (settledFacts_history (initialLaw setup) horizon scheduler
              middleTrace) who responder response goodMiddle
            intro equal
            exact (same equal).elim

/-- A legal risk-menu prefix supplies all owner packet facts from its actual
trace. Earlier silence is allowed, and only persistent owner clarity is needed. -/
theorem riskPacketFacts_history
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (control : (application setup leaks).Control)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player)
    (clear : (runtime setup).persistentServiceRisk leaks bound who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) = false) :
    OwnFreshCalls setup leaks bound control.execution who ∧
      FreshCallsConform setup leaks control.execution who ∧
      OneCallPerEvent setup leaks control.execution who ∧
      ∀ message, message.sender = who → Emitted setup leaks control.execution message →
        SettledGood setup leaks control.execution message := by
  let app := application setup leaks
  let menu := bounds.riskMenu (runtime setup) leaks bound
  have covered : ∀ past view response,
      response ∈ (menu.uniformResponses who past view).support →
        response ∈ bounds.riskActions (runtime setup) leaks bound who past view := by
    intro past view response supported
    exact (menu.uniformResponses_support who past view response).mp supported
  have supported := menu.roundSupported_uniform (initialLaw setup) horizon scheduler trace
  have rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler trace
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
      have clearPrior := (runtime setup).persistentServiceRisk_clear_before_environment leaks bound
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
      obtain ⟨priorTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
        menu.uniformResponses count (by omega) prior priorMem
      rw [← active] at rawTrace
      exact (good message authored emittedBefore).owner_environment contract.inclusion
        (settledFacts_history (initialLaw setup) horizon scheduler priorTrace) moved rawTrace who
        callsNext conformNext onceNext authored emittedBefore

end Vegas
