/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingProperBinding
import Vegas.Examples.CommitSeedSignallingPublicationChoice
import Vegas.Pending.PhaseSignedBindings
import Vegas.Pending.PhaseRecordedCountedRequest
import Vegas.Pending.PhaseFailureCoverage
import Interaction.ReactiveRecordedResponse
import Interaction.ReactiveRecovery

/-! # Successful current binding values from original proper-policy records -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem fixed_late_binding_response_result
    (selected : app.Scheduler) (control : app.Control)
    (trace : (countedMenu.protocol initial horizon selected).Trace (some control))
    (owner : Player) (event : graph.EventId)
    (binding : graph.outputLayout event = .binding owner .bool)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, event⟩)
    (response : app.Action)
    (supported : response ∈ (fixedLatePolicy owner (control.execution.recall owner)
      (control.execution.observe app owner)).support)
    (nonempty : response.transmission ≠ none) :
    ∃ serial,
      response = phaseBindingResponse runtime leaks owner event .bool (.success true) serial ∧
      control.execution.application.current.native.candidates.lookup (owner, .prepared serial) =
        .fresh := by
  classical
  have proper : response ∈ (properPolicy fixedLateRule owner (control.execution.recall owner)
      (control.execution.observe app owner)).support := by
    unfold fixedLatePolicy at supported
    split at supported
    · have silent := congrArg (fun action : app.Action => action.transmission)
        ((PMF.mem_support_pure_iff _ _).mp supported)
      exact (nonempty silent).elim
    · exact supported
  let results : List app.PlayerEntry → app.PlayerView →
      PMF (PublicationResult (simpleExpr.Val .bool)) := fun past view =>
    (trueBindingLaw owner event .bool binding past view).map PublicationResult.success
  have constant (past : List app.PlayerEntry) (view : app.PlayerView) :
      results past view = PMF.pure (.success true) := by
    simp only [results, trueBindingLaw, PMF.pure_map]
  have valid := raw_native_valid selected control
    (countedMenu.toRawTrace initial horizon selected trace)
  have service := phaseCountServicePolicy_binding setup .concurrentReveals runtime leaks bounds
    trueBindingLaw fixedLateRule 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num)
    control.execution valid owner event .bool binding request
  change properPolicy fixedLateRule owner _ _ = _ at service
  have encoded : response ∈ (PhaseCount.phaseBindingPolicy runtime leaks bounds owner event .bool
      results (control.execution.recall owner) (control.execution.observe app owner)).support := by
    rw [service] at proper
    dsimp only [PhaseCount.bindingServiceReference, PhaseCount.bindingServiceBase,
      PhaseCount.bindingResultEncoder] at proper
    simp only [zero_add, mix_zero] at proper
    split at proper
    · exact proper
    · split at proper
      · exact proper
      · have silent := congrArg (fun action : app.Action => action.transmission)
          ((PMF.mem_support_pure_iff _ _).mp proper)
        exact (nonempty silent).elim
  unfold PhaseCount.phaseBindingPolicy at encoded
  split at encoded
  · have silent := congrArg (fun action : app.Action => action.transmission)
      ((PMF.mem_support_pure_iff _ _).mp encoded)
    exact (nonempty silent).elim
  · rename_i serial chosen
    split at encoded
    · rw [constant, PMF.pure_map, PMF.mem_support_pure_iff] at encoded
      exact ⟨serial, encoded, reactiveFreshSlot_spec
        (control.execution.observe app owner).application.1 serial chosen⟩
    · have silent := congrArg (fun action : app.Action => action.transmission)
        ((PMF.mem_support_pure_iff _ _).mp encoded)
      exact (nonempty silent).elim

private theorem fixed_late_binding_record_true
    (seed : Seeds) (control : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some control))
    (owner : Player)
    (ownConsistent : (fixedLatePolicy owner).Consistent (control.execution.recall owner))
    (entry : app.PlayerEntry) (recorded : entry ∈ control.execution.recall owner)
    (material : WitnessedSubmission graph)
    (transmitted : entry.action.transmission = some material)
    (candidate : Handle graph)
    (materialCall : material.call.packet = .commitment (bindingEvent owner) candidate) :
    ∃ serial,
      entry.action = phaseBindingResponse runtime leaks owner (bindingEvent owner) .bool
        (.success true) serial ∧
      entry.beforeView.application.1.candidates (.prepared serial) = .fresh := by
  classical
  obtain ⟨before, prior, _prefix, _acting, viewed, chosen, _suffix, _past⟩ :=
    countedMenu.recorded_response_supported initial horizon (family seed) control trace owner
      (fixedLatePolicy owner) ownConsistent entry recorded
  obtain ⟨coordinate, publicRequest, _attempt, addressed⟩ :=
    PhaseCount.recorded_material_request runtime leaks bounds plan
      (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
      (setup.initialLaw.map encodeInputs) horizon (family seed) control trace owner entry recorded
        material transmitted
  rw [viewed] at publicRequest
  have valid := raw_native_valid (family seed) before
    (countedMenu.toRawTrace initial horizon (family seed) prior)
  have sourceRequest :=
    (before.execution.application.requests_publicView valid owner coordinate).mp publicRequest
  have eventEq : coordinate.event = bindingEvent owner := by
    rw [materialCall] at addressed
    exact (Option.some.inj addressed).symm
  have coordinateEq : coordinate =
      ⟨before.execution.application.attempt, bindingEvent owner⟩ := by
    cases coordinate with
    | mk attempt event => exact congrArg₂ CommitAttemptEvent.mk sourceRequest.1 eventEq
  have sourceRequested : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, bindingEvent owner⟩ := coordinateEq ▸ sourceRequest
  obtain ⟨serial, declared, fresh⟩ := fixed_late_binding_response_result (family seed) before prior
    owner (bindingEvent owner) (bindingEvent_layout owner) sourceRequested entry.action chosen
      (by rw [transmitted]; exact Option.some_ne_none _)
  have entryFresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh := by
    rw [viewed]
    exact fresh
  exact ⟨serial, declared, entryFresh⟩

/-- An accepted own binding in any later phase retains the result of an
actual original proper-policy submission. Signed provenance identifies its
record even after its commitment namespace has retired. -/
theorem accepted_binding_success_of_true_records
    (menu : app.ResponseMenu) (seed : Seeds) (control : app.Control)
    (trace : (menu.protocol initial horizon (family seed)).Trace (some control))
    (owner : Player)
    (records : ∀ entry ∈ control.execution.recall owner,
      ∀ material : WitnessedSubmission graph, entry.action.transmission = some material →
      ∀ candidate, material.call.packet = .commitment (bindingEvent owner) candidate →
      ∃ serial,
        entry.action = phaseBindingResponse runtime leaks owner (bindingEvent owner) .bool
          (.success true) serial ∧
        entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (candidate : Handle graph)
    (accepted : control.execution.application.current.native.accepted (.inr (bindingEvent owner)) =
      some candidate) :
    control.execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success true)) := by
  classical
  have raw := menu.toRawTrace initial horizon (family seed) trace
  have bindings := phaseBindingRecord_history runtime leaks plan (setup.initialLaw.map encodeInputs)
    horizon (family seed) raw
  obtain ⟨_payload, typed⟩ := bindings.active.accepted_typed (.inr (bindingEvent owner))
    candidate accepted
  have owned : candidate.1 = owner :=
    (EventField.binding.inj (typed.symm.trans (bindingEvent_layout owner))).1
  have signed := phaseSignedBindings_history runtime leaks plan (setup.initialLaw.map encodeInputs)
    horizon (family seed) raw
  obtain ⟨message, output, sender, named⟩ := signed.2.1.2 (bindingEvent owner) candidate accepted
  rw [owned] at output
  have senderOwner : message.sender = owner := sender.trans owned
  change message ∈ app.outputs (control.execution.recall owner) at output
  have inputs := app.history_inputRecall initial horizon (family seed) raw
  change control.execution.InputRecall app at inputs
  have input : message ∈ control.execution.network.inputs := by
    rw [← inputs owner] at output
    exact (List.mem_filter.mp output).1
  obtain ⟨entry, recorded, material, transmitted, _emitted, state, known, packet⟩ :=
    (app.history_provenance initial horizon (family seed) raw).inputs message input
  rw [senderOwner] at recorded
  have materialCall : material.call.packet = .commitment (bindingEvent owner) candidate := by
    have exactCall := phase_emit_call state message.sender known material
    change state.emit message.sender known material = message.payload at packet
    exact exactCall.symm.trans
      ((congrArg (fun payload => payload.packet.call) packet).trans named)
  obtain ⟨serial, declared, entryFresh⟩ := records entry recorded material transmitted candidate
    materialCall
  have sameMaterial := congrArg (fun action : app.Action => action.transmission) declared
  rw [transmitted] at sameMaterial
  have sameCall := congrArg (fun actual : app.Submission => actual.call.packet)
    (Option.some.inj sameMaterial)
  change material.call.packet =
    .commitment (bindingEvent owner) (owner, .prepared serial) at sameCall
  rw [materialCall] at sameCall
  have sameHandle : candidate = (owner, .prepared serial) := (Payload.commitment.inj sameCall).2
  have meaning := phase_recorded_binding_result runtime leaks initial horizon (family seed) raw
    owner (bindingEvent owner) .bool (.success true) serial entry recorded declared entryFresh
  have fixed := (State.bindingResult_eq_success_iff
    control.execution.application.current.native (owner, .prepared serial) .bool true).mp meaning
  have stored := bindings.active.opening_stored (ownBindingRef owner) (owner, .prepared serial)
    true (sameHandle ▸ accepted) fixed
  fin_cases owner <;> exact stored

/-- Proper-policy consistency establishes each factual TRUE preparation
record used by accepted-binding readback. -/
theorem fixed_late_accepted_binding_success_of_consistent
    (seed : Seeds) (control : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some control))
    (owner : Player)
    (ownConsistent : (fixedLatePolicy owner).Consistent (control.execution.recall owner))
    (candidate : Handle graph)
    (accepted : control.execution.application.current.native.accepted (.inr (bindingEvent owner)) =
      some candidate) :
    control.execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success true)) := by
  apply accepted_binding_success_of_true_records countedMenu seed control trace owner ?_ candidate
    accepted
  intro entry recorded material transmitted handle materialCall
  exact fixed_late_binding_record_true seed control trace owner ownConsistent entry recorded
    material transmitted handle materialCall

/-- The consistent own record required by accepted-binding readback follows
from the literal initialized proper-policy experiment. -/
theorem initialized_fixed_late_accepted_binding_success
    (players : Player → app.Policy) (seed : Seeds) (count : Nat) (control : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some control))
    (reached : control.execution ∈
      (app.runRounds (family seed) players count initialExecution).support)
    (owner : Player) (policy : players owner = fixedLatePolicy owner)
    (candidate : Handle graph)
    (accepted : control.execution.application.current.native.accepted (.inr (bindingEvent owner)) =
      some candidate) :
    control.execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success true)) := by
  have consistent := (app.consistentRecall_policyInvariant players).runRounds (family seed) count
    initialExecution control.execution (fun _ => .nil) reached
  have focal := consistent owner
  rw [policy] at focal
  exact fixed_late_accepted_binding_success_of_consistent seed control trace owner focal candidate
    accepted

/-- An active owner at a completed binding has a true current value under
the same initialized fixed-late deviation, including after restore and retry.
Completion and public failure coverage derive its accepted association. -/
theorem completed_binding_success_of_true_records
    (menu : app.ResponseMenu) (seed : Seeds) (control : app.Control)
    (trace : (menu.protocol initial horizon (family seed)).Trace (some control))
    (owner : Player)
    (records : ∀ entry ∈ control.execution.recall owner,
      ∀ material : WitnessedSubmission graph, entry.action.transmission = some material →
      ∀ candidate, material.call.packet = .commitment (bindingEvent owner) candidate →
      ∃ serial,
        entry.action = phaseBindingResponse runtime leaks owner (bindingEvent owner) .bool
          (.success true) serial ∧
        entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (completed : bindingEvent owner ∈
      control.execution.application.current.native.config.cut.completed)
    (active : owner ∉ control.execution.application.current.excluded) :
    control.execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success true)) := by
  classical
  have raw := menu.toRawTrace initial horizon (family seed) trace
  have coverage := phaseFailureCoverage_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon (family seed) raw
  have present : control.execution.application.current.native.accepted
      (.inr (bindingEvent owner)) ≠ none := by
    intro vacant
    have missed := (control.execution.application.current.native.publicView_missedBinding
      (bindingEvent owner) owner .bool (bindingEvent_layout owner)).mpr ⟨completed, vacant⟩
    have acting : graph.actor? (bindingEvent owner) = some owner := by fin_cases owner <;> rfl
    exact active (coverage.active.covered (bindingEvent owner) owner acting (Or.inl missed))
  obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
  exact accepted_binding_success_of_true_records menu seed control trace owner records candidate
    accepted

/-- Proper-policy consistency establishes the factual preparation records
at a completed current binding, regardless of its retired origin. -/
theorem fixed_late_completed_binding_success_of_consistent
    (seed : Seeds) (control : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some control))
    (owner : Player)
    (ownConsistent : (fixedLatePolicy owner).Consistent (control.execution.recall owner))
    (completed : bindingEvent owner ∈
      control.execution.application.current.native.config.cut.completed)
    (active : owner ∉ control.execution.application.current.excluded) :
    control.execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success true)) := by
  apply completed_binding_success_of_true_records countedMenu seed control trace owner ?_ completed
    active
  intro entry recorded material transmitted handle materialCall
  exact fixed_late_binding_record_true seed control trace owner ownConsistent entry recorded
    material transmitted handle materialCall

/-- The initialized experiment derives the complete proper own record used
by completed-binding readback, without a resampled continuation policy. -/
theorem initialized_fixed_late_completed_binding_success
    (players : Player → app.Policy) (seed : Seeds) (count : Nat) (control : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some control))
    (reached : control.execution ∈
      (app.runRounds (family seed) players count initialExecution).support)
    (owner : Player) (policy : players owner = fixedLatePolicy owner)
    (completed : bindingEvent owner ∈
      control.execution.application.current.native.config.cut.completed)
    (active : owner ∉ control.execution.application.current.excluded) :
    control.execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success true)) := by
  have consistent := (app.consistentRecall_policyInvariant players).runRounds (family seed) count
    initialExecution control.execution (fun _ => .nil) reached
  have focal := consistent owner
  rw [policy] at focal
  exact fixed_late_completed_binding_success_of_consistent seed control trace owner focal completed
    active

end Vegas.Examples.CommitSeedSignalling
