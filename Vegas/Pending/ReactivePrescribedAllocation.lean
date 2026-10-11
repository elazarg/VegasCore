/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCandidateBudget
import Vegas.Pending.ReactiveSafety
import Vegas.Pending.ReactivePolicyFacts
import Vegas.Pending.ReactiveBindingAllocation
import Vegas.Pending.ReactiveSampledResolutionSettlement
import Interaction.ReactivePolicyInvariant
import Vegas.Pending.ReactiveResponseSampling
import Vegas.Pending.ReactiveEventStability
import Vegas.Pending.ReactiveSettledVerdict
import Vegas.Pending.ReactiveAcceptedIntentionRecall
import Vegas.Pending.ReactiveOriginalResponseStability
import Vegas.Pending.ReactiveBindingResources
import Vegas.Pending.ReactiveFrontierSampling
import Vegas.Pending.ReactiveSampledAcceptance

/-! # Canonical prepared allocation through actual prescribed play -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Existing submitted slots enumerate precisely the occupied prepared prefix. -/
def PrescribedCandidateAllocation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ who,
    let slots := runtime.submittedCandidateSlots leaks (execution.recall who)
    slots = List.range slots.length ∧ ∀ serial,
      execution.application.candidates.lookup (who, .prepared serial) = .fresh ↔
        slots.length ≤ serial

theorem prescribedCandidateAllocation_initial (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) : runtime.PrescribedCandidateAllocation leaks
      (.initial (runtime.reactiveApplication leaks) (State.initial inputs)) := by
  intro who
  constructor
  · rfl
  · intro serial
    simp [submittedCandidateSlots, ReactiveApplication.Execution.initial,
      State.initial_candidate]

theorem PrescribedCandidateAllocation.candidateRecall (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (allocated : runtime.PrescribedCandidateAllocation leaks execution) :
    runtime.CandidateRecall leaks execution := by
  intro who serial absent
  have bounds := allocated who
  rw [bounds.1, List.mem_range] at absent
  exact (bounds.2 serial).mpr (by omega)

/-- Authentic inclusion cannot occupy a slot absent from its author's recall;
 already occupied slots retain their immutable meaning through every command. -/
theorem PrescribedCandidateAllocation.environment (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (allocated : runtime.PrescribedCandidateAllocation leaks execution)
    (provenance : execution.Provenance (runtime.reactiveApplication leaks))
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : runtime.PrescribedCandidateAllocation leaks next := by
  have recall := (runtime.reactiveApplication leaks).environmentStep_recall execution next
    command reached
  have unused := runtime.candidateRecall_environment leaks execution next command
    (allocated.candidateRecall runtime leaks execution) provenance reached
  intro who
  have bounds := allocated who
  simp only [recall]
  refine ⟨bounds.1, ?_⟩
  intro serial
  by_cases within : serial < (runtime.submittedCandidateSlots leaks
      (execution.recall who)).length
  · have fixed : execution.application.candidates.lookup (who, .prepared serial) ≠ .fresh := by
      intro fresh
      have lower := (bounds.2 serial).mp fresh
      omega
    have same := runtime.reactive_environment_candidate_fixed leaks execution next command
      (who, .prepared serial) fixed reached
    rw [same]
    exact bounds.2 serial
  · constructor
    · intro _
      omega
    · intro _
      apply unused who serial
      rw [recall, bounds.1, List.mem_range]
      exact within



private theorem reactiveDecision_prepared_response (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (action : graph.Action event)
    (view : PlayerView graph) (serial : Nat)
    (slot : runtime.responseCandidateSlot leaks
      (runtime.reactiveDecision leaks who event action view) = some serial) :
    ∃ payload result, runtime.reactiveDecision leaks who event action view =
        runtime.reactiveBinding leaks who event payload result serial ∧
      reactiveFreshSlot view = some serial := by
  cases node : nodeView graph event with
  | sample => simp [responseCandidateSlot, reactiveDecision, node] at slot
  | bind owner payload outputEq codeEq =>
      cases selected : reactiveFreshSlot view with
      | none => simp [responseCandidateSlot, reactiveDecision, node, selected] at slot
      | some allocated =>
          have equal : allocated = serial := by
            simpa [responseCandidateSlot, reactiveDecision, node, selected,
              Payload.preparedCommitment?] using slot
          subst allocated
          exact ⟨payload, cast (congrArg EventField.Action outputEq) action,
            runtime.reactiveDecision_binding_eq leaks who owner event payload outputEq codeEq
              node action view serial selected, rfl⟩
  | resolve owner payload binding checks outputEq codeEq =>
      cases transmitted : (runtime.reactiveDecision leaks who event action view).transmission with
      | none => simp [responseCandidateSlot, transmitted] at slot
      | some material =>
          obtain ⟨candidate, value, packet⟩ :=
            runtime.reactiveDecision_resolution_transmitted_packet leaks who owner event payload
              binding checks outputEq codeEq node action view material transmitted
          simp [responseCandidateSlot, transmitted, packet, Payload.preparedCommitment?] at slot

/-- Every supported prepared-slot response is an authentic binding declaration
 at the least genuinely fresh slot of its current private view. -/
theorem prescribedReactivePolicy_prepared_response (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (policy : graph.BehavioralPolicy who) (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈ (runtime.prescribedReactivePolicy leaks who policy
      (execution.recall who) (execution.observe (runtime.reactiveApplication leaks) who)).support)
    (serial : Nat) (slot : runtime.responseCandidateSlot leaks action = some serial) :
    ∃ event payload result, action = runtime.reactiveBinding leaks who event payload result serial ∧
      reactiveFreshSlot (execution.observe
        (runtime.reactiveApplication leaks) who).application = some serial := by
  rw [runtime.prescribedReactivePolicy_apply] at supported
  obtain ⟨intentions, _, issued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨⟨physical, saved⟩, produced, image⟩ := PMF.support_map .. ▸ issued
  dsimp only at image
  subst physical
  unfold prescribedReactiveResponse at produced
  split at produced
  · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at produced
    simp [produced.1, responseCandidateSlot] at slot
  · rename_i event turn
    split at produced
    · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at produced
      simp [produced.1, responseCandidateSlot] at slot
    · split at produced
      · split at produced
        · split at produced
          · obtain ⟨choice, _, equal⟩ := PMF.support_map .. ▸ produced
            have actionEq := congrArg Prod.fst equal
            dsimp only at actionEq
            rw [← actionEq] at slot ⊢
            obtain ⟨payload, result, binding, allocated⟩ :=
              reactiveDecision_prepared_response runtime leaks who event choice _ serial slot
            exact ⟨event, payload, result, binding, allocated⟩
          · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at produced
            simp [produced.1, responseCandidateSlot] at slot
        · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at produced
          simp [produced.1, responseCandidateSlot] at slot
      · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at produced
        simp [produced.1, responseCandidateSlot] at slot



theorem PrescribedCandidateAllocation.freshSlot (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (allocated : runtime.PrescribedCandidateAllocation leaks execution) (who : Player) :
    reactiveFreshSlot (execution.observe (runtime.reactiveApplication leaks) who).application =
      some (runtime.submittedCandidateSlots leaks (execution.recall who)).length := by
  classical
  let count := (runtime.submittedCandidateSlots leaks (execution.recall who)).length
  have bounds := (allocated who).2
  have fresh : ∃ serial, execution.application.candidates.lookup (who, .prepared serial) =
      .fresh := ⟨count, (bounds count).mpr le_rfl⟩
  unfold reactiveFreshSlot
  change (if available : ∃ serial,
      execution.application.candidates.lookup (who, .prepared serial) = .fresh then
    some (Nat.find available) else none) = some count
  rw [dite_eq_left fresh]
  apply congrArg some
  exact Nat.le_antisymm (Nat.find_min' fresh ((bounds count).mpr le_rfl))
    ((bounds _).mp (Nat.find_spec fresh))

/-- Actual prescribed callbacks allocate successive prepared slots exactly once;
 other packets and silent callbacks allocate no prepared slot. -/
theorem PrescribedCandidateAllocation.respond (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (allocated : runtime.PrescribedCandidateAllocation leaks execution)
    (who : Player) (policy : graph.BehavioralPolicy who)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈ (runtime.prescribedReactivePolicy leaks who policy
      (execution.recall who) (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    runtime.PrescribedCandidateAllocation leaks
      (execution.respond (runtime.reactiveApplication leaks) who action) := by
  let app := runtime.reactiveApplication leaks
  cases selected : runtime.responseCandidateSlot leaks action with
  | none =>
      have noSlot : ∀ observer serial,
          (execution.respond app who action).application.candidates.lookup
            (observer, .prepared serial) =
          execution.application.candidates.lookup (observer, .prepared serial) := by
        intro observer serial
        cases action with
        | mk transmission =>
          cases transmission with
          | none => rfl
          | some material =>
              apply submission_candidate_other execution.application who observer serial
                material.call
              right
              have absent : material.call.packet.preparedCommitment? = none := by
                simpa [responseCandidateSlot] using selected
              rw [absent]
              simp
      intro observer
      have slotsSame : runtime.submittedCandidateSlots leaks
          ((execution.respond app who action).recall observer) =
          runtime.submittedCandidateSlots leaks (execution.recall observer) := by
        by_cases same : observer = who
        · subst observer
          rw [runtime.submittedCandidateSlots_respond, selected]
          simp
        · rw [app.respond_recall_other execution who observer same action]
      rw [slotsSame]
      exact ⟨(allocated observer).1, fun serial =>
        (noSlot observer serial) ▸ (allocated observer).2 serial⟩
  | some serial =>
      obtain ⟨event, payload, result, actionEq, fresh⟩ :=
        runtime.prescribedReactivePolicy_prepared_response leaks execution who policy action
          supported serial selected
      have serialEq : serial =
          (runtime.submittedCandidateSlots leaks (execution.recall who)).length :=
        Option.some.inj (fresh.symm.trans (allocated.freshSlot runtime leaks execution who))
      subst serial
      subst action
      intro observer
      dsimp only
      by_cases same : observer = who
      · subst observer
        let count := (runtime.submittedCandidateSlots leaks (execution.recall who)).length
        have slots := runtime.submittedCandidateSlots_respond leaks execution who
          (runtime.reactiveBinding leaks who event payload result count)
        have responseSlot : runtime.responseCandidateSlot leaks
            (runtime.reactiveBinding leaks who event payload result count) = some count := rfl
        rw [responseSlot] at slots
        simp only [Option.toList_some] at slots
        rw [slots]
        constructor
        · rw [(allocated who).1]
          simp only [List.length_append, List.length_singleton, List.length_range]
          exact List.range_succ.symm
        · intro query
          have equivalent := runtime.submitted_binding_fresh_iff leaks execution who event count
            (match result with | .failure => none | .success value => some ⟨payload, value⟩)
            (.prepared query)
          have old := (allocated who).2 query
          change execution.application.candidates.lookup (who, .prepared query) = .fresh ↔
            count ≤ query at old
          simp only [List.length_append, List.length_singleton]
          change (execution.respond app who
            (runtime.reactiveBinding leaks who event payload result
              count)).application.candidates.lookup
              (who, .prepared query) = .fresh ↔ count + 1 ≤ query
          cases result
          all_goals
            dsimp only at equivalent
            constructor
            · intro occupied
              obtain ⟨different, available⟩ := equivalent.mp occupied
              have lower := old.mp available
              have apart : query ≠ count := fun equal => different (congrArg Slot.prepared equal)
              omega
            · intro bound
              apply equivalent.mpr
              refine ⟨?_, old.mpr (by omega)⟩
              intro equal
              have same := Slot.prepared.inj equal
              omega
      · rw [app.respond_recall_other execution who observer same]
        refine ⟨(allocated observer).1, ?_⟩
        intro query
        have candidates := submission_candidate_other execution.application who observer query
          ⟨.commitment event (who, .prepared
            (runtime.submittedCandidateSlots leaks (execution.recall who)).length),
            match result with | .failure => none | .success value => some ⟨payload, value⟩⟩
          (Or.inl same)
        change (submitStep _ who _).candidates.lookup (observer, .prepared query) = .fresh ↔ _
        cases result <;>
          simpa only [reactiveBinding] using
            (Iff.of_eq (congrArg (fun value => value = .fresh) candidates)).trans
              ((allocated observer).2 query)



/-- The actual prescribed profile preserves allocation and authentic envelope
 provenance through every supported callback and scheduler command. -/
theorem prescribedCandidateAllocation_policyInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile) :
    (runtime.reactiveApplication leaks).PolicyInvariant
      (fun who => runtime.prescribedReactivePolicy leaks who (profile who))
      (fun execution => runtime.PrescribedCandidateAllocation leaks execution ∧
        execution.Provenance (runtime.reactiveApplication leaks)) := by
  constructor
  · intro execution who action valid supported
    exact ⟨valid.1.respond runtime leaks execution who (profile who) action supported,
      (runtime.reactiveApplication leaks).respond_provenance execution who action valid.2⟩
  · intro execution next command valid reached
    exact ⟨valid.1.environment runtime leaks execution next valid.2 command reached,
      (runtime.reactiveApplication leaks).environment_provenance execution next command
        valid.2 reached⟩

/-- Every initialized actual prescribed run uses consecutive prepared slots,
 with arbitrary opponents' graph policies and an arbitrary native scheduler. -/
theorem prescribedCandidateAllocation_runRounds (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile) (inputs : graph.Inputs)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat)
    (next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ ((runtime.reactiveApplication leaks).runRounds scheduler
      (fun who => runtime.prescribedReactivePolicy leaks who (profile who)) count
        (.initial (runtime.reactiveApplication leaks) (State.initial inputs))).support) :
    runtime.PrescribedCandidateAllocation leaks next := by
  exact ((runtime.prescribedCandidateAllocation_policyInvariant leaks profile).runRounds scheduler
    count _ next ⟨runtime.prescribedCandidateAllocation_initial leaks inputs,
      MessageNetwork.Satisfies.empty⟩ reached).1

private theorem reactiveDecision_binding_count (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (action : graph.Action event)
    (view : PlayerView graph) (actor : graph.actor? event = some who)
    (available : ∃ serial, reactiveFreshSlot view = some serial) :
    (runtime.responseCandidateSlot leaks
      (runtime.reactiveDecision leaks who event action view)).toList.length =
      if bindingOwnedBy graph who event then 1 else 0 := by
  cases node : nodeView graph event with
  | sample payload law outputEq codeEq =>
      simp [responseCandidateSlot, reactiveDecision, node, bindingOwnedBy, outputEq]
  | bind owner payload outputEq codeEq =>
      have equal : owner = who := Option.some.inj
        ((graph.actor?_of_outputLayout_binding outputEq).symm.trans
        actor)
      subst owner
      obtain ⟨serial, selected⟩ := available
      simp [responseCandidateSlot, reactiveDecision, node, selected, Payload.preparedCommitment?,
        bindingOwnedBy, outputEq]
  | resolve owner payload binding checks outputEq codeEq =>
      cases transmitted : (runtime.reactiveDecision leaks who event action view).transmission with
      | none => simp [responseCandidateSlot, transmitted, bindingOwnedBy, outputEq]
      | some material =>
          obtain ⟨candidate, value, packet⟩ :=
            runtime.reactiveDecision_resolution_transmitted_packet leaks who owner event payload
              binding checks outputEq codeEq node action view material transmitted
          simp [responseCandidateSlot, transmitted, packet, Payload.preparedCommitment?,
            bindingOwnedBy, outputEq]

/-- Every genuine sampled binding, including failure, accounts for exactly one
 prepared-slot transmission; private resolution intentions account for none. -/
theorem prescribedReactivePosterior_binding_count (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support)
    (available : ∀ entry ∈ history, ∃ serial,
      reactiveFreshSlot entry.beforeView.application = some serial) :
    (runtime.submittedCandidateSlots leaks history).length =
      (intentions.filterMap id).countP
        (fun remembered => bindingOwnedBy graph who remembered.event) :=
    by
  induction consistent generalizing intentions with
  | nil =>
      have empty := runtime.prescribedReactivePosterior_length leaks who policy
        .nil intentions supported
      have zero : intentions = [] := List.eq_nil_of_length_eq_zero empty
      simp [zero, submittedCandidateSlots]
  | @snoc history latest consistent positive ih =>
      obtain ⟨previous, prior, saved, memoryEq, produced⟩ :=
        runtime.prescribedReactivePosterior_snoc_support leaks who policy history latest
          positive intentions supported
      have preceding := ih previous prior (fun entry retained => available entry
        (List.mem_append_left _ retained))
      have slotsAppend : runtime.submittedCandidateSlots leaks (history ++ [latest]) =
          runtime.submittedCandidateSlots leaks history ++
            (runtime.responseCandidateSlot leaks latest.action).toList := by
        simp only [submittedCandidateSlots, List.map_append, List.map_singleton,
          List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
        cases runtime.responseCandidateSlot leaks latest.action <;> rfl
      have increment : (runtime.responseCandidateSlot leaks latest.action).toList.length =
          (saved.toList).countP (fun remembered => bindingOwnedBy graph who remembered.event) := by
        cases saved with
        | none =>
            have silent := runtime.prescribedReactiveResponse_none_silent leaks who policy
              history previous latest.beforeView latest.action produced
            simp [responseCandidateSlot, silent]
        | some remembered =>
            have paired : (latest, some remembered) ∈ (history ++ [latest]).zip intentions := by
              rw [memoryEq, List.zip_append
                (runtime.prescribedReactivePosterior_length leaks who policy
                  consistent previous prior).symm]
              exact List.mem_append_right _ (by simp)
            have declared := runtime.prescribedReactivePosterior_decision_alignment leaks who
              policy (.snoc latest consistent positive) intentions supported latest remembered
                paired
            have owned := (runtime.prescribedReactiveResponse_some_ready leaks who policy
              history previous latest.beforeView latest.action remembered produced).2
            rw [declared]
            simpa using reactiveDecision_binding_count runtime leaks who remembered.event
              remembered.action latest.beforeView.application owned
              (available latest (List.mem_append_right _ (by simp)))
      rw [slotsAppend, List.length_append, memoryEq, List.filterMap_append, List.countP_append]
      rw [preceding]
      congr 1

private def bindingCount (config : graph.Config) (who : Player) : Nat :=
  (graph.publicObserve config).completionOrder.countP fun event =>
    match graph.outputLayout event with
    | .binding owner _ => decide (owner = who)
    | .publicData _ | .privateInput _ _ | .publication _ => false

private theorem bindingCount_cut_eq (left right : graph.Config)
    (same : left.cut = right.cut) (who : Player) :
    bindingCount left who = bindingCount right who := by
  have permutation : (left.history.map Completion.event).Perm
      (right.history.map Completion.event) :=
    (List.perm_ext_iff_of_nodup left.history_nodup right.history_nodup).mpr (by
      intro event
      rw [left.history_exact, right.history_exact, same])
  exact permutation.countP_eq _

private theorem foreign_bindingCount {who : Player} {first last : graph.Config}
    (sequence : graph.ForeignCompletionSequence who first last) :
    bindingCount last who = bindingCount first who := by
  induction sequence with
  | refl => rfl
  | snoc previous event ready owner actor foreign action value supported ih =>
      have output := (graph.nodes event).output_public_or_binding_of_actor owner actor
      have notBinding : (match graph.outputLayout event with
          | .binding actual _ => decide (actual = who)
          | .publicData _ | .privateInput _ _ | .publication _ => false) = false := by
        rcases output with visible | ⟨payload, binding⟩
        · cases field : graph.outputLayout event <;> simp [field, EventField.IsPublic] at visible ⊢
        · simp [binding, foreign]
      simpa [bindingCount, EventGraph.publicObserve, Config.complete, notBinding] using ih

/-- Pending foreign decisions do not change the fresh sampler's actual public
 binding serial; the equality follows from the operational frontier replay. -/
theorem ReactiveFrontier.fresh_bindingCount (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.RevealRelaxedOrdered)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (profile : graph.BehavioralProfile) (memories : Player → List (Option graph.Completion))
    (consistent : ∀ owner,
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (frontier : graph.Config)
    (relation : runtime.ReactiveFrontier leaks execution memories frontier)
    (who : Player) (event : graph.EventId)
    (ready : execution.application.config.cut.Ready event)
    (actor : graph.actor? event = some who)
    (fresh : event ∉ (memories who).filterMap (fun saved => saved.map Completion.event)) :
    ({execution.application with config := frontier} : State graph).publicView.bindingCount who =
      execution.application.publicView.bindingCount who := by
  obtain ⟨last, replay, same⟩ := relation.foreign_sequence runtime leaks
    ordered
    execution stable
    profile memories consistent supported frontier who event ready actor fresh
  change bindingCount frontier who = bindingCount execution.application.config who
  exact (bindingCount_cut_eq frontier last (semanticKey_cut_eq same) who).trans
    ((foreign_bindingCount replay).trans (bindingCount_cut_eq
      (runtime.originalConfig leaks execution memories)
      execution.application.config rfl who))




private theorem bindingCount_ownCompletions (config : graph.Config) (who : Player) :
    bindingCount config who = (graph.ownCompletions who config.history).countP
      (fun remembered => bindingOwnedBy graph who remembered.event) := by
  have count : ∀ history : List graph.Completion,
      (history.map Completion.event).countP (bindingOwnedBy graph who) =
        (graph.ownCompletions who history).countP
          (fun remembered => bindingOwnedBy graph who remembered.event) := by
    intro history
    induction history with
    | nil => rfl
    | cons completion rest ih =>
        by_cases owned : graph.actor? completion.event = some who
        · simpa [ownCompletions, owned, List.countP_cons] using ih
        · have unrelated : bindingOwnedBy graph who completion.event = false := by
            cases output : graph.outputLayout completion.event with
            | publicData | privateInput | publication => simp [bindingOwnedBy, output]
            | binding owner payload =>
                have different : owner ≠ who := by
                  intro equal
                  subst owner
                  exact owned (graph.actor?_of_outputLayout_binding output)
                simp [bindingOwnedBy, output, different]
          simpa [ownCompletions, owned, unrelated, List.countP_cons] using ih
  exact count config.history

/-- The initialized allocation invariant and actual posterior binding count
 establish the canonical physical prefix at a genuine fresh owned callback. -/
theorem ReactiveFrontier.fresh_preparedPrefix (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (profile : graph.BehavioralProfile) (memories : Player → List (Option graph.Completion))
    (consistent : ∀ owner,
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (control.execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (control.execution.recall owner)).support)
    (frontier : graph.Config)
    (relation : runtime.ReactiveFrontier leaks control.execution memories frontier)
    (allocated : runtime.PrescribedCandidateAllocation leaks control.execution)
    (who : Player) (event : graph.EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (actor : graph.actor? event = some who)
    (fresh : event ∉ (memories who).filterMap (fun saved => saved.map Completion.event)) :
    control.execution.application.PreparedPrefix who := by
  have counts := runtime.prescribedReactivePosterior_binding_count leaks who (profile who)
    (consistent who) (memories who) (supported who) (by
      intro entry retained
      obtain ⟨serial, _, selected⟩ := runtime.reactiveFreshSlot_recorded leaks inputs horizon
        scheduler control trace who entry retained
      exact ⟨serial, selected⟩)
  rw [← relation.intentions who, ← bindingCount_ownCompletions frontier who] at counts
  have physicalCount := relation.fresh_bindingCount runtime leaks ordered control.execution
    (runtime.entryEventStable_history leaks (inputs.map State.initial) horizon scheduler trace)
    profile memories consistent supported frontier who event ready actor fresh
  have equal : (runtime.submittedCandidateSlots leaks (control.execution.recall who)).length =
      control.execution.application.publicView.bindingCount who := counts.trans physicalCount
  intro serial
  rw [← equal]
  exact (allocated who).2 serial

/-- The existing prepared-prefix invariant strengthens actual sampled-call
 acceptance to the canonical packet condition checked by the source audit. -/
theorem reactiveDecision_emitted_conforming (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (who : Player) (event : graph.EventId)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (actor : graph.actor? event = some who)
    (prepared : execution.application.PreparedPrefix who)
    (action : graph.Action event) (material : WitnessedSubmission graph)
    (transmitted : (runtime.reactiveDecision leaks who event action
      (execution.observe (runtime.reactiveApplication leaks) who).application).transmission =
        some material) :
    runtime.freshServiceEnvelope execution.application.publicView
      ⟨(who, execution.network.nextSerial who),
        material.emit ((runtime.reactiveApplication leaks).submit execution.application who
          material) who (execution.network.known who)⟩ := by
  have acceptable := runtime.reactiveDecision_emitted_acceptable leaks execution valid who event
    ready timely actor action material transmitted
  let state : State graph := execution.application
  let view : PlayerView graph :=
    (execution.observe (runtime.reactiveApplication leaks) who).application
  cases node : nodeView graph event with
  | sample payload law outputEq codeEq =>
      simp only [reactiveDecision, node] at transmitted
      cases transmitted
  | bind owner payload outputEq codeEq =>
      simp only [reactiveDecision, node] at transmitted
      obtain ⟨serial, selected, same⟩ := Option.map_eq_some_iff.mp transmitted
      subst material
      have counted := prepared.freshSlot runtime leaks
      have serialEq : serial = state.publicView.bindingCount who :=
        Option.some.inj (selected.symm.trans counted)
      change state.publicView.BindingIncludable runtime
        ⟨(who, execution.network.nextSerial who), .commitment event (who, .prepared serial)⟩ ∧ _
        at acceptable
      change state.publicView.BindingIncludable runtime
        ⟨(who, execution.network.nextSerial who), .commitment event (who, .prepared serial)⟩ ∧
        ((who, .prepared serial) : Handle graph) =
          (who, .prepared (state.publicView.bindingCount who)) ∧
        none = none ∧ _
      exact ⟨acceptable.1, by rw [serialEq], rfl, acceptable.2⟩
  | resolve owner payload binding checks outputEq codeEq =>
      obtain ⟨candidate, value, packet⟩ :=
        runtime.reactiveDecision_resolution_transmitted_packet leaks who owner event payload
          binding checks outputEq codeEq node action _ material transmitted
      simpa only [freshServiceAcceptable, WitnessedSubmission.emit, packet] using acceptable

/-- Supported actual prescribed responses inherit canonical audit conformance
 from the genuine physical prepared prefix. -/
theorem prescribedReactiveResponse_emitted_conforming (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (material : WitnessedSubmission graph) (remembered : graph.Completion)
    (supported : (⟨some material⟩, some remembered) ∈
      (runtime.prescribedReactiveResponse leaks who policy history intentions
        (execution.observe (runtime.reactiveApplication leaks) who)).support)
    (timely : execution.application.WithinDeadline runtime remembered.event)
    (prepared : execution.application.PreparedPrefix who) :
    runtime.freshServiceEnvelope execution.application.publicView
      ⟨(who, execution.network.nextSerial who),
        material.emit ((runtime.reactiveApplication leaks).submit execution.application who
          material) who (execution.network.known who)⟩ := by
  obtain ⟨ready, actor⟩ := runtime.prescribedReactiveResponse_some_ready leaks who policy
    history intentions _ _ remembered supported
  have decision := (runtime.prescribedReactiveResponse_some_fresh leaks who policy history
    intentions _ _ remembered supported).2.2
  apply runtime.reactiveDecision_emitted_conforming leaks execution valid who remembered.event
    ((execution.application.publicView_eventReady remembered.event).mp ready) timely actor
    prepared remembered.action material
  exact (congrArg ReactiveApplication.Action.transmission decision).symm

end Vegas.EventGraphRuntime
