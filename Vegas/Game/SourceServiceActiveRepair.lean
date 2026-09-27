/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceActiveBlockRepair
import Vegas.Game.SourceServiceActiveRepeatedBindingRepair
import Vegas.Game.SourceServiceRemainingRepair

/-! # Actual complete continuations from retained information histories

The current information history fixes the repair's initial private memory.
Its current response, partial source phase and all later phases are coupled
against the same unchanged original strategy and the same fixed legal repair.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem active_history_stopped_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (source : ∀ who, ((sourceServiceMenu setup leaks bounds rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy who)
    (target : ∀ who, ((bounds.menu (runtime setup) leaks).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy who)
    (agrees : ((sourceServiceMenu_in_effective setup leaks bounds rosters).actionRestriction
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).ExtendsProfile source target)
    (owner : Player) (policy : (application setup leaks).Policy)
    (available : ∀ past view response, response ∈ (policy past view).support →
      response ∈ (bounds.menu (runtime setup) leaks).actions owner past view)
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some owner, execution⟩)) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let reference := execution.recall owner
    let memory := BindingMemory.atRecall (runtime setup) leaks reference
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    let scheduler := rosterScheduler setup leaks rosters network
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (app.invoke players owner execution).bind
        (app.runRounds scheduler players remaining) ∧
      coupling.map Prod.snd =
        (strategy.resume owner players (some owner) execution memory).bind (fun next =>
          strategy.runJoint owner players scheduler remaining next.1 next.2) ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length scheduler).Trace
            (some ⟨0, none, next.2.1⟩)) ∧
        next.2.2.shadow.OwnBindings owner ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
          next.1.application.publicView.missedBindingBy owner = true ∨
          BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
  classical
  intro app players reference memory strategy scheduler
  let menu := sourceServiceMenu setup leaks bounds rosters
  obtain ⟨event, slot, initial, selected, _, Γ, names, sourceProgram, sourceProfile, config,
      refs, embedding, refsBefore, _, _, _, boundary, prior, sample, checkpoint, grant, reached,
      activated, sampled, configEq, publicEq, _, currentPosition, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network (failureProfile setup.program) owner ⟨remaining, some owner, execution⟩ trace rfl
  let visited := (rosters event).take slot
  let visits := (rosters event).drop (slot + 1)
  let events := (List.finRange (graph setup).order.eventCount).drop (event.val + 1)
  let future := events.flatMap (rosterBlock setup rosters)
  let before := rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
    visited.map ServiceInstruction.player ++ [.player owner]
  let ending : List (ServiceInstruction (graph setup)) :=
    match (graph setup).actor? event with
    | none => .sample event ::
        List.replicate ((runtime setup).deadline event) .tick ++ [.expire event]
    | some actor => .includeLatest event actor ::
        List.replicate ((runtime setup).deadline event) .tick ++ [.expire event]
  let current := visits.map ServiceInstruction.player ++ ending
  have slotBound : slot < (rosters event).length := (List.getElem?_eq_some_iff.mp selected).1
  have selectedValue : (rosters event)[slot] = owner := (List.getElem?_eq_some_iff.mp selected).2
  have roster : rosters event = visited ++ owner :: visits := by
    calc
      _ = visited ++ (rosters event).drop slot := (List.take_append_drop slot _).symm
      _ = _ := by rw [List.drop_eq_getElem_cons slotBound, selectedValue]
  have visitedLength : visited.length = slot := by
    simp only [visited, List.length_take, Nat.min_eq_left slotBound.le]
  have full : rosterPlan setup rosters =
      rosterPlanPrefix setup rosters event.val ++ rosterBlock setup rosters event ++ future := by
    have same := congrArg (List.flatMap (rosterBlock setup rosters))
      ((List.finRange (graph setup).order.eventCount).take_append_drop (event.val + 1))
    rw [List.flatMap_append] at same
    change rosterPlanPrefix setup rosters (event.val + 1) ++ future = rosterPlan setup rosters
      at same
    rw [rosterPlanPrefix_succ] at same
    exact same.symm
  have deadline : (runtime setup).deadline event = event.val + 1 := rfl
  have split : rosterPlan setup rosters = before ++ current ++ future := by
    cases owned : (graph setup).actor? event <;>
      simpa only [before, current, ending, rosterBlock, roster, owned, List.map_append,
        List.map_cons, List.append_assoc, List.cons_append, List.nil_append, deadline] using full
  have position : execution.environmentRecall.length = before.length := by
    simp only [before, List.length_append, List.length_singleton, List.length_map, visitedLength]
    exact currentPosition
  have endingLength : ending.length = (runtime setup).deadline event + 2 := by
    cases actual : (graph setup).actor? event <;> simp [ending, actual]
  have currentLength : current.length = visits.length + ((runtime setup).deadline event + 2) := by
    simp only [current, List.length_append, List.length_map, endingLength]
  have remainingEq : remaining = current.length + future.length := by
    have account := (menu.roundSupported_uniform (initialLaw setup)
      (rosterPlan setup rosters).length scheduler trace).1
    have total := congrArg List.length split
    simp only [List.length_append] at total
    change execution.environmentRecall.length + remaining = (rosterPlan setup rosters).length
      at account
    rw [position] at account
    omega
  have granted : execution.application.serviceGrant = some event :=
    (congrArg PublicView.serviceGrant publicEq).trans grant
  have ready : execution.application.config.cut.Ready event := by
    rw [configEq]
    exact checkpoint.ready event rfl
  have rawTrace := menu.toRawTrace (initialLaw setup) (rosterPlan setup rosters).length scheduler
    trace
  have recalled := app.history_inputRecall (initialLaw setup) (rosterPlan setup rosters).length
    scheduler rawTrace
  have sound := ((runtime setup).packetEvidence leaks).history_sound (initialLaw setup)
    (rosterPlan setup rosters).length scheduler rawTrace
  have binding : execution.application.BindingInvariant := by
    change execution = prior.sampledActivation (application setup leaks) owner sample at sampled
    rw [sampled]
    exact (checkpoint.run_core menu.uniformResponses network
      (visited.map ServiceInstruction.player) prior reached).2.1
  have frame := BindingMemory.frame_atRecall (runtime setup) leaks owner execution
  have onlyBindings : memory.shadow.OwnBindings owner := BindingShadow.ownBindings_empty owner
  have existsCurrent :
      ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
        coupling.map Prod.fst = (app.invoke players owner execution).bind
          ((runtime setup).runInteractionPlan leaks players network current) ∧
        coupling.map Prod.snd =
          (strategy.resume owner players (some owner) execution memory).bind (fun next =>
            strategy.runJoint owner players scheduler current.length next.1 next.2) ∧
        ∀ next ∈ coupling.support,
          Nonempty ((menu.protocol (initialLaw setup)
            (rosterPlan setup rosters).length scheduler).Trace
              (some ⟨future.length, none, next.2.1⟩)) ∧
          ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
            (runtime setup).permittedServiceEnvelope record.observation record.ledger
              record.input.envelope = false) ∨
            next.1.application.publicView.missedBindingBy owner = true ∨
            BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
    by_cases ownBinding : ∃ payload, (graph setup).outputLayout event = .binding owner payload
    · obtain ⟨payload, outputEq⟩ := ownBinding
      cases node : nodeView (graph setup) event with
      | sample ty law shape codeEq => rw [shape] at outputEq; cases outputEq
      | resolve actor ty handle checks shape codeEq => rw [shape] at outputEq; cases outputEq
      | bind actor ty shape codeEq =>
          rw [shape] at outputEq
          cases outputEq
          have owned : (graph setup).actor? event = some owner :=
            (EventCode.actor_cast shape ((graph setup).nodes event)).symm.trans
              (congrArg (fun code : EventCode (graph setup).layout (.binding owner payload) =>
                code.actor) codeEq)
          have tailEq : current = visits.map ServiceInstruction.player ++
              (.includeLatest event owner ::
                List.replicate ((runtime setup).deadline event) .tick ++
                [.expire event]) := by simp only [current, ending, owned]
          have cut : remaining - current.length = future.length := by omega
          by_cases recorded :
              (runtime setup).eventRecorded leaks (execution.recall owner) event = true
          · obtain ⟨coupling, first, second, related⟩ :=
              recorded_binding_history_response_block_coupling setup leaks bounds values capacity
                rosters opportunities network source target agrees owner policy available
                prior execution activated event payload shape codeEq node granted recorded
                remaining trace
                before future visits ((runtime setup).deadline event)
                (by simpa only [tailEq, List.append_assoc] using split) position
                (by rw [← tailEq]; omega)
            refine ⟨coupling, ?_, ?_, fun next member => ?_⟩
            · simpa only [tailEq] using first
            · simpa only [tailEq] using second
            · have connected := related next member
              refine ⟨?_, connected.2.imp_right Or.inr⟩
              simpa only [← tailEq, cut] using connected.1
          · obtain ⟨coupling, first, second, related⟩ := binding_window_stopped_coupling
              setup leaks bounds values capacity rosters opportunities network source target
              agrees owner policy available reference event payload shape codeEq node remaining
              prior
              execution execution activated memory frame trace (Nat.le_refl _) recalled granted
              (Bool.eq_false_iff.mpr recorded) visited visits roster
              (by rw [visitedLength]; exact currentPosition) before future
              (by simpa only [tailEq, List.append_assoc] using split) position
              (by rw [remainingEq, tailEq]; simp only [List.length_append, List.length_map,
                List.length_cons, List.length_replicate, List.length_nil]; omega)
            have tailLength : visits.length + 1 + (runtime setup).deadline event + 1 =
                current.length := by rw [currentLength]; omega
            refine ⟨coupling, ?_, ?_, fun next member => ?_⟩
            · simpa only [tailEq] using first
            · simpa only [tailLength] using second
            · have connected := related next member
              refine ⟨?_, ?_⟩
              · simpa only [tailLength, cut] using connected.1
              · rcases connected.2 with bad | omitted | paired
                · exact Or.inl bad
                · exact Or.inr (Or.inl (PublicView.missedBindingBy_of_event _ owner event owned
                    omitted))
                · exact Or.inr (Or.inr paired)
    · obtain ⟨coupling, first, second, related⟩ := active_nonbinding_block_stopped_coupling
        setup leaks bounds values capacity rosters opportunities network source target
        agrees
        owner policy available reference memory prior execution execution activated frame
        onlyBindings
        (Nat.le_refl _) recalled sound binding event
        (fun payload shape => ownBinding ⟨payload, shape⟩)
        granted ready future.length visits ((runtime setup).deadline event) (by
          have same : future.length + visits.length + ((runtime setup).deadline event + 2) =
              remaining := by rw [remainingEq, currentLength]; omega
          rw [same]
          exact trace) before future (by
          change rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++
            ending ++ future
          simpa only [current, List.append_assoc] using split) position
      exact ⟨coupling, first, second, fun next member =>
        ⟨(related next member).1, (related next member).2.imp_right Or.inr⟩⟩
  obtain ⟨firstBlock, first, second, related⟩ := existsCurrent
  have existsTail next (member : next ∈ firstBlock.support) :
      ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
        coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
          future next.1 ∧
        coupling.map Prod.snd = strategy.runJoint owner players scheduler future.length
          next.2.1 next.2.2 ∧
        ∀ final ∈ coupling.support,
          ((∃ record ∈ app.executionTraffic final.1, record.input.envelope.sender = owner ∧
            (runtime setup).permittedServiceEnvelope record.observation record.ledger
              record.input.envelope = false) ∨
            final.1.application.publicView.missedBindingBy owner = true ∨
            BindingMemory.Frame (runtime setup) leaks final.2.2 owner final.1 final.2.1) := by
    by_cases bad : (∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
        (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.input.envelope = false) ∨
        next.1.application.publicView.missedBindingBy owner = true
    · let left := (runtime setup).runInteractionPlan leaks players network future next.1
      let right := strategy.runJoint owner players scheduler future.length next.2.1 next.2.2
      refine ⟨FinDist.product left right, FinDist.map_fst_product ..,
        FinDist.map_snd_product .., ?_⟩
      intro final supported
      have reached : final.1 ∈ left.support := by
        rw [← FinDist.map_fst_product left right, FinDist.support_map]
        exact ⟨final, supported, rfl⟩
      rcases bad with ⟨record, present, authored, forbidden⟩ | missed
      · exact Or.inl ⟨record, ((runtime setup).executionTraffic_runInteractionPlan leaks players
          network future next.1 final.1 reached).subset present, authored, forbidden⟩
      · exact Or.inr (Or.inl (omission_plan_persistent setup leaks players network future owner
          next.1 final.1 missed reached))
    · have connected := related next member
      obtain ⟨nextTrace⟩ := connected.1
      have paired := (connected.2.resolve_left (fun traffic => bad (Or.inl traffic))).resolve_left
        (fun missed => bad (Or.inr missed))
      have leftSupport : next.1 ∈ ((app.invoke players owner execution).bind
          ((runtime setup).runInteractionPlan leaks players network current)).support := by
        rw [← first, FinDist.support_map]
        exact ⟨next, member, rfl⟩
      obtain ⟨responded, invoked, continued⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ leftSupport)
      obtain ⟨response, _, responseEq⟩ := FinDist.support_map .. ▸ invoked
      have nextRecall := (runtime setup).runInteractionPlan_inputRecall leaks players network
        current responded next.1 (responseEq ▸ app.respond_inputRecall execution owner response
          recalled) continued
      have soundInvariant : app.PolicyInvariant players
          (((runtime setup).packetEvidence leaks).Sound) := {
        respond := fun execution who response valid _ =>
          ((runtime setup).packetEvidence leaks).sound_respond execution who response valid
        environment := ((runtime setup).packetEvidence leaks).sound_environment }
      have nextSound := (runtime setup).runInteractionPlan_preserves leaks players network _
        soundInvariant current responded next.1
        (responseEq ▸ ((runtime setup).packetEvidence leaks).sound_respond execution owner response
          sound) continued
      have nextBinding := (runtime setup).runInteractionPlan_preserves leaks players network _
        (ReactiveApplication.Invariant.policyInvariant app
          ((runtime setup).reactiveBindingInvariant leaks) players) current responded next.1
        (responseEq ▸ ((runtime setup).reactiveBindingInvariant leaks).respond execution owner
          response binding) continued
      have nextPosition : next.1.environmentRecall.length = (before ++ current).length := by
        rw [(runtime setup).runInteractionPlan_recall leaks players network current responded next.1
          continued, ← responseEq, app.respond_environmentRecall, position]
        exact List.length_append.symm
      have nextStarted : reference.length ≤ (next.2.1.recall owner).length := by
        have monotone := ((runtime setup).runInteractionPlan_recall_prefix leaks players network
          current responded next.1 continued owner).length_le
        rw [← responseEq, app.respond_recall_length] at monotone
        have same := frame_recall_length setup leaks next.2.2 owner next.1 next.2.1 paired
        dsimp only [reference]
        omega
      have rightSupport : next.2 ∈
          ((strategy.resume owner players (some owner) execution memory).bind (fun middle =>
            strategy.runJoint owner players scheduler current.length
              middle.1 middle.2)).support := by
        rw [← second, FinDist.support_map]
        exact ⟨next, member, rfl⟩
      obtain ⟨middle, resumed, advanced⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ rightSupport)
      have nextMemory := BindingMemory.retainedImplementation_runJoint_ownBindings
        (runtime setup) leaks menu owner reference (players owner) players scheduler current.length
        middle.1 middle.2 (BindingMemory.retainedImplementation_resume_ownBindings (runtime setup)
          leaks menu owner reference (players owner) players (some owner) execution memory
          onlyBindings
          middle resumed) next.2 advanced
      obtain ⟨coupling, first, second, related⟩ :=
        remaining_events_stopped_coupling setup leaks bounds
        values capacity rosters opportunities network source target agrees owner policy
        available reference next.2.2 next.1 next.2.1 paired nextMemory nextStarted nextRecall
        nextSound
        nextBinding events 0 (by simpa only [Nat.zero_add] using nextTrace) (before ++ current) []
        (by simpa only [List.append_nil] using split) nextPosition
      exact ⟨coupling, first, second, fun final supported => (related final supported).2.2⟩
  let tail := fun next member => (existsTail next member).choose
  let coupling := firstBlock.bindOnSupport tail
  have physical : coupling.map Prod.fst = (app.invoke players owner execution).bind
      ((runtime setup).runInteractionPlan leaks players network (current ++ future)) := by
    rw [FinDist.map_bindOnSupport]
    calc
      _ = firstBlock.bind (fun next =>
          (runtime setup).runInteractionPlan leaks players network future next.1) := by
        apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
        intro next member
        exact (existsTail next member).choose_spec.1
      _ = _ := by
        rw [← FinDist.bind_map, first, FinDist.bind_bind]
        apply FinDist.bind_congr
        intro afterResponse _
        exact ((runtime setup).runInteractionPlan_append leaks players network current future
          afterResponse).symm
  have privateLaw : coupling.map Prod.snd =
      (strategy.resume owner players (some owner) execution memory).bind (fun next =>
        strategy.runJoint owner players scheduler remaining next.1 next.2) := by
    rw [FinDist.map_bindOnSupport]
    calc
      _ = firstBlock.bind (fun next =>
          strategy.runJoint owner players scheduler future.length next.2.1 next.2.2) := by
        apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
        intro next member
        exact (existsTail next member).choose_spec.2.1
      _ = (firstBlock.map Prod.snd).bind (fun next =>
          strategy.runJoint owner players scheduler future.length next.1 next.2) := by
        rw [FinDist.bind_map]
      _ = _ := by
        rw [second, FinDist.bind_bind, remainingEq]
        apply FinDist.bind_congr
        intro next _
        exact (ReactiveApplication.Implementation.runJoint_add strategy owner players scheduler
          current.length future.length next.1 next.2).symm
  refine ⟨coupling, ?_, privateLaw, ?_⟩
  · rw [physical]
    apply FinDist.bind_congr
    intro afterResponse supported
    obtain ⟨response, _, rfl⟩ := FinDist.support_map .. ▸ supported
    have same : (current ++ future).length = remaining := by
      rw [List.length_append, remainingEq]
    rw [← same]
    exact (roster_segment_rounds setup leaks rosters network players before (current ++ future) []
      (by simpa only [List.append_nil, List.append_assoc] using split)
      (execution.respond app owner response) (by
        rw [app.respond_environmentRecall]; exact position)).symm
  · intro final supported
    have rightSupport : final.2 ∈
        ((strategy.resume owner players (some owner) execution memory).bind (fun middle =>
          strategy.runJoint owner players scheduler remaining middle.1 middle.2)).support := by
      rw [← privateLaw, FinDist.support_map]
      exact ⟨final, supported, rfl⟩
    obtain ⟨middle, resumed, advanced⟩ :=
      Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ rightSupport)
    have opponents : ∀ who, who ≠ owner → menu.Admissible (initialLaw setup)
        (rosterPlan setup rosters).length scheduler who (players who) := by
      intro who different
      simpa only [players, Function.update_of_ne different] using
        (sourceServiceMenu_in_effective setup leaks bounds rosters).decoded_admissible
          (initialLaw setup) (rosterPlan setup rosters).length scheduler source target agrees who
    have covered := BindingMemory.retainedImplementation_response_available (runtime setup)
      leaks menu owner reference (players owner)
    obtain ⟨middleTrace⟩ := menu.trace_implementation_resume (initialLaw setup)
      (rosterPlan setup rosters).length scheduler strategy owner players opponents
      (fun memory past view response supported => covered memory (past, view) response supported)
      remaining (some owner) execution memory trace middle resumed
    have memoryValid := BindingMemory.retainedImplementation_resume_ownBindings (runtime setup)
      leaks menu owner reference (players owner) players (some owner) execution memory
          onlyBindings
      middle resumed
    refine ⟨?_, ?_, ?_⟩
    · exact menu.trace_implementation_runJoint (initialLaw setup) (rosterPlan setup rosters).length
        scheduler strategy owner players opponents
        (fun memory past view response supported => covered memory (past, view) response supported)
        0 remaining middle.1 middle.2 (by simpa only [Nat.zero_add] using middleTrace)
        final.2 advanced
    · exact BindingMemory.retainedImplementation_runJoint_ownBindings (runtime setup) leaks menu
        owner reference (players owner) players scheduler remaining middle.1 middle.2 memoryValid
        final.2 advanced
    · obtain ⟨next, member, reached⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bindOnSupport .. ▸ supported)
      exact (existsTail next member).choose_spec.2.2 final reached

end Vegas.SourceProgram.RevealService
