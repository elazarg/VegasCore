/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceProgramRepair
import Vegas.Game.SourceServiceForeignBindingBlock
import Vegas.Pending.ReactiveServiceAudit

/-! # Whole source-event blocks in actual continuation repair

The actual retained history supplies the source boundary before the grant.
Each source constructor then has its exact physical block coupling against the
same repaired policy and unchanged opponents. No payoff comparison is assumed.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem event_block_stopped_coupling
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
    (reference : List (application setup leaks).PlayerEntry)
    (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (application setup leaks))
    (sound : ((runtime setup).packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (event : (graph setup).EventId) (remaining : Nat)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining + (rosterBlock setup rosters event).length, none, repaired⟩))
    (before after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ rosterBlock setup rosters event ++ after)
    (prefixEq : before = rosterPlanPrefix setup rosters event.val)
    (position : original.environmentRecall.length = before.length) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
        (rosterBlock setup rosters event) original ∧
      coupling.map Prod.snd = strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network)
          (rosterBlock setup rosters event).length repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining, none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
          next.1.application.publicView.missedBindingBy owner = true ∨
          BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
  classical
  intro app players strategy
  let menu := sourceServiceMenu setup leaks bounds rosters
  let scheduler := rosterScheduler setup leaks rosters network
  let body : List (ServiceInstruction (graph setup)) :=
    (rosters event).map ServiceInstruction.player ++
      (match (graph setup).actor? event with
      | none => .sample event :: List.replicate (event.val + 1) .tick ++ [.expire event]
      | some actor => .includeLatest event actor ::
          List.replicate (event.val + 1) .tick ++ [.expire event])
  have block : rosterBlock setup rosters event = body := by
    cases owned : (graph setup).actor? event <;>
      simp only [rosterBlock, body, owned, List.append_assoc, List.cons_append, List.nil_append]
  have cursor : repaired.environmentRecall.length = before.length := by
    rw [← frame.service]
    exact position
  have planPrefix : (rosterPlan setup rosters).take repaired.environmentRecall.length =
      rosterPlanPrefix setup rosters event.val := by
    rw [cursor, split, List.append_assoc, List.take_left, prefixEq]
  obtain ⟨initial, _, Γ, config, refs, boundary⟩ := sourceService_phase_boundary setup leaks
    bounds values capacity rosters opportunities network
      ⟨remaining + (rosterBlock setup rosters event).length, none, repaired⟩ trace rfl event
      planPrefix
  have phase : before.length = (rosterPlanPrefix setup rosters event.val).length := by
    rw [prefixEq]
  have paired := frame
  have nextTrace :
      (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length scheduler).Trace
      (some ⟨remaining + body.length, none, repaired⟩) := by
    rw [← block]
    exact trace
  have nextPosition := position
  have nextSplit : rosterPlan setup rosters = before ++ body ++ after := by
    rw [← block]
    exact split
  have rightRecall := app.history_inputRecall (initialLaw setup) (rosterPlan setup rosters).length
    scheduler (menu.toRawTrace (initialLaw setup) (rosterPlan setup rosters).length
      scheduler nextTrace)
  have leftNextRecall := leftRecall
  have leftSound := sound
  have leftNextBinding := leftBinding
  have total : body.length = (rosters event).length + ((event.val + 1) + 2) := by
    cases owned : (graph setup).actor? event <;>
      simp only [body, owned, List.length_append, List.length_map, List.length_cons,
        List.length_replicate, List.length_nil]
  have phaseTrace :
      (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length scheduler).Trace
      (some ⟨remaining + (rosters event).length + ((event.val + 1) + 2),
        none, repaired⟩) := by
    simpa only [total, Nat.add_assoc] using nextTrace
  have nextStarted : reference.length ≤ (repaired.recall owner).length := started
  have existsBody : ∃ coupling : PMF
      (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
        body original ∧
      coupling.map Prod.snd = strategy.runJoint owner players scheduler body.length
        repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty ((menu.protocol (initialLaw setup)
          (rosterPlan setup rosters).length scheduler).Trace
          (some ⟨remaining, none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
          next.1.application.publicView.missedBindingBy owner = true ∨
          BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
    have repairedReady : repaired.application.config.cut.Ready event := boundary.ready event rfl
    cases node : nodeView (graph setup) event with
    | sample payload law outputEq codeEq =>
      have owned : (graph setup).actor? event = none :=
        (EventCode.actor_cast outputEq ((graph setup).nodes event)).symm.trans
          (congrArg (fun code : EventCode (graph setup).layout (.publicData payload) =>
            code.actor) codeEq)
      have ready : original.application.config.cut.Ready event :=
        ready_of_publicView_eq frame.publicView repairedReady
      obtain ⟨coupling, first, second, related⟩ := sample_block_stopped_coupling setup leaks bounds
        rosters network source target agrees owner policy available reference memory
        original repaired paired onlyBindings nextStarted leftNextRecall
        rightRecall (by rw [paired.network]; exact boundary.serials)
        event payload law outputEq codeEq node
        ready remaining (rosters event) (event.val + 1) phaseTrace
        before after
        (by simpa only [body, owned, List.append_assoc] using nextSplit) nextPosition
      refine ⟨coupling, ?_, ?_, fun next member => ?_⟩
      · simpa only [body, owned] using first
      · simpa only [body, owned] using second
      · exact ⟨(related next member).1, ((related next member).2).imp_right Or.inr⟩
    | bind actor payload outputEq codeEq =>
      have owned : (graph setup).actor? event = some actor :=
        (EventCode.actor_cast outputEq ((graph setup).nodes event)).symm.trans
          (congrArg (fun code : EventCode (graph setup).layout (.binding actor payload) =>
            code.actor) codeEq)
      by_cases same : actor = owner
      · subst actor
        have deadline : (runtime setup).deadline event = event.val + 1 := rfl
        obtain ⟨coupling, first, second, related⟩ := binding_phase_stopped_coupling setup leaks
          bounds values capacity rosters opportunities network source target agrees owner
          policy available reference memory original repaired paired
          nextStarted leftNextRecall event payload outputEq codeEq node repairedReady
          (boundary.unsent owner event (Nat.le_refl _)) remaining phaseTrace
          before after
          (by simpa only [body, owned, deadline, List.append_assoc] using nextSplit) nextPosition
          phase
        refine ⟨coupling, ?_, ?_, fun next member => ?_⟩
        · simpa only [body, owned, deadline] using first
        · simpa only [body, owned, deadline] using second
        · refine ⟨(related next member).1, ?_⟩
          rcases (related next member).2 with bad | missed | framed
          · exact Or.inl bad
          · exact Or.inr (Or.inl (PublicView.missedBindingBy_of_event _ owner event owned missed))
          · exact Or.inr (Or.inr framed)
      · obtain ⟨coupling, first, second, related⟩ := foreign_binding_block_stopped_coupling setup
          leaks bounds values capacity rosters opportunities network source target agrees
          owner policy available reference memory original repaired paired
          onlyBindings nextStarted leftNextRecall event actor same payload outputEq codeEq node
          repairedReady remaining (rosters event) (event.val + 1) phaseTrace
          before after
          (by simpa only [body, owned, List.append_assoc] using nextSplit) nextPosition
        refine ⟨coupling, ?_, ?_, fun next member => ?_⟩
        · simpa only [body, owned] using first
        · simpa only [body, owned] using second
        · exact ⟨(related next member).1, ((related next member).2).imp_right Or.inr⟩
    | resolve actor payload binding checks outputEq codeEq =>
      have owned : (graph setup).actor? event = some actor :=
        (EventCode.actor_cast outputEq ((graph setup).nodes event)).symm.trans
          (congrArg (fun code : EventCode (graph setup).layout (.publication payload) =>
            code.actor) codeEq)
      obtain ⟨coupling, first, second, related⟩ := resolution_block_stopped_coupling setup leaks
        bounds values capacity rosters opportunities network source target agrees owner
        policy available reference memory original repaired paired onlyBindings
        nextStarted leftNextRecall leftSound leftNextBinding event actor payload binding checks
        outputEq codeEq node repairedReady remaining (rosters event)
        (event.val + 1) phaseTrace
        before after
        (by simpa only [body, owned, List.append_assoc] using nextSplit) nextPosition
      refine ⟨coupling, ?_, ?_, fun next member => ?_⟩
      · simpa only [body, owned] using first
      · simpa only [body, owned] using second
      · exact ⟨(related next member).1, ((related next member).2).imp_right Or.inr⟩
  obtain ⟨coupling, first, second, related⟩ := existsBody
  refine ⟨coupling, ?_, ?_, related⟩
  · rw [block]
    exact first
  · rw [block]
    exact second

end Vegas
