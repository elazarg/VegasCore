/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceActiveResolutionRepair
import Vegas.Game.SourceServiceActiveOffTurnRepair
import Vegas.Game.SourceServiceEventRepair

/-! # Repair from an active nonbinding information site to its phase boundary

The current response is executed once, at the player's actual sampled input.
The same fixed implementation then runs the remaining real roster, reserved
inclusion or public sample, and every clock/expiry instruction.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem active_nonbinding_block_stopped_coupling
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
    (prior original repaired : (application setup leaks).Execution)
    (sampled : original ∈
      (prior.environmentStep (application setup leaks) (.activate owner)).support)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (application setup leaks))
    (sound : ((runtime setup).packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (event : (graph setup).EventId)
    (notBinding : ∀ payload, (graph setup).outputLayout event ≠ .binding owner payload)
    (granted : repaired.application.serviceGrant = some event)
    (ready : original.application.config.cut.Ready event)
    (remaining : Nat) (visits : List Player) (ticks : Nat)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining + visits.length + (ticks + 2), some owner, repaired⟩))
    (before after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++
      (match (graph setup).actor? event with
      | none => .sample event :: List.replicate ticks .tick ++ [.expire event]
      | some actor => .includeLatest event actor ::
          List.replicate ticks .tick ++ [.expire event]) ++ after)
    (position : original.environmentRecall.length = before.length) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    let ending : List (ServiceInstruction (graph setup)) :=
      match (graph setup).actor? event with
      | none => .sample event :: List.replicate ticks .tick ++ [.expire event]
      | some actor => .includeLatest event actor :: List.replicate ticks .tick ++ [.expire event]
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (app.invoke players owner original).bind
        ((runtime setup).runInteractionPlan leaks players network
          (visits.map ServiceInstruction.player ++ ending)) ∧
      coupling.map Prod.snd =
        (strategy.resume owner players (some owner) repaired memory).bind (fun next =>
          strategy.runJoint owner players (rosterScheduler setup leaks rosters network)
            (visits.map ServiceInstruction.player ++ ending).length next.1 next.2) ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining, none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
          BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
  classical
  intro app players strategy ending
  let menu := sourceServiceMenu setup leaks bounds rosters
  let scheduler := rosterScheduler setup leaks rosters network
  let suffix := visits.map ServiceInstruction.player ++ ending
  let rank := remaining + visits.length + (ticks + 2)
  have length : suffix.length = visits.length + (ticks + 2) := by
    cases actual : (graph setup).actor? event <;> simp [suffix, ending, actual]
  have originalGrant : original.application.serviceGrant = some event :=
    (congrArg PublicView.serviceGrant frame.publicView).trans granted
  have existsResponse :
      ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
        coupling.map Prod.fst = app.invoke players owner original ∧
        coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
        ∀ next ∈ coupling.support,
          Nonempty ((menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
            scheduler).Trace (some ⟨rank, none, next.2.1⟩)) ∧
          ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
            (runtime setup).permittedServiceEnvelope record.observation record.ledger
              record.input.envelope = false) ∨
            BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
              reference.length ≤ (next.2.1.recall owner).length) := by
    by_cases owned : (graph setup).actor? event = some owner
    · cases node : nodeView (graph setup) event with
      | bind actor payload outputEq codeEq =>
          have actual : (graph setup).actor? event = some actor :=
            (EventCode.actor_cast outputEq ((graph setup).nodes event)).symm.trans
              (congrArg (fun code : EventCode (graph setup).layout (.binding actor payload) =>
                code.actor) codeEq)
          have same := Option.some.inj (actual.symm.trans owned)
          exact False.elim (notBinding payload (same ▸ outputEq))
      | sample payload law outputEq codeEq =>
          have actual : (graph setup).actor? event = none :=
            (EventCode.actor_cast outputEq ((graph setup).nodes event)).symm.trans
              (congrArg (fun code : EventCode (graph setup).layout (.publicData payload) =>
                code.actor) codeEq)
          rw [actual] at owned
          cases owned
      | resolve actor payload binding checks outputEq codeEq =>
          have actual : (graph setup).actor? event = some actor :=
            (EventCode.actor_cast outputEq ((graph setup).nodes event)).symm.trans
              (congrArg (fun code : EventCode (graph setup).layout (.publication payload) =>
                code.actor) codeEq)
          cases Option.some.inj (actual.symm.trans owned)
          exact resolution_history_response_coupling setup leaks bounds values capacity rosters
            opportunities network source target agrees owner policy available reference
            memory prior original repaired sampled frame started leftRecall sound leftBinding
            event payload binding checks outputEq codeEq node granted rank trace
    · exact off_turn_history_response_coupling setup leaks bounds rosters network source target
        agrees owner policy available reference memory prior original repaired sampled frame
        started leftRecall (by
          intro selected selectedGrant
          cases Option.some.inj (selectedGrant.symm.trans originalGrant)
          exact owned) rank trace
  obtain ⟨step, first, second, related⟩ := existsResponse
  have existsTail next (member : next ∈ step.support) :
      ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
        coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
          suffix next.1 ∧
        coupling.map Prod.snd = strategy.runJoint owner players scheduler suffix.length
          next.2.1 next.2.2 ∧
        ∀ final ∈ coupling.support,
          Nonempty ((menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
            scheduler).Trace (some ⟨remaining, none, final.2.1⟩)) ∧
          ((∃ record ∈ app.executionTraffic final.1, record.input.envelope.sender = owner ∧
            (runtime setup).permittedServiceEnvelope record.observation record.ledger
              record.input.envelope = false) ∨
            BindingMemory.Frame (runtime setup) leaks final.2.2 owner final.1 final.2.1) := by
    obtain ⟨nextTrace⟩ := (related next member).1
    by_cases bad : ∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
        (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.input.envelope = false
    · let left := (runtime setup).runInteractionPlan leaks players network suffix next.1
      let right := strategy.runJoint owner players scheduler suffix.length next.2.1 next.2.2
      refine ⟨FinDist.product left right, FinDist.map_fst_product ..,
        FinDist.map_snd_product .., ?_⟩
      intro final supported
      have leftSupport : final.1 ∈ left.support := by
        rw [← FinDist.map_fst_product left right, FinDist.support_map]
        exact ⟨final, supported, rfl⟩
      have rightSupport : final.2 ∈ right.support := by
        rw [← FinDist.map_snd_product left right, FinDist.support_map]
        exact ⟨final, supported, rfl⟩
      refine ⟨?_, ?_⟩
      · apply menu.trace_implementation_runJoint (initialLaw setup)
          (rosterPlan setup rosters).length scheduler strategy owner players _ _
          remaining suffix.length next.2.1 next.2.2 _ final.2 rightSupport
        · intro who different
          simpa only [players, Function.update_of_ne different] using
            (sourceServiceMenu_in_effective setup leaks bounds rosters).decoded_admissible
              (initialLaw setup) (rosterPlan setup rosters).length scheduler source target agrees
                who
        · intro current past view response supported
          exact BindingMemory.retainedImplementation_response_available (runtime setup) leaks
            menu owner reference (players owner) current (past, view) response supported
        · rw [length]
          simpa only [rank, Nat.add_assoc] using nextTrace
      · obtain ⟨record, present, authored, forbidden⟩ := bad
        exact Or.inl ⟨record, ((runtime setup).executionTraffic_runInteractionPlan leaks players
          network suffix next.1 final.1 leftSupport).subset present, authored, forbidden⟩
    · obtain ⟨paired, nextStarted⟩ := (related next member).2.resolve_left bad
      have moved : next.1 ∈ (app.invoke players owner original).support := by
        rw [← first, FinDist.support_map]
        exact ⟨next, member, rfl⟩
      obtain ⟨response, _, same⟩ := FinDist.support_map .. ▸ moved
      have resumed : next.2 ∈
          (strategy.resume owner players (some owner) repaired memory).support := by
        rw [← second, FinDist.support_map]
        exact ⟨next, member, rfl⟩
      have nextMemory := BindingMemory.retainedImplementation_resume_ownBindings (runtime setup)
        leaks menu owner reference (players owner) players (some owner) repaired memory onlyBindings
          next.2 resumed
      have nextRecall : next.1.InputRecall app := by
        rw [← same]
        exact app.respond_inputRecall original owner response leftRecall
      have nextSound : ((runtime setup).packetEvidence leaks).Sound next.1 := by
        rw [← same]
        exact ((runtime setup).packetEvidence leaks).sound_respond original owner response sound
      have nextBinding : next.1.application.BindingInvariant := by
        rw [← same]
        exact ((runtime setup).reactiveBindingInvariant leaks).respond original owner response
          leftBinding
      have unchanged := (runtime setup).reactive_respond_application leaks original owner response
      have nextGrant : next.2.1.application.serviceGrant = some event := by
        rw [← same] at paired
        exact (congrArg PublicView.serviceGrant paired.publicView).symm.trans
          ((congrArg PublicView.serviceGrant unchanged.2).trans originalGrant)
      have nextReady : next.1.application.config.cut.Ready event := by
        rw [← same, unchanged.1]
        exact ready
      have nextPosition : next.1.environmentRecall.length = before.length := by
        rw [← same, app.respond_environmentRecall]
        exact position
      cases node : nodeView (graph setup) event with
      | sample payload law outputEq codeEq =>
          have actual : (graph setup).actor? event = none :=
            (EventCode.actor_cast outputEq ((graph setup).nodes event)).symm.trans
              (congrArg (fun code : EventCode (graph setup).layout (.publicData payload) =>
                code.actor) codeEq)
          have rawTrace := menu.toRawTrace (initialLaw setup) (rosterPlan setup rosters).length
            scheduler nextTrace
          obtain ⟨coupling, leftLaw, rightLaw, connected⟩ := sample_block_stopped_coupling
            setup leaks bounds rosters network source target agrees owner policy available reference
            next.2.2 next.1 next.2.1 paired nextMemory nextStarted nextRecall
            (app.history_inputRecall (initialLaw setup) (rosterPlan setup rosters).length scheduler
              rawTrace)
            (paired.network ▸ app.serialsBeforeNext_history scheduler (initialLaw setup)
              (rosterPlan setup rosters).length rawTrace)
            event payload law outputEq codeEq node
            ((congrArg PublicView.serviceGrant paired.publicView).trans nextGrant) nextReady
            remaining visits ticks nextTrace before after
            (by simpa only [actual] using split) nextPosition
          exact ⟨coupling, by simpa only [suffix, ending, actual] using leftLaw,
            by simpa only [suffix, ending, actual] using rightLaw, connected⟩
      | bind actor payload outputEq codeEq =>
          have different : actor ≠ owner := by
            intro equal
            exact notBinding payload (equal ▸ outputEq)
          have actual : (graph setup).actor? event = some actor :=
            (EventCode.actor_cast outputEq ((graph setup).nodes event)).symm.trans
              (congrArg (fun code : EventCode (graph setup).layout (.binding actor payload) =>
                code.actor) codeEq)
          obtain ⟨coupling, leftLaw, rightLaw, connected⟩ := foreign_binding_block_stopped_coupling
            setup leaks bounds values capacity rosters opportunities network source target
            agrees owner policy available reference next.2.2 next.1 next.2.1 paired nextMemory
            nextStarted nextRecall event actor different payload outputEq codeEq node nextGrant
            remaining visits ticks nextTrace before after (by simpa only [actual] using split)
            nextPosition
          exact ⟨coupling, by simpa only [suffix, ending, actual] using leftLaw,
            by simpa only [suffix, ending, actual] using rightLaw, connected⟩
      | resolve actor payload binding checks outputEq codeEq =>
          have actual : (graph setup).actor? event = some actor :=
            (EventCode.actor_cast outputEq ((graph setup).nodes event)).symm.trans
              (congrArg (fun code : EventCode (graph setup).layout (.publication payload) =>
                code.actor) codeEq)
          obtain ⟨coupling, leftLaw, rightLaw, connected⟩ := resolution_block_stopped_coupling
            setup leaks bounds values capacity rosters opportunities network source target
            agrees owner policy available reference next.2.2 next.1 next.2.1 paired nextMemory
            nextStarted nextRecall nextSound nextBinding event actor payload binding checks
            outputEq codeEq node nextGrant remaining visits ticks nextTrace before after
            (by simpa only [actual] using split) nextPosition
          exact ⟨coupling, by simpa only [suffix, ending, actual] using leftLaw,
            by simpa only [suffix, ending, actual] using rightLaw, connected⟩
  let tail := fun next member => (existsTail next member).choose
  let coupling := step.bindOnSupport tail
  refine ⟨coupling, ?_, ?_, ?_⟩
  · rw [FinDist.map_bindOnSupport]
    calc
      _ = step.bind (fun next => (runtime setup).runInteractionPlan leaks players network
          suffix next.1) := by
        apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
        intro next member
        exact (existsTail next member).choose_spec.1
      _ = _ := by rw [← FinDist.bind_map, first]
  · rw [FinDist.map_bindOnSupport]
    calc
      _ = step.bind (fun next => strategy.runJoint owner players scheduler suffix.length
          next.2.1 next.2.2) := by
        apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
        intro next member
        exact (existsTail next member).choose_spec.2.1
      _ = (step.map Prod.snd).bind (fun next => strategy.runJoint owner players scheduler
          suffix.length next.1 next.2) := by rw [FinDist.bind_map]
      _ = _ := by rw [second]
  · intro final supported
    obtain ⟨next, member, reached⟩ :=
      Set.mem_iUnion₂.mp (FinDist.support_bindOnSupport .. ▸ supported)
    exact (existsTail next member).choose_spec.2.2 final reached

end Vegas.SourceProgram.RevealService
