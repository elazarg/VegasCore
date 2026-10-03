/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecisionResources
import Vegas.Game.SourceServiceInclusionSupport
import Vegas.Game.SourceServiceRepairForeignWindow
import Vegas.Pending.ReactiveResolutionFinalBlock
import Vegas.Pending.ReactiveUnsubmittedWindow
import Vegas.Pending.ReactiveSilentSettlement
import Interaction.ReactiveTrafficContinuation

/-! # A guarded resolution response at an actual retained opportunity

The response starts at the actual sampled information site. Every effective
action is coupled to the same private implementation or yields persistent
public traffic evidence, with a real retained successor history.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem roster_tail_of_inclusion
    (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player)
    (event : (graph setup).EventId) (owner : Player)
    (before after : List (ServiceInstruction (graph setup))) (visits : List Player)
    (ticks slot : Nat)
    (split : rosterPlan setup rosters = before ++
      visits.map (ServiceInstruction.player (graph := graph setup)) ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]) ++ after)
    (position : before.length = (rosterPlanPrefix setup rosters event.val).length + slot) :
    rosters event = (rosters event).take slot ++ visits := by
  have found : (rosterPlan setup rosters)[before.length + visits.length]? =
      some (.includeLatest event owner) := by
    rw [split, List.append_assoc, ← (show
      (visits.map (ServiceInstruction.player (graph := graph setup))).length = visits.length from
      List.length_map
        (ServiceInstruction.player (graph := graph setup))),
      ← List.length_append, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  obtain ⟨_, indexEq, prefixEq⟩ := roster_inclusion_prefix setup rosters
    (before.length + visits.length) event owner found
  have prefixLaw : (rosterPlan setup rosters).take (before.length + visits.length) =
      before ++ visits.map (ServiceInstruction.player (graph := graph setup)) := by
    rw [split, List.append_assoc, ← (show
      (visits.map (ServiceInstruction.player (graph := graph setup))).length = visits.length from
      List.length_map
        (ServiceInstruction.player (graph := graph setup))),
      ← List.length_append, List.take_left]
  rw [prefixLaw] at prefixEq
  have leading : before = rosterPlanPrefix setup rosters event.val ++
      ((rosters event).take slot).map (ServiceInstruction.player (graph := graph setup)) := by
    have initial := congrArg (List.take before.length) prefixEq
    rw [List.take_left, position, List.take_append, List.take_of_length_le (by omega),
      Nat.add_sub_cancel_left, ← List.map_take] at initial
    exact initial
  have mapped : (rosters event).map (ServiceInstruction.player (graph := graph setup)) =
      ((rosters event).take slot ++ visits).map
        (ServiceInstruction.player (graph := graph setup)) := by
    rw [leading, List.append_assoc] at prefixEq
    rw [List.map_append]
    exact (List.append_cancel_left prefixEq).symm
  have injective : Function.Injective
      (ServiceInstruction.player (graph := graph setup)) :=
    fun _ _ equality => ServiceInstruction.player.inj equality
  exact injective.list_map mapped

theorem resolution_history_response_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
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
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (application setup leaks))
    (sound : ((runtime setup).packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (event : (graph setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (ready : repaired.application.config.cut.Ready event)
    (remaining : Nat)
    (visits : List Player) (ticks : Nat)
    (dueTicks : (runtime setup).deadline event ≤ ticks)
    (before after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]) ++ after)
    (position : original.environmentRecall.length = before.length)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some owner, repaired⟩)) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining, none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.envelope = false) ∨
        (∀ (later : Player → app.Policy) (scheduler : (runtime setup).NetworkPolicy leaks)
          (final : app.Execution), final ∈ ((runtime setup).runInteractionPlan leaks later scheduler
            (visits.map ServiceInstruction.player ++
              (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
                next.1).support → event ∈ final.application.missedEvents) ∨
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          next.2.2.shadow = memory.shadow) := by
  classical
  intro app players strategy
  let menu := sourceServiceMenu setup leaks bounds rosters
  let scheduler := rosterScheduler setup leaks rosters network
  have owned : (graph setup).actor? event = some owner := by
    have actor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq ((graph setup).nodes event)] at actor
    exact actor
  obtain ⟨ready, timely, rightBinding, rightRecall, _, serials, first⟩ :=
    sourceService_decision_resources setup leaks bounds values capacity rosters opportunities
      network owner ⟨remaining, some owner, repaired⟩ trace rfl event ready
        owner owned
  have rightReady : repaired.application.config.cut.Ready event := ready
  have rightTimely : repaired.application.WithinDeadline (runtime setup) event := timely
  have rightBound : repaired.application.BindingInvariant := rightBinding
  have rightRecalled : repaired.InputRecall app := rightRecall
  have rightSerials : repaired.network.SerialsBeforeNext :=
    app.serialsBeforeNext_history scheduler (initialLaw setup) (rosterPlan setup rosters).length
      (menu.toRawTrace (initialLaw setup) (rosterPlan setup rosters).length scheduler trace)
  have originalReady : original.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, frame.publicView, State.publicView_eventReady]
    exact rightReady
  have originalTimely : original.application.WithinDeadline (runtime setup) event := by
    unfold State.WithinDeadline at rightTimely ⊢
    have clocks : original.application.clock = repaired.application.clock :=
      congrArg PublicView.clock frame.publicView
    have activations : original.application.activatedAt = repaired.application.activatedAt :=
      congrArg PublicView.activatedAt frame.publicView
    rw [clocks, activations]
    exact rightTimely
  have originalFirst : original.network.nextSerial owner =
      Message.distinctAuthoredCount original.network.ledger owner →
      (runtime setup).eventRecorded leaks (original.recall owner) event = false := by
    intro counted
    rw [(runtime setup).eventRecorded_congr leaks _ _ frame.submissions event]
    apply first
    change repaired.network.nextSerial owner =
      Message.distinctAuthoredCount repaired.network.ledger owner
    rwa [frame.network] at counted
  have existsCoupling : ∃ coupling : PMF
      (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        (∃ record, app.trafficStep (some ⟨remaining, some owner, original⟩)
            (some ⟨remaining, none, next.1⟩) = [record] ∧ record.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.envelope = false) ∨
        (∀ (later : Player → app.Policy) (scheduler : (runtime setup).NetworkPolicy leaks)
          (final : app.Execution), final ∈ ((runtime setup).runInteractionPlan leaks later scheduler
            (visits.map ServiceInstruction.player ++
              (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
                next.1).support → event ∈ final.application.missedEvents) ∨
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          next.2.2.shadow = memory.shadow := by
    by_cases required : decisionRequired setup leaks rosters owner
        (repaired.recall owner) (repaired.observe app owner)
    · have requirement := required
      obtain ⟨candidate, candidateTurn, _, _, unsent, _⟩ := requirement
      have selectedTurn := ownTurn?_of_ready setup repaired.application rightReady owned
      cases Option.some.inj (candidateTurn.symm.trans selectedTurn)
      obtain ⟨selectedEvent, slot, initial, selectedOwner, _, Γ, names, residual, residualProfile,
          sourceConfig,
          refs, embedding, refsBefore, _, _, _, boundary, priorState, sample, checkpoint, sole,
          prefixReached, moved, sampledEq, _, publicEq, _, clock, _⟩ :=
        sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
          network (failureProfile setup.program) owner ⟨remaining, some owner, repaired⟩ trace rfl
      have eventEq : selectedEvent = event :=
        (sole.2 event ((repaired.application.publicView_eventReady event).mpr rightReady)).symm
      subst selectedEvent
      change repaired.environmentRecall.length =
        (rosterPlanPrefix setup rosters event.val).length + slot + 1 at clock
      change repaired = priorState.sampledActivation app owner sample at sampledEq
      have currentPosition : repaired.environmentRecall.length = before.length := by
        rw [← frame.service]
        exact position
      have roster := roster_tail_of_inclusion setup rosters event owner before after visits ticks
        (slot + 1) split (by omega)
      have rosterEq : rosters event = (rosters event).take slot ++ owner :: visits := by
        rw [List.take_add_one, selectedOwner] at roster
        simpa only [Option.toList_some, List.singleton_append, List.append_assoc] using roster
      have absent : owner ∉ visits :=
        (sourceService_decisionRequired_iff_no_later_owner setup leaks bounds values capacity
          rosters opportunities network owner ⟨remaining, some owner, repaired⟩ trace rfl event
          rightReady owned unsent ((rosters event).take slot) visits rosterEq
          (by
            rw [List.length_take, Nat.min_eq_left
              (List.getElem?_eq_some_iff.mp selectedOwner).1.le]
            exact clock)).mp required
      obtain ⟨entered, activated⟩ := checkpoint.invariant.activatedAt_eq_some_of_ready_actor event
        (checkpoint.ready event rfl) (by rw [owned]; rfl)
      have originalActivated : original.application.activatedAt event = some entered := by
        rw [show original.application.activatedAt = boundary.application.activatedAt from
          congrArg PublicView.activatedAt (frame.publicView.trans publicEq)]
        exact activated
      have age : entered ≤ original.application.clock := by
        rw [show original.application.clock = boundary.application.clock from
          congrArg PublicView.clock (frame.publicView.trans publicEq)]
        exact checkpoint.invariant.activated_le event entered activated
      have priorUnsent : (runtime setup).eventRecorded leaks (priorState.recall owner) event =
          false := by
        rw [sampledEq] at unsent
        exact unsent
      have silentReached := (runtime setup).compiled_unsubmitted_window leaks bounds
        menu.uniformResponses (fun who past view response supported =>
          sourceServiceMenu_in_compiled setup leaks bounds rosters who past view
            ((menu.uniformResponses_support who past view response).mp supported)) network event
        owner owned ((rosters event).take slot) boundary priorState
        (soleReady_of_ready setup boundary.application (checkpoint.ready event rfl))
        prefixReached priorUnsent
      have preserved := (runtime setup).silent_window_preserves leaks
        (fun _ => app.silentPolicy) network owner boundary
        (fun current who response _ _ supported => app.mem_silentPolicy_support.mp supported)
        (fun message => message.id ∈ boundary.network.ledger.map Message.id) checkpoint.published
        ((rosters event).take slot) priorState silentReached
      have published : original.network.Satisfies fun message => message.sender = owner →
          message.id ∈ original.network.ledger.map Message.id := by
        rw [frame.network, sampledEq]
        change (priorState.network.learn owner sample).Satisfies (fun message =>
          message.sender = owner → message.id ∈ priorState.network.ledger.map Message.id)
        rw [preserved.2.1]
        exact (preserved.2.2.2.2.1.learn owner sample).mono fun _ known _ => known
      exact (frame.required_resolution_stopped_response_coupling bounds menu players reference
        started leftRecall rightRecalled sound leftBinding rightBound remaining event payload
        binding checks outputEq codeEq node
        ((soleReady_of_ready setup original.application originalReady).ownTurn owned)
        originalReady originalTimely originalFirst (frame.network ▸ rightSerials) published
        entered ticks originalActivated (by omega) visits absent (by
          intro response member
          change response ∈ sourceServiceActions setup leaks bounds rosters owner _ _
          rw [sourceServiceActions, ite_eq_left required]
          exact member) (by simpa only [players, Function.update_self] using available _ _))
    · obtain ⟨coupling, firstLaw, secondLaw, related⟩ := frame.resolution_stopped_response_coupling
        bounds menu players reference started leftRecall rightRecalled sound leftBinding rightBound
        remaining event payload binding checks outputEq codeEq node
        ((soleReady_of_ready setup original.application originalReady).ownTurn owned) originalReady
        originalTimely originalFirst (frame.network ▸ rightSerials) (by
          intro response member
          change response ∈ sourceServiceActions setup leaks bounds rosters owner _ _
          rw [sourceServiceActions, ite_eq_right required]
          exact member) (by simpa only [players, Function.update_self] using available _ _)
      exact ⟨coupling, firstLaw, secondLaw, fun next member =>
        (related next member).imp_right Or.inr⟩
  obtain ⟨coupling, leftLaw, rightLaw, related⟩ := existsCoupling
  refine ⟨coupling, leftLaw, rightLaw, ?_⟩
  intro next member
  have rightSupport :
      next.2 ∈ (strategy.resume owner players (some owner) repaired memory).support :=
    by
      rw [← rightLaw, PMF.support_map]
      exact ⟨next, member, rfl⟩
  refine ⟨?_, ?_⟩
  · apply menu.trace_implementation_resume (initialLaw setup) (rosterPlan setup rosters).length
      scheduler strategy owner players _ _ remaining (some owner) repaired memory trace next.2
        rightSupport
    · intro who different
      simpa only [players, Function.update_of_ne different] using
        (sourceServiceMenu_in_effective setup leaks bounds rosters).decoded_admissible
          (initialLaw setup) (rosterPlan setup rosters).length scheduler source target agrees who
    · intro next past view response member
      exact BindingMemory.retainedImplementation_response_available (runtime setup) leaks menu
        owner reference (players owner) next (past, view) response member
  · rcases related next member with bad | missed | good
    · obtain ⟨record, step, authored, rejected⟩ := bad
      have reached : next.1 ∈ (app.invoke players owner original).support := by
        rw [← leftLaw, PMF.support_map]
        exact ⟨next, member, rfl⟩
      obtain ⟨response, _, same⟩ := PMF.support_map .. ▸ reached
      refine Or.inl ⟨record, ?_, authored, rejected⟩
      rw [← same, app.executionTraffic_activated_response prior original owner response
        remaining sampled]
      have publicSame : prior.observeEnvironment app = original.observeEnvironment app := by
        have supported := sampled
        rw [ReactiveApplication.Execution.activation_samples, PMF.support_map] at supported
        obtain ⟨observed, _, equal⟩ := supported
        rw [← equal]
        rfl
      have trafficSame := app.trafficStep_public
        ⟨remaining + 1, none, prior⟩ ⟨remaining, none, next.1⟩
        ⟨remaining, some owner, original⟩ ⟨remaining, none, next.1⟩ publicSame rfl
      rw [same, trafficSame, step]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact Or.inr (Or.inl missed)
    · exact Or.inr (Or.inr good)

end Vegas
