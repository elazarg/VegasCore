/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSubmittedBinding
import Vegas.Game.SourceServiceRepeatedBlock
import Vegas.Game.SourceServiceRepairForeignWindow
import Interaction.ReactiveTrafficContinuation

/-! # Active comparison after an earlier retained binding

The pending binding may precede the private repair's initial memory. The
actual retained history supplies its typed candidate and exact pending packet.
The current response and every later roster visit use the same fixed repair;
protected inclusion uses the unchanged-candidate branch when no shadow entry
was needed. All repaired endpoints have real retained histories.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem recorded_response_tail
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (players : Player → (application setup leaks).Policy)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (serial nonce : Nat) (value : L.Val payload)
    (execution left right : (application setup leaks).Execution)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner left right)
    (shadow : memory.shadow = .empty)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (right.recall owner).length)
    (response : (application setup leaks).Action)
    (replay : response ∈ ((application setup leaks).replayPolicy (execution.recall owner)
      (execution.observe (application setup leaks) owner)).support)
    (rightEq : right = execution.respond (application setup leaks) owner response)
    (recalled : execution.InputRecall (application setup leaks))
    (leftRecall : left.InputRecall (application setup leaks))
    (serials : execution.network.SerialsBeforeNext)
    (repeated : execution.network.nextSerial owner ≠
      execution.network.ledger.countP (fun message => message.sender = owner))
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (vacant : execution.application.accepted (.inr event) = none)
    (unused : execution.application.HandleUnused (owner, .prepared serial))
    (candidate : execution.application.candidates.lookup (owner, .prepared serial) =
      .openable ⟨payload, value⟩)
    (pending : (⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩ :
      Message Player (WitnessedPacket (graph setup))) ∈ execution.network.pending)
    (unpublished : (owner, nonce) ∉ execution.network.ledger.map Message.id)
    (packets : execution.network.Satisfies fun packet =>
      packet.id ∈ execution.network.ledger.map Message.id ∨
        packet = ⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩)
    (available : ∀ past view action, action ∈ (players owner past view).support →
      action ∈ (bounds.menu (runtime setup) leaks).actions owner past view)
    (before after : List (ServiceInstruction (graph setup))) (visits : List Player) (ticks : Nat)
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]) ++ after)
    (position : execution.environmentRecall.length = before.length) :
    let app := application setup leaks
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    let tail := visits.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
    ∃ joint : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      joint.map Prod.fst = (runtime setup).runInteractionPlan leaks players network tail left ∧
      joint.map Prod.snd = strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network) tail.length right memory ∧
      ∀ final ∈ joint.support,
        (∃ record ∈ app.executionTraffic final.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        BindingMemory.Frame (runtime setup) leaks final.2.2 owner final.1 final.2.1 := by
  intro app strategy tail
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩
  have data := (runtime setup).replay_response_preserves leaks _ execution packets owner
    response (app.replayPolicy_cases _ _ response replay)
  have rightApp : right.application = execution.application := rightEq ▸ data.1
  have rightLedger : right.network.ledger = execution.network.ledger :=
    rightEq ▸ data.2.1
  have rightCounter : right.network.nextSerial = execution.network.nextSerial :=
    rightEq ▸ data.2.2.2.1
  have observeEq := frame.observed
  rw [shadow] at observeEq
  rw [BindingShadow.inputView_empty] at observeEq
  have leftPublic := frame.publicView.trans (congrArg State.publicView rightApp)
  have leftCandidate : left.application.candidates.lookup (owner, .prepared serial) =
      execution.application.candidates.lookup (owner, .prepared serial) := by
    have same := congrArg (fun view : app.PlayerView =>
      view.application.candidates (.prepared serial)) observeEq
    change right.application.candidates.lookup (owner, .prepared serial) =
      left.application.candidates.lookup (owner, .prepared serial) at same
    exact same.symm.trans (congrArg
      (fun state => state.candidates.lookup (owner, .prepared serial)) rightApp)
  have leftResult : left.application.bindingResult (owner, .prepared serial) payload =
      execution.application.bindingResult (owner, .prepared serial) payload := by
    unfold State.bindingResult
    rw [leftCandidate]
  have readyNow : left.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, leftPublic, State.publicView_eventReady]
    exact ready
  have timelyNow : left.application.WithinDeadline (runtime setup) event := by
    unfold State.WithinDeadline
    rw [show left.application.clock = execution.application.clock from
      congrArg PublicView.clock leftPublic,
      show left.application.activatedAt = execution.application.activatedAt from
        congrArg PublicView.activatedAt leftPublic]
    exact timely
  have accepted : left.application.accepted = execution.application.accepted :=
    congrArg PublicView.accepted leftPublic
  have rightRecall : right.InputRecall app := by
    rw [rightEq]
    exact app.respond_inputRecall execution owner response recalled
  have serialsNow : left.network.SerialsBeforeNext := by
    rw [frame.network, rightEq]
    exact (app.serialsBeforeNextInvariant (fun _ _ => PMF.pure .wait)).respond
      execution owner response serials
  have packetsNow : left.network.Satisfies fun packet => packet.sender = owner →
      packet.id ∈ left.network.ledger.map Message.id ∨ packet = message := by
    rw [frame.network, rightLedger, rightEq]
    exact data.2.2.2.2.1.mono (fun _ valid _ => valid)
  exact repeated_binding_block_coupling setup leaks bounds rosters network players owner event
    payload outputEq codeEq node (.prepared serial) nonce memory left right frame
    reference started leftRecall rightRecall serialsNow
    (by rw [frame.network, rightCounter, rightLedger]; exact repeated)
    (by
      rw [rightEq]
      exact (runtime setup).eventRecorded_respond_of_recorded leaks execution
        owner owner response event recorded) readyNow timelyNow
    (by rw [accepted]; exact vacant)
    (by intro field found; exact unused field ((congrFun accepted field).symm.trans found))
    (by rw [leftCandidate, candidate]; intro impossible; cases impossible)
    (by rw [rightApp, candidate]; intro impossible; cases impossible)
    (Or.inr ⟨by rw [shadow]; rfl, by rw [shadow]; rfl,
      by rw [rightApp, leftResult]⟩)
    (by rw [frame.network, rightEq]; exact data.2.2.2.2.2 pending)
    (by rw [frame.network, rightLedger]; exact unpublished) packetsNow
    available
    before after visits ticks split
    (by rw [frame.service, rightEq, app.respond_environmentRecall]; exact position)

private theorem resume_action {Principal Memory : Type} [DecidableEq Principal]
    (app : ReactiveApplication Principal) (implementation : app.Implementation Memory)
    (owner : Principal) (players : Principal → app.Policy) (execution : app.Execution)
    (initial : Memory) (next : app.Execution × Memory)
    (reached : next ∈ (implementation.resume owner players (some owner)
      execution initial).support) :
    ∃ chosen ∈ (implementation.respond initial
      (execution.recall owner, execution.observe app owner)).support,
      (execution.respond app owner chosen.1, chosen.2) = next := by
  simpa only [ReactiveApplication.Implementation.resume, ↓reduceIte,
    PMF.support_map, Set.mem_image] using reached

private theorem recorded_resume_transport
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (players : Player → (application setup leaks).Policy)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (execution right : (application setup leaks).Execution)
    (memory : BindingMemory (runtime setup) leaks)
    (reference : List (application setup leaks).PlayerEntry)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (ready : execution.application.config.cut.Ready event)
    (reached : (right, memory) ∈
      ((BindingMemory.retainedImplementation (runtime setup) leaks
        (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)).resume
          owner players (some owner) execution
            (BindingMemory.atRecall (runtime setup) leaks reference)).support) :
    ∃ response ∈ ((application setup leaks).replayPolicy (execution.recall owner)
      (execution.observe (application setup leaks) owner)).support,
      right = execution.respond (application setup leaks) owner response := by
  classical
  let app := application setup leaks
  let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
    (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
  obtain ⟨chosen, supported, same⟩ := resume_action app strategy owner players execution
    (BindingMemory.atRecall (runtime setup) leaks reference) (right, memory) reached
  have rightEq : right = execution.respond app owner chosen.1 :=
    (congrArg Prod.fst same).symm
  have legal := BindingMemory.retainedImplementation_response_available (runtime setup) leaks
    (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
      (BindingMemory.atRecall (runtime setup) leaks reference)
        (execution.recall owner, execution.observe app owner) chosen supported
  have owned : (graph setup).actor? event = some owner := by
    have actor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq ((graph setup).nodes event)] at actor
    exact actor
  exact ⟨chosen.1, bounds.ordinary_binding_recorded (runtime setup) leaks owner
    (execution.recall owner) (execution.observe app owner) event payload outputEq codeEq node
      ((soleReady_of_ready setup execution.application ready).ownTurn owned) owned
      ((execution.application.publicView_eventReady event).mpr ready) recorded
        chosen.1 (sourceServiceMenu_in_compiled setup leaks bounds rosters owner _ _ legal),
    rightEq⟩

private theorem recorded_binding_resources
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (owner : Player) (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (ready : execution.application.config.cut.Ready event)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (remaining : Nat)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some owner, execution⟩))
    :
    let serial := execution.application.publicView.bindingCount owner
    let nonce := execution.network.ledger.countP (fun message => message.sender = owner)
    let message : Message Player (WitnessedPacket (graph setup)) :=
      ⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩
    ∃ value : L.Val payload,
      execution.application.config.cut.Ready event ∧
      execution.application.WithinDeadline (runtime setup) event ∧
      execution.InputRecall (application setup leaks) ∧
      execution.network.SerialsBeforeNext ∧
      execution.application.HandleUnused (owner, .prepared serial) ∧
      execution.network.nextSerial owner ≠ nonce ∧
      execution.application.candidates.lookup (owner, .prepared serial) =
        .openable ⟨payload, value⟩ ∧
      execution.application.accepted (.inr event) = none ∧
      message ∈ execution.network.pending ∧
      message.id ∉ execution.network.ledger.map Message.id ∧
      execution.network.Satisfies (fun packet =>
        packet.id ∈ execution.network.ledger.map Message.id ∨ packet = message) := by
  classical
  intro serial nonce message
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  have owned : (graph setup).actor? event = some owner := by
    have actor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq ((graph setup).nodes event)] at actor
    exact actor
  obtain ⟨ready, timely, _, recalled, _, serials, _⟩ :=
    sourceService_binding_decision_resources setup leaks bounds values capacity rosters
      opportunities network owner ⟨remaining, some owner, execution⟩ trace rfl event ready
        owner payload outputEq codeEq node owned
  obtain ⟨value, _, _, candidate, vacant, nextSerial, pending, packets, _, _⟩ :=
    sourceService_recorded_binding_resources setup leaks bounds values capacity rosters
      opportunities network owner ⟨remaining, some owner, execution⟩ trace rfl event ready
        owner payload outputEq codeEq node owned recorded
  dsimp only at ready timely recalled serials candidate vacant nextSerial pending packets
  have unused : execution.application.HandleUnused (owner, .prepared serial) := by
    obtain ⟨before, _, _, selected, _, _, _, selectedEq, _, publicEq, _, unused, _⟩ :=
      sourceService_submitted_binding setup leaks bounds values capacity rosters opportunities
        network owner ⟨remaining, some owner, execution⟩ trace rfl event ready owner
          payload outputEq codeEq node owned recorded
    rw [selectedEq] at unused
    intro field associated
    apply unused field
    exact (congrFun (congrArg PublicView.accepted publicEq) field).trans associated
  have repeated : execution.network.nextSerial owner ≠ nonce := by
    dsimp only [nonce]
    omega
  have unpublished : message.id ∉ execution.network.ledger.map Message.id := by
    obtain ⟨before, value, _, selected, visits, middle, sample, _, _, _, _, _, _, beforeSerials,
        accounted, _, reached, sampled⟩ :=
      sourceService_submitted_binding setup leaks bounds values capacity rosters opportunities
        network owner ⟨remaining, some owner, execution⟩ trace rfl event ready owner
          payload outputEq codeEq node owned recorded
    have ledger := (runtime setup).player_window_ledger leaks menu.uniformResponses network visits
      (before.respond app owner
        ((runtime setup).reactiveBinding leaks owner event payload (.success value) selected))
      middle reached
    have currentLedger : execution.network.ledger = before.network.ledger := by
      dsimp only at sampled
      rw [sampled]
      exact ledger.trans (app.respond_ledger before owner _)
    change (owner, nonce) ∉ execution.network.ledger.map Message.id
    dsimp only [nonce]
    rw [currentLedger, ← accounted owner]
    exact beforeSerials.next_unpublished owner
  exact ⟨value, ready, timely, recalled, serials, unused, repeated, candidate, vacant,
    pending, unpublished, packets⟩

theorem recorded_binding_history_response_block_coupling
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
    (prior execution : (application setup leaks).Execution)
    (sampled : execution ∈
      (prior.environmentStep (application setup leaks) (.activate owner)).support)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (ready : execution.application.config.cut.Ready event)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (remaining : Nat)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some owner, execution⟩))
    (before after : List (ServiceInstruction (graph setup))) (visits : List Player) (ticks : Nat)
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]) ++ after)
    (position : execution.environmentRecall.length = before.length)
    (enough : (visits.map (ServiceInstruction.player (graph := graph setup)) ++
      (ServiceInstruction.includeLatest event owner ::
        List.replicate ticks ServiceInstruction.tick ++
        [ServiceInstruction.expire event])).length ≤
        remaining) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let reference := execution.recall owner
    let memory := BindingMemory.atRecall (runtime setup) leaks reference
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    let tail := visits.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (app.invoke players owner execution).bind
        ((runtime setup).runInteractionPlan leaks players network tail) ∧
      coupling.map Prod.snd = (strategy.resume owner players (some owner) execution memory).bind
        (fun next => strategy.runJoint owner players (rosterScheduler setup leaks rosters network)
          tail.length next.1 next.2) ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining - tail.length, none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
  classical
  intro app players reference memory strategy tail
  let menu := sourceServiceMenu setup leaks bounds rosters
  let scheduler := rosterScheduler setup leaks rosters network
  let serial := execution.application.publicView.bindingCount owner
  let nonce := execution.network.ledger.countP (fun message => message.sender = owner)
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩
  have owned : (graph setup).actor? event = some owner := by
    have actor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq ((graph setup).nodes event)] at actor
    exact actor
  obtain ⟨value, ready, timely, recalled, serials, unused, repeated, candidate, vacant,
      pending, unpublished, packets⟩ :=
    recorded_binding_resources setup leaks bounds values capacity rosters opportunities network
      owner execution event payload outputEq codeEq node ready recorded remaining trace
  have coverage : bounds.compiledActions (runtime setup) leaks owner (execution.recall owner)
      (execution.observe app owner) ⊆ menu.actions owner (execution.recall owner)
        (execution.observe app owner) := by
    intro response member
    have optional : ¬ bindingRequired setup leaks rosters owner (execution.recall owner)
        (execution.observe app owner) := by
      rintro ⟨other, _, otherTurn, _, _, _, unsent, _⟩
      cases Option.some.inj (otherTurn.symm.trans
        (ownTurn?_of_ready setup execution.application ready owned))
      simp only [recorded, Bool.true_eq_false] at unsent
    change response ∈ sourceServiceActions setup leaks bounds rosters owner _ _
    rw [sourceServiceActions, ite_eq_right optional]
    exact member
  have frame := BindingMemory.frame_atRecall (runtime setup) leaks owner execution
  obtain ⟨first, firstLeft, firstRight, firstRelated⟩ :=
    frame.repeated_submission_stopped_response_coupling bounds menu players reference
      (Nat.le_refl _)
      recalled recalled remaining serials repeated coverage
      (by simpa only [players, Function.update_self] using available _ _)
  have firstTrace (next) (member : next ∈ first.support) :
      Nonempty ((menu.protocol (initialLaw setup) (rosterPlan setup rosters).length scheduler).Trace
        (some ⟨remaining, none, next.2.1⟩)) := by
    have reached : next.2 ∈ (strategy.resume owner players (some owner) execution memory).support :=
      by rw [← firstRight, PMF.support_map]; exact ⟨next, member, rfl⟩
    apply menu.trace_implementation_resume (initialLaw setup) (rosterPlan setup rosters).length
      scheduler strategy owner players _ _ remaining (some owner) execution memory trace next.2
        reached
    · intro who different
      simpa only [players, Function.update_of_ne different] using
        (sourceServiceMenu_in_effective setup leaks bounds rosters).decoded_admissible
          (initialLaw setup) (rosterPlan setup rosters).length scheduler source target agrees who
    · intro next past view response member
      exact BindingMemory.retainedImplementation_response_available (runtime setup) leaks menu
        owner reference (players owner) next (past, view) response member
  have badRecord (next) (member : next ∈ first.support)
      (record : app.TrafficRecord)
      (step : app.trafficStep (some ⟨remaining, some owner, execution⟩)
        (some ⟨remaining, none, next.1⟩) = [record]) :
      record ∈ app.executionTraffic next.1 := by
    have reached : next.1 ∈ (app.invoke players owner execution).support := by
      rw [← firstLeft, PMF.support_map]
      exact ⟨next, member, rfl⟩
    obtain ⟨response, _, same⟩ := PMF.support_map .. ▸ reached
    rw [← same, app.executionTraffic_activated_response prior execution owner response
      remaining sampled]
    have publicSame : prior.observeEnvironment app = execution.observeEnvironment app := by
      rw [ReactiveApplication.Execution.activation_samples, PMF.support_map] at sampled
      obtain ⟨observed, _, equal⟩ := sampled
      rw [← equal]
      rfl
    have trafficSame := app.trafficStep_public
      ⟨remaining + 1, none, prior⟩ ⟨remaining, none, next.1⟩
      ⟨remaining, some owner, execution⟩ ⟨remaining, none, next.1⟩ publicSame rfl
    rw [same, trafficSame, step]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have tails (next) (member : next ∈ first.support) :
      ∃ joint : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
        joint.map Prod.fst = (runtime setup).runInteractionPlan leaks players network tail next.1 ∧
        joint.map Prod.snd =
          strategy.runJoint owner players scheduler tail.length next.2.1 next.2.2 ∧
        ∀ final ∈ joint.support,
          (∃ record ∈ app.executionTraffic final.1, record.input.envelope.sender = owner ∧
            (runtime setup).permittedServiceEnvelope record.observation record.ledger
              record.input.envelope = false) ∨
          BindingMemory.Frame (runtime setup) leaks final.2.2 owner final.1 final.2.1 := by
    rcases firstRelated next member with ⟨record, step, authored, rejected⟩ | good
    · let left := (runtime setup).runInteractionPlan leaks players network tail next.1
      let right := strategy.runJoint owner players scheduler tail.length next.2.1 next.2.2
      refine ⟨bindPairLaw left (fun _ => right), bindPairLaw_map_fst ..,
        bindPairLaw_const_map_snd .., ?_⟩
      intro final supported
      have reached : final.1 ∈ left.support := by
        rw [← bindPairLaw_map_fst left (fun _ => right), PMF.support_map]
        exact ⟨final, supported, rfl⟩
      exact Or.inl ⟨record, ((runtime setup).executionTraffic_runInteractionPlan leaks players
        network tail next.1 final.1 reached).subset (badRecord next member record step),
        authored, rejected⟩
    · obtain ⟨paired, started, shadow, viewEq⟩ := good
      have rightSupport : next.2 ∈
          (strategy.resume owner players (some owner) execution memory).support := by
        rw [← firstRight, PMF.support_map]
        exact ⟨next, member, rfl⟩
      have leftRecall : next.1.InputRecall app := by
        have reached : next.1 ∈ (app.invoke players owner execution).support := by
          rw [← firstLeft, PMF.support_map]
          exact ⟨next, member, rfl⟩
        obtain ⟨response, _, same⟩ := PMF.support_map .. ▸ reached
        rw [← same]
        exact app.respond_inputRecall execution owner response recalled
      obtain ⟨response, replay, rightEq⟩ := recorded_resume_transport setup leaks bounds rosters
        players owner event payload outputEq codeEq node execution next.2.1 next.2.2 reference
          recorded ready rightSupport
      exact recorded_response_tail setup leaks bounds rosters network players owner event payload
        outputEq codeEq node serial nonce value execution next.1 next.2.1 next.2.2 paired
        (by simpa only [BindingMemory.atRecall] using shadow) reference started response replay
        rightEq recalled leftRecall serials repeated recorded ready timely vacant unused
        candidate pending unpublished packets
        (by simpa only [players, Function.update_self] using available) before after visits ticks
        split position
  let later := fun next member => (tails next member).choose
  refine ⟨first.bindOnSupport later, ?_, ?_, ?_⟩
  · rw [map_bindOnSupport]
    calc
      _ = first.bind (fun next =>
          (runtime setup).runInteractionPlan leaks players network tail next.1) := by
        apply bindOnSupport_eq_bind_of_eq_on_support _
        intro next member
        exact (tails next member).choose_spec.1
      _ = (first.map Prod.fst).bind
          ((runtime setup).runInteractionPlan leaks players network tail) :=
        (PMF.bind_map ..).symm
      _ = _ := by rw [firstLeft]
  · rw [map_bindOnSupport]
    calc
      _ = first.bind (fun next =>
          strategy.runJoint owner players scheduler tail.length next.2.1 next.2.2) := by
        apply bindOnSupport_eq_bind_of_eq_on_support _
        intro next member
        exact (tails next member).choose_spec.2.1
      _ = (first.map Prod.snd).bind (fun next =>
          strategy.runJoint owner players scheduler tail.length next.1 next.2) := by
        exact (PMF.bind_map first Prod.snd (fun next =>
          strategy.runJoint owner players scheduler tail.length next.1 next.2)).symm
      _ = _ := by rw [firstRight]
  · intro final supported
    obtain ⟨next, member, reached⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
    refine ⟨?_, (tails next member).choose_spec.2.2 final reached⟩
    have rightSupport : final.2 ∈
        (strategy.runJoint owner players scheduler tail.length next.2.1 next.2.2).support := by
      rw [← (tails next member).choose_spec.2.1, PMF.support_map]
      exact ⟨final, reached, rfl⟩
    apply menu.trace_implementation_runJoint (initialLaw setup) (rosterPlan setup rosters).length
      scheduler strategy owner players _ _ (remaining - tail.length) tail.length next.2.1
        next.2.2 _ final.2 rightSupport
    · intro who different
      simpa only [players, Function.update_of_ne different] using
        (sourceServiceMenu_in_effective setup leaks bounds rosters).decoded_admissible
          (initialLaw setup) (rosterPlan setup rosters).length scheduler source target agrees who
    · intro next past view response member
      exact BindingMemory.retainedImplementation_response_available (runtime setup) leaks menu
        owner reference (players owner) next (past, view) response member
    · have enoughTail : tail.length ≤ remaining := enough
      rw [Nat.sub_add_cancel enoughTail]
      exact (firstTrace next member).some

end Vegas
