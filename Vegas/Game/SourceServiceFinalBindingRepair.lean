/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecisionSupport
import Vegas.Game.SourceServiceImplementationSegment
import Vegas.Pending.ReactiveBindingFinalBlock

/-! # The final binding opportunity at an actual retained history

Allocation and deadline evidence are derived from the actual retained trace.
The complete response, arbitrary foreign tail and protected settlement have
the fixed joint private-implementation law. Every original endpoint either
remains framed or carries authentic traffic/public omission evidence.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem final_binding_history_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (players : Player → (application setup leaks).Policy)
    (owner : Player) (remaining : Nat)
    (prior original repaired : (application setup leaks).Execution)
    (sampled : original ∈
      (prior.environmentStep (application setup leaks) (.activate owner)).support)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some owner, repaired⟩))
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (recalled : original.InputRecall (application setup leaks))
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (ready : repaired.application.config.cut.Ready event)
    (unsent : (runtime setup).eventRecorded leaks (repaired.recall owner) event = false)
    (available : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (application setup leaks) owner)).support,
        response ∈ (bounds.menu (runtime setup) leaks).actions owner (original.recall owner)
          (original.observe (application setup leaks) owner))
    (before after : List (ServiceInstruction (graph setup))) (visits : List Player)
    (absent : owner ∉ visits)
    (split : rosterPlan setup rosters = before ++
      (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
      (List.replicate ((runtime setup).deadline event) .tick ++ [.expire event]) ++ after)
    (position : original.environmentRecall.length = before.length) :
    let app := application setup leaks
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    let plan := (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
      (List.replicate ((runtime setup).deadline event) .tick ++ [.expire event])
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (app.invoke players owner original).bind
        ((runtime setup).runInteractionPlan leaks players network plan) ∧
      coupling.map Prod.snd =
        (strategy.resume owner players (some owner) repaired memory).bind (fun next =>
          strategy.runJoint owner players (rosterScheduler setup leaks rosters network)
            plan.length next.1 next.2) ∧
      ∀ next ∈ coupling.support,
        (∃ record ∈ app.executionTraffic next.1, record.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.envelope = false) ∨
        event ∈ next.1.application.missedEvents ∨
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 := by
  classical
  intro app strategy plan
  have owned : (graph setup).actor? event = some owner := by
    have actor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq ((graph setup).nodes event)] at actor
    exact actor
  obtain ⟨ready, timely, _, _, _, serials, beforeFirst⟩ :=
    sourceService_binding_decision_resources setup leaks bounds values capacity rosters
      opportunities network owner ⟨remaining, some owner, repaired⟩ trace rfl event
        ready owner payload outputEq codeEq node owned
  obtain ⟨small, selected, fresh, unused, vacant, _, published⟩ := beforeFirst unsent
  obtain ⟨_, _, initial, _, _, Γ, names, residual, residualProfile, source, refs, embedding,
      refsBefore, _, _, _, boundary, _, _, checkpoint, _, _, _, _, _, publicEq, _, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network (failureProfile setup.program) owner ⟨remaining, some owner, repaired⟩ trace rfl
  have boundaryReady : boundary.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← publicEq, State.publicView_eventReady]
    exact ready
  obtain ⟨entered, activated⟩ := checkpoint.invariant.activatedAt_eq_some_of_ready_actor
    event boundaryReady (by rw [owned]; rfl)
  have currentActivated : repaired.application.activatedAt event = some entered := by
    rw [show repaired.application.activatedAt = boundary.application.activatedAt from
      congrArg PublicView.activatedAt publicEq]
    exact activated
  have currentAge : entered ≤ repaired.application.clock := by
    rw [show repaired.application.clock = boundary.application.clock from
      congrArg PublicView.clock publicEq]
    exact checkpoint.invariant.activated_le event entered activated
  have counted : original.application.publicView.bindingCount owner =
      repaired.application.publicView.bindingCount owner :=
    congrArg (fun view => view.bindingCount owner) frame.publicView
  have originalReady : original.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, frame.publicView, State.publicView_eventReady]
    exact ready
  have clocks : original.application.clock = repaired.application.clock :=
    congrArg PublicView.clock frame.publicView
  have activations : original.application.activatedAt = repaired.application.activatedAt :=
    congrArg PublicView.activatedAt frame.publicView
  have originalTimely : original.application.WithinDeadline (runtime setup) event := by
    unfold State.WithinDeadline
    rw [clocks, activations]
    exact timely
  have originalActivated : original.application.activatedAt event = some entered := by
    rw [activations]
    exact currentActivated
  have due : (runtime setup).deadline event ≤ original.application.clock +
      (runtime setup).deadline event - entered := by
    rw [clocks]
    omega
  have accepted : original.application.accepted = repaired.application.accepted :=
    congrArg PublicView.accepted frame.publicView
  have originalVacant : original.application.accepted (.inr event) = none := by
    rw [accepted]
    exact vacant
  have originalUnused : original.application.HandleUnused
      (owner, .prepared (original.application.publicView.bindingCount owner)) := by
    rw [counted]
    intro field associated
    exact unused field ((congrFun accepted field).symm.trans associated)
  have originalPublished : original.network.Satisfies fun message => message.sender = owner →
      message.id ∈ original.network.ledger.map Message.id := by
    rw [frame.network]
    exact published.mono fun _ known _ => known
  have default : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values := by
    have covered := values event
    rw [outputEq] at covered
    exact covered (L.someValue payload)
  obtain ⟨coupling, first, second, related⟩ := frame.required_binding_final_block_coupling bounds
    (sourceServiceMenu setup leaks bounds rosters) players network prior sampled reference started
      recalled remaining event payload outputEq codeEq node
      (by rw [counted]; exact (frame.slots _).mpr fresh)
      (by rw [counted]; exact selected) (by rw [counted]; exact small) default
      ((soleReady_of_ready setup original.application originalReady).ownTurn owned)
      originalReady originalTimely originalUnused unsent originalVacant originalPublished
      entered ((runtime setup).deadline event) originalActivated due visits absent
      (frame.network ▸ serials)
      (required_decision_sourceService setup leaks bounds rosters owner _ _) available
  refine ⟨coupling, first, ?_, related⟩
  rw [second]
  apply bind_congr_on_support _
  intro next supported
  symm
  refine roster_segment_runJoint setup leaks rosters network strategy owner players before plan
    after (by simpa only [plan, List.append_assoc] using split) ?_ next.1 next.2 ?_
  · simpa [plan] using absent
  · simp only [ReactiveApplication.Implementation.resume, ↓reduceIte,
      PMF.support_map] at supported
    obtain ⟨response, _, same⟩ := supported
    rw [← same, app.respond_environmentRecall, ← frame.service]
    exact position

end Vegas
