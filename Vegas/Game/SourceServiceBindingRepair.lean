/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecisionSupport
import Vegas.Pending.ReactiveBindingAuditStep
import Interaction.ReactiveMenuImplementation

/-! # Actual retained histories supply the optional binding repair

The source-service trace supplies allocation, capacity, timing and serial
resources. Every effective original response is coupled to the same private
repair, and every repaired endpoint has another actual retained trace. The
original opponents are not assumed to obey the retained menu everywhere.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- An optional pre-first response at an actual retained history has all the
operational resources required by the stopped repair. Its legal right marginal
can therefore be fed back into the same actual-history resource theorem. -/
theorem optional_binding_history_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ∀ event owner payload,
      (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (owner : Player) (remaining : Nat)
    (original repaired : (application setup leaks).Execution)
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
    (granted : repaired.application.serviceGrant = some event)
    (unsent : (runtime setup).eventRecorded leaks (repaired.recall owner) event = false)
    (optional : ¬ bindingRequired setup leaks rosters owner (repaired.recall owner)
      (repaired.observe (application setup leaks) owner))
    (available : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (application setup leaks) owner)).support,
        response ∈ (bounds.menu (runtime setup) leaks).actions owner (original.recall owner)
          (original.observe (application setup leaks) owner)) :
    let app := application setup leaks
    let menu := sourceServiceMenu setup leaks bounds rosters
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks menu
      owner reference (players owner)
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty ((menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining, none, next.2.1⟩)) ∧
        ((∃ record, app.trafficStep (some ⟨remaining, some owner, original⟩)
            (some ⟨remaining, none, next.1⟩) = [record] ∧
          record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        (BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length)) := by
  classical
  intro app menu strategy
  have owned : (graph setup).actor? event = some owner := by
    have actor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq ((graph setup).nodes event)] at actor
    exact actor
  obtain ⟨ready, _, _, rightRecall, _, serials, beforeFirst⟩ :=
    sourceService_binding_decision_resources setup leaks bounds values capacity rosters
      opportunities network profile owner ⟨remaining, some owner, repaired⟩ trace rfl event
        granted owner payload outputEq codeEq node owned
  obtain ⟨small, selected, fresh, _, _, _, _⟩ := beforeFirst unsent
  have counted : original.application.publicView.bindingCount owner =
      repaired.application.publicView.bindingCount owner :=
    congrArg (fun view => view.bindingCount owner) frame.publicView
  have originalReady : original.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, frame.publicView, State.publicView_eventReady]
    exact ready
  have originalGrant : original.application.serviceGrant = some event := by
    rw [show original.application.serviceGrant = repaired.application.serviceGrant from
      congrArg PublicView.serviceGrant frame.publicView]
    exact granted
  have coverage : bounds.compiledActions (runtime setup) leaks owner (repaired.recall owner)
      (repaired.observe app owner) ⊆ menu.actions owner (repaired.recall owner)
        (repaired.observe app owner) := by
    change _ ⊆ sourceServiceActions setup leaks bounds rosters owner _ _
    rw [sourceServiceActions, ite_eq_right optional]
  have default : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values := by
    have covered := values event
    rw [outputEq] at covered
    exact covered (L.someValue payload)
  obtain ⟨coupling, first, second, related⟩ := frame.binding_stopped_response_coupling bounds menu
    players reference started recalled rightRecall remaining event payload outputEq codeEq node
    (by rw [counted]; exact (frame.slots _).mpr fresh)
    (by rw [counted]; exact selected)
    (by rw [counted]; exact small)
    default originalGrant originalReady
    (fun _ => unsent) (frame.network ▸ serials) coverage available
  refine ⟨coupling, first, second, ?_⟩
  intro next supported
  refine ⟨?_, related next supported⟩
  have rightSupport : next.2 ∈ (strategy.resume owner players (some owner)
      repaired memory).support := by
    rw [← second, FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  simp only [ReactiveApplication.Implementation.resume, ↓reduceIte,
    FinDist.support_map] at rightSupport
  obtain ⟨response, chosen, equal⟩ := rightSupport
  have current := menu.trace_respond (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) remaining repaired owner response.1 trace
      (BindingMemory.retainedImplementation_response_available (runtime setup) leaks menu owner
        reference (players owner) memory (repaired.recall owner, repaired.observe app owner)
          response chosen)
  exact congrArg Prod.fst equal ▸ current

end Vegas.SourceProgram.RevealService
