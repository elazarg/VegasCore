/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceResolutionRepair
import Vegas.Game.SourceServiceRepairForeignWindow
import Vegas.Pending.ReactiveResolutionAuditStep
import Interaction.ReactiveTrafficContinuation

/-! # A guarded resolution response at an actual retained opportunity

The response starts at the actual sampled information site. Every effective
action is coupled to the same private implementation or yields persistent
public traffic evidence, with a real retained successor history.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem resolution_history_response_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ∀ event actor payload,
      (graph setup).outputLayout event = .binding actor payload → actor ∈ rosters event)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
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
    (granted : repaired.application.serviceGrant = some event)
    (remaining : Nat)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some owner, repaired⟩)) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining, none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length) := by
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
      network profile owner ⟨remaining, some owner, repaired⟩ trace rfl event granted
        owner owned
  have rightReady : repaired.application.config.cut.Ready event := ready
  have rightTimely : repaired.application.WithinDeadline (runtime setup) event := timely
  have rightBound : repaired.application.BindingInvariant := rightBinding
  have rightRecalled : repaired.InputRecall app := rightRecall
  have rightSerials : repaired.network.SerialsBeforeNext :=
    app.serialsBeforeNext_history scheduler (initialLaw setup) (rosterPlan setup rosters).length
      (menu.toRawTrace (initialLaw setup) (rosterPlan setup rosters).length scheduler trace)
  have originalGrant : original.application.serviceGrant = some event :=
    (congrArg PublicView.serviceGrant frame.publicView).trans granted
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
      original.network.ledger.countP (fun message => message.sender = owner) →
      (runtime setup).eventRecorded leaks (original.recall owner) event = false := by
    intro counted
    rw [(runtime setup).eventRecorded_congr leaks _ _ frame.submissions event]
    apply first
    change repaired.network.nextSerial owner =
      repaired.network.ledger.countP (fun message => message.sender = owner)
    rwa [frame.network] at counted
  obtain ⟨coupling, leftLaw, rightLaw, related⟩ := frame.resolution_stopped_response_coupling
    bounds menu players reference started leftRecall rightRecalled sound leftBinding rightBound
      remaining event payload binding checks outputEq codeEq node originalGrant originalReady
        originalTimely originalFirst (frame.network ▸ rightSerials) (by
          intro response member
          have optional : ¬ bindingRequired setup leaks rosters owner
              (repaired.recall owner) (repaired.observe app owner) := by
            rintro ⟨candidate, _, selectedGrant, bindingOutput, _⟩
            cases Option.some.inj (selectedGrant.symm.trans granted)
            rw [outputEq] at bindingOutput
            cases bindingOutput
          change response ∈ sourceServiceActions setup leaks bounds rosters owner _ _
          rw [sourceServiceActions, ite_eq_right optional]
          exact member)
        (by simpa only [players, Function.update_self] using available _ _)
  refine ⟨coupling, leftLaw, rightLaw, ?_⟩
  intro next member
  have rightSupport :
      next.2 ∈ (strategy.resume owner players (some owner) repaired memory).support :=
    by
      rw [← rightLaw, FinDist.support_map]
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
  · rcases related next member with bad | good
    · obtain ⟨record, step, authored, rejected⟩ := bad
      have reached : next.1 ∈ (app.invoke players owner original).support := by
        rw [← leftLaw, FinDist.support_map]
        exact ⟨next, member, rfl⟩
      obtain ⟨response, _, same⟩ := FinDist.support_map .. ▸ reached
      refine Or.inl ⟨record, ?_, authored, rejected⟩
      rw [← same, app.executionTraffic_activated_response prior original owner response
        remaining sampled]
      have publicSame : prior.observeEnvironment app = original.observeEnvironment app := by
        have supported := sampled
        rw [ReactiveApplication.Execution.activation_samples, FinDist.support_map] at supported
        obtain ⟨observed, _, equal⟩ := supported
        rw [← equal]
        rfl
      have trafficSame := app.trafficStep_public
        ⟨remaining + 1, none, prior⟩ ⟨remaining, none, next.1⟩
        ⟨remaining, some owner, original⟩ ⟨remaining, none, next.1⟩ publicSame rfl
      rw [same, trafficSame, step]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact Or.inr good

end Vegas.SourceProgram.RevealService
