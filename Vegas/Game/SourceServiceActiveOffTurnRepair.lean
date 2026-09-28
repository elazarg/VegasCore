/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceOffTurnWindow
import Vegas.Pending.ReactiveOffTurnRepair
import Interaction.ReactiveTrafficContinuation

/-! # An off-turn response at an actual retained information site

The actual response is coupled to the fixed legal repair without repeating
its passive activation. Every supported repair endpoint has a retained idle
history. A fresh off-turn submission supplies persistent authentic traffic
evidence; replay and silence preserve the private repair frame.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem off_turn_history_response_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
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
    (offTurn : ∀ event, original.application.serviceGrant = some event →
      (graph setup).actor? event ≠ some owner)
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
  have rawTrace := menu.toRawTrace (initialLaw setup) (rosterPlan setup rosters).length
    scheduler trace
  have rightRecall : repaired.InputRecall app :=
    app.history_inputRecall (initialLaw setup) (rosterPlan setup rosters).length scheduler rawTrace
  have rightSerials : repaired.network.SerialsBeforeNext :=
    app.serialsBeforeNext_history scheduler (initialLaw setup) (rosterPlan setup rosters).length
      rawTrace
  have coverage (response : app.Action)
      (supported : response ∈ (app.replayPolicy (repaired.recall owner)
        (repaired.observe app owner)).support) :
      response ∈ menu.actions owner (repaired.recall owner) (repaired.observe app owner) := by
    apply off_turn_replay_sourceService setup leaks bounds rosters owner _ _ _ response supported
    intro event granted
    apply offTurn event
    exact (congrArg PublicView.serviceGrant frame.publicView).trans granted
  obtain ⟨coupling, leftLaw, rightLaw, related⟩ := frame.off_turn_stopped_response_coupling
    bounds menu players reference started leftRecall rightRecall (frame.network ▸ rightSerials)
      remaining offTurn coverage
        (by simpa only [players, Function.update_self] using available _ _)
  refine ⟨coupling, leftLaw, rightLaw, ?_⟩
  intro next member
  have rightSupport : next.2 ∈
      (strategy.resume owner players (some owner) repaired memory).support := by
      rw [← rightLaw, FinDist.support_map]
      exact ⟨next, member, rfl⟩
  refine ⟨?_, ?_⟩
  · apply menu.trace_implementation_resume (initialLaw setup) (rosterPlan setup rosters).length
      scheduler strategy owner players _ _ remaining (some owner) repaired memory trace
        next.2 rightSupport
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
    · exact Or.inr ⟨good.1, good.2.1⟩

end Vegas
