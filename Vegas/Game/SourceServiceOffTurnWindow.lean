/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRepeatedWindow
import Vegas.Game.SourceServiceRepairForeignWindow
import Vegas.Pending.ReactiveOffTurnWindow

/-! # Actual retained histories through an off-turn stopped roster

The focal player may respond at every visit before another player's protected
inclusion, or before a public sample. The exact original policies are kept.
Only the repaired side uses retained actions; profile extension is invoked at
its real histories to justify the unchanged opponents there.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem off_turn_replay_sourceService
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (idle : view.application.publicView.Idle who)
    (response : (application setup leaks).Action)
    (replay : response ∈ ((application setup leaks).replayPolicy past view).support) :
    response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view := by
  classical
  have optional : ¬ bindingRequired setup leaks rosters who past view := by
    rintro ⟨event, _, _, _, owned, ready, _⟩
    exact idle event ready owned
  change response ∈ sourceServiceActions setup leaks bounds rosters who past view
  rw [sourceServiceActions, ite_eq_right optional]
  exact bounds.replay_compiled (runtime setup) leaks who past view response replay

/-- No source-owner roster restriction is imposed. Every focal visit is
classified by the focal player's idleness, while all repaired endpoints remain
actual retained histories, even on the stopped branches. -/
theorem off_turn_roster_stopped_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
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
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (application setup leaks))
    (rightRecall : repaired.InputRecall (application setup leaks))
    (serials : original.network.SerialsBeforeNext)
    (idle : original.application.publicView.Idle owner)
    (remaining : Nat) (visits : List Player)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining + visits.length, none, repaired⟩))
    (before after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++ after)
    (position : original.environmentRecall.length = before.length) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player) original ∧
      coupling.map Prod.snd = strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network) visits.length repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining, none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow = memory.shadow ∧
          next.2.1.application.playerView owner = repaired.application.playerView owner) := by
  intro app players strategy
  let menu := sourceServiceMenu setup leaks bounds rosters
  let scheduler := rosterScheduler setup leaks rosters network
  obtain ⟨coupling, first, second, related⟩ := frame.run_off_turn_stopped_coupling bounds
    menu players scheduler reference started leftRecall rightRecall serials idle
    (off_turn_replay_sourceService setup leaks bounds rosters owner)
    (by simpa only [players, Function.update_self] using available)
    before.length visits.length position
    (fun execution lower upper command supported => roster_activation_segment setup leaks
      rosters network before after visits split execution lower upper command supported)
  refine ⟨coupling, ?_, second, ?_⟩
  · rw [first]
    have law := roster_segment_rounds setup leaks rosters network players before
      (visits.map ServiceInstruction.player) after split original position
    simpa only [List.length_map] using law
  · intro next supported
    refine ⟨?_, related next supported⟩
    have rightSupport : next.2 ∈
        (strategy.runJoint owner players scheduler visits.length repaired memory).support := by
      rw [← second, PMF.support_map]
      exact ⟨next, supported, rfl⟩
    apply menu.trace_implementation_runJoint (initialLaw setup) (rosterPlan setup rosters).length
      scheduler strategy owner players _ _ remaining visits.length repaired memory trace
        next.2 rightSupport
    · intro who different
      simpa only [players, Function.update_of_ne different] using
        (sourceServiceMenu_in_effective setup leaks bounds rosters).decoded_admissible
          (initialLaw setup) (rosterPlan setup rosters).length scheduler source target agrees who
    · intro next past view response member
      exact BindingMemory.retainedImplementation_response_available (runtime setup) leaks menu
        owner reference (players owner) next (past, view) response member

end Vegas
