/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceMenu
import Vegas.Game.SourceServiceImplementationSegment
import Vegas.Pending.ReactiveBindingForeignWindow
import Vegas.Pending.ReactiveBindingContinuation
import Interaction.ReactiveMenuImplementation

/-! # Real retained traces through the other players' response visits

The original target policies stay unchanged. Profile extension is used only
at actual retained inputs; the frame supplies their equal original inputs.
The joint private-memory law and a legal retained trace survive the complete
foreign prefix, so subsequent source-service resource theorems apply there.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem repair_foreign_roster_coupling
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
    (reference : List (application setup leaks).PlayerEntry)
    (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (remaining : Nat) (visits : List Player) (absent : owner ∉ visits)
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
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player) original ∧
      coupling.map Prod.snd = strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network) visits.length repaired memory ∧
      ∀ next ∈ coupling.support,
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2 = memory ∧
          Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
            (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
              (some ⟨remaining, none, next.2.1⟩)) := by
  intro app players strategy
  let menu := sourceServiceMenu setup leaks bounds rosters
  let scheduler := rosterScheduler setup leaks rosters network
  obtain ⟨physical, first, second, related⟩ := frame.foreign_window_coupling players network
    visits absent
  let coupling := physical.map fun pair => (pair.1, pair.2, memory)
  have leftLaw : coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) original := by
    rw [FinDist.map_comp]
    exact first
  have rightLaw : coupling.map Prod.snd =
      strategy.runJoint owner players scheduler visits.length repaired memory := by
    have law := roster_segment_runJoint setup leaks rosters network strategy owner players
      before (visits.map ServiceInstruction.player) after split
      (by simpa using absent) repaired memory (by rw [← frame.service]; exact position)
    rw [List.length_map] at law
    rw [law, ← second, FinDist.map_comp, FinDist.map_comp]
    rfl
  refine ⟨coupling, leftLaw, rightLaw, ?_⟩
  intro next supported
  have rightSupport : next.2 ∈
      (strategy.runJoint owner players scheduler visits.length repaired memory).support := by
    rw [← rightLaw, FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  obtain ⟨pair, chosen, rfl⟩ := FinDist.support_map .. ▸ supported
  refine ⟨related pair chosen, rfl, ?_⟩
  apply menu.trace_implementation_runJoint (initialLaw setup) (rosterPlan setup rosters).length
    scheduler strategy owner players _ _ remaining visits.length repaired memory trace
      (pair.2, memory) rightSupport
  · intro who different
    simpa only [players, Function.update_of_ne different] using
      (sourceServiceMenu_in_effective setup leaks bounds rosters).decoded_admissible
        (initialLaw setup) (rosterPlan setup rosters).length scheduler source target agrees who
  · intro next past view response member
    exact BindingMemory.retainedImplementation_response_available (runtime setup) leaks menu
      owner reference (players owner) next (past, view) response member

end Vegas
