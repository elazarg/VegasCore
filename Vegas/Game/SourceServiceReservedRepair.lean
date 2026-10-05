/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceInclusionSupport
import Vegas.Game.SourceServiceImplementationSegment
import Vegas.Game.SourceServiceRepairForeignWindow
import Vegas.Pending.ReactiveBindingReservedInclusion

/-! # Reserved resolution repair at actual retained histories

The legal trace supplies packet conformance, the owner's turn, and the
repaired binding invariant. Protected inclusion and expiry then preserve the
joint frame under arbitrary deferred guards, including legal withholding.
The fixed implementation retains its memory and an actual retained endpoint.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem resolution_history_tail_coupling
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
    (reference : List (application setup leaks).PlayerEntry)
    (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (sound : ((runtime setup).packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (event : (graph setup).EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef (graph setup).layout (.binding actor payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve actor payload binding checks)
    (node : nodeView (graph setup) event = .resolve actor payload binding checks outputEq codeEq)
    (remaining ticks : Nat)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining + (ticks + 2), none, repaired⟩))
    (before after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++
      (.includeLatest event actor :: List.replicate ticks .tick ++ [.expire event]) ++ after)
    (position : original.environmentRecall.length = before.length) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    let ending : List (ServiceInstruction (graph setup)) :=
      .includeLatest event actor :: List.replicate ticks .tick ++ [.expire event]
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
        ending original ∧
      coupling.map Prod.snd = strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network) ending.length repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining, none, next.2.1⟩)) ∧
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
        next.2.2 = memory := by
  classical
  intro app players strategy ending
  let menu := sourceServiceMenu setup leaks bounds rosters
  let scheduler := rosterScheduler setup leaks rosters network
  have cursor : repaired.environmentRecall.length = before.length := by
    rw [← frame.service]
    exact position
  have selected : (rosterPlan setup rosters)[repaired.environmentRecall.length]? =
      some (.includeLatest event actor) := by
    rw [cursor, split, List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self]
    rfl
  obtain ⟨_, initial, _, Γ, config, refs, boundary, _, _, _, _, _, ready, _,
      _, rightBinding, _, _, _, conforming⟩ := sourceService_inclusion_boundary setup leaks
    bounds values capacity rosters opportunities network
      ⟨remaining + (ticks + 2), none, repaired⟩ trace rfl event actor selected
  have originalSole : original.application.publicView.SoleReady event := by
    rw [frame.publicView]
    exact soleReady_of_ready setup repaired.application ready
  have permitted : ∀ message ∈ original.network.pending,
      (runtime setup).permittedServiceEnvelope original.application.publicView
        original.network.ledger message = true := by
    rw [frame.network, frame.publicView]
    exact conforming.pending
  obtain ⟨physical, first, second, related⟩ := frame.resolution_reserved_tail_coupling
    onlyBindings sound leftBinding rightBinding players network event actor payload binding checks
      outputEq codeEq node originalSole permitted ticks
  let coupling := physical.map fun pair => (pair.1, pair.2, memory)
  have leftLaw : coupling.map Prod.fst =
      (runtime setup).runInteractionPlan leaks players network ending original := by
    simpa only [coupling, PMF.map_comp, Function.comp_def] using first
  have rightLaw : coupling.map Prod.snd = strategy.runJoint owner players scheduler
      ending.length repaired memory := by
    rw [roster_segment_runJoint setup leaks rosters network strategy owner players before ending
      after split (by simp [ending]) repaired memory cursor]
    change (physical.map _).map Prod.snd = _
    rw [PMF.map_comp, ← second, PMF.map_comp]
    rfl
  refine ⟨coupling, leftLaw, rightLaw, ?_⟩
  intro next supported
  obtain ⟨pair, member, rfl⟩ := PMF.support_map .. ▸ supported
  refine ⟨?_, related pair member, rfl⟩
  have reached : (pair.2, memory) ∈
      (strategy.runJoint owner players scheduler ending.length repaired memory).support := by
    rw [← rightLaw, PMF.support_map]
    refine ⟨(pair.1, pair.2, memory), ?_, rfl⟩
    rw [PMF.support_map]
    exact ⟨pair, member, rfl⟩
  apply menu.trace_implementation_runJoint (initialLaw setup) (rosterPlan setup rosters).length
    scheduler strategy owner players _ _ remaining ending.length repaired memory _
      (pair.2, memory) reached
  · intro who different
    simpa only [players, Function.update_of_ne different] using
      (sourceServiceMenu_in_effective setup leaks bounds rosters).decoded_admissible
        (initialLaw setup) (rosterPlan setup rosters).length scheduler source target agrees who
  · intro next past view response supported
    exact BindingMemory.retainedImplementation_response_available (runtime setup) leaks menu
      owner reference (players owner) next (past, view) response supported
  · have length : ending.length = ticks + 2 := by simp [ending]
    rw [length]
    exact trace

end Vegas
