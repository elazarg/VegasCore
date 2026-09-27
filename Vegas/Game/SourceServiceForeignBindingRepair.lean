/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceInclusionSupport
import Vegas.Game.SourceServiceImplementationSegment
import Vegas.Game.SourceServiceRepairForeignWindow
import Vegas.Pending.ReactiveBindingReservedInclusion

/-! # Foreign binding repair at actual retained histories

The legal trace supplies the conforming envelope and its already fixed typed
candidate. The other player's catalogue is unchanged by repair, so actual
protected inclusion and expiry preserve the complete frame, one fixed repair
implementation, and a legal retained endpoint.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem foreign_binding_history_tail_coupling
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
    (reference : List (application setup leaks).PlayerEntry)
    (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (event : (graph setup).EventId) (actor : Player) (different : actor ≠ owner)
    (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding actor payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind actor payload)
    (node : nodeView (graph setup) event = .bind actor payload outputEq codeEq)
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
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
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
  obtain ⟨_, initial, _, Γ, config, refs, boundary, _, _, _, _, _, _, _, _, granted,
      _, _, _, _, _, conforming⟩ := sourceService_inclusion_boundary setup leaks
    bounds values capacity rosters opportunities network profile
      ⟨remaining + (ticks + 2), none, repaired⟩ trace rfl event actor selected
  have originalGrant : original.application.serviceGrant = some event :=
    (congrArg PublicView.serviceGrant frame.publicView).trans granted
  have permitted : ∀ message ∈ original.network.pending,
      (runtime setup).permittedServiceEnvelope original.application.publicView
        original.network.ledger message = true := by
    rw [frame.network, frame.publicView]
    exact conforming.pending
  obtain ⟨value, _, candidate⟩ := sourceService_inclusion_binding_candidate setup leaks
    bounds values capacity rosters opportunities network profile
      ⟨remaining + (ticks + 2), none, repaired⟩ trace rfl event actor selected
        payload outputEq codeEq node
  have candidates := congrArg PlayerView.candidates (frame.views actor different)
  have fixed : original.application.candidates.lookup
      (actor, .prepared (original.application.publicView.bindingCount actor)) ≠ .fresh := by
    have counts := congrArg (fun view : PublicView (graph setup) => view.bindingCount actor)
      frame.publicView
    rw [counts]
    have same := congrFun candidates
      (.prepared (repaired.application.publicView.bindingCount actor))
    change original.application.candidates.lookup
      (actor, .prepared (repaired.application.publicView.bindingCount actor)) =
        repaired.application.candidates.lookup
          (actor, .prepared (repaired.application.publicView.bindingCount actor)) at same
    rw [same, candidate]
    intro impossible
    cases impossible
  obtain ⟨physical, first, second, related⟩ := frame.foreign_binding_reserved_tail_coupling
    onlyBindings players network event actor different payload outputEq codeEq node
      originalGrant fixed permitted ticks
  let coupling := physical.map fun pair => (pair.1, pair.2, memory)
  have leftLaw : coupling.map Prod.fst =
      (runtime setup).runInteractionPlan leaks players network ending original := by
    simpa only [coupling, FinDist.map_comp, Function.comp_def] using first
  have rightLaw : coupling.map Prod.snd = strategy.runJoint owner players scheduler
      ending.length repaired memory := by
    rw [roster_segment_runJoint setup leaks rosters network strategy owner players before ending
      after split (by simp [ending]) repaired memory cursor]
    change (physical.map _).map Prod.snd = _
    rw [FinDist.map_comp, ← second, FinDist.map_comp]
    rfl
  refine ⟨coupling, leftLaw, rightLaw, ?_⟩
  intro next supported
  obtain ⟨pair, member, rfl⟩ := FinDist.support_map .. ▸ supported
  refine ⟨?_, related pair member, rfl⟩
  have reached : (pair.2, memory) ∈
      (strategy.runJoint owner players scheduler ending.length repaired memory).support := by
    rw [← rightLaw, FinDist.support_map]
    refine ⟨(pair.1, pair.2, memory), ?_, rfl⟩
    rw [FinDist.support_map]
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

end Vegas.SourceProgram.RevealService
