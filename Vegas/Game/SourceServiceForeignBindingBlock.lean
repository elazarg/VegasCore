/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceOffTurnWindow
import Vegas.Game.SourceServiceForeignBindingRepair
import Vegas.Pending.ReactiveBindingMemoryInvariant

/-! # Complete foreign binding blocks under continuation repair

A focal player's responses throughout another player's binding phase either
leave persistent signed evidence or preserve the repaired observation relation.
The protected inclusion and expiry then preserve the same relation. Both
marginals use the actual complete block and one fixed repair implementation.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem foreign_binding_block_stopped_coupling
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
    (reference : List (application setup leaks).PlayerEntry)
    (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (application setup leaks))
    (event : (graph setup).EventId) (actor : Player) (different : actor ≠ owner)
    (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding actor payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind actor payload)
    (node : nodeView (graph setup) event = .bind actor payload outputEq codeEq)
    (granted : repaired.application.serviceGrant = some event)
    (remaining : Nat) (visits : List Player) (ticks : Nat)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining + visits.length + (ticks + 2), none, repaired⟩))
    (before after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++
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
        (visits.map ServiceInstruction.player ++ ending) original ∧
      coupling.map Prod.snd = strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network)
          (visits.map ServiceInstruction.player ++ ending).length repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
            (some ⟨remaining, none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
          BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
  classical
  intro app players strategy ending
  let menu := sourceServiceMenu setup leaks bounds rosters
  let scheduler := rosterScheduler setup leaks rosters network
  have length : ending.length = ticks + 2 := by simp [ending]
  have windowTrace : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      scheduler).Trace (some ⟨remaining + ending.length + visits.length, none, repaired⟩) := by
    have same : remaining + ending.length + visits.length =
        remaining + visits.length + (ticks + 2) := by rw [length]; omega
    rw [same]
    exact trace
  have existsWindow : ∃ coupling : PMF (app.Execution × app.Execution ×
      BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player) original ∧
      coupling.map Prod.snd = strategy.runJoint owner players scheduler visits.length
        repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty ((menu.protocol (initialLaw setup)
          (rosterPlan setup rosters).length scheduler).Trace
          (some ⟨remaining + ending.length, none, next.2.1⟩)) ∧
        ((∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
          BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
    have owned : (graph setup).actor? event = some actor := by
      exact (EventCode.actor_cast outputEq ((graph setup).nodes event)).symm.trans
        (congrArg (fun code : EventCode (graph setup).layout (.binding actor payload) =>
          code.actor) codeEq)
    have rightTrace := menu.toRawTrace (initialLaw setup) (rosterPlan setup rosters).length
      scheduler trace
    have originalGrant : original.application.serviceGrant = some event :=
      (congrArg PublicView.serviceGrant frame.publicView).trans granted
    obtain ⟨coupling, first, second, related⟩ := off_turn_roster_stopped_coupling setup leaks
      bounds rosters network source target agrees owner policy available reference memory
        original repaired frame started leftRecall
        (app.history_inputRecall (initialLaw setup) (rosterPlan setup rosters).length
          scheduler rightTrace)
        (frame.network ▸ app.serialsBeforeNext_history scheduler (initialLaw setup)
          (rosterPlan setup rosters).length rightTrace)
        (by
          intro selected selectedGrant equality
          cases Option.some.inj (selectedGrant.symm.trans originalGrant)
          exact different (Option.some.inj (owned.symm.trans equality)))
        (remaining + ending.length) visits windowTrace before (ending ++ after)
        (by simpa only [ending, List.append_assoc] using split) position
    exact ⟨coupling, first, second, fun next member =>
      ⟨(related next member).1, ((related next member).2).imp_right And.left⟩⟩
  obtain ⟨window, first, second, related⟩ := existsWindow
  have existsTail next (member : next ∈ window.support) :
      ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
        coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
          ending next.1 ∧
        coupling.map Prod.snd = strategy.runJoint owner players scheduler ending.length
          next.2.1 next.2.2 ∧
        ∀ final ∈ coupling.support,
          (∃ record ∈ app.executionTraffic final.1, record.input.envelope.sender = owner ∧
            (runtime setup).permittedServiceEnvelope record.observation record.ledger
              record.input.envelope = false) ∨
            BindingMemory.Frame (runtime setup) leaks final.2.2 owner final.1 final.2.1 := by
    by_cases bad : ∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
        (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.input.envelope = false
    · let left := (runtime setup).runInteractionPlan leaks players network ending next.1
      let right := strategy.runJoint owner players scheduler ending.length next.2.1 next.2.2
      refine ⟨bindPairLaw left (fun _ => right), bindPairLaw_map_fst ..,
        FinDist.map_snd_product .., ?_⟩
      intro final supported
      obtain ⟨record, present, authored, rejected⟩ := bad
      have reached : final.1 ∈ left.support := by
        rw [← bindPairLaw_map_fst left right, PMF.support_map]
        exact ⟨final, supported, rfl⟩
      exact Or.inl ⟨record, ((runtime setup).executionTraffic_runInteractionPlan leaks players
        network ending next.1 final.1 reached).subset present, authored, rejected⟩
    · have paired := ((related next member).2).resolve_left bad
      obtain ⟨nextTrace⟩ := (related next member).1
      have reached : next.1 ∈ ((runtime setup).runInteractionPlan leaks players network
          (visits.map ServiceInstruction.player) original).support := by
        rw [← first, PMF.support_map]
        exact ⟨next, member, rfl⟩
      have privateReached : next.2 ∈ (strategy.runJoint owner players scheduler visits.length
          repaired memory).support := by
        rw [← second, PMF.support_map]
        exact ⟨next, member, rfl⟩
      have memoryValid := BindingMemory.retainedImplementation_runJoint_ownBindings
        (runtime setup) leaks menu owner reference (players owner) players scheduler visits.length
          repaired memory onlyBindings next.2 privateReached
      have nextPosition : next.1.environmentRecall.length =
          (before ++ visits.map ServiceInstruction.player).length := by
        rw [(runtime setup).runInteractionPlan_recall leaks players network
          (visits.map ServiceInstruction.player) original next.1 reached, position,
          List.length_append]
      obtain ⟨coupling, leftLaw, rightLaw, connected⟩ :=
        foreign_binding_history_tail_coupling setup leaks
        bounds values capacity rosters opportunities network source target agrees owner
          policy reference next.2.2 next.1 next.2.1 paired memoryValid event actor different
            payload outputEq codeEq node remaining ticks
            (by rw [← length]; exact nextTrace)
            (before ++ visits.map ServiceInstruction.player) after split nextPosition
      exact ⟨coupling, leftLaw, rightLaw, fun final supported =>
        Or.inr (connected final supported).2.1⟩
  let tail := fun next member => (existsTail next member).choose
  let coupling := window.bindOnSupport tail
  have leftLaw : coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++ ending) original := by
    rw [map_bindOnSupport]
    calc
      _ = window.bind (fun next => (runtime setup).runInteractionPlan leaks players network
          ending next.1) := by
        apply bindOnSupport_eq_bind_of_eq_on_support _
        intro next member
        exact (existsTail next member).choose_spec.1
      _ = _ := by rw [← PMF.bind_map, first, ← (runtime setup).runInteractionPlan_append]
  have rightLaw : coupling.map Prod.snd = strategy.runJoint owner players scheduler
      (visits.map ServiceInstruction.player ++ ending).length repaired memory := by
    rw [List.length_append, List.length_map, ReactiveApplication.Implementation.runJoint_add,
      map_bindOnSupport]
    calc
      _ = window.bind (fun next =>
          strategy.runJoint owner players scheduler ending.length next.2.1 next.2.2) := by
        apply bindOnSupport_eq_bind_of_eq_on_support _
        intro next member
        exact (existsTail next member).choose_spec.2.1
      _ = (window.map Prod.snd).bind (fun next =>
          strategy.runJoint owner players scheduler ending.length next.1 next.2) := by
        rw [PMF.bind_map]
      _ = _ := by rw [second]
  refine ⟨coupling, leftLaw, rightLaw, ?_⟩
  intro final supported
  have rightSupport : final.2 ∈ (strategy.runJoint owner players scheduler
      (visits.map ServiceInstruction.player ++ ending).length repaired memory).support := by
    rw [← rightLaw, PMF.support_map]
    exact ⟨final, supported, rfl⟩
  refine ⟨?_, ?_⟩
  · apply menu.trace_implementation_runJoint (initialLaw setup) (rosterPlan setup rosters).length
      scheduler strategy owner players _ _ remaining
      (visits.map ServiceInstruction.player ++ ending).length repaired memory _ final.2 rightSupport
    · intro who different
      simpa only [players, Function.update_of_ne different] using
        (sourceServiceMenu_in_effective setup leaks bounds rosters).decoded_admissible
          (initialLaw setup) (rosterPlan setup rosters).length scheduler source target agrees who
    · intro next past view response member
      exact BindingMemory.retainedImplementation_response_available (runtime setup) leaks menu
        owner reference (players owner) next (past, view) response member
    · have total : remaining + (visits.map ServiceInstruction.player ++ ending).length =
          remaining + visits.length + (ticks + 2) := by
        simp only [List.length_append, List.length_map, length, Nat.add_assoc]
      rw [total]
      exact trace
  · obtain ⟨next, member, reached⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
    exact (existsTail next member).choose_spec.2.2 final reached

end Vegas
