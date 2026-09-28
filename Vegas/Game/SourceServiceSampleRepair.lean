/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceOffTurnWindow
import Vegas.Pending.ReactiveBindingExpiry
import Vegas.Pending.ReactiveServiceTraffic
import Vegas.Pending.ReactivePlayerWindow

/-! # A whole public-sample block in the stopped private repair

The arbitrary roster may include the deviator any number of times. The public
draw stays coupled after every clean response path; an observed departure
retains both actual remaining laws. Private memory and the repaired legal
history are retained through the sample and its complete clock suffix.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem sample_tail_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (owner : Player) (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (event : (graph setup).EventId) (ready : original.application.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist (graph setup).layout payload)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload law)
    (node : nodeView (graph setup) event = .sample payload law outputEq codeEq)
    (ticks : Nat) :
    let app := application setup leaks
    let ending : List (ServiceInstruction (graph setup)) :=
      .sample event :: List.replicate ticks .tick ++ [.expire event]
    ∃ coupling : FinDist (app.Execution × app.Execution),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network ending
        original ∧
      coupling.map Prod.snd = (runtime setup).runInteractionPlan leaks players network ending
        repaired ∧
      ∀ next ∈ coupling.support,
        BindingMemory.Frame (runtime setup) leaks memory owner next.1 next.2 := by
  classical
  intro app ending
  obtain ⟨sample, first, second, related⟩ := frame.sample_coupling onlyBindings event ready
    payload law outputEq codeEq node
  have visible : ((graph setup).outputLayout event).IsPublic := by rw [outputEq]; trivial
  have existsTail next (member : next ∈ sample.support) :=
    (related next member).public_clock_tail_coupling onlyBindings players network event
      visible ticks
  let tail := fun next member => (existsTail next member).choose
  have sampleLaw (execution : app.Execution) :
      (runtime setup).interactionStep leaks players network (.sample event) execution =
        execution.environmentStep app (.application (.executeSample event)) := by
    simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
    change (execution.environmentStep app (.application (.executeSample event))).bind
      FinDist.pure = _
    exact FinDist.bind_pure _
  refine ⟨sample.bindOnSupport tail, ?_, ?_, ?_⟩
  · rw [FinDist.map_bindOnSupport]
    calc
      _ = sample.bind (fun next => (runtime setup).runInteractionPlan leaks players network
          (List.replicate ticks .tick ++ [.expire event]) next.1) := by
        apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
        intro next member
        exact (existsTail next member).choose_spec.1
      _ = _ := by
        rw [← FinDist.bind_map, first]
        exact congrArg
          (fun step => step.bind ((runtime setup).runInteractionPlan leaks players network
            (List.replicate ticks .tick ++ [.expire event]))) (sampleLaw original).symm
  · rw [FinDist.map_bindOnSupport]
    calc
      _ = sample.bind (fun next => (runtime setup).runInteractionPlan leaks players network
          (List.replicate ticks .tick ++ [.expire event]) next.2) := by
        apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
        intro next member
        exact (existsTail next member).choose_spec.2.1
      _ = _ := by
        rw [← FinDist.bind_map, second]
        exact congrArg
          (fun step => step.bind ((runtime setup).runInteractionPlan leaks players network
            (List.replicate ticks .tick ++ [.expire event]))) (sampleLaw repaired).symm
  · intro next supported
    obtain ⟨middle, member, reached⟩ :=
      Set.mem_iUnion₂.mp (FinDist.support_bindOnSupport .. ▸ supported)
    exact (existsTail middle member).choose_spec.2.2 next reached

theorem sample_block_stopped_coupling
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
    (onlyBindings : memory.shadow.OwnBindings owner)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (application setup leaks))
    (rightRecall : repaired.InputRecall (application setup leaks))
    (serials : original.network.SerialsBeforeNext)
    (event : (graph setup).EventId) (payload : L.Ty)
    (law : PublicDist (graph setup).layout payload)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload law)
    (node : nodeView (graph setup) event = .sample payload law outputEq codeEq)
    (granted : original.application.serviceGrant = some event)
    (ready : original.application.config.cut.Ready event)
    (remaining : Nat) (visits : List Player) (ticks : Nat)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining + visits.length + (ticks + 2), none, repaired⟩))
    (before after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++
      (.sample event :: List.replicate ticks .tick ++ [.expire event]) ++ after)
    (position : original.environmentRecall.length = before.length) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    let ending : List (ServiceInstruction (graph setup)) :=
      .sample event :: List.replicate ticks .tick ++ [.expire event]
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
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
  have endingLength : ending.length = ticks + 2 := by simp [ending]
  have traceRank : (remaining + ending.length) + visits.length =
      remaining + visits.length + (ticks + 2) := by rw [endingLength]; omega
  have chance : (graph setup).actor? event = none := by
    have actor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq ((graph setup).nodes event)] at actor
    exact actor
  have offTurn : ∀ selected, original.application.serviceGrant = some selected →
      (graph setup).actor? selected ≠ some owner := by
    intro selected same
    cases Option.some.inj (same.symm.trans granted)
    rw [chance]
    simp
  obtain ⟨window, first, second, related⟩ := off_turn_roster_stopped_coupling setup leaks bounds
    rosters network source target agrees owner policy available reference memory original repaired
    frame started leftRecall rightRecall serials offTurn (remaining + ending.length) visits
      (by rw [traceRank]; exact trace) before (ending ++ after)
      (by simpa only [ending, List.append_assoc] using split) position
  have existsTail next (supported : next ∈ window.support) :
      ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
        coupling.map Prod.fst =
          (runtime setup).runInteractionPlan leaks players network ending next.1 ∧
        coupling.map Prod.snd =
          ((runtime setup).runInteractionPlan leaks players network ending next.2.1).map
            (fun final => (final, next.2.2)) ∧
        ∀ final ∈ coupling.support,
          (∃ record ∈ app.executionTraffic final.1, record.input.envelope.sender = owner ∧
            (runtime setup).permittedServiceEnvelope record.observation record.ledger
              record.input.envelope = false) ∨
          BindingMemory.Frame (runtime setup) leaks final.2.2 owner final.1 final.2.1 := by
    by_cases bad : ∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
        (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.input.envelope = false
    · let left := (runtime setup).runInteractionPlan leaks players network ending next.1
      let right := ((runtime setup).runInteractionPlan leaks players network ending next.2.1).map
        fun final => (final, next.2.2)
      refine ⟨FinDist.product left right, FinDist.map_fst_product ..,
        FinDist.map_snd_product .., ?_⟩
      intro final member
      left
      obtain ⟨record, present, authored, rejected⟩ := bad
      refine ⟨record, ?_, authored, rejected⟩
      have reached : final.1 ∈ left.support := by
        rw [← FinDist.map_fst_product left right, FinDist.support_map]
        exact ⟨final, member, rfl⟩
      exact ((runtime setup).executionTraffic_runInteractionPlan leaks players network ending
        next.1 final.1 reached).subset present
    · obtain ⟨paired, shadow, _⟩ := ((related next supported).2).resolve_left bad
      have reached : next.1 ∈ ((runtime setup).runInteractionPlan leaks players network
          (visits.map ServiceInstruction.player) original).support := by
        rw [← first, FinDist.support_map]
        exact ⟨next, supported, rfl⟩
      have config := ((runtime setup).player_window_application leaks players network visits
        original next.1 reached).1
      have readyNow : next.1.application.config.cut.Ready event := by rwa [config]
      obtain ⟨tail, leftLaw, rightLaw, connected⟩ := sample_tail_coupling setup leaks players
        network owner next.2.2 next.1 next.2.1 paired (by rw [shadow]; exact onlyBindings)
        event readyNow payload law outputEq codeEq node ticks
      refine ⟨tail.map (fun pair => (pair.1, pair.2, next.2.2)), ?_, ?_, ?_⟩
      · simpa only [FinDist.map_comp, Function.comp_def] using leftLaw
      · rw [FinDist.map_comp, ← rightLaw, FinDist.map_comp]
        rfl
      · intro final member
        obtain ⟨pair, chosen, rfl⟩ := FinDist.support_map .. ▸ member
        exact Or.inr (connected pair chosen)
  let tail := fun next supported => (existsTail next supported).choose
  let coupling := window.bindOnSupport tail
  have leftLaw : coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++ ending) original := by
    rw [FinDist.map_bindOnSupport]
    calc
      _ = window.bind (fun next =>
          (runtime setup).runInteractionPlan leaks players network ending next.1) := by
        apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
        intro next supported
        exact (existsTail next supported).choose_spec.1
      _ = _ := by rw [← FinDist.bind_map, first, ← (runtime setup).runInteractionPlan_append]
  have rightLaw : coupling.map Prod.snd = strategy.runJoint owner players scheduler
      (visits.map ServiceInstruction.player ++ ending).length repaired memory := by
    rw [roster_runJoint_append_reserved setup leaks rosters network strategy owner players
      before (visits.map ServiceInstruction.player) ending after split
      (by simp [ending]) repaired memory (by rw [← frame.service]; exact position),
      List.length_map, FinDist.map_bindOnSupport]
    calc
      _ = window.bind (fun next =>
          ((runtime setup).runInteractionPlan leaks players network ending next.2.1).map
            fun final => (final, next.2.2)) := by
        apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
        intro next supported
        exact (existsTail next supported).choose_spec.2.1
      _ = (window.map Prod.snd).bind (fun next =>
          ((runtime setup).runInteractionPlan leaks players network ending next.1).map
            fun final => (final, next.2)) := by rw [FinDist.bind_map]
      _ = _ := by rw [second]
  refine ⟨coupling, leftLaw, rightLaw, ?_⟩
  intro final supported
  have rightSupport : final.2 ∈ (strategy.runJoint owner players scheduler
      (visits.map ServiceInstruction.player ++ ending).length repaired memory).support := by
    rw [← rightLaw, FinDist.support_map]
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
    · have totalRank : remaining + (visits.map ServiceInstruction.player ++ ending).length =
          remaining + visits.length + (ticks + 2) := by
        simp only [List.length_append, List.length_map, endingLength, Nat.add_assoc]
      rw [totalRank]
      exact trace
  · obtain ⟨next, member, reached⟩ :=
      Set.mem_iUnion₂.mp (FinDist.support_bindOnSupport .. ▸ supported)
    exact (existsTail next member).choose_spec.2.2 final reached

end Vegas
