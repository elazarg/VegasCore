/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedBinding
import Vegas.Pending.ReactiveBindingReplay
import Vegas.Pending.ReactiveBindingBlock
import Vegas.Pending.ReactiveServiceRecall
import Vegas.Pending.ReactiveRevealSettlement

/-! # Source completion of each scheduled binding branch

Each selected source value is submitted at its scheduled owner opportunity.
Passive samples and replay before and after that opportunity retain their
physical effects. Every supported included configuration has the corresponding
binding completion, which can be paired with the actual traffic readout.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Finite Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem scheduledBindingWindow_config
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (network : (runtime setup).NetworkPolicy leaks)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (execution : (application setup leaks).Execution)
    (granted : execution.application.serviceGrant = some event)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (serial : Nat)
    (fresh : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (vacant : execution.application.accepted (.inr event) = none)
    (unused : execution.application.HandleUnused (owner, .prepared serial))
    (serials : execution.network.SerialsBeforeNext)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (roster : List Player) {slots : Nat} (slot : Fin slots) (offset : Nat)
    (notPassed : (execution.recall owner).length ≤ offset + slot.val)
    (within : offset + slot.val < (execution.recall owner).length + roster.count owner)
    (choice : PublicationResult (L.Val payload))
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (Function.update (fun _ => (application setup leaks).replayPolicy) owner
        ((application setup leaks).scheduledPolicy offset (some slot)
          (fun _ _ => PMF.pure
            ((runtime setup).reactiveBinding leaks owner event payload choice serial))
          (application setup leaks).replayPolicy)) network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) execution).support) :
    final.application.config = execution.application.config.complete event ready
      (cast (congrArg EventField.Action outputEq.symm) choice)
      (cast (congrArg EventField.Value outputEq.symm) choice) := by
  let : Fintype Player := Fintype.ofFinite Player
  let app := application setup leaks
  let response := (runtime setup).reactiveBinding leaks owner event payload choice serial
  let transport : Player → app.Policy := fun _ => app.replayPolicy
  let players := Function.update transport owner
    (app.scheduledPolicy offset (some slot) (fun _ _ => PMF.pure response) app.replayPolicy)
  obtain ⟨visited, remaining, split, selected⟩ := split_owner_visit owner roster
    (offset + slot.val - (execution.recall owner).length) (by omega)
  have before : (execution.recall owner).length + visited.count owner ≤ offset + slot.val := by
    omega
  have waiting := scheduled_window_waiting setup leaks network owner offset slot
    (fun _ _ => PMF.pure response) visited execution (Or.inl before)
  change final ∈ ((runtime setup).runInteractionPlan leaks players network
    (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) execution).support
    at reached
  simp only [split, List.map_append, List.map_cons, List.append_assoc,
    (runtime setup).runInteractionPlan_append] at reached
  rw [waiting] at reached
  obtain ⟨current, earlier, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have preserved := (runtime setup).replay_window_preserves leaks transport network owner execution
    (fun current who action _ _ member => app.replayPolicy_cases _ _ action member)
    _ published visited current earlier
  have same := preserved.1
  have currentReady : current.application.config.cut.Ready event := by rw [same]; exact ready
  have currentTimely : current.application.WithinDeadline (runtime setup) event := by
    rw [same]; exact timely
  have currentFresh : current.application.candidates.lookup (owner, .prepared serial) = .fresh := by
    rw [same]; exact fresh
  have currentVacant : current.application.accepted (.inr event) = none := by
    rw [same]; exact vacant
  have currentUnused : current.application.HandleUnused (owner, .prepared serial) := by
    rw [same]; exact unused
  have currentGrant : current.application.serviceGrant = some event := by rw [same]; exact granted
  have currentSerials := (runtime setup).runInteractionPlan_serials leaks transport network
    (visited.map ServiceInstruction.player) execution current serials earlier
  have currentPublished : current.network.Satisfies fun message =>
      message.id ∈ current.network.ledger.map Message.id := by
    rw [preserved.2.1]
    exact preserved.2.2.2.2.1
  have currentCount := fixed_plan_response_counts setup leaks network transport
    (visited.map ServiceInstruction.player) (by simp) execution current earlier owner
  simp only [List.filterMap_map, Function.comp_def, instructionActor, List.filterMap_some]
    at currentCount
  have atSlot : (current.recall owner).length = offset + slot.val := by
    rw [currentCount]
    omega
  simp only [List.cons_append, runInteractionPlan, interactionStep, interactionInstruction,
    PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, ReactiveApplication.invoke,
    ReactiveApplication.Execution.activation_samples, PMF.bind_map,
    PMF.bind_bind] at continued
  obtain ⟨sample, _observed, continued⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ continued)
  let activated := current.sampledActivation app owner sample
  have scheduled : (some slot).map (fun selected => offset + selected.val) =
      some (activated.recall owner).length := congrArg some atSlot.symm
  change final ∈ ((players owner (activated.recall owner) (activated.observe app owner)).bind
    _).support at continued
  simp only [players, Function.update_self, ReactiveApplication.scheduledPolicy,
    ite_eq_left scheduled, PMF.pure_bind] at continued
  have after : offset + slot.val <
      ((activated.respond app owner response).recall owner).length := by
    rw [app.respond_recall_length]
    simp only [↓reduceIte]
    change offset + slot.val < (current.recall owner).length + 1
    omega
  rw [scheduled_tail_waiting setup leaks network owner event offset slot
    (fun _ _ => PMF.pure response) remaining (activated.respond app owner response) after]
    at continued
  have delayed (opening : Option (Raw L)) := (runtime setup).rawBinding_delayed_inclusion leaks
    bounds transport (fun who past view action supported =>
      bounds.replay_compiled (runtime setup) leaks who past view action supported)
    network activated owner event payload outputEq codeEq node currentGrant owned currentReady
      (currentPublished.learn owner sample) (currentSerials.learn owner sample) serial opening
      remaining
  let readout := fun next : app.Execution =>
    (next.application, next.network.ledger, next.receipts, next.network.nextSerial)
  have delay : ((runtime setup).runInteractionPlan leaks transport network
      (remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
      (activated.respond app owner response)).map readout =
      ((runtime setup).interactionStep leaks transport network (.includeLatest event owner)
        (activated.respond app owner response)).map readout := by
    cases choice with
    | failure => exact delayed none
    | success value => exact delayed (some ⟨payload, value⟩)
  have mapped : readout final ∈ (((runtime setup).runInteractionPlan leaks transport network
      (remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
      (activated.respond app owner response)).map readout).support :=
    PMF.support_map .. ▸ ⟨final, continued, rfl⟩
  rw [delay] at mapped
  obtain ⟨immediate, included, sameResult⟩ := PMF.support_map .. ▸ mapped
  have immediateLaw := (runtime setup).reactiveBinding_reserved_config leaks activated owner event
    payload outputEq codeEq node choice serial currentReady currentTimely currentFresh currentVacant
      currentUnused (currentSerials.learn owner sample) transport network
  have actual : (immediate.application.config, immediate.receipts) ∈
      (((runtime setup).interactionStep leaks transport network (.includeLatest event owner)
        (activated.respond app owner response)).map
          (fun next => (next.application.config, next.receipts))).support :=
    PMF.support_map .. ▸ ⟨immediate, included, rfl⟩
  rw [immediateLaw] at actual
  have config := congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp actual)
  dsimp only at config
  have appEq : final.application = immediate.application :=
    (congrArg Prod.fst sameResult).symm
  apply (congrArg (fun state : EventGraphRuntime.State (graph setup) => state.config) appEq).trans
  apply config.trans
  change current.application.config.complete event currentReady _ _ = _
  congr 1
  exact congrArg (fun state : EventGraphRuntime.State (graph setup) => state.config) same

/-- Clock padding and expiry retain the same source binding successor for
every branch of the actual scheduled response law. -/
theorem scheduledBindingPhase_config
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (network : (runtime setup).NetworkPolicy leaks)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (execution : (application setup leaks).Execution)
    (granted : execution.application.serviceGrant = some event)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (serial : Nat)
    (fresh : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (vacant : execution.application.accepted (.inr event) = none)
    (unused : execution.application.HandleUnused (owner, .prepared serial))
    (serials : execution.network.SerialsBeforeNext)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (roster : List Player) {slots : Nat} (slot : Fin slots) (offset : Nat)
    (notPassed : (execution.recall owner).length ≤ offset + slot.val)
    (within : offset + slot.val < (execution.recall owner).length + roster.count owner)
    (choice : PublicationResult (L.Val payload))
    (ticks : Nat) (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (Function.update (fun _ => (application setup leaks).replayPolicy) owner
        ((application setup leaks).scheduledPolicy offset (some slot)
          (fun _ _ => PMF.pure
            ((runtime setup).reactiveBinding leaks owner event payload choice serial))
          (application setup leaks).replayPolicy)) network
      ((roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        List.replicate ticks .tick ++ [.expire event]) execution).support) :
    final.application.config = execution.application.config.complete event ready
      (cast (congrArg EventField.Action outputEq.symm) choice)
      (cast (congrArg EventField.Value outputEq.symm) choice) := by
  let app := application setup leaks
  let players := Function.update (fun _ => app.replayPolicy) owner
    (app.scheduledPolicy offset (some slot)
      (fun _ _ => PMF.pure
        ((runtime setup).reactiveBinding leaks owner event payload choice serial)) app.replayPolicy)
  change final ∈ ((runtime setup).runInteractionPlan leaks players network
    ((roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
      List.replicate ticks .tick ++ [.expire event]) execution).support at reached
  rw [List.append_assoc, (runtime setup).runInteractionPlan_append] at reached
  obtain ⟨included, supported, continued⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have config := scheduledBindingWindow_config setup leaks bounds network owner event payload
    outputEq codeEq node owned execution granted ready timely serial fresh vacant unused serials
      published roster slot offset notPassed within choice included supported
  have settled : ¬included.application.config.cut.Ready event := by
    rw [config]
    intro unfinished
    exact unfinished.1 (Finset.mem_insert_self ..)
  obtain ⟨endpoint, law, state, _, _, _⟩ := (runtime setup).settled_reveal_expiry leaks
    players network included event settled ticks
  rw [law] at continued
  cases (PMF.mem_support_pure_iff _ _).mp continued
  rw [state]
  exact config

end Vegas
