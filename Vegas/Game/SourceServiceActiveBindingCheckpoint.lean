/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceActiveBindingLaw
import Vegas.Game.SourceServiceTimedBindingCheckpoint

/-! # Binding completion after an already observed owner opportunity

The current opportunity has already sampled pending traffic. Its scheduled
binding and the subsequent protected service complete the selected source
value without sampling that opportunity a second time.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Finite Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The scheduled source value is the actual completed binding, including
when its chosen opportunity is the current, already sampled activation. -/
theorem scheduledBindingActive_config
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
    (remaining : List Player) {slots : Nat} (slot : Fin slots) (offset : Nat)
    (notPassed : (execution.recall owner).length ≤ offset + slot.val)
    (within : offset + slot.val < (execution.recall owner).length + 1 + remaining.count owner)
    (choice : PublicationResult (L.Val payload)) (ticks : Nat)
    (final : (application setup leaks).Execution) :
    let app := application setup leaks
    let players := Function.update (fun _ => app.replayPolicy) owner
      (app.scheduledPolicy offset (some slot)
        (fun _ _ => PMF.pure
          ((runtime setup).reactiveBinding leaks owner event payload choice serial))
        app.replayPolicy)
    final ∈ ((app.invoke players owner execution).bind
      ((runtime setup).runInteractionPlan leaks players network
        ((remaining.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
          List.replicate ticks .tick ++ [.expire event]))).support →
    final.application.config = execution.application.config.complete event ready
      (cast (congrArg EventField.Action outputEq.symm) choice)
      (cast (congrArg EventField.Value outputEq.symm) choice) := by
  intro app players reached
  let : Fintype Player := Fintype.ofFinite Player
  let response := (runtime setup).reactiveBinding leaks owner event payload choice serial
  let first := remaining.map ServiceInstruction.player ++ [.includeLatest event owner]
  let maintenance : List (ServiceInstruction (graph setup)) :=
    List.replicate ticks .tick ++ [.expire event]
  have split : ((app.invoke players owner execution).bind
      ((runtime setup).runInteractionPlan leaks players network (first ++ maintenance))) =
      (((app.invoke players owner execution).bind
        ((runtime setup).runInteractionPlan leaks players network first)).bind
          ((runtime setup).runInteractionPlan leaks players network maintenance)) := by
    rw [PMF.bind_bind]
    apply bind_congr_on_support _
    intro current _
    exact (runtime setup).runInteractionPlan_append leaks players network first maintenance current
  have reached : final ∈ ((app.invoke players owner execution).bind
      ((runtime setup).runInteractionPlan leaks players network
        (first ++ maintenance))).support := by
    simpa only [first, maintenance, List.append_assoc] using reached
  rw [split] at reached
  obtain ⟨included, includedSupport, continued⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have config : included.application.config = execution.application.config.complete event ready
      (cast (congrArg EventField.Action outputEq.symm) choice)
      (cast (congrArg EventField.Value outputEq.symm) choice) := by
    by_cases now : offset + slot.val = (execution.recall owner).length
    · have scheduled : some (offset + slot.val) = some (execution.recall owner).length :=
        congrArg some now
      simp only [players, ReactiveApplication.invoke, Function.update_self,
        ReactiveApplication.scheduledPolicy, Option.map_some, ite_eq_left scheduled,
        PMF.bind_map, PMF.pure_bind] at includedSupport
      have after : offset + slot.val <
          ((execution.respond app owner response).recall owner).length := by
        rw [app.respond_recall_length]
        simp only [↓reduceIte, now]
        omega
      rw [scheduled_tail_waiting setup leaks network owner event offset slot
        (fun _ _ => PMF.pure response) remaining
        (execution.respond app owner response) after] at includedSupport
      let transport : Player → app.Policy := fun _ => app.replayPolicy
      let readout := fun current : app.Execution =>
        (current.application, current.network.ledger, current.receipts, current.network.nextSerial)
      have delayed (opening : Option (Raw L)) := (runtime setup).rawBinding_delayed_inclusion
        leaks bounds transport (fun who past view action member =>
          bounds.replay_compiled (runtime setup) leaks who past view action member)
        network execution owner event payload outputEq codeEq node granted owned ready
        published serials serial opening remaining
      have delay : ((runtime setup).runInteractionPlan leaks transport network first
          (execution.respond app owner response)).map readout =
          ((runtime setup).interactionStep leaks transport network (.includeLatest event owner)
            (execution.respond app owner response)).map readout := by
        cases choice with
        | failure => exact delayed none
        | success value => exact delayed (some ⟨payload, value⟩)
      have member : readout included ∈ (((runtime setup).runInteractionPlan leaks transport
          network first (execution.respond app owner response)).map readout).support :=
        PMF.support_map .. ▸ ⟨included, includedSupport, rfl⟩
      rw [delay] at member
      obtain ⟨immediate, immediateSupport, equal⟩ := PMF.support_map .. ▸ member
      have actual : (immediate.application.config, immediate.receipts) ∈
          (((runtime setup).interactionStep leaks transport network (.includeLatest event owner)
            (execution.respond app owner response)).map
              (fun current => (current.application.config, current.receipts))).support :=
        PMF.support_map .. ▸ ⟨immediate, immediateSupport, rfl⟩
      rw [(runtime setup).reactiveBinding_reserved_config leaks execution owner event payload
        outputEq codeEq node choice serial ready timely fresh vacant unused serials
        transport network]
        at actual
      have same := congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp actual)
      exact (congrArg (fun value => value.1.config) equal).symm.trans same
    · have scheduled : some (offset + slot.val) ≠ some (execution.recall owner).length :=
        fun equal => now (Option.some.inj equal)
      simp only [players, ReactiveApplication.invoke, Function.update_self,
        ReactiveApplication.scheduledPolicy, Option.map_some, ite_eq_right scheduled,
        PMF.bind_map] at includedSupport
      obtain ⟨action, chosen, later⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ includedSupport)
      let current := execution.respond app owner action
      have preserved := (runtime setup).replay_response_preserves leaks
        (fun message => message.id ∈ execution.network.ledger.map Message.id) execution
        published owner action (app.replayPolicy_cases _ _ action chosen)
      have same : current.application = execution.application := preserved.1
      have currentPublished : current.network.Satisfies fun message =>
          message.id ∈ current.network.ledger.map Message.id := by
        rw [preserved.2.1]
        exact preserved.2.2.2.2.1
      have currentCount : (current.recall owner).length = (execution.recall owner).length + 1 := by
        simpa only [↓reduceIte] using app.respond_recall_length execution owner owner action
      have result := scheduledBindingWindow_config setup leaks bounds network owner event payload
        outputEq codeEq node owned current (by rw [same]; exact granted)
        (by rw [same]; exact ready) (by rw [same]; exact timely) serial
        (by rw [same]; exact fresh) (by rw [same]; exact vacant) (by rw [same]; exact unused)
        ((app.serialsBeforeNextInvariant (fun _ _ => PMF.pure .wait)).respond
          execution owner action serials) currentPublished remaining
        slot offset (by rw [currentCount]; omega) (by rw [currentCount]; exact within)
        choice included later
      exact result.trans (by congr 1; exact congrArg (fun state => state.config) same)
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
