/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingForeignWindow
import Vegas.Pending.ReactiveDecisionFinalMiss

/-! # A pending owner envelope through arbitrary foreign responses

The ideal network preserves envelope authorship under replay. A foreign roster
may add arbitrary traffic, but cannot change the focal owner's private candidate
view or replace that owner's unique unpublished envelope. No global conformance
premise is imposed on the other players.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem foreign_response_data
    (execution : (runtime.reactiveApplication leaks).Execution) (owner actor : Player)
    (different : actor ≠ owner)
    (safe : Message Player (WitnessedPacket graph) → Prop)
    (foreign : ∀ message, message.sender ≠ owner → safe message)
    (packets : execution.network.Satisfies safe)
    (response : (runtime.reactiveApplication leaks).Action) :
    let next := execution.respond (runtime.reactiveApplication leaks) actor response
    next.application.playerView owner = execution.application.playerView owner ∧
      next.network.ledger = execution.network.ledger ∧ next.receipts = execution.receipts ∧
      next.network.Satisfies safe ∧ execution.network.pending ⊆ next.network.pending := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨rfl, rfl, rfl, packets, List.Subset.refl _⟩
  | some material =>
      refine ⟨?_, rfl, rfl, packets.submit actor _ (foreign _ different), ?_⟩
      · exact (submitStep_playerView_other (material.call.register execution.application actor)
          actor owner different.symm material.call.packet).trans
            (material.call.register_other execution.application actor owner different.symm)
      · exact fun _ member => List.mem_append_left _ member

/-- A foreign response window preserves the complete owner candidate view,
pending owner-envelope constraints, and all prior pending packets. Every
foreign response and passive sample is quantified through the real service law. -/
theorem foreign_window_data
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player)
    (safe : Message Player (WitnessedPacket graph) → Prop)
    (foreign : ∀ message, message.sender ≠ owner → safe message)
    (visits : List Player) (absent : owner ∉ visits)
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (packets : initial.network.Satisfies safe)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support) :
    final.application.playerView owner = initial.application.playerView owner ∧
      final.network.ledger = initial.network.ledger ∧ final.receipts = initial.receipts ∧
      final.network.Satisfies safe ∧ initial.network.pending ⊆ final.network.pending := by
  let app := runtime.reactiveApplication leaks
  induction visits generalizing initial with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨rfl, rfl, rfl, packets, List.Subset.refl _⟩
  | cons actor rest ih =>
      have different : actor ≠ owner := fun equal => absent (by
        simp only [equal, List.mem_cons_self])
      have restAbsent : owner ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨response, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have data := runtime.foreign_response_data leaks (initial.sampledActivation app actor sample)
        owner actor different safe foreign (packets.learn actor sample) response
      obtain ⟨view, ledger, receipts, valid, pending⟩ := ih restAbsent _ data.2.2.2.1 reached
      exact ⟨view.trans data.1, ledger.trans data.2.1, receipts.trans data.2.2.1,
        valid, List.Subset.trans data.2.2.2.2 pending⟩

private theorem reactiveLatest_unique_owner
    (current : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (message : Message Player (WitnessedPacket graph))
    (authored : message.sender = owner)
    (addressed : message.payload.call.event? graph = some event)
    (pending : message ∈ current.network.pending)
    (unpublished : message.id ∉ current.network.ledger.map Message.id)
    (packets : ∀ packet ∈ current.network.pending, packet.sender = owner →
      packet.id ∈ current.network.ledger.map Message.id ∨ packet = message) :
    runtime.reactiveLatest leaks event owner
        (current.observeEnvironment (runtime.reactiveApplication leaks)) = .include message.id ∧
      current.network.lookup message.id = some message := by
  constructor
  · unfold reactiveLatest
    split
    · rename_i missing
      have excluded := List.find?_eq_none.mp missing message (List.mem_reverse.mpr pending)
      have unspent : (current.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
          (runtime.reactiveApplication leaks) message.id := unpublished
      simp only [authored, addressed, unspent, and_self, decide_true] at excluded
      contradiction
    · rename_i selected found
      have member := List.mem_reverse.mp (List.mem_of_find?_eq_some found)
      have good : selected.sender = owner ∧ selected.payload.call.event? graph = some event ∧
          (current.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
            (runtime.reactiveApplication leaks) selected.id := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      rcases packets selected member good.1 with published | same
      · exact (good.2.2 published).elim
      · exact congrArg ReactiveApplication.Command.include (congrArg Message.id same)
  · have unique (packet : Message Player (WitnessedPacket graph))
        (member : packet ∈ current.network.pending) (same : packet.id = message.id) :
        packet = message := by
      have sender : packet.sender = owner := (congrArg Prod.fst same).trans authored
      exact (packets packet member sender).resolve_left (by simpa only [same] using unpublished)
    cases found : current.network.lookup message.id with
    | none =>
        have excluded := List.find?_eq_none.mp found message pending
        exact (excluded (decide_eq_true_iff.mpr rfl)).elim
    | some selected =>
        have same : selected.id = message.id := by
          simpa only [decide_eq_true_eq] using List.find?_some found
        exact congrArg some (unique selected (List.mem_of_find?_eq_some found) same)

/-- Foreign fresh submissions and arbitrary known-envelope forwarding cannot
redirect the owner's reserved selection. All other pending traffic is retained. -/
theorem foreign_window_selection
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (event : graph.EventId) (message : Message Player (WitnessedPacket graph))
    (authored : message.sender = owner)
    (addressed : message.payload.call.event? graph = some event)
    (packets : initial.network.Satisfies fun packet => packet.sender = owner →
      packet.id ∈ initial.network.ledger.map Message.id ∨ packet = message)
    (pending : message ∈ initial.network.pending)
    (unpublished : message.id ∉ initial.network.ledger.map Message.id)
    (visits : List Player) (absent : owner ∉ visits)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support) :
    runtime.reactiveLatest leaks event owner
        (final.observeEnvironment (runtime.reactiveApplication leaks)) = .include message.id ∧
      final.network.lookup message.id = some message := by
  obtain ⟨_, ledger, _, valid, retained⟩ := runtime.foreign_window_data leaks players network owner
    _ (fun packet different same => (different same).elim) visits absent initial final packets
      reached
  apply runtime.reactiveLatest_unique_owner leaks final owner event message authored addressed
    (retained pending) (by rwa [ledger])
  intro packet member sender
  simpa only [ledger] using valid.pending packet member sender

end Vegas.EventGraphRuntime
