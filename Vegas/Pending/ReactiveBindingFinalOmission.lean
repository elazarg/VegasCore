/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingDeadline
import Vegas.Pending.ReactivePlayerWindow
import Vegas.Pending.ReactiveBindingContinuation
import Interaction.MessageNetworkInvariant

/-! # Missing the last binding opportunity with a foreign response tail

After the binding owner has no remaining opportunity, other players may still
send arbitrary raw traffic and replay known envelopes. They cannot create a
new envelope signed by that owner. Reserved inclusion therefore cannot rescue
an omitted binding, and actual expiry supplies public missed-binding evidence.
No observation failure or conformance assumption on those later players is used.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem foreign_response_published
    (execution : (runtime.reactiveApplication leaks).Execution) (owner actor : Player)
    (different : actor ≠ owner)
    (published : execution.network.Satisfies fun message => message.sender = owner →
      message.id ∈ execution.network.ledger.map Message.id)
    (response : (runtime.reactiveApplication leaks).Action) :
    let next := execution.respond (runtime.reactiveApplication leaks) actor response
    next.network.ledger = execution.network.ledger ∧
      next.network.Satisfies (fun message => message.sender = owner →
        message.id ∈ execution.network.ledger.map Message.id) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨rfl, published⟩
  | some transmission =>
      cases transmission with
      | submit material =>
          refine ⟨rfl, published.submit actor _ ?_⟩
          intro authored
          exact (different authored).elim
      | replay id =>
          refine ⟨?_, published.replay actor id⟩
          change (execution.network.replay actor id).2.ledger = execution.network.ledger
          unfold MessageNetwork.replay
          split <;> rfl

/-- Arbitrary later players cannot forge the absent owner's pending envelope.
All their observations, submissions, catalog changes and replays remain actual. -/
theorem foreign_window_owner_published
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player) (visits : List Player)
    (absent : owner ∉ visits)
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (published : initial.network.Satisfies fun message => message.sender = owner →
      message.id ∈ initial.network.ledger.map Message.id)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support) :
    final.network.ledger = initial.network.ledger ∧
      final.network.Satisfies (fun message => message.sender = owner →
        message.id ∈ final.network.ledger.map Message.id) := by
  let app := runtime.reactiveApplication leaks
  induction visits generalizing initial with
  | nil =>
      cases FinDist.mem_support_pure.mp reached
      exact ⟨rfl, published⟩
  | cons actor rest ih =>
      have different : actor ≠ owner := fun same => absent (by
        simp only [same, List.mem_cons_self])
      have restAbsent : owner ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, FinDist.bind_map,
        FinDist.bind_bind] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨response, _, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      have preserved := runtime.foreign_response_published leaks
        (initial.sampledActivation app actor sample) owner actor different
        (published.learn actor sample) response
      let next := (initial.sampledActivation app actor sample).respond app actor response
      have pending : next.network.Satisfies (fun message => message.sender = owner →
          message.id ∈ next.network.ledger.map Message.id) := by
        rw [preserved.1]
        exact preserved.2
      obtain ⟨ledger, valid⟩ := ih restAbsent _ pending reached
      exact ⟨ledger.trans preserved.1, valid⟩

/-- Only unpublished envelopes authored by the designated binding owner can
be selected. Unrelated raw traffic does not obstruct the absence test. -/
theorem reactiveLatest_wait_of_owner_published
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId)
    (published : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.id ∈ execution.network.ledger.map Message.id) :
    runtime.reactiveLatest leaks event owner
      (execution.observeEnvironment (runtime.reactiveApplication leaks)) = .wait := by
  unfold reactiveLatest
  split
  · rfl
  · rename_i message found
    have member := List.mem_reverse.mp (List.mem_of_find?_eq_some found)
    have selected : message.sender = owner ∧ message.payload.call.event? graph = some event ∧
        (execution.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
          (runtime.reactiveApplication leaks) message.id := by
      simpa only [decide_eq_true_eq] using List.find?_some found
    exact (selected.2.2 (published message member selected.1)).elim

private theorem binding_omission_of_selection_waits
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (initial : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (ready : initial.application.config.cut.Ready event)
    (unbound : initial.application.accepted (.inr event) = none)
    (selected : runtime.reactiveLatest leaks event owner
      (initial.observeEnvironment (runtime.reactiveApplication leaks)) = .wait)
    (entered ticks : Nat)
    (activated : initial.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ initial.application.clock + ticks - entered)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
          initial).support) :
    final.application.publicView.missedBinding event = true := by
  let app := runtime.reactiveApplication leaks
  let waited : app.Execution := { initial with environmentRecall := initial.environmentRecall ++
    [⟨initial.observeEnvironment app, .wait⟩] }
  have waitLaw : runtime.interactionStep leaks players network (.includeLatest event owner)
      initial = FinDist.pure waited := by
    simp only [interactionStep, interactionInstruction, FinDist.pure_bind, selected]
    change (initial.environmentStep app .wait).bind FinDist.pure = _
    rw [FinDist.bind_pure]
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
    rfl
  obtain ⟨after, law, missed⟩ := runtime.binding_deadline_omission leaks players network waited
    owner event payload outputEq codeEq node ready unbound entered ticks activated due
  rw [List.cons_append, runInteractionPlan, waitLaw, FinDist.pure_bind, law] at reached
  cases FinDist.mem_support_pure.mp reached
  exact missed

/-- The genuine deadline obligation survives an arbitrary raw foreign tail
after the owner's last opportunity. No later policy is assumed to conform. -/
theorem foreign_tail_binding_omission
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (initial : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (ready : initial.application.config.cut.Ready event)
    (unbound : initial.application.accepted (.inr event) = none)
    (published : initial.network.Satisfies fun message => message.sender = owner →
      message.id ∈ initial.network.ledger.map Message.id)
    (entered ticks : Nat)
    (activated : initial.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ initial.application.clock + ticks - entered)
    (visits : List Player) (absent : owner ∉ visits)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
          initial).support) :
    final.application.publicView.missedBinding event = true := by
  rw [runtime.runInteractionPlan_append] at reached
  obtain ⟨middle, leading, suffix⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have application := runtime.player_window_application leaks players network visits initial
    middle leading
  have carried := runtime.foreign_window_owner_published leaks players network owner visits
    absent initial middle published leading
  have selected := runtime.reactiveLatest_wait_of_owner_published leaks middle owner event
    carried.2.pending
  have currentReady : middle.application.config.cut.Ready event := by
    rw [application.1]
    exact ready
  have currentUnbound : middle.application.accepted (.inr event) = none := by
    rw [show middle.application.accepted = initial.application.accepted from
      congrArg PublicView.accepted application.2]
    exact unbound
  have currentActivated : middle.application.activatedAt event = some entered := by
    rw [show middle.application.activatedAt = initial.application.activatedAt from
      congrArg PublicView.activatedAt application.2]
    exact activated
  have currentDue : runtime.deadline event ≤ middle.application.clock + ticks - entered := by
    rw [show middle.application.clock = initial.application.clock from
      congrArg PublicView.clock application.2]
    exact due
  exact runtime.binding_omission_of_selection_waits leaks players network middle owner event payload
    outputEq codeEq node currentReady currentUnbound selected entered ticks currentActivated
      currentDue final suffix

/-- Silence and every replay at the last owner visit leave the binding absent,
even when arbitrary raw foreign traffic follows before inclusion and expiry. -/
theorem last_binding_transport_omission
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (initial : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (ready : initial.application.config.cut.Ready event)
    (unbound : initial.application.accepted (.inr event) = none)
    (published : initial.network.Satisfies fun message => message.sender = owner →
      message.id ∈ initial.network.ledger.map Message.id)
    (entered ticks : Nat)
    (activated : initial.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ initial.application.clock + ticks - entered)
    (visits : List Player) (absent : owner ∉ visits)
    (response : (runtime.reactiveApplication leaks).Action)
    (transport : ∀ submission, response.transmission ≠ some (.submit submission))
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
          (initial.respond (runtime.reactiveApplication leaks) owner response)).support) :
    final.application.publicView.missedBinding event = true := by
  let app := runtime.reactiveApplication leaks
  have unchanged : (initial.respond app owner response).application = initial.application := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some transmission =>
        cases transmission with
        | replay id => rfl
        | submit submission => exact (transport submission rfl).elim
  have packets : (initial.respond app owner response).network.Satisfies
      (fun message => message.sender = owner → message.id ∈
        (initial.respond app owner response).network.ledger.map Message.id) := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact published
    | some transmission =>
        cases transmission with
        | submit submission => exact (transport submission rfl).elim
        | replay id =>
            have ledger : (initial.network.replay owner id).2.ledger =
                initial.network.ledger := by
              unfold MessageNetwork.replay
              split <;> rfl
            change (initial.network.replay owner id).2.Satisfies
              (fun message => message.sender = owner → message.id ∈
                (initial.network.replay owner id).2.ledger.map Message.id)
            rw [ledger]
            exact published.replay owner id
  exact runtime.foreign_tail_binding_omission leaks players network
    (initial.respond app owner response) owner event payload outputEq codeEq node
    (unchanged.symm ▸ ready) (unchanged.symm ▸ unbound) packets entered ticks
    (unchanged.symm ▸ activated) (unchanged.symm ▸ due) visits absent final reached

namespace BindingMemory

/-- On the omitted-response branch, the repaired marginal is still the same
fixed retained implementation. The two continuations may diverge arbitrarily;
the original side has actual deadline evidence at every terminal branch. -/
theorem omitted_binding_continuation_coupling
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (original repaired : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (memory : BindingMemory runtime leaks)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (ready : original.application.config.cut.Ready event)
    (unbound : original.application.accepted (.inr event) = none)
    (published : original.network.Satisfies fun message => message.sender = owner →
      message.id ∈ original.network.ledger.map Message.id)
    (entered ticks : Nat)
    (activated : original.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ original.application.clock + ticks - entered)
    (visits : List Player) (absent : owner ∉ visits)
    (omits : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
        ∀ submission, response.transmission ≠ some (.submit submission)) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    let plan := visits.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = (app.invoke players owner original).bind
        (runtime.runInteractionPlan leaks players network plan) ∧
      coupling.map Prod.snd =
        (strategy.resume owner players (some owner) repaired memory).bind (fun next =>
          (runtime.runInteractionPlan leaks players network plan next.1).map
            fun execution => (execution, next.2)) ∧
      ∀ next ∈ coupling.support, next.1.application.publicView.missedBinding event = true := by
  intro app strategy plan
  let left := (app.invoke players owner original).bind
    (runtime.runInteractionPlan leaks players network plan)
  let right := (strategy.resume owner players (some owner) repaired memory).bind fun next =>
    (runtime.runInteractionPlan leaks players network plan next.1).map
      fun execution => (execution, next.2)
  refine ⟨FinDist.product left right, FinDist.map_fst_product .., FinDist.map_snd_product .., ?_⟩
  intro next supported
  have leftSupported : next.1 ∈ left.support := by
    rw [← FinDist.map_fst_product left right, FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  change next.1 ∈ (((players owner (original.recall owner) (original.observe app owner)).map
    (original.respond app owner)).bind
      (runtime.runInteractionPlan leaks players network plan)).support at leftSupported
  rw [FinDist.bind_map] at leftSupported
  obtain ⟨response, chosen, reached⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ leftSupported)
  exact runtime.last_binding_transport_omission leaks players network original owner event payload
    outputEq codeEq node ready unbound published entered ticks activated due visits absent response
      (omits response chosen) next.1 reached

end BindingMemory

end Vegas.EventGraphRuntime
