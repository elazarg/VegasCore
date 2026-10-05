/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDecisionDeadline
import Vegas.Pending.ReactivePlayerWindow
import Vegas.Pending.ReactiveBindingContinuation
import Interaction.MessageNetworkInvariant

/-! # Missing the last owned decision with a foreign response tail

After the decision owner has no remaining opportunity, other players may still
send arbitrary raw traffic. They cannot create a
new envelope signed by that owner. Reserved inclusion therefore cannot rescue
a missed decision, and actual expiry supplies its public marker.
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
  | some material =>
      refine ⟨rfl, published.submit actor _ ?_⟩
      intro authored
      exact (different authored).elim

/-- Arbitrary later players cannot forge the absent owner's pending envelope.
All their observations, submissions, and catalog changes remain actual. -/
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
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨rfl, published⟩
  | cons actor rest ih =>
      have different : actor ≠ owner := fun same => absent (by
        simp only [same, List.mem_cons_self])
      have restAbsent : owner ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨response, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
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

/-- Only unpublished envelopes authored by the designated decision owner can
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

private theorem decision_miss_of_selection_waits
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (initial : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (owned : graph.actor? event = some owner)
    (ready : initial.application.config.cut.Ready event)
    (selected : runtime.reactiveLatest leaks event owner
      (initial.observeEnvironment (runtime.reactiveApplication leaks)) = .wait)
    (entered ticks : Nat)
    (activated : initial.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ initial.application.clock + ticks - entered)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
          initial).support) :
    event ∈ final.application.missedEvents := by
  let app := runtime.reactiveApplication leaks
  let waited : app.Execution := { initial with environmentRecall := initial.environmentRecall ++
    [⟨initial.observeEnvironment app, .wait⟩] }
  have waitLaw : runtime.interactionStep leaks players network (.includeLatest event owner)
      initial = PMF.pure waited := by
    simp only [interactionStep, interactionInstruction, PMF.pure_bind, selected]
    change (initial.environmentStep app .wait).bind PMF.pure = _
    rw [PMF.bind_pure]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl
  obtain ⟨after, law, missed⟩ := runtime.decision_deadline_missed leaks players network waited
    owner event owned ready entered ticks activated due
  rw [List.cons_append, runInteractionPlan, waitLaw, PMF.pure_bind, law] at reached
  cases (PMF.mem_support_pure_iff _ _).mp reached
  exact missed

/-- The genuine deadline obligation survives an arbitrary raw foreign tail
after the owner's last opportunity. No later policy is assumed to conform. -/
theorem foreign_tail_decision_miss
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (initial : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (owned : graph.actor? event = some owner)
    (ready : initial.application.config.cut.Ready event)
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
    event ∈ final.application.missedEvents := by
  rw [runtime.runInteractionPlan_append] at reached
  obtain ⟨middle, leading, suffix⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have application := runtime.player_window_application leaks players network visits initial
    middle leading
  have carried := runtime.foreign_window_owner_published leaks players network owner visits
    absent initial middle published leading
  have selected := runtime.reactiveLatest_wait_of_owner_published leaks middle owner event
    carried.2.pending
  have currentReady : middle.application.config.cut.Ready event := by
    rw [application.1]
    exact ready
  have currentActivated : middle.application.activatedAt event = some entered := by
    rw [show middle.application.activatedAt = initial.application.activatedAt from
      congrArg PublicView.activatedAt application.2]
    exact activated
  have currentDue : runtime.deadline event ≤ middle.application.clock + ticks - entered := by
    rw [show middle.application.clock = initial.application.clock from
      congrArg PublicView.clock application.2]
    exact due
  exact runtime.decision_miss_of_selection_waits leaks players network middle owner event owned
    currentReady selected entered ticks currentActivated
      currentDue final suffix

/-- Silence at the last owner visit leaves the decision incomplete,
even when arbitrary raw foreign traffic follows before inclusion and expiry. -/
theorem last_decision_transport_miss
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (initial : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (owned : graph.actor? event = some owner)
    (ready : initial.application.config.cut.Ready event)
    (published : initial.network.Satisfies fun message => message.sender = owner →
      message.id ∈ initial.network.ledger.map Message.id)
    (entered ticks : Nat)
    (activated : initial.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ initial.application.clock + ticks - entered)
    (visits : List Player) (absent : owner ∉ visits)
    (response : (runtime.reactiveApplication leaks).Action)
    (transport : ∀ submission, response.transmission ≠ some submission)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
          (initial.respond (runtime.reactiveApplication leaks) owner response)).support) :
    event ∈ final.application.missedEvents := by
  let app := runtime.reactiveApplication leaks
  have unchanged : (initial.respond app owner response).application = initial.application := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some submission => exact (transport submission rfl).elim
  have packets : (initial.respond app owner response).network.Satisfies
      (fun message => message.sender = owner → message.id ∈
        (initial.respond app owner response).network.ledger.map Message.id) := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact published
    | some submission => exact (transport submission rfl).elim
  exact runtime.foreign_tail_decision_miss leaks players network
    (initial.respond app owner response) owner event owned
    (unchanged.symm ▸ ready) packets entered ticks
    (unchanged.symm ▸ activated) (unchanged.symm ▸ due) visits absent final reached

namespace BindingMemory

/-- On the omitted-response branch, the repaired marginal is still the same
fixed retained implementation. The two continuations may diverge arbitrarily;
the original side has actual deadline evidence at every terminal branch. -/
theorem omitted_decision_continuation_coupling
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (original repaired : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (memory : BindingMemory runtime leaks)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId) (owned : graph.actor? event = some owner)
    (ready : original.application.config.cut.Ready event)
    (published : original.network.Satisfies fun message => message.sender = owner →
      message.id ∈ original.network.ledger.map Message.id)
    (entered ticks : Nat)
    (activated : original.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ original.application.clock + ticks - entered)
    (visits : List Player) (absent : owner ∉ visits)
    (omits : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
        ∀ submission, response.transmission ≠ some submission) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    let plan := visits.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = (app.invoke players owner original).bind
        (runtime.runInteractionPlan leaks players network plan) ∧
      coupling.map Prod.snd =
        (strategy.resume owner players (some owner) repaired memory).bind (fun next =>
          (runtime.runInteractionPlan leaks players network plan next.1).map
            fun execution => (execution, next.2)) ∧
      ∀ next ∈ coupling.support, event ∈ next.1.application.missedEvents := by
  intro app strategy plan
  let left := (app.invoke players owner original).bind
    (runtime.runInteractionPlan leaks players network plan)
  let right := (strategy.resume owner players (some owner) repaired memory).bind fun next =>
    (runtime.runInteractionPlan leaks players network plan next.1).map
      fun execution => (execution, next.2)
  refine ⟨bindPairLaw left (fun _ => right), bindPairLaw_map_fst ..,
    bindPairLaw_const_map_snd .., ?_⟩
  intro next supported
  have leftSupported : next.1 ∈ left.support := by
    rw [← bindPairLaw_map_fst left (fun _ => right), PMF.support_map]
    exact ⟨next, supported, rfl⟩
  change next.1 ∈ (((players owner (original.recall owner) (original.observe app owner)).map
    (original.respond app owner)).bind
      (runtime.runInteractionPlan leaks players network plan)).support at leftSupported
  rw [PMF.bind_map] at leftSupported
  obtain ⟨response, chosen, reached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ leftSupported)
  exact runtime.last_decision_transport_miss leaks players network original owner event owned
    ready published entered ticks activated due visits absent response
      (omits response chosen) next.1 reached

end BindingMemory

end Vegas.EventGraphRuntime
