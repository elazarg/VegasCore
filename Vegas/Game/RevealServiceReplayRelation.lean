/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceReplayMenu
import Interaction.ReactivePublishedResponses
import Vegas.Pending.ReactiveReplaySelection

/-! # Comparing actual executions after published watcher replays

The relation retains the watcher's changed private recall and the additional
wire inputs. It compares ordinary players' complete information, and ignores
only published pending copies for the reserved inclusion selector. It is a
proof relation on the existing execution states, not a different runtime.

The native observation interface does not notify players of duplicate arrivals.
The lemmas would not justify erasure under an interface exposing those events.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

structure ReplayAgreement (watcher : Player)
    (first second : (application setup leaks).Execution) : Prop where
  applicationEq : first.application = second.application
  ledger : first.network.ledger = second.network.ledger
  leaked : first.network.leaked = second.network.leaked
  serials : first.network.nextSerial = second.network.nextSerial
  inputs : first.network.inputs.filter (fun input => input.broadcaster ≠ watcher) =
    second.network.inputs.filter (fun input => input.broadcaster ≠ watcher)
  pending : first.network.pending.filter
      (fun message => message.id ∉ first.network.ledger.map Message.id) =
    second.network.pending.filter
      (fun message => message.id ∉ second.network.ledger.map Message.id)
  recall : ∀ who, who ≠ watcher → first.recall who = second.recall who
  position : first.environmentRecall.length = second.environmentRecall.length
  watcherPublished : ∀ input ∈ second.network.inputs, input.broadcaster = watcher →
    input.envelope.id ∈ second.network.ledger.map Message.id
  receipts : first.receipts = second.receipts

namespace ReplayAgreement

variable {setup leaks} {watcher : Player}
  {first second : (application setup leaks).Execution}

theorem refl (execution : (application setup leaks).Execution)
    (published : ∀ input ∈ execution.network.inputs, input.broadcaster = watcher →
      input.envelope.id ∈ execution.network.ledger.map Message.id) :
    ReplayAgreement setup leaks watcher execution execution :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, published, rfl⟩

theorem observe (same : ReplayAgreement setup leaks watcher first second) (who : Player) :
    first.observe (application setup leaks) who = second.observe (application setup leaks) who := by
  simp only [ReactiveApplication.Execution.observe, MessageNetwork.observe,
    same.applicationEq, same.leaked, same.ledger, same.receipts]

theorem known (same : ReplayAgreement setup leaks watcher first second)
    (who : Player) (ordinary : who ≠ watcher) :
    first.network.known who = second.network.known who := by
  have filtered (inputs : List (NetworkInput Player ((application setup leaks).Payload))) :
      (inputs.filter (fun input => input.broadcaster ≠ watcher)).filterMap
          (fun input => if input.broadcaster = who then some input.envelope else none) =
        inputs.filterMap
          (fun input => if input.broadcaster = who then some input.envelope else none) := by
    induction inputs with
    | nil => rfl
    | cons input rest ih =>
        by_cases selected : input.broadcaster = who
        · have different : input.broadcaster ≠ watcher := selected ▸ ordinary
          simp only [List.filter_cons, decide_eq_true different, ↓reduceIte,
            List.filterMap_cons, ite_eq_left selected, ih]
        · by_cases different : input.broadcaster ≠ watcher
          · simp only [List.filter_cons, decide_eq_true different, ↓reduceIte,
              List.filterMap_cons, ite_eq_right selected, ih]
          · simp only [List.filter_cons, decide_eq_false different, Bool.false_eq_true,
              ↓reduceIte, List.filterMap_cons, ite_eq_right selected, ih]
  unfold MessageNetwork.known
  rw [← filtered first.network.inputs, same.inputs, filtered second.network.inputs,
    same.leaked, same.ledger]

theorem pending_published (same : ReplayAgreement setup leaks watcher first second)
    (published : ∀ message ∈ first.network.pending,
      message.id ∈ first.network.ledger.map Message.id) :
    ∀ message ∈ second.network.pending,
      message.id ∈ second.network.ledger.map Message.id := by
  have empty : first.network.pending.filter
      (fun message => message.id ∉ first.network.ledger.map Message.id) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro message member
    simp only [published message member, not_true_eq_false, decide_false, Bool.false_eq_true,
      not_false_eq_true]
  rw [same.pending] at empty
  intro message member
  by_contra absent
  have present : message ∈ second.network.pending.filter
      (fun message => message.id ∉ second.network.ledger.map Message.id) :=
    List.mem_filter.mpr ⟨member, by simp [absent]⟩
  rw [empty] at present
  exact List.not_mem_nil present

theorem inputs_published (same : ReplayAgreement setup leaks watcher first second)
    (published : ∀ input ∈ first.network.inputs,
      input.envelope.id ∈ first.network.ledger.map Message.id) :
    ∀ input ∈ second.network.inputs,
      input.envelope.id ∈ second.network.ledger.map Message.id := by
  intro input member
  by_cases watches : input.broadcaster = watcher
  · exact same.watcherPublished input member watches
  · have filtered : input ∈ second.network.inputs.filter
        (fun input => input.broadcaster ≠ watcher) :=
      List.mem_filter.mpr ⟨member, by simp [watches]⟩
    rw [← same.inputs] at filtered
    rw [← same.ledger]
    exact published input (List.mem_of_mem_filter filtered)

theorem reserved_selection (same : ReplayAgreement setup leaks watcher first second)
    (event : (graph setup).EventId) (owner : Player) :
    (runtime setup).reactiveLatest leaks event owner
        (first.observeEnvironment (application setup leaks)) =
      (runtime setup).reactiveLatest leaks event owner
        (second.observeEnvironment (application setup leaks)) :=
  (runtime setup).reactiveLatest_eq_of_unpublished_pending_eq leaks event owner _ _
    same.ledger same.pending

/-- Any identical ordinary response preserves the relation, including the
actual emitted packet and the ordinary player's recorded before-view. -/
theorem respond_ordinary (same : ReplayAgreement setup leaks watcher first second)
    (who : Player) (ordinary : who ≠ watcher) (response : (application setup leaks).Action) :
    ReplayAgreement setup leaks watcher
      (first.respond (application setup leaks) who response)
      (second.respond (application setup leaks) who response) := by
  obtain ⟨transmission⟩ := response
  cases transmission with
  | none =>
      refine ⟨same.applicationEq, same.ledger, same.leaked, same.serials, same.inputs,
        same.pending, ?_, same.position, same.watcherPublished, same.receipts⟩
      intro observer different
      simp only [ReactiveApplication.Execution.respond]
      split
      · rw [same.recall who ordinary, same.observe who]
      · exact same.recall observer different
  | some transmission =>
      cases transmission with
      | submit submission =>
          have emitted : (application setup leaks).packet
              ((application setup leaks).submit first.application who submission) who
              (first.network.known who) submission =
            (application setup leaks).packet
              ((application setup leaks).submit second.application who submission) who
              (second.network.known who) submission := by
            rw [same.applicationEq, same.known who ordinary]
          constructor
          · simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
              same.applicationEq]
          · exact same.ledger
          · exact same.leaked
          · simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit, same.serials]
          · simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
              List.filter_append, same.inputs, same.serials, emitted]
          · simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
              List.filter_append, same.serials, emitted]
            rw [same.pending, same.ledger]
          · intro observer different
            simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit]
            split
            · rename_i selected
              subst observer
              rw [same.recall who ordinary, same.observe who, same.serials, emitted]
            · exact same.recall observer different
          · exact same.position
          · intro input member watched
            change input ∈ second.network.inputs ++ [_] at member
            rcases List.mem_append.mp member with prior | added
            · exact same.watcherPublished input prior watched
            · obtain rfl := List.mem_singleton.mp added
              exact (ordinary watched).elim
          · exact same.receipts
      | replay id =>
          have foundEq : (first.network.known who).find? (fun packet => packet.id = id) =
              (second.network.known who).find? (fun packet => packet.id = id) := by
            rw [same.known who ordinary]
          cases found : (second.network.known who).find? (fun packet => packet.id = id) with
          | none =>
              have leftFound := foundEq.trans found
              constructor
              · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found] using same.applicationEq
              · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found] using same.ledger
              · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found] using same.leaked
              · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found] using same.serials
              · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found] using same.inputs
              · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found] using same.pending
              · intro observer different
                simp only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found]
                split
                · rename_i selected
                  subst observer
                  rw [same.recall who ordinary, same.observe who]
                · exact same.recall observer different
              · exact same.position
              · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  found] using same.watcherPublished
              · exact same.receipts
          | some packet =>
              have leftFound := foundEq.trans found
              constructor
              · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found] using same.applicationEq
              · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found] using same.ledger
              · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found] using same.leaked
              · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found] using same.serials
              · simp only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found, List.filter_append, same.inputs]
              · simp only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found, List.filter_append]
                rw [same.pending, same.ledger]
              · intro observer different
                simp only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  leftFound, found]
                split
                · rename_i selected
                  subst observer
                  rw [same.recall who ordinary, same.observe who]
                · exact same.recall observer different
              · exact same.position
              · intro input member watched
                simp only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
                  found] at member ⊢
                rcases List.mem_append.mp member with prior | added
                · exact same.watcherPublished input prior watched
                · obtain rfl := List.mem_singleton.mp added
                  exact (ordinary watched).elim
              · exact same.receipts

/-- A published watcher replay may alter its private recall and wire history;
it has the same compared state as the watcher's silent response. -/
theorem respond_watcher_replay (same : ReplayAgreement setup leaks watcher first second)
    (id : MessageId Player) (published : id ∈ second.network.ledger.map Message.id) :
    ReplayAgreement setup leaks watcher
      (first.respond (application setup leaks) watcher ⟨none⟩)
      (second.respond (application setup leaks) watcher ⟨some (.replay id)⟩) := by
  cases found : (second.network.known watcher).find? (fun packet => packet.id = id) with
  | none =>
      constructor
      · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          using same.applicationEq
      · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          using same.ledger
      · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          using same.leaked
      · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          using same.serials
      · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          using same.inputs
      · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          using same.pending
      · intro who ordinary
        simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found,
          ite_eq_right ordinary] using same.recall who ordinary
      · exact same.position
      · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          using same.watcherPublished
      · exact same.receipts
  | some packet =>
      have selected : packet.id = id := by
        have decision := List.find?_some found
        simpa only [decide_eq_true_eq] using decision
      constructor
      · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          using same.applicationEq
      · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          using same.ledger
      · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          using same.leaked
      · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          using same.serials
      · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found,
          List.filter_append, List.filter_cons, List.filter_nil, ne_eq, not_true_eq_false,
          decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil] using same.inputs
      · simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found,
          List.filter_append, List.filter_cons, List.filter_nil, selected, published,
          not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
          using same.pending
      · intro who ordinary
        simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found,
          ite_eq_right ordinary] using same.recall who ordinary
      · exact same.position
      · intro input member watches
        simp only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
          found] at member ⊢
        rcases List.mem_append.mp member with prior | added
        · exact same.watcherPublished input prior watches
        · obtain rfl := List.mem_singleton.mp added
          simpa only [selected] using published
      · exact same.receipts

theorem respond_watcher_silent (same : ReplayAgreement setup leaks watcher first second) :
    ReplayAgreement setup leaks watcher
      (first.respond (application setup leaks) watcher ⟨none⟩)
      (second.respond (application setup leaks) watcher ⟨none⟩) := by
  refine ⟨same.applicationEq, same.ledger, same.leaked, same.serials, same.inputs,
    same.pending, ?_, same.position, same.watcherPublished, same.receipts⟩
  intro who ordinary
  simpa only [ReactiveApplication.Execution.respond, ite_eq_right ordinary]
    using same.recall who ordinary

theorem with_application (same : ReplayAgreement setup leaks watcher first second)
    (state : EventGraphRuntime.State (graph setup)) :
    ReplayAgreement setup leaks watcher { first with application := state }
      { second with application := state } :=
  ⟨rfl, same.ledger, same.leaked, same.serials, same.inputs, same.pending, same.recall,
    same.position, same.watcherPublished, same.receipts⟩

/-- Public scheduler recall is retained in each execution. Only its length
selects the next instruction in the fixed service calendar. -/
theorem append_environment (same : ReplayAgreement setup leaks watcher first second)
    (leftEntry rightEntry : (application setup leaks).EnvironmentEntry) :
    ReplayAgreement setup leaks watcher
      { first with environmentRecall := first.environmentRecall ++ [leftEntry] }
      { second with environmentRecall := second.environmentRecall ++ [rightEntry] } := by
  refine ⟨same.applicationEq, same.ledger, same.leaked, same.serials, same.inputs,
    same.pending, same.recall, ?_, same.watcherPublished, same.receipts⟩
  simp only [List.length_append, List.length_singleton, same.position]

private theorem find_filter_unpublished
    (messages ledger : List (Message Player ((application setup leaks).Payload)))
    (id : MessageId Player) (fresh : id ∉ ledger.map Message.id) :
    (messages.filter (fun message => message.id ∉ ledger.map Message.id)).find?
        (fun message => message.id = id) =
      messages.find? (fun message => message.id = id) := by
  rw [List.find?_filter]
  congr 1
  funext message
  by_cases selected : message.id = id
  · simp [selected, fresh]
  · simp [selected]

theorem lookup_unpublished (same : ReplayAgreement setup leaks watcher first second)
    (id : MessageId Player) (fresh : id ∉ first.network.ledger.map Message.id) :
    first.network.lookup id = second.network.lookup id := by
  unfold MessageNetwork.lookup
  rw [← find_filter_unpublished first.network.pending first.network.ledger id fresh,
    same.pending, find_filter_unpublished second.network.pending second.network.ledger id
      (same.ledger ▸ fresh)]

private theorem filter_removeFirst
    (id : MessageId Player) (messages : List (Message Player ((application setup leaks).Payload)))
    (predicate : Message Player ((application setup leaks).Payload) → Bool)
    (excluded : ∀ message, message.id = id → predicate message = false) :
    (MessagePool.removeFirst id messages).filter predicate = messages.filter predicate := by
  induction messages with
  | nil => rfl
  | cons message rest ih =>
      rw [MessagePool.removeFirst]
      split
      · rename_i selected
        simp only [List.filter_cons, excluded message selected, Bool.false_eq_true, ↓reduceIte]
      · rw [List.filter_cons, List.filter_cons, ih]

private theorem pending_after_include
    (left right ledger : List (Message Player ((application setup leaks).Payload)))
    (id : MessageId Player) (packet : Message Player ((application setup leaks).Payload))
    (selected : packet.id = id)
    (same : left.filter (fun message => message.id ∉ ledger.map Message.id) =
      right.filter (fun message => message.id ∉ ledger.map Message.id)) :
    (MessagePool.removeFirst id left).filter
        (fun message => message.id ∉ (ledger ++ [packet]).map Message.id) =
      (MessagePool.removeFirst id right).filter
        (fun message => message.id ∉ (ledger ++ [packet]).map Message.id) := by
  have excluded (message : Message Player ((application setup leaks).Payload))
      (identified : message.id = id) :
      decide (message.id ∉ (ledger ++ [packet]).map Message.id) = false := by
    simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton,
      selected, identified, or_true, not_true_eq_false, decide_false]
  rw [filter_removeFirst id left _ excluded, filter_removeFirst id right _ excluded]
  have retained (messages : List (Message Player ((application setup leaks).Payload))) :
      messages.filter (fun message => message.id ∉ (ledger ++ [packet]).map Message.id) =
        (messages.filter (fun message => message.id ∉ ledger.map Message.id)).filter
          (fun message => message.id ≠ id) := by
    rw [List.filter_filter]
    congr 1
    funext message
    simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton,
      selected, not_or]
    cases a : decide (message.id ∈ ledger.map Message.id) <;>
      cases b : decide (message.id = id) <;> simp_all
  rw [retained, retained, same]

theorem includePending (same : ReplayAgreement setup leaks watcher first second)
    (id : MessageId Player) (fresh : id ∉ first.network.ledger.map Message.id) :
    ReplayAgreement setup leaks watcher
      (first.includePending (application setup leaks) id)
      (second.includePending (application setup leaks) id) := by
  have foundEq := same.lookup_unpublished id fresh
  cases found : second.network.lookup id with
  | none =>
      have leftFound := foundEq.trans found
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        leftFound, found] using same
  | some packet =>
      have leftFound := foundEq.trans found
      have identified : packet.id = id := by
        have selected := List.find?_some found
        simpa only [decide_eq_true_eq] using selected
      constructor
      · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          leftFound, found, same.applicationEq]
      · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          leftFound, found, same.ledger]
      · simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          leftFound, found] using same.leaked
      · simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          leftFound, found] using same.serials
      · simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          leftFound, found] using same.inputs
      · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          leftFound, found]
        rw [same.ledger]
        apply pending_after_include _ _ _ id packet identified
        simpa only [same.ledger] using same.pending
      · intro who ordinary
        simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          leftFound, found] using same.recall who ordinary
      · simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          leftFound, found] using same.position
      · intro input member watches
        simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found] at member ⊢
        have prior := same.watcherPublished input member watches
        rw [List.map_append]
        exact List.mem_append_left _ prior
      · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          leftFound, found, same.applicationEq, same.receipts]

/-- The actual environment kernels preserve continuation comparisons. Passive
sampling is unrestricted; the cleanliness premise makes its learned view inert. -/
theorem environment_bind_eq {Outcome : Type}
    (same : ReplayAgreement setup leaks watcher first second)
    (command : (application setup leaks).Command)
    (fresh : ∀ id, command = .include id → id ∉ first.network.ledger.map Message.id)
    (published : ∀ who, command = .activate who → ∀ message ∈ first.network.pending,
      message.id ∈ first.network.ledger.map Message.id)
    (leftValue rightValue : (application setup leaks).Execution → FinDist Outcome)
    (continued : ∀ left ∈ (first.environmentStep (application setup leaks) command).support,
      ∀ right, ReplayAgreement setup leaks watcher left right → leftValue left = rightValue right) :
    (first.environmentStep (application setup leaks) command).bind leftValue =
      (second.environmentStep (application setup leaks) command).bind rightValue := by
  let app := application setup leaks
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
        FinDist.pure_bind] at continued ⊢
      exact continued _ (FinDist.mem_support_pure.mpr rfl) _
        (same.append_environment _ _)
  | activate who =>
      have clean := published who rfl
      rw [first.activate_of_pending_published app who clean] at continued ⊢
      rw [second.activate_of_pending_published app who (same.pending_published clean),
        FinDist.pure_bind, FinDist.pure_bind]
      exact continued _ (FinDist.mem_support_pure.mpr rfl) _
        (same.append_environment _ _)
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
        FinDist.pure_bind] at continued ⊢
      apply continued _ (FinDist.mem_support_pure.mpr rfl)
      have unchanged (execution : (application setup leaks).Execution) :
          (execution.includePending (application setup leaks) id).environmentRecall =
            execution.environmentRecall := by
        cases found : execution.network.lookup id <;>
          simp only [ReactiveApplication.Execution.includePending,
            MessageNetwork.includePending, found]
      simpa only [unchanged] using (same.includePending id (fresh id rfl)).append_environment
        ⟨first.observeEnvironment app, .include id⟩
        ⟨second.observeEnvironment app, .include id⟩
  | application command =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.bind_map]
      rw [same.applicationEq]
      apply FinDist.bind_congr
      intro state supported
      apply continued
      · simp only [ReactiveApplication.Execution.environmentStep, FinDist.support_map]
        refine ⟨{ first with application := state }, ?_, rfl⟩
        refine ⟨state, ?_, rfl⟩
        rw [same.applicationEq]
        exact supported
      · exact (same.with_application state).append_environment _ _

end ReplayAgreement
end Vegas
