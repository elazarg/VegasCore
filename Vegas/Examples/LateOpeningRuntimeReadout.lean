/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSourceEquilibrium
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.ReactiveAssociationPersistence
import Vegas.Pending.ReactiveOpeningConformance
import Vegas.Pending.ReactiveSettledVerdict
import Vegas.Pending.ReactiveGuardConformance
import Vegas.EventGraph.ResolutionProvenance
import Vegas.EventGraph.PrivateInputs
import Vegas.Compile.EventGraphParameterReadout

/-! # Typed outcomes and immutable publications in the initialized native game

These facts concern the source program's actual compiled sequential graph.
They hold under arbitrary deadline configurations, pending observations,
schedulers and raw responses. They identify existing stored values without
assuming that an opening is included or that any player is rational.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeReadout

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol
open LateOpeningRuntimeSource

abbrev aliceInput : nativeGraph.InputId := ⟨0, by decide⟩
abbrev labelInput : nativeGraph.InputId := ⟨1, by decide⟩
abbrev aliceCandidate : Handle nativeGraph := (alice, .initial aliceInput)
abbrev aliceBinding : FieldRef nativeGraph.layout (.binding alice .bool) :=
  ⟨.inl aliceInput, rfl⟩
abbrev bobBinding : FieldRef nativeGraph.layout (.binding bob (.range 0 5)) :=
  ⟨.inr bobBindEvent, rfl⟩

def terminalStateOf (bit : Bool) (label : Fin 3)
    (alicePublication : PublicationResult Bool)
    (answerBinding answerPublication : PublicationResult Answer) :
    State simpleExpr program.terminalCtx :=
  Env.cons answerPublication <| Env.cons answerBinding <|
    Env.cons alicePublication <| sourceInitial bit label

theorem terminalStateOf_success (bit : Bool) (label : Fin 3) (answer : Answer) :
    terminalStateOf bit label (.success bit) (.success answer) (.success answer) =
      finalState bit label true answer true := rfl

/-- The native decoder retains the initialized bit and private label jointly
with both publications and the private answer binding. -/
theorem decode_terminalStateOf (physical : EventGraphRuntime.State nativeGraph)
    (bit : Bool) (label : Fin 3) (alicePublication : PublicationResult Bool)
    (answerBinding answerPublication : PublicationResult Answer)
    (inputs : physical.config.inputs = setup.eventInputs (sourceInitial bit label))
    (aliceStored : physical.config.store (.inr aliceEvent) = some alicePublication)
    (bindingStored : physical.config.store (.inr bobBindEvent) = some answerBinding)
    (answerStored : physical.config.store (.inr bobRevealEvent) = some answerPublication) :
    decodeState? (terminalRefs program) physical.config.store =
      some (terminalStateOf bit label alicePublication answerBinding answerPublication) := by
  apply decodeState?_eq_some
  intro name cell member
  cases member with
  | here => exact answerStored
  | there member => cases member with
    | here => exact bindingStored
    | there member => cases member with
      | here => exact aliceStored
      | there member => cases member with
        | here => change some (physical.config.inputs aliceInput) = _; rw [inputs]; rfl
        | there member => cases member with
          | here => change some (physical.config.inputs labelInput) = _; rw [inputs]; rfl
          | there member => cases member

private theorem initial_law_eq :
    (setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)) = initialLaw setup := by
  rw [PMF.map_comp]
  rfl

/-- Every legal initialized raw history retains one of the six actual source
initial states and its graph-reachability invariant. -/
theorem history_initial_invariant (backend : EventGraphRuntime nativeGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph))
    (horizon : Nat) (scheduler : (backend.reactiveApplication leaks).Scheduler)
    (control : (backend.reactiveApplication leaks).Control)
    (trace : ((backend.reactiveApplication leaks).protocol (initialLaw setup)
      horizon scheduler).Trace (some control)) :
    ∃ bit label,
      EventGraphRuntime.State.Invariant (graph := nativeGraph)
        (setup.eventInputs (sourceInitial bit label)) control.execution.application := by
  have aligned : ((backend.reactiveApplication leaks).protocol
      ((setup.initialLaw.map setup.eventInputs).map EventGraphRuntime.State.initial)
        horizon scheduler).Trace (some control) := by
    rwa [initial_law_eq]
  obtain ⟨inputs, supported, invariant⟩ := backend.reactive_history_invariant leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler aligned
  obtain ⟨initial, selected, rfl⟩ := PMF.support_map .. ▸ supported
  obtain ⟨bit, label, rfl⟩ := (initialLaw_support initial).mp selected
  exact ⟨bit, label, invariant⟩

/-- A successful publication is the initialized committed bit. This permits
failure, arbitrary packet aliases and arbitrary unaccepted opening claims. -/
theorem alice_success_from_initialized_bit
    (physical : EventGraphRuntime.State nativeGraph) (bit : Bool) (label : Fin 3)
    (valid : EventGraphRuntime.State.Invariant (graph := nativeGraph)
      (setup.eventInputs (sourceInitial bit label)) physical)
    (opened : Bool)
    (published : physical.config.store (.inr aliceEvent) = some (.success opened)) :
    opened = bit := by
  have stored := valid.reachable.publication_binding aliceEvent alice .bool aliceBinding []
    rfl rfl opened published
  have inherited : aliceBinding.get? physical.config.store = some (.success bit) := by
    change some (physical.config.inputs aliceInput) = _
    rw [valid.reachable.inputs_eq]
    rfl
  rw [inherited] at stored
  exact PublicationResult.success.inj (Option.some.inj stored).symm

/-- Bob cannot open a different answer after binding: every successful final
publication is the answer in the already accepted typed binding. -/
theorem bob_success_from_binding (physical : EventGraphRuntime.State nativeGraph)
    (inputs : nativeGraph.Inputs) (reachable : physical.config.Reachable inputs)
    (answer : Answer)
    (published : physical.config.store (.inr bobRevealEvent) = some (.success answer)) :
    physical.config.store (.inr bobBindEvent) = some (.success answer) := by
  exact reachable.publication_binding bobRevealEvent bob (.range 0 5) bobBinding _
    rfl rfl answer published

/-- Completion gives a complete typed source state, including failed binding
results. The initialized private cells remain the original joint parameter. -/
theorem terminal_decode_exists (physical : EventGraphRuntime.State nativeGraph)
    (bit : Bool) (label : Fin 3)
    (valid : EventGraphRuntime.State.Invariant (graph := nativeGraph)
      (setup.eventInputs (sourceInitial bit label)) physical)
    (completed : physical.config.cut.Terminal) :
    ∃ alicePublication answerBinding answerPublication,
      decodeState? (terminalRefs program) physical.config.store =
        some (terminalStateOf bit label alicePublication answerBinding answerPublication) := by
  obtain ⟨alicePublication, aliceStored⟩ := Option.isSome_iff_exists.mp
    (physical.config.store_available_of_terminal completed (.inr aliceEvent))
  obtain ⟨answerBinding, bindingStored⟩ := Option.isSome_iff_exists.mp
    (physical.config.store_available_of_terminal completed (.inr bobBindEvent))
  obtain ⟨answerPublication, answerStored⟩ := Option.isSome_iff_exists.mp
    (physical.config.store_available_of_terminal completed (.inr bobRevealEvent))
  exact ⟨alicePublication, answerBinding, answerPublication,
    decode_terminalStateOf physical bit label alicePublication answerBinding answerPublication
      valid.reachable.inputs_eq aliceStored bindingStored answerStored⟩

/-- At Bob's final publication every other compiled field has already settled. -/
theorem bob_prefix_other_field_available (physical : EventGraphRuntime.State nativeGraph)
    (ready : physical.config.cut.Ready bobRevealEvent) (field : nativeGraph.Field)
    (different : field ≠ .inr bobRevealEvent) :
    (physical.config.store field).isSome = true := by
  cases field with
  | inl input => rfl
  | inr event =>
      apply (physical.config.output_available event).mpr
      have predecessor : event ∈ nativeGraph.order.predecessors bobRevealEvent := by
        change Fin 3 at event
        fin_cases event
        · decide
        · decide
        · exact False.elim (different rfl)
      exact ready.2 predecessor

/-- Raw preparation and every future controller retain all fields settled
before the final Bob decision, independently of aliases and pending packets. -/
theorem bob_continuation_other_fields (backend : EventGraphRuntime nativeGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph))
    (players : Player → (backend.reactiveApplication leaks).Policy)
    (scheduler : (backend.reactiveApplication leaks).Scheduler) (count : Nat)
    (execution final : (backend.reactiveApplication leaks).Execution)
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (response : (backend.reactiveApplication leaks).Action)
    (reached : final ∈ ((backend.reactiveApplication leaks).runRounds scheduler players count
      (execution.respond (backend.reactiveApplication leaks) bob response)).support) :
    ∀ field : nativeGraph.Field, field ≠ .inr bobRevealEvent →
      final.application.config.store field = execution.application.config.store field := by
  intro field different
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
    (bob_prefix_other_field_available execution.application ready field different)
  have before : (execution.respond (backend.reactiveApplication leaks) bob
      response).application.config.store field = some value := by
    rw [(backend.reactive_respond_application leaks execution bob response).1]
    exact stored
  have after := (ReactiveApplication.Invariant.policyInvariant
    (backend.reactiveApplication leaks)
    (backend.reactiveStoreInvariant leaks field value) players).runRounds
      scheduler count _ final before reached
  exact after.trans stored.symm

/-- Every arbitrary raw continuation preserves the accepted answer. The
later publication may fail; if it succeeds, it must publish that answer. -/
theorem bob_continuation_success_immutable (backend : EventGraphRuntime nativeGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph))
    (players : Player → (backend.reactiveApplication leaks).Policy)
    (scheduler : (backend.reactiveApplication leaks).Scheduler) (count : Nat)
    (execution final : (backend.reactiveApplication leaks).Execution)
    (inputs : nativeGraph.Inputs) (valid : execution.application.Invariant inputs)
    (answer : Answer)
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (response : (backend.reactiveApplication leaks).Action)
    (reached : final ∈ ((backend.reactiveApplication leaks).runRounds scheduler players count
      (execution.respond (backend.reactiveApplication leaks) bob response)).support)
    (opened : Answer)
    (published : final.application.config.store (.inr bobRevealEvent) = some (.success opened)) :
    opened = answer := by
  have invariant := backend.reactiveStateInvariant leaks inputs
  have after := (ReactiveApplication.Invariant.policyInvariant
    (backend.reactiveApplication leaks) invariant players).runRounds scheduler count _ final
    (invariant.respond execution bob response valid) reached
  have retained := (ReactiveApplication.Invariant.policyInvariant
    (backend.reactiveApplication leaks)
    (backend.reactiveStoreInvariant leaks (.inr bobBindEvent)
      (.success answer)) players).runRounds scheduler count _ final
      ((backend.reactiveStoreInvariant leaks (.inr bobBindEvent)
        (.success answer)).respond execution bob response bound) reached
  have boundAnswer := bob_success_from_binding final.application inputs after.reachable
    opened published
  rw [retained] at boundAnswer
  exact PublicationResult.success.inj (Option.some.inj boundAnswer).symm

/-- The settled content test does not inspect a packet's emission time.
Certified truthful Alice openings pass its empty guard list at any record. -/
theorem alice_opening_content (record : SettledRecord nativeGraph) (id : MessageId Player)
    (bit : Bool) (token : Option (ReadinessToken nativeGraph)) :
    record.SettledContent
      ⟨id, ⟨.opening aliceEvent aliceCandidate ⟨.bool, bit⟩,
        some ⟨aliceCandidate, ⟨.bool, bit⟩⟩, token⟩⟩ := by
  refine ⟨by simp [certifiedOpening], ?_⟩
  exact (record.view.openingGuardsAccepted_iff alice aliceEvent .bool aliceBinding []
    rfl rfl rfl aliceCandidate ⟨.bool, bit⟩
      (some ⟨aliceCandidate, ⟨.bool, bit⟩⟩)).mpr ⟨bit, rfl, rfl⟩

/-- An accepted late canonical opening is permitted by the authentic settled
audit, just as an accepted protected opening is. -/
theorem accepted_alice_opening_permitted (record : SettledRecord nativeGraph)
    (id : MessageId Player) (bit : Bool) (token : Option (ReadinessToken nativeGraph))
    (accepted : (id, true) ∈ record.receipts) :
    record.permits
      ⟨id, ⟨.opening aliceEvent aliceCandidate ⟨.bool, bit⟩,
        some ⟨aliceCandidate, ⟨.bool, bit⟩⟩, token⟩⟩ = true :=
  SettledRecord.permits_of_accepted record _ aliceEvent rfl accepted
    (alice_opening_content record id bit token)

end Vegas.Examples.LateOpeningRuntimeReadout
