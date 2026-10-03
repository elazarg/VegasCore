/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingUsableStep
import Vegas.Pending.ReactiveAssociationPersistence

/-! # Publicly associated handles reject later commitments

An actual accepted field makes the handle unavailable for every subsequent
binding. Its association persists through arbitrary player and scheduler actions.
The inclusion comparison does not equate private candidate meanings.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- One existing public association suffices to forbid any commitment reusing
the same handle, even at a different ready event. -/
theorem State.bindingIncludable_false_of_associated
    (runtime : EventGraphRuntime graph) (state : State graph)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (field : graph.Field) (associated : state.accepted field = some candidate) :
    ¬ state.publicView.BindingIncludable runtime ⟨id, .commitment event candidate⟩ := by
  intro allowed
  change state.publicView.EventReady event ∧ _ ∧ _ at allowed
  cases node : nodeView graph event with
  | bind actor payload outputEq codeEq =>
      have checks := allowed.2.2
      simp only [node] at checks
      exact checks.2.2.2 field associated
  | resolve | sample => simpa only [node] using allowed.2.2

namespace BindingMemory.Frame

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Actual inclusion of a publicly used handle preserves the complete frame;
rejection follows from the shared public association, without capability equality. -/
theorem commitment_step_associated
    (frame : Frame runtime leaks memory owner original repaired)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph)) (token : Option (ReadinessToken graph))
    (found : original.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩)
    (field : graph.Field) (associated : original.application.accepted field = some candidate) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } :=
  frame.commitment_step_not_includable id event candidate evidence token found
    (original.application.bindingIncludable_false_of_associated runtime id event candidate
      field associated)

end BindingMemory.Frame

end Vegas.EventGraphRuntime
