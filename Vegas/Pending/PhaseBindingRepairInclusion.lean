/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingPreparationRepair
import Vegas.Pending.PhaseBindingService

/-! # Raw accepted binding completion and its directed private reconstruction -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace BindingShadow

/-- Completion changes the repaired field to its original private value only
when the field actually becomes available; unrelated catalogue meanings stay fixed. -/
theorem rememberCompletion_native_complete (memory : BindingShadow graph) (owner : Player)
    (state : State graph) (event : graph.EventId) (ready : state.config.cut.Ready event)
    (originalAction repairedAction : graph.Action event)
    (originalValue repairedValue : (graph.outputLayout event).Value) :
    (memory.rememberCompletion event originalAction originalValue).native owner
        (state.complete event ready repairedAction repairedValue) =
      (memory.native owner state).complete event ready originalAction originalValue := by
  change (⟨_, state.accepted, _, state.clock, _⟩ : State graph) = ⟨_, _, _, _, _⟩
  rw [State.mk.injEq]
  refine ⟨rememberCompletion_config_complete memory state.config event ready
    originalAction repairedAction originalValue repairedValue, rfl, rfl, rfl, rfl⟩

/-- The public accepted handle is shared by the original and repaired meaning. -/
theorem native_setAccepted (memory : BindingShadow graph) (owner : Player)
    (state : State graph) (accepted : AcceptedHandles graph) :
    memory.native owner { state with accepted := accepted } =
      { memory.native owner state with accepted := accepted } := rfl

/-- A single unusable binding is reconstructed with its actual original
catalogue meaning and its original typed failure, including wrong-typed raw data. -/
def failedBinding (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (serial : Nat) (original : CommitmentCandidate (Raw L)) : BindingShadow graph :=
  ((empty : BindingShadow graph).rememberCandidate (.prepared serial) original).rememberCompletion
    event (cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure)
      (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure)

omit [DecidableEq Player] in
theorem failedBinding_owned (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (serial : Nat) (original : CommitmentCandidate (Raw L)) :
    (failedBinding owner event payload outputEq serial original).OwnBindings owner :=
  ((ownBindings_empty owner).rememberCandidate _ original).rememberCompletion event payload
    outputEq _ _

/-- The saved checkpoint keeps the old slot fresh and the binding absent until
its real inclusion. No preparation is invented in that checkpoint. -/
theorem failedBinding_saved (state : State graph) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (serial : Nat) (original : CommitmentCandidate (Raw L))
    (fresh : state.candidates.lookup (owner, .prepared serial) = .fresh)
    (missing : event ∉ state.config.cut.completed) :
    (failedBinding owner event payload outputEq serial original).native owner state = state := by
  exact (rememberCompletion_native_pending _ owner state event missing _ _).trans
    (native_rememberCandidate_of_fresh state owner _ original fresh)

/-- The actual binding response constructs a native image whose original
unusable private preparation and pre-inclusion semantics are recovered exactly. -/
theorem failedBinding_preparation (state : State graph) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (serial : Nat) (opening : Option (Raw L)) (value : L.Val payload)
    (fresh : state.candidates.lookup (owner, .prepared serial) = .fresh)
    (ready : state.config.cut.Ready event) :
    let prepare (material : Option (Raw L)) :=
      submitStep (Submission.register ⟨.commitment event (owner, .prepared serial), material⟩
        state owner) owner (.commitment event (owner, .prepared serial))
    let original := prepare opening
    let repaired := prepare (some ⟨payload, value⟩)
    let memory := failedBinding owner event payload outputEq serial
      (original.candidates.lookup (owner, .prepared serial))
    memory.native owner repaired = original := by
  let prepare (material : Option (Raw L)) :=
    submitStep (Submission.register ⟨.commitment event (owner, .prepared serial), material⟩
      state owner) owner (.commitment event (owner, .prepared serial))
  have configEq : (prepare (some ⟨payload, value⟩)).config = state.config :=
    (submitStep_config _ _ _).trans
      ((⟨.commitment event (owner, .prepared serial), some ⟨payload, value⟩⟩ :
        Submission graph).register_facts owner state).1
  have missing : event ∉ (prepare (some ⟨payload, value⟩)).config.cut.completed := by
    rw [configEq]
    exact ready.1
  exact (rememberCompletion_native_pending _ owner _ event missing _ _).trans
    (native_binding_preparation state owner event serial opening payload value fresh)

end BindingShadow
end Vegas.EventGraphRuntime
