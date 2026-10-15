/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRepairInclusion
import Vegas.Pending.PhaseBindingObservation

/-! # Symmetric hidden meanings at an actual same-handle binding inclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Both actual native handlers accept the same handle with arbitrary private
preparations. The remembered original result reconstructs either accepted
meaning, including failure; no successful-store refinement is required. -/
theorem binding_handle_all_values (runtime : EventGraphRuntime graph) (state : State graph)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (id : MessageId Player) (sender : id.1 = owner) (serial : Nat)
    (first second : Option (Raw L))
    (fresh : state.candidates.lookup (owner, .prepared serial) = .fresh)
    (ready : state.config.cut.Ready event) (timely : state.WithinDeadline runtime event)
    (vacant : state.accepted (.inr event) = none)
    (unused : state.HandleUnused (owner, .prepared serial)) :
    let prepare (material : Option (Raw L)) :=
      submitStep (Submission.register ⟨.commitment event (owner, .prepared serial), material⟩
        state owner) owner (.commitment event (owner, .prepared serial))
    ∃ (left right : State graph) (memory : BindingShadow graph),
      handle runtime (prepare first) ⟨id, .commitment event (owner, .prepared serial)⟩ =
        some left ∧
      handle runtime (prepare second) ⟨id, .commitment event (owner, .prepared serial)⟩ =
        some right ∧
      memory.OwnBindings owner ∧ memory.native owner right = left ∧
      left.publicView = right.publicView ∧
      (∀ observer, observer ≠ owner → left.playerView observer = right.playerView observer) := by
  classical
  let call (material : Option (Raw L)) : Submission graph :=
    ⟨.commitment event (owner, .prepared serial), material⟩
  let prepare (material : Option (Raw L)) :=
    submitStep ((call material).register state owner) owner (call material).packet
  have configEq (material : Option (Raw L)) : (prepare material).config = state.config :=
    (submitStep_config _ _ _).trans ((call material).register_facts owner state).1
  have publicEq (material : Option (Raw L)) : (prepare material).publicView = state.publicView :=
    (submitStep_publicView _ _ _).trans ((call material).register_facts owner state).2
  have preparedReady (material) : (prepare material).config.cut.Ready event :=
    configEq material ▸ ready
  have preparedTimely (material) : (prepare material).WithinDeadline runtime event := by
    have clocks : (prepare material).clock = state.clock :=
      congrArg PublicView.clock (publicEq material)
    have activations : (prepare material).activatedAt = state.activatedAt :=
      congrArg PublicView.activatedAt (publicEq material)
    unfold State.WithinDeadline at timely ⊢
    rw [clocks, activations]
    exact timely
  have preparedVacant (material) : (prepare material).accepted (.inr event) = none :=
    (congrFun (congrArg PublicView.accepted (publicEq material)) _).trans vacant
  have preparedUnused (material) : (prepare material).HandleUnused (owner, .prepared serial) := by
    intro field accepted
    exact unused field
      ((congrFun (congrArg PublicView.accepted (publicEq material)) field).symm.trans accepted)
  have fixed (material) :
      (prepare material).candidates.lookup (owner, .prepared serial) ≠ .fresh := by
    rw [(call material).candidateAfter_eq]
    cases material <;>
      simp only [call, Submission.candidateAfter, fresh, and_self, ↓reduceIte] <;>
      intro impossible <;> cases impossible
  let result (material) := (prepare material).bindingResult (owner, .prepared serial) payload
  let finish (material) : State graph :=
    { (prepare material).complete event (preparedReady material)
        (cast (congrArg EventField.Action outputEq.symm) (result material))
        (cast (congrArg EventField.Value outputEq.symm) (result material)) with
      accepted := Function.update (prepare material).accepted (.inr event)
        (some (owner, .prepared serial)) }
  let catalogue := (empty : BindingShadow graph).rememberCandidate (.prepared serial)
    ((prepare first).candidates.lookup (owner, .prepared serial))
  let memory := catalogue.rememberCompletion event
    (cast (congrArg EventField.Action outputEq.symm) (result first))
    (cast (congrArg EventField.Value outputEq.symm) (result first))
  have preparation : catalogue.native owner (prepare second) = prepare first :=
    native_binding_preparation state owner event serial first second fresh
  have acceptedEq : (prepare second).accepted = (prepare first).accepted :=
    (congrArg PublicView.accepted (publicEq second)).trans
      (congrArg PublicView.accepted (publicEq first)).symm
  have reconstructed : memory.native owner (finish second) = finish first := by
    dsimp only [finish, memory]
    rw [native_setAccepted, rememberCompletion_native_complete]
    simp only [preparation, acceptedEq]
  have owned : memory.OwnBindings owner :=
    ((ownBindings_empty owner).rememberCandidate _ _).rememberCompletion event payload outputEq _ _
  refine ⟨finish first, finish second, memory, ?_, ?_, owned, reconstructed, ?_, ?_⟩
  · rw [handle_commitment_eq runtime (prepare first) id event (owner, .prepared serial) owner
      payload outputEq codeEq node (preparedReady first) (preparedTimely first) sender rfl
        (preparedVacant first) (preparedUnused first),
      (prepare first).candidates.freeze_eq_self_of_not_fresh _ (fixed first)]
    rfl
  · rw [handle_commitment_eq runtime (prepare second) id event (owner, .prepared serial) owner
      payload outputEq codeEq node (preparedReady second) (preparedTimely second) sender rfl
        (preparedVacant second) (preparedUnused second),
      (prepare second).candidates.freeze_eq_self_of_not_fresh _ (fixed second)]
    rfl
  · rw [← reconstructed]
    exact native_publicView owned _
  · intro observer different
    rw [← reconstructed]
    exact native_playerView_other owned _ observer different

/-- Clear phase normalization preserves all joint external views of an
arbitrary all-value shadow, including its saved checkpoint and retired records.
No successful-binding restriction is imposed on the remembered meanings. -/
theorem normalize_external_views (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (state : PhaseRuntimeState graph)
    (clear : state.current.excluded = ∅) :
    (memory.phased owner state).normalize.publicView = state.normalize.publicView ∧
      ∀ observer, observer ≠ owner →
        (memory.phased owner state).normalize.playerView observer =
          state.normalize.playerView observer := by
  rw [normalize_phased_of_clear memory owner state clear]
  exact ⟨phased_publicView owned _, fun observer different =>
    phased_playerView_other owned _ observer different⟩

end Vegas.EventGraphRuntime.BindingShadow
