/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService
import Vegas.Compile.EventGraphState
import Vegas.Compile.EventGraphHistory
import Vegas.EventGraph.SequentialLaw

/-! # Source state agreement at native reveal checkpoints

These lemmas use the existing source successor and native completion functions.
They preserve typed context references across either disclosure choice; no
source executor or native state is reconstructed or replaced. Service timing,
packet acceptance, and the information-history correspondence are separate
obligations of the adapter.
-/

noncomputable section

namespace Vegas

open SourceProgram

open EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Arbitrarily correlated initialized source states are encoded exactly in
the actual sequential runtime's initial store. -/
theorem initial_agrees (setup : Setup (Player := Player) (L := L))
    (initial : State L setup.context) :
    (ContextRefs.initial setup.context (outputLayout setup.program)).Agrees initial
      (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs initial)).config.store := by
  apply ContextRefs.initial_agrees
  intro input
  rfl

theorem initial_history (setup : Setup (Player := Player) (L := L))
    (initial : State L setup.context) :
    decodeHistory setup.program
      ((EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs initial)).config.history.map
          (setup.eventGraph.fromModeCompletion .sequential)) = fun _ => [] := rfl

/-- Native completion appends exactly the source reveal choice to the owner's
source history. Extra native response names remain in native recall and are
not mistaken for extra source decisions. -/
theorem complete_reveal_history (setup : Setup (Player := Player) (L := L))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (selected : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (native : EventGraphRuntime.State (graph setup))
    (history : decodeHistory setup.program
      (native.config.history.map (setup.eventGraph.fromModeCompletion .sequential)) =
        source.history)
    (event : (graph setup).EventId) (ready : native.config.cut.Ready event)
    (action : (graph setup).Action event) (value : ((graph setup).outputLayout event).Value)
    (disclose : Bool)
    (decoded : decodeEventAction setup.program event action =
      some (.reveal owner name disclose)) :
    decodeHistory setup.program
      ((native.complete event ready action value).config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) =
      (revealSuccessor published selected source disclose).history := by
  change decodeHistory setup.program
    ((native.config.history ++ [(⟨event, action⟩ : (graph setup).Completion)]).map
      (setup.eventGraph.fromModeCompletion .sequential)) = _
  rw [List.map_append, List.map_singleton]
  change decodeHistory setup.program
    (native.config.history.map (setup.eventGraph.fromModeCompletion .sequential) ++
      [⟨event, action⟩]) = _
  rw [decodeHistory_append_completion, decoded, history]
  rfl

/-- Once the real runtime has completed the current reveal, its store agrees
with the real source successor. The premise records the ordinary compiler's
reference order, independently of who owns this or any later event. -/
theorem complete_reveal_agrees {nativeGraph : Vegas.EventGraph Player L}
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (selected : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (empty : source.registry = [])
    (refs : ContextRefs nativeGraph.layout Γ)
    (native : EventGraphRuntime.State nativeGraph)
    (agree : refs.Agrees source.state native.config.store)
    (event : nativeGraph.EventId) (ready : native.config.cut.Ready event)
    (outputEq : nativeGraph.outputLayout event = .publication payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (disclose : Bool) :
    let result := if disclose then source.state.get selected else PublicationResult.failure
    let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose
    let stored := cast (congrArg EventGraph.EventField.Value outputEq.symm) result
    let resultRef : EventGraph.FieldRef nativeGraph.layout (.publication payload) :=
      ⟨.inr event, outputEq⟩
    (refs.cons (name := published) resultRef).Agrees
      (revealSuccessor published selected source disclose).state
      (native.complete event ready action stored).config.store := by
  dsimp only
  have sourceState : (revealSuccessor published selected source disclose).state =
      Env.cons (Val := CellVal (Player := Player) L) (x := published) (τ := .publication payload)
        (if disclose then source.state.get (τ := .commitment owner payload) selected
          else PublicationResult.failure) source.state := by
    simp only [revealSuccessor, empty, Registry.completedBy, List.filter_nil, List.map_nil,
      List.all_nil, ↓reduceIte]
  rw [sourceState]
  apply ContextRefs.Agrees.cons
  · exact ContextRefs.Agrees.complete ready _ _ refs source.state agree before
  · rw [EventGraphRuntime.State.complete, EventGraph.store_complete]
    simp only [EventGraph.FieldRef.get?, Function.update_self]
    have castSome {A B : Type} (same : A = B) (value : A) :
        cast (congrArg Option same) (some value) = some (cast same value) := by
      cases same
      rfl
    rw [castSome (congrArg EventGraph.EventField.Value outputEq)]
    have castInverse {A B : Type} (same : A = B) (value : B) :
        cast same (cast same.symm value) = value := by
      cases same
      rfl
    exact congrArg some (castInverse (congrArg EventGraph.EventField.Value outputEq) _)

/-- The ordinary menu's local decoder finds the authentic opening at a valid
source checkpoint. The candidate is obtained from the existing binding
invariant; it is not selected from a private global catalogue by the compiler. -/
theorem opening_at_checkpoint (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (selected : HasVar Γ name (.commitment owner payload))
    (source : State L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source execution.application.config.store)
    (valid : execution.application.BindingInvariant)
    (event : (graph setup).EventId)
    (ownedEvent : (graph setup).actor? event = some owner)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get selected) [] outputEq codeEq)
    (granted : execution.application.serviceGrant = some event)
    (value : L.Val payload) (bound : source.get selected = .success value) :
    ∃ candidate, execution.application.accepted (refs.get selected).field = some candidate ∧
      candidate.1 = owner ∧
      execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      opening? setup leaks owner (execution.recall owner)
          (execution.observe (application setup leaks) owner) =
        some (((runtime setup).reactiveNormalization leaks).action owner
          (execution.recall owner) (execution.observe (application setup leaks) owner)
          ((runtime setup).canonicalRevealResponse leaks event candidate
            ⟨payload, value⟩ true)) := by
  have stored : (refs.get selected).get? execution.application.config.store =
      some (.success value) := by
    simpa only [bound, cellValue] using agree selected
  obtain ⟨candidate, associated, owned, verified⟩ :=
    valid.success_provenance (refs.get selected) value stored
  refine ⟨candidate, associated, owned, verified, ?_⟩
  let view := execution.observe (application setup leaks) owner
  have seesGrant : view.application.publicView.serviceGrant = some event := granted
  have seesAccepted : view.application.publicView.accepted (refs.get selected).field =
      some candidate := associated
  have resolved : EventGraph.EventCode.resolveOutput? (refs.get selected) [] true
      view.application.observation.store = some (.success value) := by
    change EventGraph.EventCode.resolveOutput? (refs.get selected) [] true
      ((graph setup).playerStore owner execution.application.config.store) = _
    rw [EventGraph.EventCode.resolveOutput?_playerStore]
    simp only [EventGraph.EventCode.resolveOutput?, stored,
      EventGraph.GuardCheck.allAccepted?, ↓reduceIte]
    rfl
  change opening? setup leaks owner (execution.recall owner) view = _
  simp only [opening?, seesGrant, bind, Option.bind_some, ownedEvent, ne_eq, not_true_eq_false,
    ↓reduceIte, node, resolved, seesAccepted, owned]
  rfl

end Vegas
