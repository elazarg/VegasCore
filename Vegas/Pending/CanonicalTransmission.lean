module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.EffectiveAction
public import Vegas.Pending.SilentAction
public import Vegas.Pending.ReactiveCanonicalResolution
public import Vegas.Pending.ReactiveCandidateBudget
public import Vegas.Pending.ReactiveStateInvariant
public import Vegas.Pending.ReactiveAssociationEvidence

@[expose] public section

/-! # Transmission of effective graph actions at initialized turns -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (timeouts : EventTimeouts graph)
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {inputs : PMF graph.Inputs}

/-- An effective non-silent graph action produces a concrete transmission at
an actual initialized turn, including an authentic opening whose guards reject. -/
theorem canonicalServiceDecision_transmits_of_effective {horizon : Nat}
    {scheduler : ((reactiveApplication timeouts) leaks).Scheduler}
    (control : ((reactiveApplication timeouts) leaks).Control)
    (trace : (((reactiveApplication timeouts) leaks).protocol
      (inputs.map State.initial) horizon scheduler).Trace
      (some control))
    (owner : Player) (event : graph.EventId)
    (turn : control.execution.application.publicView.ownTurn? owner = some event)
    (action : graph.Action event)
    (effective : EffectiveAction control.execution.application.config event action)
    (loud : ¬ SilentAction event action) :
    ∃ material, ((canonicalServiceDecision timeouts) leaks owner (control.execution.logs owner)
      (control.execution.observe ((reactiveApplication timeouts) leaks) owner) event
        action).transmission =
        some material := by
  let app := (reactiveApplication timeouts) leaks
  have quiescent := reactive_history_quiescent timeouts leaks inputs horizon scheduler trace
  have bindingInvariant := reactiveBindingInvariant_history timeouts leaks inputs horizon scheduler
    trace
  obtain ⟨readyView, owned⟩ :=
    control.execution.application.publicView.ownTurn?_spec owner event turn
  have ready := (control.execution.application.publicView_eventReady event).mp readyView
  have active := control.execution.application.active_of_ready_owned quiescent ready owned
  cases node : nodeView graph event with
  | sample payload law outputEq codeEq =>
      have actorNone := nodeView_sample_actor outputEq codeEq
      rw [owned] at actorNone
      cases actorNone
  | bind actor payload outputEq codeEq =>
      have sameActor : actor = owner :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst actor
      have present : cast (congrArg EventGraph.EventField.Action outputEq) action ≠ none := by
        simpa only [SilentAction, node] using loud
      obtain ⟨result, actionEq⟩ : ∃ result : PublicationResult (L.Val payload),
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) (some result) := by
        cases choice : cast (congrArg EventGraph.EventField.Action outputEq) action with
        | none => exact (present choice).elim
        | some result =>
            refine ⟨result, ?_⟩
            have back := congrArg
              (cast (congrArg EventGraph.EventField.Action outputEq.symm)) choice
            simpa only [cast_cast, cast_eq] using back
      have candidates := candidateRecall_history timeouts leaks inputs horizon scheduler trace
      obtain ⟨serial, _, selected⟩ := (reactiveFreshSlot_le_recall timeouts) leaks control.execution
        owner candidates
      obtain ⟨chosen, chosenEq⟩ := canonicalFreshSlot_isSome owner
        (control.execution.observe app owner).application serial selected
      rw [actionEq, (canonicalServiceDecision_binding timeouts) leaks owner
        (control.execution.logs owner) (control.execution.observe app owner) event payload
        outputEq
        codeEq node active chosen chosenEq result]
      exact ⟨_, rfl⟩
  | resolve actor payload binding checks outputEq codeEq =>
      have sameActor : actor = owner :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst actor
      have disclose : cast (congrArg EventGraph.EventField.Action outputEq) action = true := by
        have notFalse : cast (congrArg EventGraph.EventField.Action outputEq) action ≠ false := by
          simpa only [SilentAction, node] using loud
        exact Bool.eq_true_of_not_eq_false notFalse
      have successful : ∃ value, binding.get? control.execution.application.config.store =
          some (.success value) := by
        have possible : cast (congrArg EventGraph.EventField.Action outputEq) action = true →
            ∃ value, binding.get? control.execution.application.config.store =
              some (.success value) := by
          simpa only [EffectiveAction, node] using effective
        exact possible disclose
      obtain ⟨value, stored⟩ := successful
      obtain ⟨candidate, accepted, candidateOwner, _⟩ :=
        bindingInvariant.success_provenance binding value stored
      have observedStored : binding.get?
          (control.execution.observe app owner).application.observation.store =
            some (.success value) := by
        change binding.get? (graph.playerStore owner
          control.execution.application.config.store) = _
        rw [binding.get?_playerStore owner _ rfl, stored]
      have transmits := (canonicalServiceDecision_openable timeouts) leaks owner
        (control.execution.logs owner) (control.execution.observe app owner) event owner payload
        binding checks outputEq codeEq node active value observedStored candidate accepted
        candidateOwner
      have back := congrArg (cast (congrArg EventGraph.EventField.Action outputEq.symm)) disclose
      simp only [cast_cast, cast_eq] at back
      rw [back]
      cases sent : ((canonicalServiceDecision timeouts) leaks owner (control.execution.logs owner)
          (control.execution.observe app owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).transmission with
      | none => exact (transmits sent).elim
      | some material => exact ⟨material, rfl⟩

end Vegas.EventGraphRuntime
