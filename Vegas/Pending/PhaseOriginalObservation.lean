/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDisclosingRecall
import Vegas.Pending.PhaseNativePlayerInput
import Vegas.Pending.PhaseNativeFailureRecord
import Vegas.EventGraph.ResolutionProvenance

/-! # Original-action observations at genuine clear phase histories -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
private theorem eval_cast {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {left right : EventField Player L}
    (same : left = right) (code : EventCode layout left) (action : left.Action)
    (store : Store layout) :
    (cast (congrArg (EventCode layout) same) code).eval?
        (cast (congrArg EventField.Action same) action) store =
      (code.eval? action store).map
        (fun law => law.map (cast (congrArg EventField.Value same))) := by
  cases same
  change code.eval? action store = (code.eval? action store).map (fun law => law.map id)
  cases code.eval? action store with
  | none => rfl
  | some law => exact congrArg some (PMF.map_id law).symm

omit [DecidableEq Player] in
private theorem false_resolution_result {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload)) (store : Store graph.layout)
    (result : PublicationResult (L.Val payload))
    (resolved : EventCode.resolveOutput? binding checks false store = some result) :
    result = .failure := by
  unfold EventCode.resolveOutput? at resolved
  cases bound : binding.get? store with
  | none => simp only [bound, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at resolved
  | some bound =>
      simp only [bound, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true,
        ↓reduceIte] at resolved
      cases accepted : GuardCheck.allAccepted? checks store .failure with
      | none => simp only [accepted, Option.bind_none, reduceCtorEq] at resolved
      | some allowed =>
          simpa only [accepted, Option.bind_some, ite_self, Option.pure_def,
            Option.some.injEq] using resolved.symm

omit [DecidableEq Player] in
/-- Publicly nonfailed completed resolutions retain true physical actions.
This follows from their actual supported evaluator output in the final store. -/
theorem State.history_publication_true {inputs : graph.Inputs} (state : State graph)
    (reachable : state.config.Reachable inputs)
    (clear : ∀ event owner, graph.actor? event = some owner → ¬ state.PublicFailure event)
    (completion : graph.Completion) (member : completion ∈ state.config.history)
    (payload : L.Ty) (outputEq : graph.outputLayout completion.event = .publication payload) :
    cast (congrArg EventField.Action outputEq) completion.action = true := by
  classical
  cases node : nodeView graph completion.event with
  | sample nodePayload nodeLaw nodeOutput nodeCode =>
      cases nodeOutput.symm.trans outputEq
  | bind owner nodePayload nodeOutput nodeCode =>
      cases nodeOutput.symm.trans outputEq
  | resolve owner nodePayload binding checks nodeOutput nodeCode =>
      have sameType : nodePayload = payload := EventField.publication.inj
        (nodeOutput.symm.trans outputEq)
      subst nodePayload
      cases chosen : cast (congrArg EventField.Action outputEq) completion.action with
      | true => rfl
      | false =>
          obtain ⟨law, value, stored, evaluated, positive⟩ :=
            reachable.history_output_semantics completion member
          have evaluation := eval_cast outputEq (graph.nodes completion.event) completion.action
            state.config.store
          rw [nodeCode, chosen, evaluated, Option.map_some, EventCode.resolve_eval?] at evaluation
          cases resolved : EventCode.resolveOutput? binding checks false state.config.store with
          | none => simp only [resolved, Option.map_none, reduceCtorEq] at evaluation
          | some result =>
              have failedResult := false_resolution_result binding checks state.config.store
                result resolved
              subst result
              simp only [resolved, Option.map_some, Option.some.injEq] at evaluation
              have finalValue : cast (congrArg EventField.Value outputEq) value = .failure := by
                have mapped : cast (congrArg EventField.Value outputEq) value ∈
                    (law.map (cast (congrArg EventField.Value outputEq))).support :=
                  (PMF.mem_support_map_iff _ _ _).mpr ⟨value, positive, rfl⟩
                rw [← evaluation, PMF.mem_support_pure_iff] at mapped
                exact mapped
              have acting : graph.actor? completion.event = some owner := by
                change (graph.nodes completion.event).actor = some owner
                rw [← EventCode.actor_cast outputEq, nodeCode]
                rfl
              apply False.elim
              apply clear completion.event owner acting
              exact Or.inr (by
                simp only [RecoveryState.publicationFailed, node, stored, finalValue])

namespace PhaseNativeProjection

variable [Fintype Player] (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

/-- At every genuine clear counted phase history, supported disclosing original
memories reconstruct exactly the whole physical graph configuration. -/
theorem originalConfig_eq_of_clear (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (profile : graph.BehavioralProfile)
    (discloses : ∀ who event actor observation action,
      action ∈ (graph.normalizePolicy who (profile who) event actor observation).support →
        ∀ payload (outputEq : graph.outputLayout event = .publication payload),
          cast (congrArg EventField.Action outputEq) action = true)
    (consistent : ∀ who,
      (runtime.prescribedReactivePolicy (nativeLeaks leaks plan) who (profile who)).Consistent
        ((execution runtime leaks plan current.execution).recall who))
    (memories : Player → List (Option graph.Completion))
    (supported : ∀ who, memories who ∈
      ((runtime.prescribedReactiveImplementation (nativeLeaks leaks plan) who
        (profile who)).posterior
        ((execution runtime leaks plan current.execution).recall who)).support) :
    runtime.originalConfig (nativeLeaks leaks plan)
      (execution runtime leaks plan current.execution) memories =
        current.execution.application.current.native.config := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  obtain ⟨_draw, valid⟩ :=
    phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler raw
  have record := clear_publicRecord runtime leaks plan bounds inputs horizon scheduler trace clear
  apply runtime.originalConfig_eq_of_publication_true (nativeLeaks leaks plan) profile discloses
    (execution runtime leaks plan current.execution) consistent memories supported
  intro completion member payload outputEq
  exact State.history_publication_true _ valid.active.reachable (fun event owner acting failed => by
    have excluded := (record.excluded owner).mpr ⟨event, acting, failed⟩
    simp only [clear, Finset.notMem_empty] at excluded) completion member payload outputEq

end PhaseNativeProjection

end Vegas.EventGraphRuntime
