/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveSampledAcceptance
import Vegas.Pending.ReactiveCanonicalDecision
import Vegas.Pending.ReactiveResponseSampling
import Vegas.Pending.ReactiveAssociationEvidence
import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveRecallInvariant

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A physically supported prescribed transmission is genuinely acceptable
 on its actual author view whenever the event is still within its deadline. -/
theorem prescribedReactivePolicy_emitted_acceptable (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (who : Player) (policy : graph.BehavioralPolicy who)
    (action : (runtime.reactiveApplication leaks).Action)
    (positive : action ∈ (runtime.prescribedReactivePolicy leaks who policy
      (execution.recall who) (execution.observe (runtime.reactiveApplication leaks) who)).support)
    (material : WitnessedSubmission graph) (transmitted : action.transmission = some material)
    (event : graph.EventId) (named : material.call.packet.event? graph = some event)
    (timely : execution.application.WithinDeadline runtime event) :
    runtime.freshServiceAcceptable execution.application.publicView
      ⟨(who, execution.network.nextSerial who),
        material.emit ((runtime.reactiveApplication leaks).submit execution.application who
          material)
          who (execution.network.known who)⟩ := by
  rw [runtime.prescribedReactivePolicy_apply] at positive
  obtain ⟨intentions, _, issued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ positive)
  obtain ⟨⟨physical, saved⟩, produced, image⟩ := PMF.support_map .. ▸ issued
  dsimp only at image
  subst physical
  cases saved with
  | none =>
      have silent := runtime.prescribedReactiveResponse_none_silent leaks who policy
        (execution.recall who) intentions
          (execution.observe (runtime.reactiveApplication leaks) who)
        action produced
      rw [transmitted] at silent
      cases silent
  | some remembered =>
      have addressed := (runtime.prescribedReactiveResponse_transmitted_event leaks who policy
        (execution.recall who) intentions
          (execution.observe (runtime.reactiveApplication leaks) who)
        action remembered produced material transmitted).2.2
      have same : remembered.event = event := Option.some.inj (addressed.symm.trans named)
      exact runtime.prescribedReactiveResponse_emitted_acceptable leaks execution valid who policy
        (execution.recall who) intentions action remembered produced (same ▸ timely)
          material transmitted

/-- Actual recorded transmissions are acceptable whenever their original
 author view was within the addressed event's deadline. -/
def RecordedTimelyCalls (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ who entry, entry ∈ execution.recall who → ∀ message event,
    entry.emitted = some message → message.payload.call.event? graph = some event →
    entry.beforeView.application.publicView.WithinDeadline runtime event →
    runtime.freshServiceAcceptable entry.beforeView.application.publicView message

/-- Actual prescribed callbacks retain their genuine conformance facts through
 arbitrary scheduler commands; no conformance is imposed on late calls. -/
theorem recordedTimelyCalls_policyInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile) :
    (runtime.reactiveApplication leaks).PolicyInvariant
      (fun who => runtime.prescribedReactivePolicy leaks who (profile who))
      (fun execution => execution.application.BindingInvariant ∧
        runtime.RecordedTimelyCalls leaks execution) := by
  let app := runtime.reactiveApplication leaks
  constructor
  · intro execution who action valid positive
    refine ⟨(runtime.reactiveBindingInvariant leaks).respond execution who action valid.1, ?_⟩
    intro observer entry retained message event emitted named timely
    by_cases same : observer = who
    · subst observer
      rcases action with ⟨transmission⟩
      cases transmission with
      | none =>
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
            List.mem_singleton] at retained
          rcases retained with old | rfl
          · exact valid.2 who entry old message event emitted named timely
          · cases emitted
      | some material =>
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
            List.mem_singleton] at retained
          rcases retained with old | rfl
          · exact valid.2 who entry old message event emitted named timely
          · have sameMessage := Option.some.inj emitted
            subst message
            apply runtime.prescribedReactivePolicy_emitted_acceptable leaks execution valid.1 who
              (profile who) ⟨some material⟩ positive material rfl event
            · simpa only [MessageNetwork.submit, reactiveApplication, WitnessedSubmission.emit_call]
                using named
            · exact timely
    · rw [app.respond_recall_other execution who observer same action] at retained
      exact valid.2 observer entry retained message event emitted named timely
  · intro execution next command valid reached
    refine ⟨(runtime.reactiveBindingInvariant leaks).environmentStep execution next command
      valid.1 reached, ?_⟩
    intro who entry retained message event emitted named timely
    rw [app.environmentStep_recall execution next command reached] at retained
    exact valid.2 who entry retained message event emitted named timely

end Vegas.EventGraphRuntime
