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

/-- An actual author's recorded transmissions are acceptable whenever the
original author view was within the addressed event's deadline. -/
def RecordedTimelyCalls (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ entry, entry ∈ execution.recall who → ∀ message event,
    entry.emitted = some message → message.payload.call.event? graph = some event →
    entry.beforeView.application.publicView.WithinDeadline runtime event →
    runtime.freshServiceAcceptable entry.beforeView.application.publicView message

/-- Each selected authentic author retains its actual recorded conformance
through arbitrary other-player responses and scheduler commands. -/
theorem recordedTimelyCalls_policyInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    {Selected : Type} (owners : Selected → Player)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (authentic : ∀ index, players (owners index) =
      runtime.prescribedReactivePolicy leaks (owners index) (profile (owners index))) :
    (runtime.reactiveApplication leaks).PolicyInvariant players
      (fun execution => execution.application.BindingInvariant ∧
        ∀ index, runtime.RecordedTimelyCalls leaks (owners index) execution) := by
  let app := runtime.reactiveApplication leaks
  constructor
  · intro execution who action valid positive
    refine ⟨(runtime.reactiveBindingInvariant leaks).respond execution who action valid.1, ?_⟩
    intro index entry retained message event emitted named timely
    by_cases same : owners index = who
    · subst who
      rw [authentic index] at positive
      rcases action with ⟨transmission⟩
      cases transmission with
      | none =>
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
            List.mem_singleton] at retained
          rcases retained with old | rfl
          · exact valid.2 index entry old message event emitted named timely
          · cases emitted
      | some material =>
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
            List.mem_singleton] at retained
          rcases retained with old | rfl
          · exact valid.2 index entry old message event emitted named timely
          · have sameMessage := Option.some.inj emitted
            subst message
            apply runtime.prescribedReactivePolicy_emitted_acceptable leaks execution valid.1
              (owners index) (profile (owners index)) ⟨some material⟩ positive material rfl event
            · simpa only [MessageNetwork.submit, reactiveApplication, WitnessedSubmission.emit_call]
                using named
            · exact timely
    · rw [app.respond_recall_other execution who (owners index) same action] at retained
      exact valid.2 index entry retained message event emitted named timely
  · intro execution next command valid reached
    refine ⟨(runtime.reactiveBindingInvariant leaks).environmentStep execution next command
      valid.1 reached, ?_⟩
    intro index entry retained message event emitted named timely
    rw [app.environmentStep_recall execution next command reached] at retained
    exact valid.2 index entry retained message event emitted named timely

/-- Authentic foreign authors retain recorded conformance when the focal
player uses an arbitrary raw policy in the unchanged reactive application. -/
theorem recordedTimelyCalls_unilateral_policyInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile) (focal : Player)
    (deviation : (runtime.reactiveApplication leaks).Policy) :
    (runtime.reactiveApplication leaks).PolicyInvariant
      (Function.update (fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner))
        focal deviation)
      (fun execution => execution.application.BindingInvariant ∧
        ∀ owner : {who : Player // who ≠ focal},
          runtime.RecordedTimelyCalls leaks owner.val execution) := by
  apply runtime.recordedTimelyCalls_policyInvariant leaks profile Subtype.val
  intro owner
  exact Function.update_of_ne owner.property _ _

end Vegas.EventGraphRuntime
