/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceObservation
import Vegas.Pending.PhaseBindingPolicy

/-! # Physical binding components of syntactic source policies

The source head law is evaluated on the typed semantic view decoded from the
actual local input. Its encoded result law is exact at an unsent ready binding;
no auxiliary source-history or posterior identification is asserted.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  {Γ : SourceCtx Player L} {O : Finset VarId} {owner : Player} {name : VarId} {payload : L.Ty}
  (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
  (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
  (refs : ContextRefs (graphLayout setup.program) Γ)
  (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
    (.commit name owner fresh guard next))

/-- Evaluate the original syntactic commitment head on the actual surviving
semantic view, then implement it by a globally legal physical response policy. -/
def phaseSourceBindingPolicy
    (policy : BehavioralPolicy owner (.commit name owner fresh guard next)) :
    (phaseApplication runtime leaks).Policy :=
  PhaseCount.phaseBindingPolicy runtime leaks bounds owner
    (embedding.event ⟨0, by simp only [eventCount]; omega⟩) payload fun _ view =>
      match phaseSemanticDecisionView? setup mode runtime leaks refs owner view with
      | none => PMF.pure .failure
      | some source => policy.1 rfl source

/-- Every actual unsent ready callback realizes the original source binding
head law at its decoded semantic view, with a derived globally fresh slot.
The complete policy remains legal at all other inputs by its actual menu guard. -/
theorem phaseSourceBindingPolicy_of_history
    (before : ContextRefsBefore refs embedding)
    (policy : BehavioralPolicy owner (.commit name owner fresh guard next))
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control)) (active : control.actor = some owner)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt,
        embedding.event ⟨0, by simp only [eventCount]; omega⟩⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs
      (control.execution.recall owner), PhaseCount.event? message.payload ≠ some
        ⟨control.execution.application.attempt,
          embedding.event ⟨0, by simp only [eventCount]; omega⟩⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    ∃ source serial,
      phaseSemanticDecisionView? setup mode runtime leaks refs owner
        (control.execution.observe (phaseApplication runtime leaks) owner) = some source ∧
      serial < horizon ∧
      phaseSourceBindingPolicy setup mode runtime leaks bounds fresh guard next refs embedding
          policy (control.execution.recall owner)
          (control.execution.observe (phaseApplication runtime leaks) owner) =
        (policy.1 rfl source).map (phaseBindingResponse runtime leaks owner
          (embedding.event ⟨0, by simp only [eventCount]; omega⟩) payload · serial) ∧
      (phaseSourceBindingPolicy setup mode runtime leaks bounds fresh guard next refs embedding
        policy (control.execution.recall owner)
        (control.execution.observe (phaseApplication runtime leaks) owner)).map
          (fun response =>
            let after := control.execution.respond (phaseApplication runtime leaks) owner response
            after.application.current.native.bindingResult (owner, .prepared serial) payload) =
        policy.1 rfl source := by
  let head : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp only [eventCount]; omega⟩
  have outputEq : (serviceGraph setup mode).outputLayout (embedding.event head) =
      .binding owner payload := by
    exact embedding.layout_eq head
  obtain ⟨source, decoded⟩ := phaseSemanticDecisionView?_succeeds setup mode runtime leaks
    (.commit name owner fresh guard next) refs embedding before head control.execution owner
      request.2.2.1 request.2.2.2.1
        (by rw [outputEq]; simp only [EventField.IsPublication, not_false_eq_true])
  obtain ⟨serial, bounded, law, result⟩ := PhaseCount.phaseBindingPolicy_of_history runtime leaks
    bounds owner (embedding.event head) payload outputEq
      (fun _ view => match phaseSemanticDecisionView? setup mode runtime leaks refs owner view with
        | none => PMF.pure .failure
        | some source => policy.1 rfl source)
      menu plan inputs horizon scheduler capacity control trace active request unsent values
  refine ⟨source, serial, decoded, bounded, ?_, ?_⟩
  · simpa only [phaseSourceBindingPolicy, decoded] using law
  · simpa only [phaseSourceBindingPolicy, decoded] using result

end Vegas
