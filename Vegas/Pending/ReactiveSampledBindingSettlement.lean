/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBinding

/-! # Actual accepted binding settlements realize sampled graph actions -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Authentic delayed acceptance of the compiler's actual sampled binding
realizes its original graph action. Readiness, deadline and handle availability
are consequences of actual acceptance, rather than extra service premises. -/
theorem reactiveDecision_binding_accepted_continuation
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (action : graph.Action event) (serial : Nat)
    (execution later : (runtime.reactiveApplication leaks).Execution)
    (allocated : reactiveFreshSlot
      ((runtime.reactiveApplication leaks).observePlayer execution.application owner) = some serial)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy) (rounds : Nat)
    (reached : later ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) owner
        (runtime.reactiveDecision leaks owner event action
          ((runtime.reactiveApplication leaks).observePlayer
            execution.application owner)))).support)
    (after : State graph)
    (accepted : (runtime.reactiveApplication leaks).handle later.application
      ⟨(owner, execution.network.nextSerial owner),
        ⟨.commitment event (owner, .prepared serial), none, some ⟨event⟩⟩⟩ = some after) :
    ∃ ready : later.application.config.cut.Ready event,
      PMF.pure after.config = later.application.config.step event ready action := by
  have fresh := reactiveFreshSlot_spec
    ((runtime.reactiveApplication leaks).observePlayer execution.application owner) serial allocated
  rw [runtime.reactiveDecision_binding_eq leaks owner owner event payload outputEq codeEq
    node action _ serial allocated] at reached
  have meaning := runtime.reactiveBinding_continuation_result leaks owner event payload
    (cast (congrArg EventField.Action outputEq) action) serial execution later fresh
    scheduler players rounds reached
  have physical := reactiveHandle_call accepted
  change handle runtime later.application
    ⟨(owner, execution.network.nextSerial owner),
      .commitment event (owner, .prepared serial)⟩ = some after at physical
  have originalCall := physical
  simp only [handle] at physical
  split at physical
  · rename_i ready
    split at physical
    · rename_i timely
      simp only [node, Message.sender] at physical
      simp only [dite_eq_ite, Option.ite_none_right_eq_some, Option.some.injEq,
        true_and] at physical
      obtain ⟨vacant, unused, _⟩ := physical
      have exactHandle := runtime.handle_commitment_eq later.application
        (owner, execution.network.nextSerial owner) event (owner, .prepared serial)
        owner payload outputEq codeEq node ready timely rfl rfl vacant unused
      have equal := Option.some.inj (originalCall.symm.trans exactHandle)
      refine ⟨ready, ?_⟩
      rw [equal]
      change PMF.pure (later.application.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm)
          (later.application.bindingResult (owner, .prepared serial) payload))
        (cast (congrArg EventField.Value outputEq.symm)
          (later.application.bindingResult (owner, .prepared serial) payload))) = _
      rw [meaning]
      symm
      have law := later.application.config.step_eq_map_of_code event ready outputEq _ codeEq
        (cast (congrArg EventField.Action outputEq) action)
        (PMF.pure (cast (congrArg EventField.Action outputEq) action)) rfl
      simpa only [PMF.pure_map, cast_cast, cast_eq] using law
    · simp at physical
  · simp at physical

end Vegas.EventGraphRuntime
