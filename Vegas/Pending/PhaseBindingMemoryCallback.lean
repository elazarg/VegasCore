/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingResponseWitness
import Vegas.Pending.PhaseBindingMemoryFreshness

/-! # Actual callback alternatives inside an opaque commitment phase -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A callback without an unsent current request has only the silent response.
This includes both absent requests and requests already represented in recall. -/
theorem onePacketActions_eq_singleton_of_no_unsent (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (absent : ¬∃ coordinate, execution.application.SeedRequest owner coordinate ∧
      ∀ message ∈ (app).outputs (execution.recall owner),
        event? message.payload ≠ some coordinate) :
    onePacketActions runtime leaks bounds owner (execution.recall owner)
      (execution.observe app owner) = {⟨none⟩} := by
  apply Finset.ext
  intro response
  constructor
  · intro offered
    apply Finset.mem_singleton.mpr
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some material =>
        obtain ⟨coordinate, request⟩ := onePacket_request_of_nonsilent runtime leaks bounds plan
          inputs horizon scheduler remaining owner execution trace material offered
        exact (absent ⟨coordinate, request, unsent_of_nonsilent runtime leaks bounds plan ordered
          inputs horizon scheduler remaining owner execution trace coordinate request material
            offered⟩).elim
  · intro silent
    rw [Finset.mem_singleton.mp silent]
    exact silence_onePacket runtime leaks bounds owner _ _

end Vegas.EventGraphRuntime.PhaseCount

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Two actual opaque callbacks are either both silent or share a genuinely
unsent binding coordinate. The alternative is derived from their counted traces. -/
theorem callback_binding_or_silent (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (firstRemaining secondRemaining : Nat) (owner : Player)
    (left right : (app).Execution)
    (leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨firstRemaining, some owner, left⟩))
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨secondRemaining, some owner, right⟩))
    (memory : BindingShadow graph)
    (application : left.application = memory.phased owner right.application)
    (network : left.network = right.network)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : right.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment) :
    (PhaseCount.onePacketActions runtime leaks bounds owner (left.recall owner)
        (left.observe app owner) = {⟨none⟩} ∧
      PhaseCount.onePacketActions runtime leaks bounds owner (right.recall owner)
        (right.observe app owner) = {⟨none⟩}) ∨
      ∃ event payload, graph.outputLayout event = .binding owner payload ∧
        phase.low ≤ event.val ∧ event.val < phase.high ∧
        right.application.SeedRequest owner ⟨right.application.attempt, event⟩ ∧
        ∀ message ∈ (app).outputs (right.recall owner), PhaseCount.event? message.payload ≠
          some ⟨right.application.attempt, event⟩ := by
  classical
  have firstRecall := (app).history_inputRecall _ horizon scheduler
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler leftTrace)
  have secondRecall := (app).history_inputRecall _ horizon scheduler
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler rightTrace)
  have outputs : (app).outputs (left.recall owner) = (app).outputs (right.recall owner) := by
    rw [← firstRecall owner, ← secondRecall owner, network]
  by_cases usable : ∃ coordinate, right.application.SeedRequest owner coordinate ∧
      ∀ message ∈ (app).outputs (right.recall owner),
        PhaseCount.event? message.payload ≠ some coordinate
  · obtain ⟨coordinate, request, unsent⟩ := usable
    obtain ⟨current, present, member⟩ := request.2.1
    have currentEq : current = phase := by
      simpa only [installed, List.head?_cons, Option.mem_def, Option.some.injEq] using present.symm
    subst current
    have inside := (phase.mem_events coordinate.event).mp member
    have field := phase.fields coordinate.event inside.1 inside.2
    rw [committing] at field
    obtain ⟨actor, payload, binding⟩ := field
    have typed := (graph.nodes coordinate.event).output_public_or_binding_of_actor owner
      request.2.2.2.1
    have actorEq : actor = owner := by
      rcases typed with publicField | ⟨kind, ownField⟩
      · rw [binding] at publicField
        cases publicField
      · cases binding.symm.trans ownField
        rfl
    subst actor
    have same : coordinate = ⟨right.application.attempt, coordinate.event⟩ := by
      cases coordinate with
      | mk attempt event =>
          simp only [CommitAttemptEvent.mk.injEq]
          exact ⟨request.1, trivial⟩
    rw [same] at request unsent
    exact Or.inr ⟨_, payload, binding, inside.1, inside.2, request, unsent⟩
  · have leftAbsent : ¬∃ coordinate, left.application.SeedRequest owner coordinate ∧
        ∀ message ∈ (app).outputs (left.recall owner),
          PhaseCount.event? message.payload ≠ some coordinate := by
      rintro ⟨coordinate, request, unsent⟩
      apply usable
      refine ⟨coordinate, ?_, ?_⟩
      · rw [application] at request
        exact request
      · rw [outputs] at unsent
        exact unsent
    exact Or.inl ⟨PhaseCount.onePacketActions_eq_singleton_of_no_unsent runtime leaks bounds
      plan ordered inputs horizon scheduler firstRemaining owner left leftTrace
        leftAbsent,
      PhaseCount.onePacketActions_eq_singleton_of_no_unsent runtime leaks bounds plan ordered
        inputs horizon scheduler secondRemaining owner right rightTrace usable⟩

end Vegas.EventGraphRuntime.BindingShadow
