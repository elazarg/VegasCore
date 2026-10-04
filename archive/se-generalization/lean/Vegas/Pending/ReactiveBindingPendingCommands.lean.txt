/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameCommands
import Vegas.Pending.ReactiveBindingPendingExpiry
import Vegas.Pending.ReactiveAuthorizationProgress

/-! # Actual scheduler commands with one pending binding override

The existing frame remains valid while its one uncompleted completion override
names the actual current binding. Clock advancement, samples and expiry retain
both physical marginals. A completed-boundary shadow is recovered only when
that actual event completes. Packet inclusion and whole-policy comparison are
separate from this command closure.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace BindingShadow

/-- Every completion override is already completed except the named pending event. -/
def CompletedExcept (memory : BindingShadow graph) (config : graph.Config)
    (pending : graph.EventId) : Prop :=
  ∀ event, (memory.actions event).isSome ∨ (memory.values (.inr event)).isSome →
    event = pending ∨ event ∈ config.cut.completed

/-- Ordinary completed memory has no exceptional uncompleted event. -/
theorem CompletedAt.completedExcept {memory : BindingShadow graph} {config : graph.Config}
    (past : memory.CompletedAt config) (pending : graph.EventId) :
    memory.CompletedExcept config pending := fun event present => Or.inr (past event present)

/-- Candidate-only memory updates do not alter the pending completion exception. -/
theorem CompletedExcept.rememberCandidate {memory : BindingShadow graph}
    {config : graph.Config} {pending : graph.EventId}
    (past : memory.CompletedExcept config pending) (slot : CandidateSlot graph)
    (value : CommitmentCandidate (Raw L)) :
    (memory.rememberCandidate slot value).CompletedExcept config pending := past

/-- A fresh pending override has only the event it actually names as an exception. -/
theorem CompletedAt.rememberCompletion_except {memory : BindingShadow graph}
    {config : graph.Config} (past : memory.CompletedAt config) (pending : graph.EventId)
    (action : graph.Action pending) (value : (graph.outputLayout pending).Value) :
    (memory.rememberCompletion pending action value).CompletedExcept config pending := by
  classical
  intro event present
  by_cases same : event = pending
  · exact Or.inl same
  · right
    apply past event
    simpa only [BindingShadow.rememberCompletion, Function.update_of_ne same,
      Function.update_of_ne (Sum.inr_injective.ne same)] using present

/-- The pending exception persists as the actual completed cut grows. -/
theorem CompletedExcept.mono {memory : BindingShadow graph} {before after : graph.Config}
    {pending : graph.EventId} (past : memory.CompletedExcept before pending)
    (completed : before.cut.completed ⊆ after.cut.completed) :
    memory.CompletedExcept after pending := by
  intro event present
  exact (past event present).imp_right (fun member => completed member)

/-- Actual completion of the exceptional event restores the original boundary invariant. -/
theorem CompletedExcept.completedAt {memory : BindingShadow graph} {config : graph.Config}
    {pending : graph.EventId} (past : memory.CompletedExcept config pending)
    (completed : pending ∈ config.cut.completed) : memory.CompletedAt config := by
  intro event present
  rcases past event present with same | earlier
  · exact same ▸ completed
  · exact earlier

end BindingShadow

variable [DecidableEq Player]
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

namespace BindingMemory

/-- The actual fresh unusable repair installs exactly one pending completion exception. -/
theorem repairResponse_unusable_completedExcept
    (who : Player) (memory : BindingMemory runtime leaks)
    (actual : (runtime.reactiveApplication leaks).PlayerView)
    (config : graph.Config) (past : memory.shadow.CompletedAt config)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (originalFresh : (memory.shadow.inputView runtime leaks actual).application.candidates
      (.prepared serial) = .fresh)
    (actualFresh : actual.application.candidates (.prepared serial) = .fresh)
    (unusable : opening.bind (fun raw => raw.as? payload) = none) :
    (memory.repairResponse runtime leaks who actual
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩).2.CompletedExcept
        config event := by
  simp only [repairResponse, node, originalFresh, actualFresh, unusable]
  exact (past.rememberCandidate _ _).rememberCompletion_except _ _ _

namespace Frame

variable {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Expiry has a full joint frame law while the only ready event has the
remembered original failure. Unready, inactive and early expiry stutter. -/
theorem expire_pending_binding_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (pending : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout pending = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes pending) = .bind owner payload)
    (node : nodeView graph pending = .bind owner payload outputEq codeEq)
    (ready : original.application.config.cut.Ready pending)
    (sole : ∀ event, original.application.config.cut.Ready event → event = pending)
    (rememberedAction : memory.shadow.actions pending = some
      (cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure))
    (rememberedValue : memory.shadow.values (.inr pending) = some
      (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure))
    (event : graph.EventId) :
    let app := runtime.reactiveApplication leaks
    ∃ coupling : PMF (app.Execution × app.Execution),
      coupling.map Prod.fst = original.environmentStep app (.application (.expire event)) ∧
      coupling.map Prod.snd = repaired.environmentStep app (.application (.expire event)) ∧
      ∀ pair ∈ coupling.support, Frame runtime leaks memory owner pair.1 pair.2 := by
  have readiness (event : graph.EventId) : original.application.config.cut.Ready event ↔
      repaired.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← State.publicView_eventReady, frame.publicView]
  have clocks : original.application.clock = repaired.application.clock :=
    congrArg PublicView.clock frame.publicView
  have activations : original.application.activatedAt = repaired.application.activatedAt :=
    congrArg PublicView.activatedAt frame.publicView
  by_cases actualReady : original.application.config.cut.Ready event
  swap
  · exact frame.application_stutter_coupling (.expire event)
      (environmentStep_expire_of_not_ready runtime original.application event actualReady)
      (environmentStep_expire_of_not_ready runtime repaired.application event
        (fun rightReady => actualReady ((readiness event).mpr rightReady)))
  have same := sole event actualReady
  subst event
  cases activated : original.application.activatedAt pending with
  | none =>
      have rightInactive : repaired.application.activatedAt pending = none := by
        rw [← activations, activated]
      exact frame.application_stutter_coupling (.expire pending)
        (environmentStep_expire_of_not_activated runtime original.application pending ready
          activated)
        (environmentStep_expire_of_not_activated runtime repaired.application pending
          ((readiness pending).mp ready) rightInactive)
  | some entered =>
      have rightActivated : repaired.application.activatedAt pending = some entered := by
        rw [← activations, activated]
      by_cases due : runtime.deadline pending ≤ original.application.clock - entered
      swap
      · have rightEarly : ¬runtime.deadline pending ≤ repaired.application.clock - entered := by
          rwa [← clocks]
        exact frame.application_stutter_coupling (.expire pending)
          (environmentStep_expire_of_not_due runtime original.application pending ready entered
            activated due)
          (environmentStep_expire_of_not_due runtime repaired.application pending
            ((readiness pending).mp ready) entered rightActivated rightEarly)
      obtain ⟨left, right, first, second, related⟩ := frame.expire_pending_failure pending payload
        outputEq codeEq node ready rememberedAction rememberedValue entered activated due
      refine ⟨PMF.pure (left, right), ?_, ?_, ?_⟩
      · rw [PMF.pure_map, first]
      · rw [PMF.pure_map, second]
      · intro pair supported
        cases (PMF.mem_support_pure_iff _ _).mp supported
        exact related

/-- Actual application commands preserve the full pending frame and its one
exception. When the actual event is completed, the full boundary invariant
follows from that exception rather than being presumed at transmission. -/
theorem pending_application_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (pending : graph.EventId)
    (past : memory.shadow.CompletedExcept original.application.config pending)
    (payload : L.Ty)
    (outputEq : graph.outputLayout pending = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes pending) = .bind owner payload)
    (node : nodeView graph pending = .bind owner payload outputEq codeEq)
    (ready : original.application.config.cut.Ready pending)
    (sole : ∀ event, original.application.config.cut.Ready event → event = pending)
    (rememberedAction : memory.shadow.actions pending = some
      (cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure))
    (rememberedValue : memory.shadow.values (.inr pending) = some
      (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure))
    (command : EnvironmentCommand graph) :
    let app := runtime.reactiveApplication leaks
    ∃ coupling : PMF (app.Execution × app.Execution),
      coupling.map Prod.fst = original.environmentStep app (.application command) ∧
      coupling.map Prod.snd = repaired.environmentStep app (.application command) ∧
      ∀ pair ∈ coupling.support,
        Frame runtime leaks memory owner pair.1 pair.2 ∧
          memory.shadow.CompletedExcept pair.1.application.config pending ∧
          (pending ∈ pair.1.application.config.cut.completed →
            memory.shadow.CompletedAt pair.1.application.config) := by
  let app := runtime.reactiveApplication leaks
  have existsCoupling : ∃ coupling : PMF (app.Execution × app.Execution),
      coupling.map Prod.fst = original.environmentStep app (.application command) ∧
      coupling.map Prod.snd = repaired.environmentStep app (.application command) ∧
      ∀ pair ∈ coupling.support, Frame runtime leaks memory owner pair.1 pair.2 := by
    cases command with
    | advanceClock => exact frame.advanceClock_coupling
    | executeSample event => exact frame.executeSample_coupling onlyBindings event
    | expire event =>
        exact frame.expire_pending_binding_coupling pending payload outputEq codeEq
          node ready sole rememberedAction rememberedValue event
  obtain ⟨coupling, first, second, related⟩ := existsCoupling
  refine ⟨coupling, first, second, ?_⟩
  intro pair supported
  have leftSupport : pair.1 ∈ (original.environmentStep app (.application command)).support := by
    rw [← first]
    exact PMF.support_map .. ▸ ⟨pair, supported, rfl⟩
  have completed := (runtime.reactiveCompletedInvariant leaks
    original.application.config.cut.completed).environmentStep original pair.1
      (.application command) Finset.Subset.rfl leftSupport
  have advanced := past.mono completed
  exact ⟨related pair supported, advanced, advanced.completedAt⟩

end Frame

end BindingMemory

end Vegas.EventGraphRuntime
