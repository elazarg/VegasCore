/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDisclosureStability
import Vegas.Pending.ReactiveDisclosureRealization
import Vegas.Pending.ReactivePolicyFacts
import Interaction.ReactiveRecallInvariant

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A recorded ready owner-local resolution retains its complete evaluation
 and accepted binding, even through arbitrary legal off-path interaction. -/
def RecordedResolutionFrame (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ who entry, entry ∈ execution.recall who → ∀ event payload
    (binding : FieldRef graph.layout (.binding who payload)) checks outputEq codeEq,
    nodeView graph event = .resolve who payload binding checks outputEq codeEq →
    entry.beforeView.application.who = who →
    entry.beforeView.application.publicView.EventReady event →
    (∀ disclose,
      EventCode.resolveOutput? binding checks disclose execution.application.config.store =
        EventCode.resolveOutput? binding checks disclose
          entry.beforeView.application.observation.store) ∧
    execution.application.accepted binding.field =
      entry.beforeView.application.publicView.accepted binding.field ∧
    ∀ field ∈ insert binding.field (GuardCheck.listReadFields checks),
      (execution.application.config.store field).isSome = true

/-- Causal ready fields supply the actual raw-trace resolution frame. -/
theorem recordedResolutionFrameInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (runtime.RecordedResolutionFrame leaks) := by
  let app := runtime.reactiveApplication leaks
  constructor
  · intro execution actor action valid who entry retained event payload binding checks outputEq
      codeEq node owner ready
    rcases app.respond_entry_origin execution actor who action entry retained with old | fresh
    · obtain ⟨evaluate, accepted, available⟩ :=
        valid who entry old event payload binding checks outputEq codeEq node owner ready
      have frame := (runtime.reactiveReadFrameInvariant leaks execution.application
        (insert binding.field (GuardCheck.listReadFields checks)) available).respond
          execution actor action (fun _ _ => ⟨rfl, rfl⟩)
      refine ⟨fun disclose => ?_, (frame binding.field (Finset.mem_insert_self ..)).2.trans
        accepted, ?_⟩
      · exact (EventCode.resolveOutput?_congr binding checks disclose _ _
          (fun field member => (frame field member).1)).trans (evaluate disclose)
      · intro field member
        rw [(frame field member).1]
        exact available field member
    · have equal := fresh.1
      subst actor
      rw [fresh.2] at owner ready ⊢
      have physicalReady : execution.application.config.cut.Ready event :=
        (execution.application.publicView_eventReady event).mp ready
      have reads := resolution_readFields event who payload binding checks outputEq codeEq
      have available : ∀ field ∈ insert binding.field (GuardCheck.listReadFields checks),
          (execution.application.config.store field).isSome = true :=
        fun field member => execution.application.config.read_available physicalReady
          (reads.symm ▸ member)
      have frame := (runtime.reactiveReadFrameInvariant leaks execution.application
        (insert binding.field (GuardCheck.listReadFields checks)) available).respond
          execution who action (fun _ _ => ⟨rfl, rfl⟩)
      refine ⟨fun disclose => ?_, (frame binding.field (Finset.mem_insert_self ..)).2, ?_⟩
      · exact (EventCode.resolveOutput?_congr binding checks disclose _ _
          (fun field member => (frame field member).1)).trans
            (EventCode.resolveOutput?_playerStore binding checks
              execution.application.config.store disclose).symm
      · intro field member
        rw [(frame field member).1]
        exact available field member
  · intro execution next command valid _ reached who entry retained event payload binding checks
      outputEq codeEq node owner ready
    rw [app.environmentStep_recall execution next command reached] at retained
    obtain ⟨evaluate, accepted, available⟩ :=
      valid who entry retained event payload binding checks outputEq codeEq node owner ready
    have frame := (runtime.reactiveReadFrameInvariant leaks execution.application
      (insert binding.field (GuardCheck.listReadFields checks)) available).environmentStep
        execution next command (fun _ _ => ⟨rfl, rfl⟩) reached
    refine ⟨fun disclose => ?_, (frame binding.field (Finset.mem_insert_self ..)).2.trans
      accepted, ?_⟩
    · exact (EventCode.resolveOutput?_congr binding checks disclose _ _
        (fun field member => (frame field member).1)).trans (evaluate disclose)
    · intro field member
      rw [(frame field member).1]
      exact available field member

/-- Every actual initialized legal raw trace retains each recorded resolution frame. -/
theorem recordedResolutionFrame_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) : runtime.RecordedResolutionFrame leaks control.execution := by
  exact (runtime.recordedResolutionFrameInvariant leaks scheduler).history initial horizon
    (fun _ _ who entry member => False.elim (List.not_mem_nil member)) trace

/-- The actual raw trace preserves a genuinely recorded silent resolution's
 semantic failure, including TRUE intentions rejected by deferred guards. -/
theorem reactiveSilentDecision_history_failure (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control))
    (valid : control.execution.application.BindingInvariant)
    (who : Player) (remembered : graph.Completion)
    (ready : control.execution.application.config.cut.Ready remembered.event)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding who payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout remembered.event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes remembered.event) = .resolve who payload binding checks)
    (node : nodeView graph remembered.event = .resolve who payload binding checks outputEq codeEq)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (retained : entry ∈ control.execution.recall who)
    (matching : runtime.ReactiveSilentDecision leaks who entry remembered) :
    EventCode.resolveOutput? binding checks
      (cast (congrArg EventField.Action outputEq) remembered.action)
        control.execution.application.config.store = some .failure := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨_, silent, owner, _, wasReady, _, generated⟩ := matching
  obtain ⟨evaluate, accepted, _⟩ :=
    (runtime.recordedResolutionFrame_history leaks initial horizon scheduler control trace)
      who entry retained remembered.event payload binding checks outputEq codeEq node owner wasReady
  have resolved : EventCode.resolveOutput? binding checks true
      entry.beforeView.application.observation.store =
        EventCode.resolveOutput? binding checks true
          (app.observePlayer control.execution.application who).observation.store :=
    (evaluate true).symm.trans
      (EventCode.resolveOutput?_playerStore binding checks
        control.execution.application.config.store true).symm
  have packet := reactiveResolutionPacket_eq_of_resolution who remembered.event payload binding
    checks outputEq remembered.action entry.beforeView.application
      (app.observePlayer control.execution.application who) resolved accepted.symm
  have absent : reactiveResolutionPacket who remembered.event payload binding checks outputEq
      remembered.action entry.beforeView.application = none := by
    rw [generated] at silent
    simp only [reactiveDecision, node] at silent
    cases selected : reactiveResolutionPacket who remembered.event payload binding checks outputEq
      remembered.action entry.beforeView.application with
    | none => rfl
    | some material => simp only [selected, Option.map_some] at silent; cases silent
  have nowSilent : (runtime.reactiveDecision leaks who remembered.event remembered.action
      (app.observePlayer control.execution.application who)).transmission = none := by
    simp only [reactiveDecision, node, ← packet, absent, Option.map_none]
  apply runtime.reactiveDecision_silent_resolution_failure leaks control.execution.application
    valid who remembered.event ready payload binding checks outputEq codeEq node
  simpa only [cast_cast, cast_eq] using nowSilent

end Vegas.EventGraphRuntime
