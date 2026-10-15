/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingExpiryCoupling

/-! # Actual scheduler histories for paired chance and clear expiry outcomes -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- The common chance kernel produces a genuine repaired prefix under the
same selected scheduler atom, at the same remaining protocol budget. -/
theorem sample_trace (frame : Frame runtime leaks memory owner original repaired)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (PhaseRuntimeState graph)) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (prior : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, repaired⟩))
    (onlyBindings : memory.shadow.OwnBindings owner)
    (event : graph.EventId) (ready : original.application.current.native.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (node : nodeView graph event = .sample payload law outputEq codeEq)
    (allowed : original.application.commandAllowed (.executeSample event) = true)
    (next : (phaseApplication runtime leaks).Execution)
    (selected : ((.application (.executeSample event)) :
      (phaseApplication runtime leaks).Command) ∈
        (scheduler original.environmentRecall
          (original.observeEnvironment (phaseApplication runtime leaks))).support)
    (moved : next ∈ (original.environmentStep (phaseApplication runtime leaks)
      (.application (.executeSample event))).support) :
    ∃ image, Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, image⟩)) ∧ Frame runtime leaks memory owner next image := by
  obtain ⟨coupled, leftLaw, rightLaw, valid⟩ := frame.sample_coupling onlyBindings event ready
    payload law outputEq codeEq node allowed
  have source : next ∈ (coupled.map Prod.fst).support := by rw [leftLaw]; exact moved
  obtain ⟨pair, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp source
  have image : pair.2 ∈ (repaired.environmentStep (phaseApplication runtime leaks)
      (.application (.executeSample event))).support := by
    rw [← rightLaw, PMF.mem_support_map_iff]
    exact ⟨pair, supported, rfl⟩
  have chosen : ((.application (.executeSample event)) :
      (phaseApplication runtime leaks).Command) ∈
        (scheduler repaired.environmentRecall
          (repaired.observeEnvironment (phaseApplication runtime leaks))).support := by
    rw [← frame.scheduler_law scheduler]
    exact selected
  refine ⟨pair.2, menu.trace_environment initial horizon scheduler remaining repaired _
    (.application (.executeSample event)) prior chosen image, ?_⟩
  rw [← same]
  exact valid pair supported

/-- A realized source expiry whose actual result is clear extends to a real
image history. Source clear survival discharges the strategic timeout branch;
no target expiry outcome or completion law is assumed. -/
theorem expiry_trace (frame : Frame runtime leaks memory owner original repaired)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (PhaseRuntimeState graph)) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (prior : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, repaired⟩))
    (event : graph.EventId) (next : (phaseApplication runtime leaks).Execution)
    (selected : ((.application (.expire event)) : (phaseApplication runtime leaks).Command) ∈
      (scheduler original.environmentRecall
        (original.observeEnvironment (phaseApplication runtime leaks))).support)
    (moved : next ∈ (original.environmentStep (phaseApplication runtime leaks)
      (.application (.expire event))).support)
    (clear : next.application.current.excluded = ∅) :
    ∃ image, Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, image⟩)) ∧ Frame runtime leaks memory owner next image := by
  obtain ⟨image, supported, paired⟩ := frame.expiry_coupling event next moved clear
  have chosen : ((.application (.expire event)) : (phaseApplication runtime leaks).Command) ∈
      (scheduler repaired.environmentRecall
        (repaired.observeEnvironment (phaseApplication runtime leaks))).support := by
    rw [← frame.scheduler_law scheduler]
    exact selected
  exact ⟨image, menu.trace_environment initial horizon scheduler remaining repaired _
    (.application (.expire event)) prior chosen supported, paired⟩

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
