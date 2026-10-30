/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceFailureRecord
import Vegas.Pending.ReactiveEventStability

/-! # A failed binding output is an owed failure

**The failed-binding record.** At every legal history of the supplied runtime,
under arbitrary responses and every scheduler, the configuration decodes at a
prefix, and every completed binding event whose output is a failure makes its
owner owe a failure at the decoded point (`Vegas.FailedBindingRecord`,
`Vegas.failedBindingRecord_history`). The record reads the stored binding
result, and owing a failure is closed under later source steps.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}


section Record

variable (profile : BehavioralProfile setup.program)

/-- **The failed-binding record.** The configuration decodes at a prefix, and
every completed binding event whose output is a failure makes its owner owe a
failure at the decoded point. -/
def FailedBindingRecord (execution : (application setup runtime leaks).Execution) : Prop :=
  ∃ rank, Nonempty (SourceResidual setup profile rank execution.application.config) ∧
    ∀ event ∈ execution.application.config.cut.completed, ∀ owner payload
      (outputEq : (graph setup).outputLayout event = .binding owner payload),
      (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
        (.binding owner payload)).get? execution.application.config.store = some .failure →
        DecodedHolds (ProtocolState.OwesFailure owner setup.program) rank
          execution.application.config

/-- The failed-binding record holds at every legal initialized history, under
arbitrary responses and every scheduler. -/
theorem failedBindingRecord_history (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    {control : (application setup runtime leaks).Control}
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    FailedBindingRecord (runtime := runtime) profile control.execution := by
  obtain ⟨rank, residual, record⟩ := SourceFailureRecord.history (runtime := runtime) profile
    horizon scheduler trace
  refine ⟨rank, residual, fun event completed owner payload outputEq failed => ?_⟩
  exact record event completed owner ((graph setup).actor?_of_outputLayout_binding outputEq)
    (storeEventFailed_of_ref _ event ⟨.inr event, outputEq⟩ rfl failed rfl)

end Record

end Vegas
