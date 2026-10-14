/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionPairedTransition

/-! # Exact failed-owner labels at paired exclusion boundaries -/

noncomputable section

namespace Vegas.EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- All owners with a publicly missed binding or failed publication. -/
def State.failureOwners (state : State graph) : Finset Player := by
  classical
  exact Finset.univ.filter fun owner =>
    ∃ event, graph.actor? event = some owner ∧ state.PublicFailure event

/-- The public failure record determines the permanent excluded-owner set. -/
theorem PublicExclusionRecord.failureOwners_eq {state : RecoveryState graph}
    (valid : PublicExclusionRecord state) : state.native.failureOwners = state.excluded := by
  classical
  ext owner
  simp only [State.failureOwners, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (valid.excluded owner).symm

namespace RecoveryProjection

variable (runtime : EventGraphRuntime graph)
  (leaks : Interaction.MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The failed owners in the actual native endpoint, prior to recovery drain. -/
def nativeFailureOwners : (runtime.reactiveApplication leaks).ProtocolState → Finset Player
  | none => ∅
  | some control => control.execution.application.failureOwners

/-- The actual permanent excluded set at the recovery endpoint. -/
def recoveryFailureOwners : (runtime.recoveryApplication leaks).ProtocolState → Finset Player
  | none => ∅
  | some control => control.execution.application.excluded

/-- The natural coupled step preserves the complete first failed-owner label,
including outcomes where recovery drains additional automatic failures. -/
theorem PairedExclusionRecord.failureOwners_eq
    {first : (runtime.reactiveApplication leaks).ProtocolState}
    {second : (runtime.recoveryApplication leaks).ProtocolState}
    (record : PairedExclusionRecord runtime leaks first second) :
    nativeFailureOwners runtime leaks first = recoveryFailureOwners runtime leaks second := by
  cases first <;> cases second
  · rfl
  · exact record.elim
  · exact record.elim
  · exact PublicExclusionRecord.failureOwners_eq record

end RecoveryProjection
end Vegas.EventGraphRuntime
