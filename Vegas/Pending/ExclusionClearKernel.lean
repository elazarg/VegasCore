/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionPrefix

/-! # Native transition probabilities before public exclusion

Exact public failure records identify native outcomes whose recovery closure
has empty exclusion. On these outcomes automatic completion is the identity.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem inclusionResult_eq_of_record (state : RecoveryState graph)
    (valid : PublicExclusionRecord state) (message : Message Player (Payload graph))
    (native : State graph) (accepted : handle runtime state.native message = some native)
    (clear : PublicExclusionRecord (⟨native, ∅⟩ : RecoveryState graph)) :
    (state.inclusionResult message.payload native).drain = ⟨native, ∅⟩ := by
  have rawRecord := valid.inclusionResult runtime message native accepted
  have empty := rawRecord.excluded_eq_of_publicView_eq clear rfl
  rw [RecoveryState.inclusionResult_drain_of_empty state message.payload native empty]

theorem environmentResult_eq_of_record (state : RecoveryState graph)
    (valid : PublicExclusionRecord state) (chosen : EnvironmentCommand graph)
    (native : State graph)
    (realized : native ∈ (environmentStep runtime state.native chosen).support)
    (clear : PublicExclusionRecord (⟨native, ∅⟩ : RecoveryState graph)) :
    (state.environmentResult chosen native).drain = ⟨native, ∅⟩ := by
  have rawRecord := valid.environmentResult runtime chosen native realized
  have empty := rawRecord.excluded_eq_of_publicView_eq clear rfl
  rw [RecoveryState.environmentResult_drain_of_empty state chosen native empty]

/-- Native and recovery application kernels give the same mass to every
publicly clear native outcome. Distinct native draws cannot merge into that
clear outcome during automatic closure. -/
theorem environment_apply_clear (state : RecoveryState graph)
    (valid : PublicExclusionRecord state) (chosen : EnvironmentCommand graph)
    (native : State graph)
    (clear : PublicExclusionRecord (⟨native, ∅⟩ : RecoveryState graph)) :
    (state.environment runtime chosen) ⟨native, ∅⟩ =
      (environmentStep runtime state.native chosen) native := by
  classical
  let closure := fun next => (state.environmentResult chosen next).drain
  have unique : ∀ next ∈ (environmentStep runtime state.native chosen).support,
      (⟨native, ∅⟩ : RecoveryState graph) ∈ (PMF.pure (closure next)).support → next = native := by
    intro next _supported reached
    have same := (PMF.mem_support_pure_iff _ _).mp reached
    have empty : (state.environmentResult chosen next).excluded = ∅ := by
      simpa only [closure, RecoveryState.drain_excluded] using
        congrArg RecoveryState.excluded same.symm
    have reduced : closure next = (⟨next, ∅⟩ : RecoveryState graph) :=
      RecoveryState.environmentResult_drain_of_empty state chosen next empty
    exact congrArg RecoveryState.native (reduced.symm.trans same.symm)
  change ((environmentStep runtime state.native chosen).map closure) _ = _
  rw [← pmf_bind_pure_eq_map, bind_apply_of_unique_branch _ _ _ native unique]
  by_cases supported : native ∈ (environmentStep runtime state.native chosen).support
  · have selected : closure native = (⟨native, ∅⟩ : RecoveryState graph) :=
      environmentResult_eq_of_record runtime state valid chosen native supported clear
    rw [selected, PMF.pure_apply_self, mul_one]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr supported, zero_mul]

end Vegas.EventGraphRuntime.RecoveryProjection
