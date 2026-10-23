/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingAdmittedInclude
import Vegas.Pending.ReactiveBindingFrameForeign
import Vegas.Pending.ReactiveCountedSurvivor
import Vegas.Pending.PhasePacketAddress
import Vegas.Pending.ReactiveBindingSubmittedResponse

/-! # Submitted private records survive actual physical phase operations -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The physical catalogue retains the exact meaning of every fixed handle,
including unopenable candidates, across all actual phase transitions. -/
theorem phaseApplication_preservesFixedCandidates (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after =>
      KeepsFixedCandidates before.current.native after.current.native) where
  refl _ _ _ := rfl
  submit state who material candidate fixed := by
    change (submitStep (material.call.register state.current.native who) who
      material.call.packet).candidates.lookup candidate = _
    have registered := material.call.register_lookup_of_not_fresh state.current.native who
      candidate fixed
    rw [submitStep_lookup_of_not_fresh _ _ _ candidate (by rwa [registered]), registered]
  handle state message next accepted candidate fixed := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      change (PhaseRuntimeState.settle state.phases state.generation state.entry
        (state.current.inclusionResult message.payload.packet.call native)
        state.retired).current.native.candidates.lookup candidate = _
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1]
      exact handle_lookup_of_not_fresh runtime state.current.native native
        ⟨message.id, message.payload.packet.call⟩ candidate fixed handled
    · cases accepted
  environment state command next reached candidate fixed := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ reached
      change (PhaseRuntimeState.settle state.phases state.generation state.entry
        (state.current.environmentResult command native)
        state.retired).current.native.candidates.lookup candidate = _
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1]
      exact congrFun (congrArg CommitmentCandidates.lookup
        (environmentStep_tables runtime state.current.native native command supported).2) candidate
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl

namespace BindingMemory.RecordsSubmittedBindings

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory nextMemory : BindingMemory runtime leaks} {owner : Player}
  {original repaired nextOriginal nextRepaired : (runtime.reactiveApplication leaks).Execution}

/-- Recorded values depend on the original inputs and fixed candidate meanings,
not on the semantic store, checkpoint boundary, or representation of recall. -/
theorem rebase
    (recorded : memory.RecordsSubmittedBindings runtime leaks owner original repaired)
    (inputs : nextOriginal.network.inputs = original.network.inputs)
    (left : KeepsFixedCandidates original.application nextOriginal.application)
    (right : KeepsFixedCandidates repaired.application nextRepaired.application)
    (shadow : nextMemory.shadow = memory.shadow) :
    nextMemory.RecordsSubmittedBindings runtime leaks owner nextOriginal nextRepaired := by
  intro message member sender event candidate call payload outputEq codeEq node
  rw [inputs] at member
  obtain ⟨remembered, firstFixed, secondFixed, succeeds, successes⟩ :=
    recorded message member sender event candidate call payload outputEq codeEq node
  have leftLookup := left candidate firstFixed
  have rightLookup := right candidate secondFixed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [State.bindingResult, leftLookup, shadow] using remembered
  · rwa [leftLookup]
  · rwa [rightLookup]
  · simpa only [State.bindingResult, rightLookup] using succeeds
  · simpa only [State.bindingResult, leftLookup, rightLookup] using successes

end BindingMemory.RecordsSubmittedBindings
end Vegas.EventGraphRuntime
