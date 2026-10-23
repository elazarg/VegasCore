/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameStep
import Vegas.Pending.PhaseSeedBudget
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.EventValueSwap

/-! # Reconstructing saved and live states during a private binding repair -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace BindingShadow

/-- Reconstruct the original semantic state only on fields and actions already
present. A remembered future binding never appears in an earlier checkpoint. -/
def config (memory : BindingShadow graph) (state : graph.Config) : graph.Config where
  inputs := state.inputs
  cut := state.cut
  outputs := fun event => (state.outputs event).map fun value =>
    (memory.values (.inr event)).getD value
  output_available event := by simpa only [Option.isSome_map] using state.output_available event
  history := state.history.map memory.completion
  history_nodup := by simpa only [List.map_map, completion, Function.comp_def] using
    state.history_nodup
  history_exact event := by
    simpa only [List.map_map, completion, Function.comp_def] using (state.history_exact event)

@[simp] theorem config_cut (memory : BindingShadow graph) (state : graph.Config) :
    (memory.config state).cut = state.cut := rfl

@[simp] theorem config_history (memory : BindingShadow graph) (state : graph.Config) :
    (memory.config state).history = state.history.map memory.completion := rfl

theorem config_store {memory : BindingShadow graph} {owner : Player}
    (owned : memory.OwnBindings owner) (state : graph.Config) :
    (memory.config state).store = memory.store state.store := by
  funext field
  cases field with
  | inl input =>
      simp only [Config.store_input, store, owned.input_value_none input,
        Option.getD_none, Option.map_some]
      rfl
  | inr event => rfl

@[simp] theorem config_empty (state : graph.Config) :
    (empty : BindingShadow graph).config state = state := by
  apply Config.ext_fields (left := (empty : BindingShadow graph).config state)
    (right := state) rfl rfl
  · funext event
    simp only [config, empty, Option.getD_none]
    exact congrFun Option.map_id _
  · exact List.map_id'' completion_empty _

/-- Fresh slots in old saved catalogues stay fresh. A preparation remembered
later belongs to the physical live catalogue, which restoration keeps. -/
def candidate (memory : BindingShadow graph) (slot : CandidateSlot graph) :
    CommitmentCandidate (Raw L) → CommitmentCandidate (Raw L)
  | .fresh => .fresh
  | actual => (memory.candidates slot).getD actual

@[simp] theorem candidate_empty (slot : CandidateSlot graph)
    (value : CommitmentCandidate (Raw L)) :
    (empty : BindingShadow graph).candidate slot value = value := by
  cases value <;> rfl

variable [DecidableEq Player]

/-- Reconstruct private candidate meanings for their owner, without materializing
later preparations in the saved checkpoint's older catalogue. -/
def native (memory : BindingShadow graph) (owner : Player) (state : State graph) : State graph :=
  { state with
    config := memory.config state.config
    candidates := ⟨fun who slot => if who = owner then
      memory.candidate slot (state.candidates.table who slot)
      else state.candidates.table who slot⟩ }

@[simp] theorem native_empty (owner : Player) (state : State graph) :
    (empty : BindingShadow graph).native owner state = state := by
  have candidates : (⟨fun who slot => if who = owner then
      (empty : BindingShadow graph).candidate slot (state.candidates.table who slot)
      else state.candidates.table who slot⟩ :
      CommitmentCandidates Player (CandidateSlot graph) (Raw L)) = state.candidates := by
    cases state.candidates with
    | mk table => simp only [candidate_empty, ite_self]
  simp only [native, config_empty, candidates]

def recovery (memory : BindingShadow graph) (owner : Player) (state : RecoveryState graph) :
    RecoveryState graph := ⟨memory.native owner state.native, state.excluded⟩

@[simp] theorem recovery_empty (owner : Player) (state : RecoveryState graph) :
    (empty : BindingShadow graph).recovery owner state = state := by
  cases state
  simp only [recovery, native_empty]

/-- The catalogue comes from the current physical state even when semantic
restoration reads an older private binding from the entry checkpoint. -/
theorem restore_phased (memory : BindingShadow graph) (owner : Player)
    (entry current : RecoveryState graph) :
    PhaseRuntimeState.restore (memory.recovery owner entry) (memory.recovery owner current) =
      memory.recovery owner (PhaseRuntimeState.restore entry current) := rfl

/-- The same phase boundary is finished before and after reconstruction. -/
theorem phased_finished (memory : BindingShadow graph) (owner : Player)
    (phase : RuntimePhase graph) (state : RecoveryState graph) :
    phase.Finished (memory.recovery owner state) ↔ phase.Finished state := Iff.rfl

end BindingShadow

end Vegas.EventGraphRuntime
