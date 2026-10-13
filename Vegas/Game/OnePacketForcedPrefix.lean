/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketIntendedProjection
import Vegas.Game.OnePacketPrescribedSupport

/-! # Forced states along native histories

Exclusion persists under every source step: a failed commitment stays in the
store, and a failed reveal stays published
(`Vegas.SourceProgram.ProtocolState.excluded_step`). Failed reveals and owed
failures persist as well, so a source point reached by a step from a point that
is not forced for `who` is not forced either
(`Vegas.forcedPoint_of_step`). Hence every state along a native history of the
one-packet game that ends in a forced state of `who` is forced for `who`
(`Vegas.forcedState_of_transition`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A failed commitment stays failed when a cell is bound on top of it. -/
theorem failedCommitment_cons {Γ : SourceCtx Player L} {who : Player} {name : VarId}
    {kind : CellTy Player L} (value : CellVal L kind) (state : State L Γ)
    (failed : FailedCommitment who state) :
    FailedCommitment who (Env.cons (x := name) value state) := by
  obtain ⟨cell, payload, found, stored⟩ := failed
  exact ⟨cell, payload, .there found, stored⟩

/-- A failed commitment of the entry configuration excludes its player at the
entry point. -/
theorem excluded_entry (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ)
    (failed : FailedCommitment who config.state) : Excluded who program (entry program config) := by
  cases program <;> exact failed

/-- **Exclusion persists** under every source step, whatever anyone plays. -/
theorem excluded_step (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → (target : ProtocolState program) →
    Excluded who program state → target ∈ (step program state joint).support →
      Excluded who program target
  | _, _, .ret _, _, _, target, excluded, reached => by
      rw [step, PMF.mem_support_pure_iff] at reached
      rw [reached]
      exact excluded
  | _, _, .sample _ _ _ next, state, joint, target, excluded, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          exact excluded_entry who next _ (failedCommitment_cons _ _ excluded)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact excluded_step who next rest joint after excluded supported
  | _, _, .commit _ _ _ _ next, state, joint, target, excluded, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          exact excluded_entry who next _ (failedCommitment_cons _ _ excluded)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact excluded_step who next rest joint after excluded supported
  | _, _, .reveal _ _ _ _ _ _ next, state, joint, target, excluded, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          exact Or.inr (excluded_entry who next _ (failedCommitment_cons _ _ excluded))
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases excluded with ⟨own, publication⟩ | later
          · exact Or.inl ⟨own, (base_step next rest joint after supported).symm ▸ publication⟩
          · exact Or.inr (excluded_step who next rest joint after later supported)

end Vegas.SourceProgram.ProtocolState

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- **Forcedness reaches back over a source step.** A source point from which a
step reaches a point forced for `who` is forced for `who`. -/
theorem forcedPoint_of_step {who : Player} {point target : ProtocolState setup.program}
    {joint : Player → Option (OwnAction Player L)}
    (reached : target ∈ (ProtocolState.step setup.program point joint).support)
    (forced : ForcedPoint setup who target) : ForcedPoint setup who point := by
  refine ⟨fun failed => forced.1 (ProtocolState.revealFailed_step who setup.program point joint
    target failed reached), fun other different => ⟨fun excluded => (forced.2 other different).1
      (ProtocolState.excluded_step other setup.program point joint target excluded reached),
    fun owed => (forced.2 other different).2
      (ProtocolState.owesFailure_step other setup.program point joint target owed reached)⟩⟩

/-- A forced state of `who` is an initialized state whose decoded point is
forced for `who`. -/
theorem forcedState_iff_decodedPoint
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {who : Player} (control : (application setup leaks).Control) :
    ForcedState setup leaks who (some control) ↔
      ∃ point, decodedPoint setup control.execution.application.config = some point ∧
        ForcedPoint setup who point := by
  constructor
  · rintro ⟨rank, point, ordered, decoded, forced⟩
    have exists_ : ∃ rank, control.execution.application.config.cut.IsPrefix rank :=
      ⟨rank, ordered⟩
    refine ⟨point, ?_, forced⟩
    unfold decodedPoint
    rw [dite_eq_left_of_eq_true (eq_true exists_), show exists_.choose = rank from
      isPrefix_unique exists_.choose_spec ordered]
    exact decoded
  · rintro ⟨point, decoded, forced⟩
    unfold decodedPoint at decoded
    split at decoded
    · rename_i ordered
      exact ⟨_, point, ordered.choose_spec, decoded, forced⟩
    · cases decoded

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **Forced states reach back along native transitions.** If a native
transition of the one-packet game from an initialized state reaches a forced
state of `who`, that initialized state is forced for `who`. -/
theorem forcedState_of_transition {who : Player} {before : (application setup leaks).Control}
    {after : (application setup leaks).ProtocolState}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some before))
    (joint : Player → Option (application setup leaks).Action)
    (realized : after ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
      (some before) joint).support)
    (forced : ForcedState setup leaks who after) :
    ForcedState setup leaks who (some before) := by
  cases after with
  | none => exact forced.elim
  | some next =>
      obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
        (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler prior before rfl
      obtain ⟨target, decoded, forcedTarget⟩ := (forcedState_iff_decodedPoint next).mp forced
      refine (forcedState_iff_decodedPoint before).mpr ?_
      rcases transition_configStep (initialLaw setup) horizon scheduler before next joint
          realized with same | ⟨event, ready, action, member⟩
      · rw [same] at decoded
        exact ⟨target, decoded, forcedTarget⟩
      · obtain ⟨point, reachedPoint, beforeEq, afterEq, supported⟩ :=
          decodedPoint_step residual event ready action _ member
        rw [afterEq, Option.some.injEq] at decoded
        subst decoded
        exact ⟨point, beforeEq, forcedPoint_of_step supported forcedTarget⟩

end Vegas
