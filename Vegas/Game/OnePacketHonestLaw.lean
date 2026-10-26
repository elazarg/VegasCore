/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketExclusionPayoff

/-! # Decoded properties along rounds

An execution satisfies a property of its decoding when its configuration has a
source residual at a prefix where the property holds of its decoding
(`Vegas.DecodedExecution`). Under any players and any scheduler, a step-closed
property of the decoding is kept by every round
(`Vegas.DecodedExecution.round`) and hence by every run of rounds
(`Vegas.DecodedExecution.runRounds`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Debts

variable (setup runtime leaks) in
/-- An execution whose configuration has a source residual at a prefix where a
property holds of its decoding. -/
def DecodedExecution (profile : BehavioralProfile setup.program)
    (property : ProtocolState setup.program → Prop)
    (execution : (application setup runtime leaks).Execution) : Prop :=
  ∃ rank, Nonempty (SourceResidual setup profile rank execution.application.config) ∧
    DecodedHolds property rank execution.application.config

variable {profile : BehavioralProfile setup.program}

/-- A round keeps a step-closed property of the decoding. -/
theorem DecodedExecution.round {property : ProtocolState setup.program → Prop}
    (closed : StepClosed setup property) {scheduler : (application setup runtime leaks).Scheduler}
    {players : Player → (application setup runtime leaks).Policy}
    {execution next : (application setup runtime leaks).Execution}
    (holds : DecodedExecution setup runtime leaks profile property execution)
    (moved : next ∈ ((application setup runtime leaks).round scheduler players execution).support) :
    DecodedExecution setup runtime leaks profile property next := by
  obtain ⟨rank, ⟨residual⟩, decoded⟩ := holds
  have step := round_configStep setup leaks scheduler players execution next moved
  rcases step.prefix rank residual.checkpoint.ordered with same | advanced
  · refine ⟨rank, residual.configStep step rank ?_, ?_⟩
    · rw [same]
      exact residual.checkpoint.ordered
    · exact residual.decodedHolds_configStep closed decoded step (by
        rw [same]
        exact residual.checkpoint.ordered)
  · exact ⟨rank + 1, residual.configStep step (rank + 1) advanced,
      residual.decodedHolds_configStep closed decoded step advanced⟩

/-- Rounds keep a step-closed property of the decoding. -/
theorem DecodedExecution.runRounds {property : ProtocolState setup.program → Prop}
    (closed : StepClosed setup property) (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy) :
    ∀ (more : Nat) (execution : (application setup runtime leaks).Execution),
      DecodedExecution setup runtime leaks profile property execution →
      ∀ final ∈ ((application setup runtime leaks).runRounds scheduler players more
        execution).support,
        DecodedExecution setup runtime leaks profile property final := by
  intro more
  induction more with
  | zero =>
      intro execution holds final reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact holds
  | succ more ih =>
      intro execution holds final reached
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact ih middle (holds.round closed moved) final rest

end Debts

end Vegas
