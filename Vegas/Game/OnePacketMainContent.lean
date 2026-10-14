/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketZeroContent
import Vegas.Game.OnePacketSlotContent

/-! # Source-main responses have positive content -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- A main-supported choice at an actual debt-free owner response has positive
source content. Menu normalization to silence also has positive content. -/
theorem contentFactor_pos_of_honestChoice
    (source : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (choice : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
      (some (execution.recall who, execution.observe (application setup leaks) who)))
    (chosen : choice.1 = some response)
    (supported : choice ∈ (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler
      source who (some (execution.recall who,
        execution.observe (application setup leaks) who))).support) :
    0 < contentFactor setup leaks source who execution
      (execution.respond (application setup leaks) who response) response := by
  have nonnegative := contentFactor_nonneg source who execution
    (execution.respond (application setup leaks) who response) response
  by_contra notPositive
  have zero : contentFactor setup leaks source who execution
      (execution.respond (application setup leaks) who response) response = 0 :=
    le_antisymm (le_of_not_gt notPositive) nonnegative
  by_cases silent : response.transmission = none
  · simp [contentFactor, silent] at zero
  · obtain ⟨event, payload, outputEq, codeEq, turn, node⟩ :=
      zeroContent_binding source trace notOwed response member silent zero
    have site := onePacket_coveredPendingBinding source covers capacity trace who event turn node
    have impossible := (tierMasses_of_zeroContent source trace who event site response silent zero
      choice chosen).1
    exact supported impossible

end Vegas
