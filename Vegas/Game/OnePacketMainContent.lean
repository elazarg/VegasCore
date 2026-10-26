/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketZeroContent

/-! # Source-main responses have positive content -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- A main-supported choice at an actual debt-free owner response has positive
source content. Menu normalization to silence also has positive content. -/
theorem contentFactor_pos_of_honestChoice
    (source : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    {remaining : Nat} {who : Player} {execution : (application setup runtime leaks).Execution}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (response : (application setup runtime leaks).Action)
    (member : response ∈ bounds.onePacketActions runtime leaks who
      (execution.recall who) (execution.observe (application setup runtime leaks) who))
    (choice : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).Choice who
      (some (execution.recall who, execution.observe (application setup runtime leaks) who)))
    (chosen : choice.1 = some response)
    (supported : choice ∈ (honestChoice setup runtime leaks bounds (initialLaw setup) horizon
      scheduler
      source who (some (execution.recall who,
        execution.observe (application setup runtime leaks) who))).support) :
    0 < contentFactor setup runtime leaks source who execution
      (execution.respond (application setup runtime leaks) who response) response := by
  have nonnegative := contentFactor_nonneg (runtime := runtime) source who execution
    (execution.respond (application setup runtime leaks) who response) response
  by_contra notPositive
  have zero : contentFactor setup runtime leaks source who execution
      (execution.respond (application setup runtime leaks) who response) response = 0 :=
    le_antisymm (le_of_not_gt notPositive) nonnegative
  by_cases silent : response.transmission = none
  · simp [contentFactor, silent] at zero
  · obtain ⟨event, payload, outputEq, codeEq, turn, node⟩ :=
      zeroContent_binding (runtime := runtime) source trace notOwed response member silent zero
    have site := onePacket_coveredPendingBinding (runtime := runtime) source covers capacity trace
      who event turn node
    have impossible := (tierMasses_of_zeroContent (runtime := runtime) source trace who event site
      response silent zero
      choice chosen).1
    exact supported impossible

end Vegas
