/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSwapRegular
import Vegas.Game.OnePacketProjectedDecision

/-! # Debt-free histories are regular

Along a native history of the one-packet game whose decoded point leaves
nobody owing a failure, every decoded point is a state of an intended history
(`Vegas.intendedHistory?_isSome_of_debtFree`), hence forced for every player
(`Vegas.forcedState_of_debtFree`). At an own turn of the observer the source
weight of such a history is the counterfactual reach of its intended replay,
positive under a fully mixed assessment, so every response of another player
along it is regular (`Vegas.regularTrace_of_debtFree`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **Debt-free states are forced** for every player. -/
theorem forcedState_of_debtFree (wellFormed : setup.WellFormed)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (free : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point)
    (player : Player) : ForcedState setup leaks player (some control) := by
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome_of_debtFree wellFormed trace control rfl
    free
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace control rfl
  have decoded := decodedPoint_eq residual
  have replayState : replay.state = decodedPoint setup control.execution.application.config :=
    intendedHistory?_state trace replayed
  rw [decoded] at replayState
  exact (forcedState_iff_decodedPoint control).mpr ⟨_, decoded,
    forcedPoint_of_intended player (intended_of_history wellFormed replay.trace _ replayState)⟩

private theorem regularTrace_of_debtFree_weight (wellFormed : setup.WellFormed)
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) : ∀ {state}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    (control : (application setup leaks).Control), state = some control →
    (∀ point, decodedPoint setup control.execution.application.config = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point) →
    0 < othersSourceWeight setup leaks bounds horizon scheduler assessment who trace →
      RegularTrace setup leaks bounds horizon scheduler assessment who trace
  | _, .start, _, _, _, _ => trivial
  | _, .extend (source := before) (target := after) prior joint legal realized, control, current,
      free, positive => by
      have recursive := fun next same freeNext positiveNext =>
        regularTrace_of_debtFree_weight wellFormed assessment who prior next same freeNext
          positiveNext
      subst current
      change 0 < othersSourceWeight setup leaks bounds horizon scheduler assessment who prior *
        transitionSourceFactor setup leaks assessment who before joint (some control) at positive
      obtain ⟨priorPos, factorPos⟩ :=
        (pos_and_pos_or_neg_and_neg_of_mul_pos positive).resolve_right fun negative =>
          absurd negative.1 (not_lt.mpr (othersSourceWeight_nonneg assessment who prior))
      have realizedRaw : some control ∈ ((application setup leaks).transition (initialLaw setup)
          horizon scheduler before joint).support := realized
      cases before with
      | none =>
          obtain rfl := trace_eq_start_of_none prior
          exact ⟨trivial, trivial⟩
      | some current =>
          have freeCurrent := debtFree_of_transition prior joint realizedRaw free
          refine ⟨recursive current rfl freeCurrent priorPos, ?_⟩
          intro actor acting other
          have forced := fun player =>
            forcedState_of_debtFree wellFormed prior freeCurrent player
          refine ⟨⟨⟨⟨_, prior⟩, ?_, forced actor⟩, forced who⟩, ?_⟩
          · exact (bounds.onePacketMenu (runtime setup) leaks).info (initialLaw setup)
              horizon scheduler actor _
          · unfold transitionSourceFactor at factorPos
            simp only [acting, other, ↓reduceIte] at factorPos
            exact factorPos

/-- **Debt-free histories at an own turn are regular.** For a well-formed setup,
under a fully mixed assessment, a native history whose decoded point leaves
nobody owing a failure, at which `who` has its own ready event, is regular for
`who`. -/
theorem regularTrace_of_debtFree (wellFormed : setup.WellFormed)
    {assessment : setup.intendedModel.BehavioralAssessment} (mixed : assessment.IsFullyMixed)
    (who : Player) {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (free : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point)
    {event : (graph setup).EventId}
    (turn : (control.execution.observe (application setup leaks)
      who).application.publicView.ownTurn? who = some event) :
    RegularTrace setup leaks bounds horizon scheduler assessment who trace := by
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome_of_debtFree wellFormed trace control rfl
    free
  have forced := forcedState_of_debtFree wellFormed trace free who
  have matching := actorCompletionsMatch_of_forced assessment who trace control rfl forced
  have settled := unsettledContent_eq_one_of_ownTurn assessment who trace forced turn
  refine regularTrace_of_debtFree_weight wellFormed assessment who trace control rfl free ?_
  rw [othersSourceWeight_eq_replay assessment who trace replayed
    (replayMatches_of_actorCompletions assessment who trace matching), settled, mul_one]
  exact counterfactualReach_pos_of_mixed mixed who replay

end Vegas
