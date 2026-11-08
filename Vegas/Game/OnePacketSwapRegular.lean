/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSwapReplay
import Vegas.Game.OnePacketForcedRegular

/-! # Swapped histories are regular

**Intended histories stay intended.** Every state reached by a history of the
intended game is a point of the intended game (`Vegas.intended_of_history`),
hence forced for every player.

**Regularity of the image.** Fix intended histories `first` and `second` of equal
length and a native history whose intended replay is `first`. Along the image of
the history under the swap between the two ends, every decoded point is the
state of a prefix of `second`, so it is forced for every player. Every source
factor of the image is positive once its source weight is
(`Vegas.regularTrace_mapTrace_of_weight_pos`). The source weight of the image is
the counterfactual reach of `second` times the unsettled content, so at an own
turn of the observer, under a fully mixed intended assessment, it is positive
and the image is regular (`Vegas.regularTrace_mapTrace`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}

/-- **Every state of an intended history is intended.** -/
theorem intended_of_history (wellFormed : setup.WellFormed) :
    ∀ {state : setup.ProtocolState} (_trace : setup.intendedProtocol.Trace state)
      (point : ProtocolState setup.program), state = some point →
      ProtocolState.Intended setup.program point
  | state, trace, point, same => by
      have intended := setup.intendedState_trace wellFormed trace
      simpa only [same, Setup.IntendedState] using intended

end Vegas

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)} [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  [DecidableEq (CellTy Player L)]

section Image

variable (wellFormed : setup.WellFormed) {first second : setup.intendedProtocol.History}
  {p q : ProtocolState setup.program} (firstState : first.state = some p)
  (secondState : second.state = some q)
  (sameLength : first.trace.length = second.trace.length)
  {publicAgree : PublicCellsAgree setup p q} {succeed : CommitmentCellsSucceed setup p q}
  (handlePairs : Handle (graph setup) → Option (Raw L × Raw L))
  {allowed : Set (graph setup).Inputs}
  (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
    state.swap (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) ∈
      (initialLaw setup).support)
  (bounded : ∀ handle raw, raw ∈ bounds.values →
    (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).raw handle raw ∈
      bounds.values)

include wellFormed firstState secondState sameLength initialClosed bounded in
/-- **Swapped states along a replayed history are forced.** At every initialized
state of a native history whose replay is a prefix of `first`, the swapped state
is forced for every player. -/
theorem forcedState_swap_of_replay (player : Player) {control : (application setup timeouts
  leaks).Control}
    (trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some control))
    (guarded : SwapGuardState setup timeouts (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
      handlePairs) allowed (some control))
    {replay : setup.intendedProtocol.History}
    (replayed : intendedHistory? setup timeouts leaks bounds horizon scheduler trace = some replay)
    (isPrefix : TracePrefix replay.trace first.trace) :
    ForcedState setup timeouts leaks player
      ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).protocolState (timeouts
        := timeouts)
        (some control)) := by
  obtain ⟨image, _, _, _, imageState⟩ := intendedHistory?_mapTrace (timeouts := timeouts)
    wellFormed firstState secondState
    sameLength handlePairs initialClosed bounded trace guarded replayed isPrefix
  have replayState := intendedHistory?_state (timeouts := timeouts) trace replayed
  change replay.state = decodedPoint setup control.execution.application.config at replayState
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (timeouts := timeouts) (failureProfile
    setup.program)
    (bounds.onePacketMenu timeouts leaks) horizon scheduler trace control rfl
  have decoded := decodedPoint_eq residual
  refine (forcedState_iff_decodedPoint (timeouts := timeouts) _).mpr ⟨_, ?_, forcedPoint_of_intended
    player
    (intended_of_history wellFormed image.trace _ (by
      rw [imageState, replayState, decoded]; rfl))⟩
  change decodedPoint setup (control.execution.application.config.swap
    (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed))) = _
  rw [decodedPoint_betweenPairs, decoded]
  rfl

include wellFormed firstState secondState sameLength initialClosed bounded in
/-- **A swapped history of positive source weight is regular**, when its replay
is a prefix of `first`. -/
theorem regularTrace_mapTrace_of_weight_pos
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) :
    ∀ {state} (trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      state)
      (guarded : SwapGuardState setup timeouts
        (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) allowed state)
      {replay : setup.intendedProtocol.History},
      intendedHistory? setup timeouts leaks bounds horizon scheduler trace = some replay →
      TracePrefix replay.trace first.trace →
      0 < othersSourceWeight setup timeouts leaks bounds horizon scheduler assessment who
        ((onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup) horizon scheduler
          (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
          bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).mapTrace trace guarded) →
      RegularTrace setup timeouts leaks bounds horizon scheduler assessment who
        ((onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup) horizon scheduler
          (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
          bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).mapTrace trace guarded)
  | _, .start, _, _, _, _, _ => trivial
  | _, .extend (source := before) (target := after) prior joint legal realized, guarded, replay,
      replayed, firstPrefix, positive => by
      have priorGuard := (onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup)
        horizon scheduler
        (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
        bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).guard_source prior legal realized
          guarded
      change (intendedHistory? setup timeouts leaks bounds horizon scheduler prior).bind
        (fun history => advanceIntended? setup timeouts leaks history before after) = some replay
        at replayed
      obtain ⟨previous, previousReplay, advanced⟩ := Option.bind_eq_some_iff.mp replayed
      have previousPrefix := (tracePrefix_of_advanceIntended? (timeouts := timeouts) advanced).trans
        firstPrefix
      rw [StateSymmetry.mapTrace_extend] at positive ⊢
      change 0 < othersSourceWeight setup timeouts leaks bounds horizon scheduler assessment who _ *
        transitionSourceFactor setup timeouts leaks assessment who _ _ _ at positive
      have priorNonneg := othersSourceWeight_nonneg (timeouts := timeouts) (bounds := bounds)
        (horizon := horizon)
        (scheduler := scheduler) assessment who
        ((onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup) horizon scheduler
          (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
          bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).mapTrace prior priorGuard)
      have factorNonneg := transitionSourceFactor_nonneg (timeouts := timeouts) (setup := setup)
        (leaks := leaks)
        assessment who
        ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).protocolState
          (timeouts := timeouts) before)
        ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).joint (timeouts :=
          timeouts) joint)
        ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).protocolState
          (timeouts := timeouts) after)
      obtain ⟨priorPos, factorPos⟩ :=
        (pos_and_pos_or_neg_and_neg_of_mul_pos positive).resolve_right
          fun negative => absurd negative.1 (not_lt.mpr priorNonneg)
      refine ⟨regularTrace_mapTrace_of_weight_pos assessment who prior
        priorGuard previousReplay
        previousPrefix priorPos, ?_⟩
      cases before with
      | none => trivial
      | some current =>
          cases after with
          | none => trivial
          | some next =>
              intro actor acting other
              have forced := fun player => forcedState_swap_of_replay (timeouts := timeouts)
                wellFormed firstState
                secondState sameLength handlePairs initialClosed bounded player prior priorGuard
                previousReplay previousPrefix
              refine ⟨⟨⟨⟨_, (onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup)
                horizon scheduler
                (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
                bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).mapTrace prior priorGuard⟩,
                  ?_, forced actor⟩, forced who⟩, ?_⟩
              · exact (bounds.onePacketMenu timeouts leaks).info (initialLaw setup)
                  horizon scheduler actor _
              · have actingCurrent : current.actor = some actor := acting
                change 0 < transitionSourceFactor setup timeouts leaks assessment who
                  (some (HiddenSwap.control (timeouts := timeouts) (HiddenSwap.ofPairs (betweenPairs
                    publicAgree succeed)
                    handlePairs) current))
                  ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).joint
                    (timeouts := timeouts) joint)
                  (some (HiddenSwap.control (timeouts := timeouts) (HiddenSwap.ofPairs (betweenPairs
                    publicAgree succeed)
                    handlePairs) next)) at factorPos
                unfold transitionSourceFactor at factorPos
                simp only [HiddenSwap.control, actingCurrent, other, ↓reduceIte] at factorPos
                exact factorPos

include wellFormed firstState secondState sameLength initialClosed bounded in
/-- **A replayed history maps to a history replaying `second`.** -/
theorem intendedHistory?_mapTrace_full {state : (application setup timeouts leaks).ProtocolState}
    (trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state)
    (guarded : SwapGuardState setup timeouts (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
      handlePairs) allowed state)
    (replayed : intendedHistory? setup timeouts leaks bounds horizon scheduler trace = some first) :
    intendedHistory? setup timeouts leaks bounds horizon scheduler
        ((onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup) horizon scheduler
          (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
          bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).mapTrace trace guarded) = some
            second := by
  obtain ⟨image, imageReplay, imagePrefix, imageLength, _⟩ := intendedHistory?_mapTrace (timeouts
    := timeouts)
    wellFormed firstState secondState sameLength handlePairs initialClosed bounded trace guarded
    replayed .refl
  rw [imageReplay]
  exact congrArg some (imagePrefix.eq_of_length (imageLength.trans sameLength))

include wellFormed firstState secondState sameLength initialClosed bounded in
/-- **The source weight of a swapped history at an own turn** is the
counterfactual reach of `second`. -/
theorem othersSourceWeight_mapTrace (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) {control : (application setup timeouts leaks).Control}
    (trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some control))
    (guarded : SwapGuardState setup timeouts (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
      handlePairs) allowed (some control))
    (replayed : intendedHistory? setup timeouts leaks bounds horizon scheduler trace = some first)
    {event : (graph setup).EventId}
    (turn : (control.execution.observe (application setup timeouts leaks)
      who).application.publicView.ownTurn? who = some event) :
    othersSourceWeight setup timeouts leaks bounds horizon scheduler assessment who
        ((onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup) horizon scheduler
          (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
          bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).mapTrace trace guarded) =
      setup.intendedModel.counterfactualReachProbability assessment.strategy who
        second.trace := by
  have imageReplay := intendedHistory?_mapTrace_full (timeouts := timeouts) wellFormed firstState
    secondState sameLength
    handlePairs initialClosed bounded trace guarded replayed
  have forced := forcedState_swap_of_replay (timeouts := timeouts) wellFormed firstState secondState
    sameLength
    handlePairs initialClosed bounded who trace guarded replayed .refl
  have matching := actorCompletionsMatch_of_forced (timeouts := timeouts) assessment who
    ((onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup) horizon scheduler
      (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
      bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).mapTrace trace guarded) _ rfl forced
  have imageTurn : ((HiddenSwap.control (timeouts := timeouts) (HiddenSwap.ofPairs (betweenPairs
    publicAgree succeed)
      handlePairs) control).execution.observe (application setup timeouts leaks)
      who).application.publicView.ownTurn? who = some event := by
    change (((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).execution
      control.execution).observe (application setup timeouts leaks)
        who).application.publicView.ownTurn?
        who = some event
    rw [HiddenSwap.observe_execution]
    exact turn
  have settled := unsettledContent_eq_one_of_ownTurn (timeouts := timeouts) assessment who
    ((onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup) horizon scheduler
      (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
      bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).mapTrace trace guarded) forced imageTurn
  rw [othersSourceWeight_eq_replay (timeouts := timeouts) assessment who _ imageReplay
    (replayMatches_of_actorCompletions (timeouts := timeouts) assessment who _ matching), settled,
      mul_one]

omit [Fintype Player] [DecidableEq (CellTy Player L)] in
/-- Under a fully mixed assessment every intended history has positive
counterfactual reach. -/
theorem counterfactualReach_pos_of_mixed [Finite Player]
    {assessment : setup.intendedModel.BehavioralAssessment}
    (mixed : assessment.IsFullyMixed) (who : Player) (history : setup.intendedProtocol.History) :
    0 < setup.intendedModel.counterfactualReachProbability assessment.strategy who
      history.trace := by
  have reach := setup.intendedModel.historyReachWeight_pos_of_fullSupport assessment.strategy
    (fun player site choice => mixed player site choice) history
  have positive : 0 < (setup.intendedModel.historyReachWeight assessment.strategy
      ⟨history.state, history.trace⟩).toReal :=
    ENNReal.toReal_pos reach.ne' (PMF.apply_ne_top _ _)
  rw [InformationModel.historyReachProbability_eq_player_mul_counterfactual] at positive
  exact ((pos_and_pos_or_neg_and_neg_of_mul_pos positive).resolve_right fun negative =>
    absurd negative.1 (not_lt.mpr (InformationModel.playerReachProbability_nonneg _ _ _ _))).2

include wellFormed firstState secondState sameLength initialClosed bounded in
/-- **A swapped history at an own turn is regular** under a fully mixed
assessment. -/
theorem regularTrace_mapTrace {assessment : setup.intendedModel.BehavioralAssessment}
    (mixed : assessment.IsFullyMixed) (who : Player) {control : (application setup timeouts
      leaks).Control}
    (trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some control))
    (guarded : SwapGuardState setup timeouts (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
      handlePairs) allowed (some control))
    (replayed : intendedHistory? setup timeouts leaks bounds horizon scheduler trace = some first)
    {event : (graph setup).EventId}
    (turn : (control.execution.observe (application setup timeouts leaks)
      who).application.publicView.ownTurn? who = some event) :
    RegularTrace setup timeouts leaks bounds horizon scheduler assessment who
      ((onePacketSwapSymmetry (timeouts := timeouts) bounds (initialLaw setup) horizon scheduler
        (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
        bounded (EventGraph.ValueSwap.ofPairs_expiryFixed _)).mapTrace trace guarded) := by
  refine regularTrace_mapTrace_of_weight_pos (timeouts := timeouts) wellFormed firstState
    secondState sameLength
    handlePairs initialClosed bounded assessment who trace guarded replayed .refl ?_
  rw [othersSourceWeight_mapTrace (timeouts := timeouts) wellFormed firstState secondState
    sameLength handlePairs
    initialClosed bounded assessment who trace guarded replayed turn]
  exact counterfactualReach_pos_of_mixed mixed who second

end Image

end Vegas
