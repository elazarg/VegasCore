/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSwapReplay
import Vegas.Game.OnePacketForcedInputs
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

/-- **Every state of an intended history is intended.** -/
theorem intended_of_history (wellFormed : setup.WellFormed) :
    ∀ {state : setup.ProtocolState} (_trace : setup.intendedProtocol.Trace state)
      (point : ProtocolState setup.program), state = some point →
      ProtocolState.Intended setup.program point
  | _, .start, _, initialized => by cases initialized
  | _, .extend (source := before) prior joint legal realized, point, reached => by
      have recursive := fun current same => intended_of_history wellFormed prior current same
      subst reached
      cases before with
      | none =>
          change some point ∈ (setup.initialLaw.map fun initial => some
            (ProtocolState.entry setup.program (setup.initialConfig initial))).support
            at realized
          obtain ⟨initial, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
          cases Option.some.inj same
          exact ProtocolState.intended_entry setup.program _
            (setup.initialConfig_intended wellFormed supported)
            (wellFormed.guardsSatisfiable initial supported)
      | some current =>
          change some point ∈ ((ProtocolState.step setup.program current joint).map some).support
            at realized
          obtain ⟨target, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
          cases Option.some.inj same
          refine ProtocolState.intended_step setup.program current joint point
            (recursive current rfl) (fun who => ?_) reached
          have member := legal.2 who
          revert member
          cases joint who <;> exact id

end Vegas

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
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
theorem forcedState_swap_of_replay (player : Player) {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (guarded : SwapGuardState setup (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
      handlePairs) allowed (some control))
    {replay : setup.intendedProtocol.History}
    (replayed : intendedHistory? setup leaks bounds horizon scheduler trace = some replay)
    (isPrefix : TracePrefix replay.trace first.trace) :
    ForcedState setup leaks player
      ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).protocolState
        (some control)) := by
  obtain ⟨image, _, _, _, imageState⟩ := intendedHistory?_mapTrace firstState secondState
    sameLength handlePairs initialClosed bounded trace guarded replayed isPrefix
  have replayState := intendedHistory?_state trace replayed
  change replay.state = decodedPoint setup control.execution.application.config at replayState
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace control rfl
  have decoded := decodedPoint_eq residual
  refine (forcedState_iff_decodedPoint _).mpr ⟨_, ?_, forcedPoint_of_intended player
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
    ∀ {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
      (guarded : SwapGuardState setup
        (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) allowed state)
      {replay : setup.intendedProtocol.History},
      intendedHistory? setup leaks bounds horizon scheduler trace = some replay →
      TracePrefix replay.trace first.trace →
      0 < othersSourceWeight setup leaks bounds horizon scheduler assessment who
        ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler
          (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
          bounded).mapTrace trace guarded) →
      RegularTrace setup leaks bounds horizon scheduler assessment who
        ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler
          (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
          bounded).mapTrace trace guarded)
  | _, .start, _, _, _, _, _ => trivial
  | _, .extend (source := before) (target := after) prior joint legal realized, guarded, replay,
      replayed, firstPrefix, positive => by
      have priorGuard := (onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler
        (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
        bounded).guard_source legal realized guarded
      change (intendedHistory? setup leaks bounds horizon scheduler prior).bind
        (fun history => advanceIntended? setup leaks history before after) = some replay
        at replayed
      obtain ⟨previous, previousReplay, advanced⟩ := Option.bind_eq_some_iff.mp replayed
      have previousPrefix := (tracePrefix_of_advanceIntended? advanced).trans firstPrefix
      rw [StateSymmetry.mapTrace_extend] at positive ⊢
      change 0 < othersSourceWeight setup leaks bounds horizon scheduler assessment who _ *
        transitionSourceFactor setup leaks assessment who _ _ _ at positive
      have priorNonneg := othersSourceWeight_nonneg (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler) assessment who
        ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler
          (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
          bounded).mapTrace prior priorGuard)
      have factorNonneg := transitionSourceFactor_nonneg (setup := setup) (leaks := leaks)
        assessment who
        ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).protocolState before)
        ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).joint joint)
        ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).protocolState after)
      obtain ⟨priorPos, factorPos⟩ :=
        (pos_and_pos_or_neg_and_neg_of_mul_pos positive).resolve_right
          fun negative => absurd negative.1 (not_lt.mpr priorNonneg)
      refine ⟨regularTrace_mapTrace_of_weight_pos assessment who prior priorGuard previousReplay
        previousPrefix priorPos, ?_⟩
      cases before with
      | none => trivial
      | some current =>
          cases after with
          | none => trivial
          | some next =>
              intro actor acting other
              have forced := fun player => forcedState_swap_of_replay wellFormed firstState
                secondState sameLength handlePairs initialClosed bounded player prior priorGuard
                previousReplay previousPrefix
              refine ⟨⟨⟨⟨_, (onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler
                (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) initialClosed
                bounded).mapTrace prior priorGuard⟩, ?_, forced actor⟩, forced who⟩, ?_⟩
              · exact (bounds.onePacketMenu (runtime setup) leaks).info (initialLaw setup)
                  horizon scheduler actor _
              · have actingCurrent : current.actor = some actor := acting
                change 0 < transitionSourceFactor setup leaks assessment who
                  (some (HiddenSwap.control (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
                    handlePairs) current))
                  ((HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).joint joint)
                  (some (HiddenSwap.control (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
                    handlePairs) next)) at factorPos
                unfold transitionSourceFactor at factorPos
                simp only [HiddenSwap.control, actingCurrent, other, ↓reduceIte] at factorPos
                exact factorPos

end Image

end Vegas
