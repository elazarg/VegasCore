/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketResponseBound
import Vegas.Game.OnePacketStepPositive
import Vegas.Game.OnePacketInitialFloor
import Vegas.Game.OnePacketCounterpartDomination
import Vegas.Game.OnePacketCounterpartRatio

/-! # The certificate's honest counterparts

Under the certificate's profiles, at a decision input of `who` at its own turn
with a debt-free witness, every irregular history has a regular counterpart of
the input with the same operational record whose reach dominates the history's
reach up to the factorization factor times the counterpart ratio
(`Vegas.reach_le_counterpart_certificate`): the response and first-step bounds
hold (`Vegas.swapResponseBound_certificate`, `Vegas.swapFirstBound_certificate`),
irregular responses are bounded through the positive operational mass
(`Vegas.certificate_mass_pos`), and the initial floor bounds the initial draw
(`Vegas.initialFloor_le`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  [DecidableEq (CellTy Player L)]

variable (setup leaks bounds horizon scheduler) in
/-- **The comparison factor of a counterpart** at stage `n`: the largest of one,
the inverse initial floor, the inverse content floor and the response ratio. -/
def counterpartFactor (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale floor : ℕ → ℝ) (n : ℕ) : ℝ :=
  max 1 (max (max (1 / initialFloor setup leaks bounds horizon scheduler)
    (1 / contentFloor setup leaks bounds horizon scheduler (sequence n)))
    ((1 / floor n + slotError (scale n) (floor n) (trembleSlots setup bounds).card) *
      (1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card)))

/-- **The certificate's honest counterparts.** For a well-formed setup with
independent hidden initial cells, under a fully mixed source assessment at stage
`n`, at a decision input of `who` at its
own turn, take an irregular history `h` and a history `W` of the input whose
decoded point `w` leaves nobody owing a failure. When the commitment cells where
`h`'s decoded point and `w` differ hold values at both, and the message bounds
cover every binding field, some regular history of the input has, when the
factorization error is below one, reach under the certificate's profiles at
least the reach of `h` over the factorization factor times the slot error, one
plus it, and the comparison factor to the power `2 * horizon + 1`. -/
theorem reach_le_counterpart_certificate (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent) (covered : BindingFieldsCovered bounds)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (small : ∀ n, scale n ≤ 1 / 4) (floor : ℕ → ℝ) (floor_pos : ∀ n, 0 < floor n)
    [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]
    (floored : ∀ n, floor n ≤ contentFloor setup leaks bounds horizon scheduler (sequence n))
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (error_tendsto : Tendsto (fun n => slotError (scale n) (floor n)
      (trembleSlots setup bounds).card) atTop (nhds 0))
    (n : ℕ) (mixed : (sequence n).IsFullyMixed)
    {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (history witness : (onePacketInformation setup leaks bounds horizon
      scheduler).InformationHistory who (some (past, view)))
    {current witnessControl : (application setup leaks).Control}
    (historyState : history.1.state = some current)
    (witnessState : witness.1.state = some witnessControl)
    {p w : ProtocolState setup.program}
    (decodedP : decodedPoint setup current.execution.application.config = some p)
    (decodedW : decodedPoint setup witnessControl.execution.application.config = some w)
    (freeW : ∀ player, ¬ ProtocolState.OwesFailure player setup.program w)
    (succeed : CommitmentCellsSucceed setup p w)
    (irregularHistory : ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      history.1.trace) :
    ∃ counterpart : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who (some (past, view)),
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who counterpart.1.trace ∧
      ((1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) ^
          (2 * horizon + 1) - 1 < 1 →
      ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
          (certificateProfile setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one weights n) history.1).toReal ≤
        (1 + ((1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) ^
            (2 * horizon + 1) - 1)) /
          (1 - ((1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) ^
            (2 * horizon + 1) - 1)) *
          (slotError (scale n) (floor n) (trembleSlots setup bounds).card *
            (1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) *
            counterpartFactor setup leaks bounds horizon scheduler sequence scale floor n ^
              (2 * horizon + 1)) *
        ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
          (certificateProfile setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one weights n) counterpart.1).toReal) := by
  set steps := certificateOperationalSteps wellFormed sequence scale scale_pos scale_le_one small
    floor floor_pos floored covers capacity weights who error_tendsto
  have positive := certificate_mass_pos wellFormed sequence scale scale_pos scale_le_one small
    floor floor_pos floored covers capacity weights who error_tendsto
  have errorNonneg : 0 ≤ slotError (scale n) (floor n) (trembleSlots setup bounds).card :=
    slotError_nonneg (scale_pos n).le (floor_pos n) _
  have K₁Nonneg : 0 ≤ 1 / floor n + slotError (scale n) (floor n)
      (trembleSlots setup bounds).card :=
    add_nonneg (div_nonneg zero_le_one (floor_pos n).le) errorNonneg
  obtain ⟨counterpart, regular, record, upper⟩ := counterpart_bound_of_witness wellFormed
    independent (steps := steps) positive n mixed
    (initialFloor_pos setup leaks bounds horizon scheduler)
    (fun _ supported => initialFloor_le setup leaks bounds horizon scheduler supported)
    K₁Nonneg errorNonneg
    (swapResponseBound_certificate wellFormed sequence scale scale_pos scale_le_one small floor
      floor_pos floored covers capacity weights who n)
    (swapFirstBound_certificate wellFormed sequence scale scale_pos scale_le_one small floor
      floor_pos floored covers capacity weights who n)
    turn history witness historyState witnessState decodedP decodedW freeW succeed covered
    irregularHistory
  have sameRecall : ownerRecall setup leaks who counterpart.1.state =
      ownerRecall setup leaks who history.1.state := by
    rw [ownerRecall_eq_of_infoOf setup leaks ((onePacket_infoOf who counterpart.1.trace).symm.trans
        counterpart.2),
      ownerRecall_eq_of_infoOf setup leaks ((onePacket_infoOf who history.1.trace).symm.trans
        history.2)]
  have ratioNonneg : 0 ≤ slotError (scale n) (floor n) (trembleSlots setup bounds).card *
      (1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) *
      counterpartFactor setup leaks bounds horizon scheduler sequence scale floor n ^
        (2 * horizon + 1) :=
    mul_nonneg (mul_nonneg errorNonneg (by linarith))
      (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  refine ⟨counterpart, regular, fun errorSmall => ?_⟩
  exact reach_le_of_counterpart (IrregularStepBound.ofResponseMass steps positive) n
    history.1.trace counterpart.1.trace regular record sameRecall ratioNonneg upper errorSmall

end Vegas
