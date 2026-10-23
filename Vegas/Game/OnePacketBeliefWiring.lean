/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCertificateDischarge
import Vegas.Game.OnePacketSlotLawForced

/-! # The operational side of the forced-belief inputs

Operational steps depend on their profiles only through their properties, so
steps for one profile sequence are steps for every sequence equal to it
(`Vegas.OperationalSteps.ofProfilesEq`), with the same masses. Profiles
assembled from the certificate's components are the certificate's profiles,
so at the tremble scale over the combined floor the certificate's operational
steps are steps of every assembled sequence
(`Vegas.assembledOperationalSteps`). The tremble scale is negligible against
the combined floor to the depth (`Vegas.tendsto_trembleScale_div_pow`). This
fixes the operational steps, scale, floors and depth of
`Vegas.OnePacketBeliefInputs` (`Vegas.OnePacketBeliefInputs.ofCertificate`),
leaving the intended own completions, the fibers and the honest counterparts as
inputs.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- Operational steps of one profile sequence are operational steps of every
sequence equal to it, with the same masses and errors. -/
def OperationalSteps.ofProfilesEq {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles other : ℕ → ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {who : Player} (steps : OperationalSteps setup leaks bounds horizon scheduler sequence
      profiles who)
    (same : ∀ n, other n = profiles n) :
    OperationalSteps setup leaks bounds horizon scheduler sequence other who where
  mass := steps.mass
  error := steps.error
  mass_nonneg := steps.mass_nonneg
  error_nonneg := steps.error_nonneg
  error_tendsto := steps.error_tendsto
  environment n := by
    rw [same n]
    exact steps.environment n
  component n := by
    rw [same n]
    exact steps.component n

variable [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  [Finite setup.intendedProtocol.History]
  [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

/-- **Operational steps of assembled profiles.** For a well-formed setup, at
the tremble scale over the combined floor of a source sequence to a depth, the
certificate's operational steps are operational steps of every sequence of
profiles assembled from the certificate's components. -/
def assembledOperationalSteps (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (depth : ℕ)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon scheduler (sequence n)) depth n)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    (who : Player) :
    OperationalSteps setup leaks bounds horizon scheduler sequence
      (fun n => (targetSequence n).strategy) who :=
  have floorPos := fun n => combinedFloor_pos setup leaks bounds horizon scheduler (sequence n)
  have floorLe := fun n => combinedFloor_le_one setup leaks bounds horizon scheduler (sequence n)
  OperationalSteps.ofProfilesEq
    (certificateOperationalSteps wellFormed sequence scale scale_pos scale_le_one
      (fun n => (scaleEq n).trans_le (trembleScale_le_quarter (floorPos n).le (floorLe n)))
      (fun n => combinedFloor setup leaks bounds horizon scheduler (sequence n)) floorPos
      (fun n => combinedFloor_le_contentFloor setup leaks bounds horizon scheduler (sequence n))
      covers capacity weights who
      (by
        simp only [scaleEq]
        exact tendsto_slotError _ floorPos floorLe depth _))
    assembled

open Classical in
/-- **The forced-belief inputs from the certificate.** For a well-formed setup,
along profiles assembled from the certificate's components at the tremble scale
over the combined floor of the source sequence to a depth, the operational steps
are the certificate's, the scale is the tremble scale, the floors are the
combined floors and the depth is the given depth. The intended own completions,
the common fibers and the honest counterparts remain inputs. -/
def OnePacketBeliefInputs.ofCertificate (wellFormed : setup.WellFormed)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {scale : ℕ → ℝ} {scale_pos : ∀ n, 0 < scale n} {scale_le_one : ∀ n, scale n ≤ 1}
    (depth : ℕ)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon scheduler (sequence n)) depth n)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    {weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p)}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    {who : Player} {site : (onePacketN).InformationSite who}
    {sourceSite : setup.intendedModel.InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup leaks who site.1)
    (slack : ℝ) (slack_nonneg : 0 ≤ slack)
    (ownIntended : ∀ n (history : (onePacketN).InformationHistory who site.1),
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (bounds := bounds) (horizon := horizon) (scheduler := scheduler) who
        history.1.trace)
    (fiberMass : ℕ → ℝ)
    (fiber : ∀ n point, ∑ history with RegularTrace setup leaks bounds horizon scheduler
        (sequence n) who history.1.trace ∧
        replayProjection setup leaks bounds horizon scheduler sourceSite site decision projected
          history = point,
      operationalWeight setup leaks who
        (roundOrResponseMass (scheduler := scheduler)
          (stepResponse bounds (keyWeights setup leaks bounds horizon scheduler (weights n))
            (scale n)))
        (operationalRecord setup leaks bounds horizon scheduler history.1.trace) = fiberMass n)
    (counterpart : ℕ → (onePacketN).InformationHistory who site.1 →
      (onePacketN).InformationHistory who site.1)
    (commonWeight : ℕ → (onePacketN).InformationHistory who site.1 → ℝ)
    (counterpart_regular : ∀ n history, ¬ RegularTrace setup leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who
        (counterpart n history).1.trace)
    (irregular_le : ∀ n history, ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n)
        who history.1.trace →
      ((onePacketN).historyReachWeight (targetSequence n).strategy history.1).toReal ≤
        scale n ^ 3 * commonWeight n history)
    (counterpart_ge : ∀ n history, ¬ RegularTrace setup leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      scale n ^ 2 * combinedFloor setup leaks bounds horizon scheduler (sequence n) ^ depth *
          commonWeight n history ≤
        slack * ((onePacketN).historyReachWeight (targetSequence n).strategy
          (counterpart n history).1).toReal) :
    OnePacketBeliefInputs setup leaks bounds horizon scheduler sequence targetSequence site
      sourceSite decision projected where
  steps := assembledOperationalSteps wellFormed sequence scale scale_pos scale_le_one depth
    scaleEq covers capacity weights assembled who
  scale := scale
  floors n := combinedFloor setup leaks bounds horizon scheduler (sequence n)
  depth := depth
  slack := slack
  floors_pos n := combinedFloor_pos setup leaks bounds horizon scheduler (sequence n)
  scale_nonneg n := (scale_pos n).le
  negligible := by
    simp only [scaleEq]
    exact tendsto_trembleScale_div_pow _
      (fun n => combinedFloor_pos setup leaks bounds horizon scheduler (sequence n))
      (fun n => combinedFloor_le_one setup leaks bounds horizon scheduler (sequence n))
  slack_nonneg := slack_nonneg
  ownIntended := ownIntended
  fiberMass := fiberMass
  fiber := fiber
  counterpart := counterpart
  commonWeight := commonWeight
  counterpart_regular := counterpart_regular
  irregular_le := irregular_le
  counterpart_ge := counterpart_ge

end Vegas
