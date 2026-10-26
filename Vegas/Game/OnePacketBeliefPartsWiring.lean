/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketBeliefWiring

/-! # The certificate's side of the two parts of the forced-belief inputs

The honest-counterpart part of the forced-belief inputs takes the tremble scale
over the combined floor of the source sequence to a depth, with the combined
floors and that depth (`Vegas.OnePacketCounterpartInputs.ofCertificate`). It
reads no debt-freedom and no own completions. The own part takes the
certificate's operational steps of the assembled profiles
(`Vegas.OnePacketOwnInputs.ofCertificate`). The honest counterparts, the
intended own completions and the common fibers remain inputs.
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
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  [Finite setup.intendedProtocol.History]

local notation "onePacketN" =>
  onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

/-- **The honest-counterpart inputs from the certificate.** At the tremble scale
over the combined floor of the source sequence to a depth, the floors are the
combined floors and the depth is the given depth. The honest counterparts of
irregular histories remain inputs. -/
def OnePacketCounterpartInputs.ofCertificate
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    {who : Player} {site : (onePacketN).InformationSite who}
    {scale : ℕ → ℝ} (scale_pos : ∀ n, 0 < scale n) (depth : ℕ)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup runtime leaks bounds horizon scheduler (sequence n)) depth n)
    (slack : ℝ) (slack_nonneg : 0 ≤ slack)
    (counterpart : ℕ → (onePacketN).InformationHistory who site.1 →
      (onePacketN).InformationHistory who site.1)
    (commonWeight : ℕ → (onePacketN).InformationHistory who site.1 → ℝ)
    (counterpart_regular : ∀ n history, ¬ RegularTrace setup runtime leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
        (counterpart n history).1.trace)
    (irregular_le : ∀ n history, ¬ RegularTrace setup runtime leaks bounds horizon scheduler
      (sequence n)
        who history.1.trace →
      ((onePacketN).historyReachWeight (targetSequence n).strategy history.1).toReal ≤
        scale n ^ 3 * commonWeight n history)
    (counterpart_ge : ∀ n history, ¬ RegularTrace setup runtime leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      scale n ^ 2 * combinedFloor setup runtime leaks bounds horizon scheduler (sequence n) ^
        depth *
          commonWeight n history ≤
        slack * ((onePacketN).historyReachWeight (targetSequence n).strategy
          (counterpart n history).1).toReal) :
    OnePacketCounterpartInputs setup runtime leaks bounds horizon scheduler sequence targetSequence
      site where
  scale := scale
  floors n := combinedFloor setup runtime leaks bounds horizon scheduler
    (sequence n)
  depth := depth
  slack := slack
  floors_pos n := combinedFloor_pos setup runtime leaks bounds horizon
    scheduler (sequence n)
  scale_nonneg n := (scale_pos n).le
  negligible := by
    simp only [scaleEq]
    exact tendsto_trembleScale_div_pow _
      (fun n => combinedFloor_pos setup runtime leaks bounds horizon scheduler (sequence n))
      (fun n => combinedFloor_le_one setup runtime leaks bounds horizon scheduler (sequence n))
  slack_nonneg := slack_nonneg
  counterpart := counterpart
  commonWeight := commonWeight
  counterpart_regular := counterpart_regular
  irregular_le := irregular_le
  counterpart_ge := counterpart_ge

variable [Finite (onePacketProtocol setup runtime leaks bounds horizon scheduler).History]

open Classical in
/-- **The own inputs from the certificate.** For a well-formed setup, along
profiles assembled from the certificate's components at the tremble scale over
the combined floor of the source sequence to a depth, the operational steps are
the certificate's. The intended own completions and the common fibers remain
inputs. -/
def OnePacketOwnInputs.ofCertificate (wellFormed : setup.WellFormed)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {scale : ℕ → ℝ} {scale_pos : ∀ n, 0 < scale n} {scale_le_one : ∀ n, scale n ≤ 1}
    (depth : ℕ)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup runtime leaks bounds horizon scheduler (sequence n)) depth n)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    {weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p)}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      scale_pos
      scale_le_one weights targetSequence)
    {who : Player} {site : (onePacketN).InformationSite who}
    {sourceSite : setup.intendedModel.InformationSite who}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup runtime leaks who site.1)
    (ownIntended : ∀ n (history : (onePacketN).InformationHistory who site.1),
      RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler) who
        history.1.trace)
    (fiberMass : ℕ → ℝ)
    (fiber : ∀ n point, ∑ history with RegularTrace setup runtime leaks bounds horizon scheduler
        (sequence n) who history.1.trace ∧
        replayProjection setup runtime leaks bounds horizon scheduler sourceSite site decision
          projected
          history = point,
      operationalWeight setup runtime leaks who
        (roundOrResponseMass (runtime := runtime) (scheduler := scheduler)
          (stepResponse (runtime := runtime) bounds (keyWeights setup runtime leaks bounds horizon
            scheduler (weights n))
            (scale n)))
        (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace) =
          fiberMass n) :
    OnePacketOwnInputs setup runtime leaks bounds horizon scheduler sequence targetSequence site
      sourceSite decision projected where
  steps := assembledOperationalSteps (runtime := runtime) wellFormed sequence
    scale scale_pos scale_le_one depth
    scaleEq covers capacity weights assembled who
  ownIntended := ownIntended
  fiberMass := fiberMass
  fiber := fiber

end Vegas
