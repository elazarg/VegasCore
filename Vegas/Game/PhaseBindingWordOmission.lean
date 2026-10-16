/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingWaitingLaw

/-! # The original source omission draw at actual paired binding callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- Actual clear source playedness and the compiler address derive equality
of the ORIGINAL omission distributions. Hidden typed results and owner-private
source views may differ; no response-likelihood equality is an input. -/
theorem phaseBindingWord_missing_eq_of_histories
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (n : Nat) (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (first second : (app).Control)
    (firstTrace : (E).Trace (some first)) (secondTrace : (E).Trace (some second))
    (firstClear : first.execution.application.current.excluded = ∅)
    (secondClear : second.execution.application.current.excluded = ∅)
    (firstReady : first.execution.application.current.native.config.cut.Ready event)
    (secondReady : second.execution.application.current.native.config.cut.Ready event) :
    ((approximation.sequence n).strategy owner
      (setup.commitRecoveryClearInformation wellFormed owner
        (phaseSourceView? setup mode runtime leaks owner event
          (first.execution.observe app owner)))).map
            (fun choice => CommitRecoveryMove.missed choice.1) =
      ((approximation.sequence n).strategy owner
        (setup.commitRecoveryClearInformation wellFormed owner
          (phaseSourceView? setup mode runtime leaks owner event
            (second.execution.observe app owner)))).map
              (fun choice => CommitRecoveryMove.missed choice.1) := by
  have firstRaw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler firstTrace
  have secondRaw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler secondTrace
  obtain ⟨firstSource, _firstTrace, _firstExcluded, _firstGeneration, _firstActor, firstView⟩ :=
    phase_ready_binding_sourceView setup mode runtime leaks plan maximal horizon scheduler firstRaw
      owner event payload binding firstReady firstClear
  obtain ⟨secondSource, _secondTrace, _secondExcluded, _secondGeneration, _secondActor,
      secondView⟩ := phase_ready_binding_sourceView setup mode runtime leaks plan maximal horizon
        scheduler secondRaw owner event payload binding secondReady secondClear
  have firstPosition := phaseSourceView?_position setup mode runtime leaks first.execution owner
    event _ firstView
  have secondPosition := phaseSourceView?_position setup mode runtime leaks second.execution owner
    event _ secondView
  have firstPlayed := phase_ready_binding_information setup mode runtime leaks plan maximal
    horizon scheduler firstRaw owner event payload binding firstReady firstClear wellFormed
  have secondPlayed := phase_ready_binding_information setup mode runtime leaks plan maximal
    horizon scheduler secondRaw owner event payload binding secondReady secondClear wellFormed
  rw [firstView] at firstPlayed
  rw [secondView] at secondPlayed
  rw [firstView, secondView]
  exact setup.commitRecovery_approximation_missing_eq_of_position finite wellFormed target
    approximation n owner _ _ (firstPosition.trans secondPosition.symm) firstPlayed secondPlayed

end Vegas
