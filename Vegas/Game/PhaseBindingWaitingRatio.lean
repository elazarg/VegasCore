/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseWaitingMass

/-! # Actual same-event binding waiting ratios with counted noise retained -/

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

variable (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

include maximal

/-- Actual source playedness supplies the omission atom; no equality of counted
noise menus is required at the two initialized callback prefixes. -/
theorem phaseSourcePerturbedStrategy_waiting_ratio (n : Nat)
    (capacity : horizon ≤ bounds.candidateCount)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (first second : (app).Control)
    (firstTrace : (E).Trace (some first)) (secondTrace : (E).Trace (some second))
    (firstActor : first.actor = some who) (secondActor : second.actor = some who)
    (firstRequest : first.execution.application.SeedRequest who
      ⟨first.execution.application.attempt, event⟩)
    (secondRequest : second.execution.application.SeedRequest who
      ⟨second.execution.application.attempt, event⟩)
    (firstUnsent : ∀ message ∈ (app).outputs (first.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨first.execution.application.attempt, event⟩)
    (secondUnsent : ∀ message ∈ (app).outputs (second.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨second.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (firstClear : first.execution.application.current.excluded = ∅)
    (secondClear : second.execution.application.current.excluded = ∅)
    (floor : ℝ) (floorPositive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (firstChoice : (N).Choice who (some (first.execution.recall who,
      first.execution.observe app who)))
    (secondChoice : (N).Choice who (some (second.execution.recall who,
      second.execution.observe app who)))
    (firstSelected : firstChoice.1 = some ⟨none⟩)
    (secondSelected : secondChoice.1 = some ⟨none⟩) :
    let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le
        slotWeight slotNonnegative slotBounded
    let firstMass := (strategy who _ firstChoice).toReal
    let secondMass := (strategy who _ secondChoice).toReal
    firstMass - secondMass = noise *
      ((((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy initial horizon scheduler
          who _ firstChoice).toReal) -
        (((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy initial horizon scheduler
          who _ secondChoice).toReal)) ∧
    (1 - noise) * floor ≤ secondMass ∧
    firstMass ≤ (1 + noise / ((1 - noise) * floor)) * secondMass := by
  intro strategy firstMass secondMass
  have paired := phaseSourceMixture_silence_eq_of_history setup mode runtime leaks bounds plan
    horizon scheduler finite wellFormed target approximation maximal n capacity who event payload
      binding first second firstTrace secondTrace firstActor secondActor firstRequest
        secondRequest firstUnsent secondUnsent values firstClear secondClear
  have same := (paired.2.2 slotWeight slotNonnegative slotBounded).2 firstChoice secondChoice
    firstSelected secondSelected
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler
    secondTrace
  obtain ⟨source, _sourceTrace, _sourceExcluded, _sourceGeneration, _sourceActor, decoded⟩ :=
    phase_ready_binding_sourceView setup mode runtime leaks plan maximal horizon scheduler raw who
      event payload binding secondRequest.2.2.1 secondClear
  have played := phase_ready_binding_information setup mode runtime leaks plan maximal horizon
    scheduler raw who event payload binding secondRequest.2.2.1 secondClear wellFormed
  rw [decoded] at played
  have actor := phaseSourceView?_actor setup mode runtime leaks second.execution who event _ decoded
  have atCommit := phaseSourceView?_atCommit setup mode runtime leaks second.execution who event _
    decoded who payload binding
  rw [show (serviceGraph setup mode).actor? event = some who from
    (serviceGraph setup mode).actor?_of_outputLayout_binding binding] at actor
  have lower := setup.commitRecovery_missing_floor wellFormed (approximation.sequence n) floor
    floored who _ actor atCommit played
  have atom := phaseSourceMixture_silence_atom setup mode runtime leaks bounds plan horizon
    scheduler wellFormed (approximation.sequence n) who second slotWeight slotNonnegative
      slotBounded secondChoice secondSelected
  have law := phaseSourceMixture_silence_law_of_history setup mode runtime leaks bounds plan horizon
    scheduler wellFormed (approximation.sequence n) capacity second secondTrace who event payload
      binding secondActor secondRequest secondUnsent values slotWeight slotNonnegative slotBounded
  rw [decoded] at law
  have lowerAtom : floor ≤ ((mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed
        (approximation.sequence n) initial horizon scheduler who _)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed
        (approximation.sequence n) initial horizon scheduler who _)) secondChoice).toReal := by
    rw [atom, congrArg (fun probability : PMF Bool => probability true) law]
    exact lower
  exact waiting_mix_ratio _ _ _ _ firstChoice secondChoice same floor noise floorPositive
    noiseNonnegative noiseSmall lowerAtom

end Vegas
