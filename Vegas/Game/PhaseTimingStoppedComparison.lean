/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingContinuationComparison
import Vegas.Game.PhaseTimingTaggedNoise
import Vegas.Pending.PhaseCommitmentMenuShape
import Vegas.Pending.PhaseAttemptInputAtom

/-! # Same original member profiles on actual current-block continuation paths -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Pool" => FreeKeyedPool
  (fun agent : (N).InformationAgent (N).playedInformation =>
    PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
  (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent) (Subtype.val (Sigma.snd agent)))
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

/-- On the genuine first-E/attempt-exit/full-input stopped law, the SAME original
per-owner members and fixed focal intervention satisfy the concrete near-one
path comparison. Every marked transmission has derived prepared binding
syntax; all other ORIGINAL noisy atoms and full entry recall are retained. -/
theorem phase_timing_continuation_stopped_noise
    [setup.FiniteInitialLaw]
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
      setup.commitRecoveryContinuingChoice)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : ∀ who, (N).Policy who)
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor) (floorBounded : floor ≤ 1)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (small : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : Player → (p : Pool) → Parts p)
    (members : ∀ who, (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (focal : Player) (intervention : (N).BehavioralPolicy focal)
    (entry final : (app).Control)
    (entryTrace : (E).Trace (some entry)) (finalTrace : (E).Trace (some final))
    (isPrefix : TracePrefix entryTrace finalTrace)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : entry.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (allValues : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (clear : final.execution.application.current.excluded = ∅)
    (ready : final.execution.application.current.native.config.cut.Ready event)
    (certificate : (E).WellFoundedHistories) (site : (N).InformationSite focal)
    (atSite : (N).infoOf focal finalTrace = site.1) :
    let sources := fun who => setup.commitRecoveryValueAssessment wellFormed
      (approximation.sequence n) who (members who)
    let zero := Function.update (fun who =>
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (sources who) 0 (by norm_num) (by norm_num) slotWeight
          slotPositive.le slotBounded parts who) focal intervention
    let noisy := Function.update (fun who =>
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (sources who) noise nonnegative small.le slotWeight
          slotPositive.le slotBounded parts who) focal intervention
    let stopped := fun history : (E).History => match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ final.execution.application.attempt ∨
          (N).infoOf focal history.trace = site.1
    ∃ records : ∀ who, List ((N).InfoState who × (E).Action who),
      (∀ who, (N).ownPlay who finalTrace = records who ++ (N).ownPlay who entryTrace) ∧
      (∀ who record, record ∈ records who → record.2.transmission ≠ none →
        ∃ event serial preparation evidence,
          record.2 = ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩,
            evidence⟩⟩) ∧
      ∃ chance : ℝ, 0 ≤ chance ∧
        (∀ profile : ∀ who, (N).BehavioralPolicy who,
          (((N).runBehavioralFrom profile (finalTrace.length - entryTrace.length)
            ⟨some entry, entryTrace⟩) ⟨some final, finalTrace⟩).toReal =
            chance * ∏ who, (N).ownPlayReachProbability (profile who) (records who)) ∧
        let positions := Σ who, Fin (records who).length
        let atom := fun index : positions =>
          (((noisy index.1 (records index.1)[index.2.val].1).map Subtype.val)
            (some (records index.1)[index.2.val].2)).toReal
        let removed := fun index : positions =>
          if index.1 ≠ focal ∧ (records index.1)[index.2.val].2.transmission ≠ none then noise *
            ((((menu).uniformPolicy initial horizon scheduler index.1
              (records index.1)[index.2.val].1).map Subtype.val)
                (some (records index.1)[index.2.val].2)).toReal else 0
        (((N).runBehavioralUntil certificate noisy stopped ⟨some entry, entryTrace⟩)
          ⟨some final, finalTrace⟩).toReal ≤
          (1 + noise / (slotWeight * floor)) ^ Fintype.card positions *
            (((N).runBehavioralUntil certificate zero stopped ⟨some entry, entryTrace⟩)
              ⟨some final, finalTrace⟩).toReal +
          chance * ∑ index, removed index * ∏ other ∈ Finset.univ.erase index, atom other := by
  classical
  intro sources zero noisy stopped
  obtain ⟨records, recordEq, bindingRecord, chance, nonnegativeChance, factor, bounded⟩ :=
    phase_timing_continuation_path_noise setup mode runtime leaks bounds plan horizon scheduler
      bound finite wellFormed target approximation maximal fallback n capacity floor positive
        floorBounded floored noise nonnegative small slotWeight slotPositive slotBounded parts
          members focal intervention entry final entryTrace finalTrace isPrefix phase remaining
            installed committing event inside allValues clear ready
  refine ⟨records, recordEq, bindingRecord, chance, nonnegativeChance, factor, ?_⟩
  intro positions atom removed
  have initialized : initial =
      (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan) := by
    simp only [PMF.map_comp, Function.comp_def]
  have untilAtom (profile : ∀ who, (N).BehavioralPolicy who) :
      (N).runBehavioralUntil certificate profile stopped ⟨some entry, entryTrace⟩
          ⟨some final, finalTrace⟩ =
        (N).runBehavioralFrom profile (finalTrace.length - entryTrace.length)
          ⟨some entry, entryTrace⟩ ⟨some final, finalTrace⟩ := by
    convert! (phase_current_attempt_until_atom runtime leaks bounds initial horizon scheduler plan
      (setup.initialLaw.map encodeInputs) initialized certificate entry final entryTrace finalTrace
        isPrefix phase remaining installed event inside clear ready focal site atSite profile)
      using 1
    apply congrArg (fun stopping : (E).History → Prop =>
      (N).runBehavioralUntil certificate profile stopping ⟨some entry, entryTrace⟩
        ⟨some final, finalTrace⟩)
    funext history
    rcases history with ⟨state, trace⟩
    cases state <;> rfl
  rw [untilAtom noisy, untilAtom zero]
  exact bounded

end Vegas
