/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingBindingNoise
import Vegas.Pending.PhaseBindingMemoryCallback

/-! # All actual waiting callbacks in a commitment interval -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler

include maximal

/-- A clear callback in an actual commitment interval either has the genuine
binding omission lower bound or the singleton silence menu. Thus the SAME
near-one WAIT factor covers sent and absent requests as well as unsent ones. -/
theorem phaseTimingComponent_commitment_silence_noise
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)]
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (floorPositive : 0 < floor) (floorBounded : floor ≤ 1)
    (floored : ∀ (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
      (choice : setup.commitRecoveryModel.Choice who site.1),
      floor ≤ ((approximation.sequence n).strategy who site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (weights : PMF (PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
      (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound agent)))
    (current : (app).Control) (trace : (E).Trace (some current))
    (acting : current.actor = some agent.1)
    (atInput : agent.2.1 = some
      (current.execution.recall agent.1, current.execution.observe app agent.1))
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : current.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (allValues : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (clear : current.execution.application.current.excluded = ∅) :
    let residual := weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num)
        slotWeight slotPositive.le slotBounded agent)
    let perturbed := weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed (approximation.sequence n) noise noiseNonnegative
        noiseSmall.le slotWeight slotPositive.le slotBounded agent)
    ∃ silent : (N).Choice agent.1 agent.2.1, silent.1 = some ⟨none⟩ ∧
      slotWeight * floor ≤ (residual silent).toReal ∧
      (1 - noise) * (residual silent).toReal ≤ (perturbed silent).toReal ∧
      (perturbed silent).toReal ≤
        (1 + noise / (slotWeight * floor)) * (residual silent).toReal := by
  classical
  intro residual perturbed
  by_cases usable : ∃ coordinate, current.execution.application.SeedRequest agent.1 coordinate ∧
      ∀ message ∈ (app).outputs (current.execution.recall agent.1),
        PhaseCount.event? message.payload ≠ some coordinate
  · obtain ⟨coordinate, request, unsent⟩ := usable
    obtain ⟨actual, head, inside⟩ := request.2.1
    have same : actual = phase := by
      simpa only [installed, List.head?_cons, Option.mem_def, Option.some.injEq] using head.symm
    subst actual
    have fields := phase.fields coordinate.event ((phase.mem_events coordinate.event).mp inside).1
      ((phase.mem_events coordinate.event).mp inside).2
    rw [committing] at fields
    obtain ⟨owner, payload, binding⟩ := fields
    have actorEq := ((serviceGraph setup mode).actor?_of_outputLayout_binding binding).symm.trans
      request.2.2.2.1
    cases Option.some.inj actorEq
    have currentTag : coordinate = ⟨current.execution.application.attempt, coordinate.event⟩ := by
      cases coordinate with
      | mk tag event =>
          simp only [CommitAttemptEvent.mk.injEq]
          exact ⟨request.1, trivial⟩
    rw [currentTag] at request unsent
    exact phaseTimingComponent_silence_noise_comparison setup mode runtime leaks bounds plan
      horizon scheduler bound finite wellFormed target approximation maximal n capacity floor
        floorPositive floored noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded
          agent weights current trace acting atInput coordinate.event payload binding request unsent
            (allValues payload) clear
  · let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
    have initialEq : inputs.map (PhaseRuntimeState.initial plan) = initial := by
      simp only [inputs, PMF.map_comp, Function.comp_def]
    have counted : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some current) := by rw [initialEq]; exact trace
    have sameControl : current = ⟨current.remaining, some agent.1, current.execution⟩ := by
      cases current with
      | mk fuel actor execution => cases acting; rfl
    have activeTrace : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some ⟨current.remaining, some agent.1, current.execution⟩) :=
      sameControl ▸ counted
    have singleton := PhaseCount.onePacketActions_eq_singleton_of_no_unsent runtime leaks bounds
      plan (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler current.remaining
        agent.1 current.execution activeTrace usable
    have valueEq (choice : (N).Choice agent.1 agent.2.1) : choice.1 = some ⟨none⟩ := by
      let raw : Option (app).Action := choice.1
      have legal : raw ∈ (N).menu agent.1 agent.2.1 := choice.2
      rw [atInput] at legal
      change ∃ action ∈ PhaseCount.onePacketActions runtime leaks bounds agent.1
        (current.execution.recall agent.1) (current.execution.observe (app) agent.1),
          raw = some action at legal
      obtain ⟨action, offered, equal⟩ := legal
      rw [singleton] at offered
      exact equal.trans (congrArg some (Finset.mem_singleton.mp offered))
    let : Subsingleton ((N).Choice agent.1 agent.2.1) :=
      ⟨fun first second => Subtype.ext ((valueEq first).trans (valueEq second).symm)⟩
    let silent := (residual.support_nonempty).choose
    have residualOne : residual silent = 1 := by
      rw [eq_pure_of_subsingleton residual silent, PMF.pure_apply_self]
    have perturbedOne : perturbed silent = 1 := by
      rw [eq_pure_of_subsingleton perturbed silent, PMF.pure_apply_self]
    refine ⟨silent, valueEq silent, ?_, ?_, ?_⟩
    · rw [residualOne, ENNReal.toReal_one]
      calc
        slotWeight * floor ≤ 1 * floor :=
          mul_le_mul_of_nonneg_right slotBounded floorPositive.le
        _ ≤ 1 := by simpa only [one_mul] using floorBounded
    · rw [residualOne, perturbedOne, ENNReal.toReal_one, mul_one]
      linarith
    · rw [residualOne, perturbedOne, ENNReal.toReal_one, mul_one]
      exact le_add_of_nonneg_right (div_nonneg noiseNonnegative
        (mul_nonneg slotPositive.le floorPositive.le))


/-- At an actual commitment callback, deleting precisely the RAW transmission
summand leaves a nonnegative atom bounded by the SAME zero-noise atom times
the near-one WAIT factor. Source accepted failures stay in the residual atom. -/
theorem phaseTimingComponent_commitment_trimmed_atom
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)]
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (floorPositive : 0 < floor) (floorBounded : floor ≤ 1)
    (floored : ∀ (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
      (choice : setup.commitRecoveryModel.Choice who site.1),
      floor ≤ ((approximation.sequence n).strategy who site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (weights : PMF (PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
      (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound agent)))
    (current : (app).Control) (trace : (E).Trace (some current))
    (acting : current.actor = some agent.1)
    (atInput : agent.2.1 = some
      (current.execution.recall agent.1, current.execution.observe app agent.1))
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : current.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (allValues : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (clear : current.execution.application.current.excluded = ∅)
    (choice : (N).Choice agent.1 agent.2.1) :
    let residual := weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num)
        slotWeight slotPositive.le slotBounded agent)
    let perturbed := weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed (approximation.sequence n) noise noiseNonnegative
        noiseSmall.le slotWeight slotPositive.le slotBounded agent)
    let removed := if (choice.1.getD ⟨none⟩).transmission ≠ none then noise *
      (((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1) choice).toReal else 0
    0 ≤ (perturbed choice).toReal - removed ∧
      (perturbed choice).toReal - removed ≤ (perturbed choice).toReal ∧
      (perturbed choice).toReal - removed ≤
        (1 + noise / (slotWeight * floor)) * (residual choice).toReal := by
  classical
  intro residual perturbed removed
  have denominator : 0 < slotWeight * floor := mul_pos slotPositive floorPositive
  have ratioNonnegative : 0 ≤ noise / (slotWeight * floor) :=
    div_nonneg noiseNonnegative denominator.le
  by_cases sent : (choice.1.getD ⟨none⟩).transmission ≠ none
  · have decomposition := phaseTimingComponent_mixture_raw_mixture setup mode runtime leaks bounds
      initial horizon scheduler bound wellFormed (approximation.sequence n) noise noiseNonnegative
        noiseSmall.le slotWeight slotPositive.le slotBounded agent weights
    have atom : (perturbed choice).toReal - removed =
        (1 - noise) * (residual choice).toReal := by
      dsimp only [perturbed, removed]
      rw [decomposition, mix_apply_toReal, ite_eq_left sent]
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [atom]
      exact mul_nonneg (sub_nonneg.mpr noiseSmall.le) ENNReal.toReal_nonneg
    · exact sub_le_self _ (by dsimp only [removed]; rw [ite_eq_left sent]; positivity)
    · rw [atom]
      exact mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg
  · have valueEq : choice.1 = some ⟨none⟩ := by
      let raw : Option (app).Action := choice.1
      have legal : raw ∈ (N).menu agent.1 agent.2.1 := choice.2
      rw [atInput] at legal
      change ∃ action ∈ PhaseCount.onePacketActions runtime leaks bounds agent.1
        (current.execution.recall agent.1) (current.execution.observe (app) agent.1),
          raw = some action at legal
      obtain ⟨action, _offered, equal⟩ := legal
      have equalRaw : choice.1 = some action := equal
      have noTransmission : action.transmission = none := by
        simpa only [equalRaw, Option.getD_some] using not_ne_iff.mp sent
      have actionEq : action = ⟨none⟩ := by
        cases action with
        | mk transmission => cases noTransmission; rfl
      exact equalRaw.trans (congrArg some actionEq)
    obtain ⟨silent, silentEq, _lower, _retained, upper⟩ :=
      phaseTimingComponent_commitment_silence_noise setup mode runtime leaks bounds plan horizon
        scheduler bound finite wellFormed target approximation maximal n capacity floor
          floorPositive
          floorBounded floored noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded
            agent weights current trace acting atInput phase remaining installed committing
              allValues
              clear
    have same : choice = silent := Subtype.ext (valueEq.trans silentEq.symm)
    dsimp only [removed]
    rw [ite_eq_right sent, sub_zero]
    refine ⟨ENNReal.toReal_nonneg, le_rfl, ?_⟩
    simpa only [same] using upper

end Vegas
