/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueGoodBinding
import Vegas.Game.PhaseTimingRawBindingLimit

/-! # Vanishing actual native Bayes error under the chosen noise schedule -/

noncomputable section

namespace Vegas

open Filter Topology SourceProgram EventGraph EventGraphRuntime Interaction GameTheory
  GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [goodLimitHistories : Fintype
    ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).History]
  [goodLimitInputEquality : ∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial runtimePlan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "nativeInitial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial runtimePlan (encodeInputs draw))
local notation "M" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) nativeInitial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance phaseRecoveryValueGoodLimitPoolFintype : Fintype Pool := Fintype.ofFinite _

variable [nature : (phaseApplication runtime leaks).FiniteNature
  (setup.initialLaw.map (fun draw => PhaseRuntimeState.initial runtimePlan (encodeInputs draw)))
    scheduler]

local notation "NativeAgent" => InformationModel.InformationAgent (M)
  (InformationModel.playedInformation (M))
local notation "NativePool" => FreeKeyedPool
  (fun agent : NativeAgent => PhasePublicExclusion setup mode runtime leaks
    (Subtype.val (Sigma.snd agent)))
  (fun agent : NativeAgent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent : NativeAgent => phaseTimingKey runtime leaks (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
local notation "NativeParts" => PhaseTimingPart setup mode runtime leaks bounds nativeInitial
  horizon scheduler bound
local notation "nativePool" => phaseTimingPool setup mode runtime leaks bounds nativeInitial
  horizon scheduler bound

local instance phaseRecoveryValueGoodLimitNativeHistories :
    Fintype (((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial runtimePlan (encodeInputs draw))
        horizon scheduler).History) := Fintype.ofFinite _

omit goodLimitHistories goodLimitInputEquality nature in
private theorem info_cast
    (old : PMF (phaseApplication runtime leaks).State) (oldLaw : old = nativeInitial)
    (focal : Player) (original : (app).Control)
    (trace : ((menu).protocol old horizon scheduler).Trace (some original))
    (site : ((menu).information old horizon scheduler).InformationSite focal)
    (observed : ((menu).information old horizon scheduler).infoOf focal trace = site.1) :
    (M).infoOf focal (oldLaw ▸ trace) = (oldLaw ▸ site).1 := by
  subst old
  exact observed

open Classical in
/-- The existing noise choice makes the actual native Bayes belief converge in
L1 to the explicitly retained ORIGINAL-memory weight on every clear binding
fiber. Opening WAIT and all other nonsend RAW factors remain in that weight. -/
theorem exists_phase_value_good_belief_vanishes
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
      setup.commitRecoveryContinuingChoice)
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    [setup.FiniteInitialLaw]
    (capacity : horizon ≤ bounds.candidateCount) (covered : bounds.CoversOutputValues)
    (slotWeight : ℕ → ℝ) (slotPositive : ∀ n, 0 < slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1) :
    ∃ (noise : ℕ → ℝ) (noisePositive : ∀ n, 0 < noise n)
      (noiseSmall : ∀ n, noise n < 1 / 2),
      Filter.Tendsto noise Filter.atTop (nhds 0) ∧
      let lawEq : initial = nativeInitial := by
        simpa only [Function.comp_def] using
          PMF.map_comp encodeInputs setup.initialLaw (PhaseRuntimeState.initial runtimePlan)
      ∀ (fallback : ∀ who, (N).Policy who)
        (weights : ℕ → (p : Pool) → PMF (Parts p))
        (nativeWeights : ℕ → (p : NativePool) → PMF (NativeParts p))
        (actual : ℕ → (N).BehavioralAssessment),
        (∀ n who (site : (N).InformationSite who),
          ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
          (actual n).strategy who site.1 = ((N).agentBehavior (N).playedInformation fallback
            (fun agent => (weights n (pool agent)).bind
              (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
                wellFormed (approximation.sequence n) (noise n) (noisePositive n).le
                  (by linarith [noiseSmall n]) (slotWeight n) (slotPositive n).le (slotBounded n)
                    agent))) who site.1) →
        (∀ n, (actual n).IsFullyMixed) →
        (∀ n, BehavioralAssessment.IsBayesConsistent (N) (actual n)
          ((menu).decisionInformationAntichain initial horizon scheduler)) →
        let nativeActual := fun n => (lawEq ▸ (actual n).strategy : ∀ who, (M).BehavioralPolicy who)
        (∀ n (agent : NativeAgent), nativeActual n agent.1 agent.2.1 =
          (nativeWeights n (nativePool agent)).bind
            (phaseTimingComponent setup mode runtime leaks bounds nativeInitial horizon scheduler
              bound
              wellFormed (approximation.sequence n) (noise n) (noisePositive n).le
                (by linarith [noiseSmall n]) (slotWeight n) (slotPositive n).le (slotBounded n)
                  agent)) →
        ∀ (focal : Player) (site : (N).InformationSite focal)
          (original : (app).Control) (trace : (E).Trace (some original)),
          (N).infoOf focal trace = site.1 → original.actor = some focal →
          ∀ (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
          (serviceGraph setup mode).outputLayout event = .binding focal payload →
          original.execution.application.current.excluded = ∅ →
          original.execution.application.SeedRequest focal
            ⟨original.execution.application.attempt, event⟩ →
          let priors := fun n who => (independentProduct (weights n)).bind fun plan =>
            (setup.commitRecoveryValuePlan finite wellFormed
              (approximation.sequence n).strategy who).map (Prod.mk plan)
          let members := fun n who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds
            initial horizon scheduler bound fallback wellFormed
              (setup.commitRecoveryValueAssessment wellFormed (approximation.sequence n) who
                memory.2)
                (noise n) (noisePositive n).le (by linarith [noiseSmall n]) (slotWeight n)
                  (slotPositive n).le (slotBounded n) memory.1 who
          let raw := fun n who => ((app).policyMixture (priors n who) (members n who)).policy
          let retained := fun (chance : ℕ → (N).InformationHistory focal site.1 → ℝ) n
              (history : (N).InformationHistory focal site.1) =>
            phaseTimingPlanPolicy_value_retainedWeight setup mode runtime leaks bounds runtimePlan
              initial horizon scheduler bound fallback wellFormed (approximation.sequence n) finite
                (weights n) (noise n) (noisePositive n).le (by linarith [noiseSmall n])
                  (slotWeight n) (slotPositive n).le (slotBounded n) focal (raw n focal) history.1
                    (chance n history)
          ∃ chance : ℕ → (N).InformationHistory focal site.1 → ℝ,
            (∀ᶠ n in Filter.atTop, (∀ history, 0 ≤ retained chance n history) ∧
              0 < ∑ history, retained chance n history) ∧
            Filter.Tendsto (fun n => ∑ history,
              |((actual n).belief focal site history).toReal - retained chance n history /
                ∑ next, retained chance n next|) Filter.atTop (nhds 0) := by
  obtain ⟨_floor, noise, _floorPositive, noisePositive, noiseSmall, _floored, noiseVanishes,
      shareVanishes⟩ := exists_phase_timing_raw_binding_share_vanishes setup mode runtime leaks
    bounds runtimePlan horizon scheduler bound finite wellFormed target approximation maximal
      capacity covered slotWeight slotPositive slotBounded
  refine ⟨noise, noisePositive, noiseSmall, noiseVanishes, ?_⟩
  intro lawEq fallback weights nativeWeights actual assembled mixed bayes nativeActual
    assembledNative focal site original trace atSite active event payload output clear request
    priors members raw retained
  let nativeSite : (M).InformationSite focal := lawEq ▸ site
  have nativeAtSite := info_cast setup mode runtime leaks bounds runtimePlan horizon scheduler
    initial lawEq focal original trace site atSite
  have limit := shareVanishes nativeWeights nativeActual assembledNative focal nativeSite original
    (lawEq ▸ trace) nativeAtSite active event payload output clear request
  let share := fun n => phaseOpponentRawBindingShare setup mode runtime leaks bounds runtimePlan
    horizon scheduler (noise n) focal (nativeActual n) nativeSite
  have smallEventually : ∀ᶠ n in Filter.atTop, share n < 1 :=
    (tendsto_order.1 limit).2 1 (by norm_num)
  have unflagged : ¬ PhasePublicExclusion setup mode runtime leaks site.1 := by
    rintro ⟨past, view, observed, excluded⟩
    have actualInfo : (N).infoOf focal trace = some (original.execution.recall focal,
        original.execution.observe (app) focal) :=
      ((menu).info initial horizon scheduler focal trace).trans (by
        simp only [ReactiveApplication.observe, active, ite_true])
    have pairEq := Option.some.inj (observed.symm.trans (atSite.symm.trans actualInfo))
    have viewEq : view = original.execution.observe (app) focal := congrArg Prod.snd pairEq
    rw [viewEq] at excluded
    exact excluded clear
  have each (n : ℕ) : ∃ chance : (N).InformationHistory focal site.1 → ℝ,
      share n < 1 → (∀ history, 0 ≤ retained (fun _ => chance) n history) ∧
        (0 < ∑ history, retained (fun _ => chance) n history) ∧
        (∑ history, |((actual n).belief focal site history).toReal -
          retained (fun _ => chance) n history / ∑ next, retained (fun _ => chance) n next|) ≤
            2 * share n := by
    by_cases small : share n < 1
    · obtain ⟨chance, nonnegative, positive, close⟩ :=
        phaseTimingPlanPolicy_value_good_binding setup mode runtime leaks bounds runtimePlan
          horizon scheduler bound maximal fallback wellFormed (approximation.sequence n)
            (approximation.mixed n) finite (weights n) (noise n) (noisePositive n).le
              (by linarith [noiseSmall n]) (slotWeight n) (slotPositive n).le (slotBounded n)
                (actual n) (assembled n) (mixed n) (bayes n) focal site unflagged original trace
                  atSite active event clear request small
      exact ⟨chance, fun _ => ⟨fun history => (nonnegative history).1, positive, close⟩⟩
    · exact ⟨fun _ => 0, fun impossible => (small impossible).elim⟩
  choose chance bounds using each
  refine ⟨chance, smallEventually.mono (fun n small =>
    ⟨(bounds n small).1, (bounds n small).2.1⟩), ?_⟩
  have upper : ∀ᶠ n in Filter.atTop,
      (∑ history, |((actual n).belief focal site history).toReal -
        retained chance n history / ∑ next, retained chance n next|) ≤ 2 * share n :=
    smallEventually.mono fun n small => (bounds n small).2.2
  have upperLimit : Filter.Tendsto (fun n => 2 * share n) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _) upper upperLimit

end Vegas
