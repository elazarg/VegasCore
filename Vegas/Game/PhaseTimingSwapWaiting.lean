/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingSwapSilence
import Vegas.Game.PhaseTimingPoolPlan
import Vegas.Game.PhaseTimingKeyProperties
import Vegas.Game.PhaseTimingRawMixture
import Vegas.Game.PhaseTimingValueNoise
import GameTheoryExtensions.Analysis.Protocol.FreeKeyedPoolObservation

/-! # One full timing plan at swapped actual binding callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

private theorem silence_atom_map {Owner : Type} (application : ReactiveApplication Owner)
    (law : PMF application.Action) :
    (law.map (fun response => response.transmission.isNone)) true = law ⟨none⟩ := by
  classical
  have preimage (response : application.Action) :
      true = response.transmission.isNone ↔ response = ⟨none⟩ := by
    rcases response with ⟨transmission⟩
    cases transmission <;> simp
  simp only [PMF.map_apply, preimage, tsum_ite_eq]

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State)
  (initialLaw : initial = setup.initialLaw.map
    (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    initial horizon scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    initial horizon scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent =>
  PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent =>
  PhaseUnprotected runtime leaks bound (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

private theorem binding_played (remaining : Nat) (who : Player) (execution : (app).Execution)
    (trace : (E).Trace (some ⟨remaining, some who, execution⟩)) :
    some (execution.recall who, execution.observe app who) ∈ (N).playedInformation who := by
  have present := (N).mem_playedInformation (who := who)
    (history := ⟨some ⟨remaining, some who, execution⟩, trace⟩)
    (by change ¬ (remaining = 0 ∧ some who = none); simp)
  change ((menu).signals initial horizon scheduler).infoOf who trace ∈ _ at present
  rw [(menu).info initial horizon scheduler who trace] at present
  simpa only [ReactiveApplication.observe, ↓reduceIte] using present

private theorem plan_noise_split (fallback : ∀ owner, (N).Policy owner)
    (wellFormed : setup.WellFormed) (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (played : some (past, view) ∈ (N).playedInformation who) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound fallback
        wellFormed source noise nonnegative bounded slotWeight slotNonnegative slotBounded parts who
          past view =
      mix noise nonnegative bounded
        (((menu).uniformPolicy initial horizon scheduler who (some (past, view))).map
          (fun choice => choice.1.getD ⟨none⟩))
        (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source 0 (by norm_num) (by norm_num) slotWeight slotNonnegative
            slotBounded parts who past view) := by
  rw [phaseTimingPlanPolicy_apply, dite_eq_left played,
    phaseTimingPlanPolicy_apply, dite_eq_left played, phaseTimingComponent_raw_mixture, mix_map]

private theorem plan_silent_atom (fallback : ∀ owner, (N).Policy owner)
    (wellFormed : setup.WellFormed) (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (played : some (past, view) ∈ (N).playedInformation who)
    (silent : (N).Choice who (some (past, view))) (selected : silent.1 = some ⟨none⟩) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound fallback
        wellFormed source noise nonnegative bounded slotWeight slotNonnegative slotBounded parts
          who past view ⟨none⟩ =
      (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed source noise nonnegative bounded slotWeight slotNonnegative slotBounded
          ⟨who, ⟨some (past, view), played⟩⟩
            (parts (pool ⟨who, ⟨some (past, view), played⟩⟩))) silent := by
  have injective : Function.Injective (fun choice : (N).Choice who (some (past, view)) =>
      choice.1.getD ⟨none⟩) := by
    intro first second same
    obtain ⟨firstAction, _firstLegal, firstEq⟩ := first.2
    obtain ⟨secondAction, _secondLegal, secondEq⟩ := second.2
    apply Subtype.ext
    simpa only [firstEq, secondEq, Option.getD_some, Option.some.injEq] using same
  rw [phaseTimingPlanPolicy_apply, dite_eq_left played]
  have atom := pmf_map_apply_of_injective
    (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
      wellFormed source noise nonnegative bounded slotWeight slotNonnegative slotBounded
        ⟨who, ⟨some (past, view), played⟩⟩
          (parts (pool ⟨who, ⟨some (past, view), played⟩⟩))) injective silent
  simp only [selected, Option.getD_some] at atom
  convert! atom using 1

include initialLaw in
private theorem plan_value_silence_base
    [setup.FiniteInitialLaw]
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : ∀ owner, (N).Policy owner) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (finite : setup.program.FiniteBindingTypes)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p) (who : Player)
    (member : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (current : (app).Control) (trace : (E).Trace (some current))
    (acting : current.actor = some who) (clear : current.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : current.execution.application.SeedRequest who
      ⟨current.execution.application.attempt, event⟩) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound fallback
        wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who member)
          noise nonnegative bounded slotWeight slotNonnegative slotBounded parts who
            (current.execution.recall who) (current.execution.observe app who) ⟨none⟩ =
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound fallback
        wellFormed assessment noise nonnegative bounded slotWeight slotNonnegative slotBounded
          parts who (current.execution.recall who) (current.execution.observe app who) ⟨none⟩ := by
  subst initial
  let initial := setup.initialLaw.map
    (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
  let currentModel := ReactiveApplication.ResponseMenu.information
    (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
  classical
  rcases current with ⟨remaining, actor, execution⟩
  change actor = some who at acting
  subst actor
  have played := binding_played setup mode runtime leaks bounds _ horizon scheduler remaining
    who execution trace
  let silent : (currentModel).Choice who (some (execution.recall who, execution.observe app who)) :=
    ⟨some ⟨none⟩, ⟨⟨none⟩, PhaseCount.silence_onePacket runtime leaks bounds who _ _, rfl⟩⟩
  have scalar := phaseTimingComponent_value_silent_base setup mode runtime leaks bounds plan
    horizon scheduler bound maximal fallback wellFormed assessment mixed finite noise nonnegative
      bounded slotWeight slotNonnegative slotBounded parts who member
        ⟨remaining, some who, execution⟩ trace rfl clear event payload binding request played
          silent rfl
  rw [plan_silent_atom setup mode runtime leaks bounds _ horizon scheduler bound fallback
    wellFormed _ noise nonnegative bounded slotWeight slotNonnegative slotBounded parts who _ _
      played silent rfl,
    plan_silent_atom setup mode runtime leaks bounds _ horizon scheduler bound fallback
      wellFormed _ noise nonnegative bounded slotWeight slotNonnegative slotBounded parts who _ _
        played silent rfl]
  exact scalar

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
      setup.commitRecoveryContinuingChoice)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
  (swap : HiddenSwap (serviceGraph setup mode)) (remaining : Nat) (who : Player)
  (original : (phaseApplication runtime leaks).Execution)
  (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    initial horizon scheduler).Trace (some ⟨remaining, some who, original⟩))
  (swappedTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    initial horizon scheduler).Trace (some ⟨remaining, some who, swap.phaseExecution original⟩))
  (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
  (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
  (request : original.application.SeedRequest who ⟨original.application.attempt, event⟩)
  (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (original.recall who),
    PhaseCount.event? message.payload ≠ some ⟨original.application.attempt, event⟩)
  (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
  (clear : original.application.current.excluded = ∅)

include initialLaw maximal capacity trace swappedTrace binding request unsent values clear in
/-- The same actual full timing plan has identical NON-RAW binding WAIT mass
across a hidden swap that may alter original private inputs. Current keys,
pools and selected timing options are derived from the actual histories. -/
theorem phaseTimingPlanPolicy_binding_residual_silence_swap
    (fallback : ∀ owner, (N).Policy owner)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p) :
    (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound fallback
      wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
        slotNonnegative slotBounded parts who (original.recall who) (original.observe app who)).map
          (fun response => response.transmission.isNone) =
      (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
      fallback
        wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
          slotNonnegative slotBounded parts who ((swap.phaseExecution original).recall who)
            ((swap.phaseExecution original).observe app who)).map
              (fun response => response.transmission.isNone) := by
  subst initial
  let initial := setup.initialLaw.map
    (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
  let currentModel := ReactiveApplication.ResponseMenu.information
    (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
  let currentAgent := InformationModel.InformationAgent currentModel
    (InformationModel.playedInformation currentModel)
  let currentFree := fun agent : currentAgent =>
    PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent))
  let currentKeyed := fun agent : currentAgent =>
    PhaseUnprotected runtime leaks bound (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
  let currentPoolKey := fun agent : currentAgent => phaseTimingKey runtime leaks
    (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
  let currentPool := phaseTimingPool setup mode runtime leaks bounds initial horizon
    scheduler bound
  classical
  have firstPlayed := binding_played setup mode runtime leaks bounds _ horizon scheduler
    remaining who original trace
  have secondPlayed := binding_played setup mode runtime leaks bounds _ horizon scheduler
    remaining who (swap.phaseExecution original) swappedTrace
  let first : currentAgent := ⟨who, ⟨_, firstPlayed⟩⟩
  let second : currentAgent := ⟨who, ⟨_, secondPlayed⟩⟩
  have firstNotFree : ¬ currentFree first := by
    rintro ⟨past, view, equal, excluded⟩
    cases Option.some.inj equal
    exact excluded clear
  have secondNotFree : ¬ currentFree second := by
    rintro ⟨past, view, equal, excluded⟩
    cases Option.some.inj equal
    exact excluded clear
  have sameKey : currentPoolKey first = currentPoolKey second :=
    (phaseTimingKey_swap_at_binding runtime leaks swap
      (serviceGraph_revealRelaxedOrdered setup mode) original who event payload binding
      request).symm
  have classified : currentKeyed first ↔ currentKeyed second :=
    phaseUnprotected_iff_of_timingKey_eq runtime leaks bound who _ _ _ _ sameKey
  have samePool : currentPool first = currentPool second :=
    freeKeyedPool_eq_of_not_free firstNotFree secondNotFree classified sameKey
  have secondUnsent : ∀ message ∈ (app).outputs ((swap.phaseExecution original).recall who),
      PhaseCount.event? message.payload ≠ some ⟨original.application.attempt, event⟩ := by
    change ∀ message ∈ (app).outputs ((original.recall who).map swap.phaseEntry), _
    rw [swap.phaseOutputs_entry]
    exact unsent
  have paired := phaseSourceMixture_silence_eq_of_history setup mode runtime leaks bounds plan
    horizon scheduler finite wellFormed target approximation maximal n capacity who event payload
      binding ⟨remaining, some who, original⟩ ⟨remaining, some who, swap.phaseExecution original⟩
        trace swappedTrace rfl rfl request request unsent secondUnsent values clear clear
  have prescribedSame :
      (phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
        wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
          slotNonnegative slotBounded who first.2.1).map
            (fun choice => (choice.1.getD ⟨none⟩).transmission.isNone) =
      (phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
        wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
          slotNonnegative slotBounded who second.2.1).map
            (fun choice => (choice.1.getD ⟨none⟩).transmission.isNone) := by
    simpa only [phaseSourcePerturbedStrategy, mix_zero] using
      (paired.2.2 slotWeight slotNonnegative slotBounded).1
  have slotSame := (paired.2.2 1 (by norm_num) le_rfl).1
  simp only [mix_one] at slotSame
  have keyedSame (option : LateOption bounds.candidateCount) :
      (phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon scheduler
        wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
          slotNonnegative slotBounded who first.2.1 option).map
            (fun choice => (choice.1.getD ⟨none⟩).transmission.isNone) =
      (phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon scheduler
        wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
          slotNonnegative slotBounded who second.2.1 option).map
            (fun choice => (choice.1.getD ⟨none⟩).transmission.isNone) := by
    have sourceSame := phaseSourceTimingPolicy_binding_silence_swap setup mode runtime leaks bounds
      plan horizon scheduler finite wellFormed target approximation maximal n swap remaining who
        original trace swappedTrace event payload binding request unsent values clear option
    have timingSame :
        (phaseSourceTimingStrategy setup mode runtime leaks bounds wellFormed
          (approximation.sequence n) initial horizon scheduler option who first.2.1).map
            (fun choice => (choice.1.getD ⟨none⟩).transmission.isNone) =
        (phaseSourceTimingStrategy setup mode runtime leaks bounds wellFormed
          (approximation.sequence n) initial horizon scheduler option who second.2.1).map
            (fun choice => (choice.1.getD ⟨none⟩).transmission.isNone) := by
      have left := phaseSourceTimingStrategy_map_val setup mode runtime leaks bounds wellFormed
        (approximation.sequence n) initial horizon scheduler option who (original.recall who)
          (original.observe app who)
      have right := phaseSourceTimingStrategy_map_val setup mode runtime leaks bounds wellFormed
        (approximation.sequence n) initial horizon scheduler option who
          ((swap.phaseExecution original).recall who) ((swap.phaseExecution original).observe
      app who)
      have mapLeft := congrArg (fun law : PMF (Option (app).Action) => law.map
        (fun action => (action.getD ⟨none⟩).transmission.isNone)) left
      have mapRight := congrArg (fun law : PMF (Option (app).Action) => law.map
        (fun action => (action.getD ⟨none⟩).transmission.isNone)) right
      simp only [PMF.map_comp, Function.comp_def, Option.getD_some] at mapLeft mapRight
      exact mapLeft.trans (sourceSame.trans mapRight.symm)
    simp only [phaseSourceTimingComponent, mix_zero, mix_map]
    rw [slotSame, timingSame]
  have components := bind_freeKeyedComponent_map_eq_of_not_free
    (Outcome := Bool) (free := currentFree) (keyed := currentKeyed) (key := currentPoolKey)
    (fun (agent : currentAgent) choice => mix 0 (by norm_num) (by norm_num)
      ((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1) (PMF.pure choice))
    (fun agent => phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
        slotNonnegative slotBounded agent.1 agent.2.1)
    (fun agent option => phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon
      scheduler wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
        slotNonnegative slotBounded agent.1 agent.2.1 option)
    (fun p => PMF.pure (parts p))
    (fun (agent : currentAgent) (choice : (currentModel).Choice agent.1 agent.2.1) =>
      (choice.1.getD ⟨none⟩).transmission.isNone)
    first second firstNotFree samePool prescribedSame keyedSame
  simpa only [PMF.pure_bind, phaseTimingPlanPolicy_apply, dite_eq_left firstPlayed,
    dite_eq_left secondPlayed, PMF.map_comp, Function.comp_def, phaseTimingComponent,
      phaseTimingPool] using components

include initialLaw maximal capacity trace swappedTrace binding request unsent values clear in
/-- Actual binding WAIT atoms under one full timing plan differ only through
the explicit RAW menu draw. The near-one relative bound allows different raw
menu cardinalities and original private inputs, with no likelihood premise. -/
theorem phaseTimingPlanPolicy_binding_waiting_swap_of_floor
    (fallback : ∀ owner, (N).Policy owner)
    (floor : ℝ) (floorPositive : 0 < floor)
    (floored : ∀ (owner : Player) (site : setup.commitRecoveryModel.InformationSite owner)
      (choice : setup.commitRecoveryModel.Choice owner site.1),
      floor ≤ ((approximation.sequence n).strategy owner site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p) :
    let first := phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
      bound fallback wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le
        slotWeight slotPositive.le slotBounded parts who (original.recall who)
          (original.observe app who)
    let second := phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
      bound fallback wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le
        slotWeight slotPositive.le slotBounded parts who ((swap.phaseExecution original).recall who)
          ((swap.phaseExecution original).observe app who)
    let firstRaw := ((menu).uniformPolicy initial horizon scheduler who
      (some (original.recall who, original.observe app who))).map
        (fun choice => choice.1.getD ⟨none⟩)
    let secondRaw := ((menu).uniformPolicy initial horizon scheduler who
      (some ((swap.phaseExecution original).recall who,
        (swap.phaseExecution original).observe app who))).map (fun choice => choice.1.getD ⟨none⟩)
    let coefficient := 1 + noise / ((1 - noise) * (slotWeight * floor))
    (first ⟨none⟩).toReal - (second ⟨none⟩).toReal = noise *
      ((firstRaw ⟨none⟩).toReal - (secondRaw ⟨none⟩).toReal) ∧
      (1 - noise) * (slotWeight * floor) ≤ (first ⟨none⟩).toReal ∧
      (1 - noise) * (slotWeight * floor) ≤ (second ⟨none⟩).toReal ∧
      (first ⟨none⟩).toReal ≤ coefficient * (second ⟨none⟩).toReal ∧
      (second ⟨none⟩).toReal ≤ coefficient * (first ⟨none⟩).toReal := by
  subst initial
  let initial := setup.initialLaw.map
    (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
  let currentModel := ReactiveApplication.ResponseMenu.information
    (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
  let currentAgent := InformationModel.InformationAgent currentModel
    (InformationModel.playedInformation currentModel)
  let currentPool := phaseTimingPool setup mode runtime leaks bounds initial horizon
    scheduler bound
  classical
  intro first second firstRaw secondRaw coefficient
  have firstPlayed := binding_played setup mode runtime leaks bounds _ horizon scheduler
    remaining who original trace
  have secondPlayed := binding_played setup mode runtime leaks bounds _ horizon scheduler
    remaining who (swap.phaseExecution original) swappedTrace
  let firstMain := phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
    bound fallback wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
      slotPositive.le slotBounded parts who (original.recall who) (original.observe app who)
  let secondMain := phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
    bound fallback wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
      slotPositive.le slotBounded parts who ((swap.phaseExecution original).recall who)
        ((swap.phaseExecution original).observe app who)
  have sameLaw := phaseTimingPlanPolicy_binding_residual_silence_swap setup mode runtime leaks
    bounds plan _ rfl horizon scheduler bound finite wellFormed target approximation maximal n
      capacity
      swap remaining who original trace swappedTrace event payload binding request unsent values
        clear fallback slotWeight slotPositive.le slotBounded parts
  have same : firstMain ⟨none⟩ = secondMain ⟨none⟩ := by
    have atom := congrArg (fun law : PMF Bool => law true) sameLaw
    simpa only [silence_atom_map] using atom
  let secondAgent : currentAgent := ⟨who, ⟨_, secondPlayed⟩⟩
  have secondUnsent : ∀ message ∈ (app).outputs ((swap.phaseExecution original).recall who),
      PhaseCount.event? message.payload ≠ some ⟨original.application.attempt, event⟩ := by
    change ∀ message ∈ (app).outputs ((original.recall who).map swap.phaseEntry), _
    rw [swap.phaseOutputs_entry]
    exact unsent
  obtain ⟨silent, silentEq, lower, _lowerNoisy, _upperNoisy⟩ :=
    phaseTimingComponent_silence_noise_comparison setup mode runtime leaks bounds plan horizon
      scheduler bound finite wellFormed target approximation maximal n capacity floor floorPositive
        floored noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded secondAgent
          (PMF.pure (parts (currentPool secondAgent)))
            ⟨remaining, some who, swap.phaseExecution original⟩
            swappedTrace rfl rfl event payload binding request secondUnsent values clear
  simp only [PMF.pure_bind] at lower
  have lowerSecond : slotWeight * floor ≤ (secondMain ⟨none⟩).toReal := by
    rw [plan_silent_atom setup mode runtime leaks bounds _ horizon scheduler bound fallback
      wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
        slotPositive.le slotBounded parts who _ _ secondPlayed silent silentEq]
    exact lower
  have lowerFirst : slotWeight * floor ≤ (firstMain ⟨none⟩).toReal := by
    rw [same]
    exact lowerSecond
  have firstSplit : first = mix noise noiseNonnegative noiseSmall.le firstRaw firstMain :=
    plan_noise_split setup mode runtime leaks bounds _ horizon scheduler bound fallback
      wellFormed
      (approximation.sequence n) noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le
        slotBounded parts who _ _ firstPlayed
  have secondSplit : second = mix noise noiseNonnegative noiseSmall.le secondRaw secondMain :=
    plan_noise_split setup mode runtime leaks bounds _ horizon scheduler bound fallback
      wellFormed
      (approximation.sequence n) noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le
        slotBounded parts who _ _ secondPlayed
  have forward := waiting_mix_ratio firstRaw secondRaw firstMain secondMain ⟨none⟩ ⟨none⟩ same
    (slotWeight * floor) noise (mul_pos slotPositive floorPositive) noiseNonnegative noiseSmall
      lowerSecond
  have backward := waiting_mix_ratio secondRaw firstRaw secondMain firstMain ⟨none⟩ ⟨none⟩ same.symm
    (slotWeight * floor) noise (mul_pos slotPositive floorPositive) noiseNonnegative noiseSmall
      lowerFirst
  rw [← firstSplit, ← secondSplit] at forward backward
  exact ⟨forward.1, backward.2.1, forward.2.1, forward.2.2, backward.2.2⟩

include initialLaw maximal capacity trace swappedTrace binding request unsent values clear in
/-- Independently predrawn sparse source-value members retain the SAME base
waiting comparison under a genuine hidden swap and one original full plan.
No full-mixing premise is imposed on either immutable member. -/
theorem phaseTimingPlanPolicy_value_binding_waiting_swap_of_floor
    [setup.FiniteInitialLaw]
    (fallback : ∀ owner, (N).Policy owner)
    (floor : ℝ) (floorPositive : 0 < floor)
    (floored : ∀ (owner : Player) (site : setup.commitRecoveryModel.InformationSite owner)
      (choice : setup.commitRecoveryModel.Choice owner site.1),
      floor ≤ ((approximation.sequence n).strategy owner site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p)
    (firstMember secondMember : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who) :
    let first := phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
      bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed (approximation.sequence n) who firstMember)
          noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le slotBounded parts who
            (original.recall who) (original.observe app who)
    let second := phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
      bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed (approximation.sequence n) who secondMember)
          noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le slotBounded parts who
            ((swap.phaseExecution original).recall who) ((swap.phaseExecution original).observe
              app who)
    let coefficient := 1 + noise / ((1 - noise) * (slotWeight * floor))
    (1 - noise) * (slotWeight * floor) ≤ (first ⟨none⟩).toReal ∧
      (1 - noise) * (slotWeight * floor) ≤ (second ⟨none⟩).toReal ∧
      (first ⟨none⟩).toReal ≤ coefficient * (second ⟨none⟩).toReal ∧
      (second ⟨none⟩).toReal ≤ coefficient * (first ⟨none⟩).toReal := by
  subst initial
  intro first second coefficient
  have firstScalar := plan_value_silence_base setup mode runtime leaks bounds plan _ rfl horizon
    scheduler bound maximal fallback wellFormed (approximation.sequence n) (approximation.mixed n)
      finite noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le slotBounded parts who
        firstMember ⟨remaining, some who, original⟩ trace rfl clear event payload binding request
  have secondScalar := plan_value_silence_base setup mode runtime leaks bounds plan _ rfl horizon
    scheduler bound maximal fallback wellFormed (approximation.sequence n) (approximation.mixed n)
      finite noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le slotBounded parts who
        secondMember ⟨remaining, some who, swap.phaseExecution original⟩ swappedTrace rfl clear
          event payload binding request
  have compared := phaseTimingPlanPolicy_binding_waiting_swap_of_floor setup mode runtime leaks
    bounds plan _ rfl horizon scheduler bound finite wellFormed target approximation maximal n
      capacity
      swap remaining who original trace swappedTrace event payload binding request unsent values
        clear fallback floor floorPositive floored noise noiseNonnegative noiseSmall slotWeight
          slotPositive slotBounded parts
  rw [firstScalar, secondScalar]
  exact compared.2

end Vegas
