/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueBinding
import Vegas.Game.PhaseTimingOpeningResponse

/-! # Immutable source coordinates in the actual finite timing-plan policy -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

open Classical in
/-- At a nonexcluded played input the finite plan selects the canonical or
timing dispatcher independently of the source assessment. Both original raw
and slot tiers remain in the literal assembled response law. -/
theorem phaseTimingPlanPolicy_dispatch
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (played : some (past, view) ∈ (N).playedInformation who)
    (unflagged : ¬ PhasePublicExclusion setup mode runtime leaks (some (past, view))) :
    let uniform := ((menu).uniformPolicy initial horizon scheduler who
      (some (past, view))).map (fun choice => choice.1.getD ⟨none⟩)
    ∃ selected : Option (LateOption bounds.candidateCount),
      ∀ source : setup.commitRecoveryModel.BehavioralAssessment,
        phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
            fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
              slotNonnegative slotBounded plan who past view =
          mix noise noiseNonnegative noiseBounded uniform
            (mix slotWeight slotNonnegative slotBounded
              (phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed source who
                past view)
              (match selected with
              | none => phaseSourcePolicy setup mode runtime leaks bounds wellFormed source who
                  past view
              | some option => phaseSourceTimingPolicy setup mode runtime leaks bounds wellFormed
                  source option who past view)) := by
  intro uniform
  let agent : Agent := ⟨who, ⟨some (past, view), played⟩⟩
  have restricted (policy : (app).Policy)
      (covered : ∀ earlier observed response, response ∈ (policy earlier observed).support →
        response ∈ PhaseCount.onePacketActions runtime leaks bounds who earlier observed) :
      (((menu).restrictPolicy initial horizon scheduler who policy) (some (past, view))).map
          (fun choice => choice.1.getD ⟨none⟩) = policy past view := by
    have equality := congrArg (fun policy : (app).Policy => policy past view)
      ((menu).decode_restrictPolicy_of_covered initial horizon scheduler who policy covered)
    simpa only [ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
      ReactiveApplication.ResponseMenu.rawChoice, PMF.map_comp, Function.comp_def] using equality
  have notFree : ¬ isFree agent := unflagged
  by_cases keyed : isKeyed agent
  · let option := ownedKeyedIdentify (key := poolKey) ⟨keyed, notFree⟩ (plan (pool agent))
    refine ⟨some option, ?_⟩
    intro source
    rw [phaseTimingPlanPolicy_apply, dite_eq_left played, phaseTimingComponent,
      freeKeyedComponent_of_ownedKeyed _ _ _ ⟨keyed, notFree⟩]
    simp only [phaseSourceTimingComponent, mix_map, phaseSourceSlotStrategy,
      phaseSourceTimingStrategy]
    rw [restricted _ (phaseSourceSlotPolicy_covered setup mode runtime leaks bounds wellFormed
        source who),
      restricted _ (phaseSourceTimingPolicy_covered setup mode runtime leaks bounds wellFormed
        source _ who)]
  · refine ⟨none, ?_⟩
    intro source
    have prescribed (part : Parts (pool agent)) :
        phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
            wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative
              slotBounded agent part =
          phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
            wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative
              slotBounded who (some (past, view)) := by
      unfold phaseTimingComponent
      obtain ⟨identify, equality⟩ := freeKeyedComponent_of_not_free (free := isFree)
        (keyed := isKeyed) (key := poolKey) _ _ _ (agent := agent) notFree
      rw [equality part, keyedComponent_of_not_keyed _ _ (fun owned => keyed owned.1)]
    rw [phaseTimingPlanPolicy_apply, dite_eq_left played, prescribed]
    simp only [phaseSourcePerturbedStrategy, mix_map, phaseSourceSlotStrategy, phaseSourceStrategy]
    rw [restricted _ (phaseSourceSlotPolicy_covered setup mode runtime leaks bounds wellFormed
        source who),
      restricted _ (phaseSourcePolicy_covered setup mode runtime leaks bounds wellFormed source
        who)]

open Classical in
/-- A genuine clear binding callback has one source-independent selected
timing branch. The literal finite-plan policy retains its uniform raw tier,
slot tier, and original source choice before either encoder. -/
theorem phaseTimingPlanPolicy_binding_readout
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (execution : (app).Execution) {inputs}
    (valid : execution.application.Invariant inputs)
    (clear : execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (played : some (execution.recall who, execution.observe (app) who) ∈
      (N).playedInformation who) :
    let past := execution.recall who
    let view := execution.observe (app) who
    let uniform := ((menu).uniformPolicy initial horizon scheduler who
      (some (past, view))).map (fun choice => choice.1.getD ⟨none⟩)
    ∃ selected : Option (LateOption bounds.candidateCount),
      ∀ source : setup.commitRecoveryModel.BehavioralAssessment,
        phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
            fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
              slotNonnegative slotBounded plan who past view =
          mix noise noiseNonnegative noiseBounded uniform
            (mix slotWeight slotNonnegative slotBounded
              (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed source who
                event payload binding past view)
              (match selected with
              | none => phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed
                  source who event payload binding past view
              | some option => phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed
                  source who event payload binding option past view)) := by
  intro past view uniform
  have unflagged : ¬ PhasePublicExclusion setup mode runtime leaks (some (past, view)) := by
    rintro ⟨earlier, observed, equal, nonempty⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj equal)
    exact nonempty clear
  obtain ⟨selected, response⟩ := phaseTimingPlanPolicy_dispatch setup mode runtime leaks bounds
    initial horizon scheduler bound fallback wellFormed noise noiseNonnegative noiseBounded
      slotWeight slotNonnegative slotBounded plan who past view played unflagged
  refine ⟨selected, ?_⟩
  intro source
  rw [response, phaseSourceSlotPolicy_binding setup mode runtime leaks bounds wellFormed source
    execution valid who event payload binding request]
  clear response
  cases selected with
  | none =>
      dsimp only
      rw [phaseSourcePolicy_binding setup mode runtime leaks bounds wellFormed source
        execution valid who event payload binding request]
  | some option =>
      dsimp only
      rw [phaseSourceTimingPolicy_binding setup mode runtime leaks bounds wellFormed source option
        execution valid who event payload binding request]

open Classical in
/-- A genuine clear binding callback reads only the current source coordinate
of its immutable ordinary policy. This is the literal finite timing-plan
member, with its original uniform raw tier and selected pool part. -/
theorem phaseTimingPlanPolicy_value_binding_congr
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (first second : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (execution : (app).Execution) {inputs}
    (valid : execution.application.Invariant inputs)
    (clear : execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (played : some (execution.recall who, execution.observe (app) who) ∈
      (N).playedInformation who)
    (same : first (phaseSourceView? setup mode runtime leaks who event
      (execution.observe (app) who)) = second (phaseSourceView? setup mode runtime leaks who event
        (execution.observe (app) who))) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who first)
          noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
            (execution.recall who) (execution.observe (app) who) =
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who second)
          noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
            (execution.recall who) (execution.observe (app) who) := by
  obtain ⟨selected, response⟩ := phaseTimingPlanPolicy_binding_readout setup mode runtime leaks
    bounds initial horizon scheduler bound fallback wellFormed noise noiseNonnegative noiseBounded
      slotWeight slotNonnegative slotBounded plan who execution valid clear event payload binding
        request played
  rw [response, response]
  clear response
  let firstSource := setup.commitRecoveryValueAssessment wellFormed assessment who first
  let secondSource := setup.commitRecoveryValueAssessment wellFormed assessment who second
  have localLaw := phaseRecoveryValueAssessment_local setup wellFormed assessment who first
    second (phaseSourceView? setup mode runtime leaks who event (execution.observe (app) who)) same
  have slot : phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed firstSource who
      event payload binding (execution.recall who) (execution.observe (app) who) =
    phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed secondSource who event
      payload binding (execution.recall who) (execution.observe (app) who) := by
    unfold phaseRecoverySlotPolicy
    rw [localLaw]
  rw [slot]
  congr 1
  congr 1
  cases selected with
  | none =>
      dsimp only
      unfold phaseRecoveryBindingPolicy
      split
      · rfl
      · split
        · unfold phaseRecoveryBindingLaw
          rw [localLaw]
        · rfl
  | some option =>
      dsimp only
      unfold phaseRecoveryTimingPolicy phaseRecoveryTimingTaggedLaw
      rw [localLaw]

open Classical in
/-- The literal assembled member has the same silent atom for every original
source-value policy at an authentic clear binding callback. Raw noise is kept
at the same physical input and is not equated across different menus. -/
theorem phaseTimingPlanPolicy_value_silence_of_history
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (first second : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (control : (app).Control)
    (trace : ((app).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial runtimePlan (encodeInputs draw))
      horizon scheduler).Trace (some control)) {inputs}
    (valid : control.execution.application.Invariant inputs)
    (clear : control.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (played : some (control.execution.recall who, control.execution.observe (app) who) ∈
      (N).playedInformation who) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who first)
          noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
            (control.execution.recall who) (control.execution.observe (app) who) ⟨none⟩ =
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who second)
          noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
            (control.execution.recall who) (control.execution.observe (app) who) ⟨none⟩ := by
  obtain ⟨selected, response⟩ := phaseTimingPlanPolicy_binding_readout setup mode runtime leaks
    bounds initial horizon scheduler bound fallback wellFormed noise noiseNonnegative noiseBounded
      slotWeight slotNonnegative slotBounded plan who control.execution valid clear event payload
        binding request played
  rw [response, response]
  clear response
  let past := control.execution.recall who
  let view := control.execution.observe (app) who
  let firstSource := setup.commitRecoveryValueAssessment wellFormed assessment who first
  let secondSource := setup.commitRecoveryValueAssessment wellFormed assessment who second
  have slotAtom : phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed firstSource
      who event payload binding past view ⟨none⟩ =
    phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed secondSource who event
      payload binding past view ⟨none⟩ := by
    have equal := phaseRecoveryValueTimingPolicy_silence_of_history setup mode runtime leaks bounds
      runtimePlan maximal horizon scheduler trace who event payload binding request.2.2.1 clear
        wellFormed assessment mixed none 1 (by norm_num) le_rfl first second
    simpa only [mix_one] using equal
  have rest : (mix slotWeight slotNonnegative slotBounded
      (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed firstSource who event
        payload binding past view)
      (match selected with
      | none => phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed firstSource
          who event payload binding past view
      | some option => phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed
          firstSource who event payload binding option past view)) ⟨none⟩ =
    (mix slotWeight slotNonnegative slotBounded
      (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed secondSource who event
        payload binding past view)
      (match selected with
      | none => phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed secondSource
          who event payload binding past view
      | some option => phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed
          secondSource who event payload binding option past view)) ⟨none⟩ := by
    cases selected with
    | none =>
        dsimp only
        have canonical := phaseRecoveryValueBindingPolicy_silence setup mode runtime leaks bounds
          wellFormed assessment who first second event payload binding past view
        simp only [mix_apply, slotAtom]
        rw [canonical]
    | some option =>
        dsimp only
        exact phaseRecoveryValueTimingPolicy_silence_of_history setup mode runtime leaks bounds
          runtimePlan maximal horizon scheduler trace who event payload binding request.2.2.1 clear
            wellFormed assessment mixed option slotWeight slotNonnegative slotBounded first second
  rw [mix_apply]
  conv_rhs => rw [mix_apply]
  exact congrArg (fun atom => ENNReal.ofReal noise *
    (((menu).uniformPolicy initial horizon scheduler who
      (some (past, view))).map (fun choice => choice.1.getD ⟨none⟩)) ⟨none⟩ +
        ENNReal.ofReal (1 - noise) * atom) rest

open Classical in
/-- The actual finite assembly is covered at every raw input, including
inputs outside initialized histories and every fixed private plan. -/
theorem phaseTimingPlanPolicy_covered
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈ (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
        slotNonnegative slotBounded plan who past view).support) :
    response ∈ (menu).actions who past view := by
  exact (menu).decode_embedPolicy_covered initial horizon scheduler who _ past view response
    supported

open Classical in
/-- At an actual opening request the complete assembled finite-plan law does
not read the source assessment. Selected WAIT and raw noise remain unchanged. -/
theorem phaseTimingPlanPolicy_opening_congr
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (first second : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (execution : (app).Execution) {inputs}
    (valid : execution.application.Invariant inputs)
    (clear : execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (played : some (execution.recall who, execution.observe (app) who) ∈
      (N).playedInformation who) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed first noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded plan who (execution.recall who) (execution.observe (app) who) =
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed second noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded plan who (execution.recall who) (execution.observe (app) who) := by
  have unflagged : ¬ PhasePublicExclusion setup mode runtime leaks
      (some (execution.recall who, execution.observe (app) who)) := by
    rintro ⟨earlier, observed, equal, nonempty⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj equal)
    exact nonempty clear
  obtain ⟨selected, response⟩ := phaseTimingPlanPolicy_dispatch setup mode runtime leaks bounds
    initial horizon scheduler bound fallback wellFormed noise noiseNonnegative noiseBounded
      slotWeight slotNonnegative slotBounded plan who (execution.recall who)
        (execution.observe (app) who) played unflagged
  rw [response, response]
  clear response
  rw [phaseSourceSlotPolicy_opening setup mode runtime leaks bounds wellFormed first execution
      valid who event payload binding checks outputEq codeEq request,
    phaseSourceSlotPolicy_opening setup mode runtime leaks bounds wellFormed second execution
      valid who event payload binding checks outputEq codeEq request]
  congr 1
  congr 1
  cases selected with
  | none =>
      dsimp only
      exact (phaseSourcePolicy_opening setup mode runtime leaks bounds wellFormed first execution
        valid who event payload binding checks outputEq codeEq request).trans
          (phaseSourcePolicy_opening setup mode runtime leaks bounds wellFormed second execution
            valid who event payload binding checks outputEq codeEq request).symm
  | some option =>
      dsimp only
      cases option with
      | none => rfl
      | some serial =>
          rw [phaseSourceTimingPolicy_opening_eq_source setup mode runtime leaks bounds wellFormed
              first serial execution valid who event payload binding checks outputEq codeEq request,
            phaseSourceTimingPolicy_opening_eq_source setup mode runtime leaks bounds wellFormed
              second serial execution valid who event payload binding checks outputEq codeEq
                request]
          exact (phaseSourcePolicy_opening setup mode runtime leaks bounds wellFormed first
            execution valid who event payload binding checks outputEq codeEq request).trans
              (phaseSourcePolicy_opening setup mode runtime leaks bounds wellFormed second execution
                valid who event payload binding checks outputEq codeEq request).symm

end Vegas
