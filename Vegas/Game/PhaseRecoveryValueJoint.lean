/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValuePosterior
import Interaction.ReactiveMixtureExtraCoordinate
import Vegas.Game.CommitRecoveryValuePlan
import Interaction.ReactiveMixtureAtoms
import Vegas.Game.PhaseSourceRecordedPosition
import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseBindingIdleMenu
import Interaction.ReactiveRecordedResponse

/-! # Joint original timing and source coordinates at actual callbacks -/

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
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial runtimePlan)
  (PMF.map encodeInputs setup.initialLaw)
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
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- The actual finite timing-plan family retains its original current pool
weight even when each member carries arbitrary additional private memory.
The extra assessment can depend on that memory and is not averaged anew. -/
theorem phaseTimingPlanPolicy_pool_posterior {Other : Type}
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : Other → setup.commitRecoveryModel.BehavioralAssessment)
    (otherLaw : PMF Other) (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (played : some (past, view) ∈ (N).playedInformation who) :
    let agent : Agent := ⟨who, ⟨some (past, view), played⟩⟩
    let original := (independentProduct weights).bind fun plan => otherLaw.map (Prod.mk plan)
    let family := fun memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed (source memory.2) noise noiseNonnegative
        noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    (((app).policyMixture original family).posterior past).map
      (fun memory => memory.1 (pool agent)) = weights (pool agent) := by
  intro agent original family
  obtain ⟨remaining, equality⟩ := (app).policyMixture_posterior_coordinate_extra weights otherLaw
    family (pool agent) past (fun before entry recorded plan other part => by
      exact congrArg (fun law : PMF (app).Action => law entry.action)
        (phaseTimingPlanPolicy_unread setup mode runtime leaks bounds initial horizon scheduler
          bound fallback wellFormed (source other) noise noiseNonnegative noiseBounded slotWeight
            slotNonnegative slotBounded who past view played before entry recorded plan part))
  have projected := congrArg (PMF.map Prod.fst) equality
  have normalized := PMF.map_comp
    (fun memory => (memory.1 (pool agent),
      (fun p : {p // p ≠ pool agent} => memory.1 p.val, memory.2)))
    (((app).policyMixture original family).posterior past) Prod.fst
  exact normalized.symm.trans (projected.trans
    (bindPairLaw_map_fst (weights (pool agent)) (fun _ => remaining)))

open Classical in
/-- At a genuine clear unsent binding callback, the current part of the
ORIGINAL timing plan and current choice of the ORIGINAL global source policy
have their exact product law after the complete actual own recall. Other plan
and source coordinates keep their posterior and the original RAW tier remains. -/
theorem phaseTimingPlanPolicy_value_joint_of_history
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (active : control.actor = some who)
    (clear : control.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    : ∃ played : some (control.execution.recall who, control.execution.observe (app) who) ∈
      (N).playedInformation who,
    let agent : Agent := ⟨who, ⟨some (control.execution.recall who,
      control.execution.observe (app) who), played⟩⟩
    let view := phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe (app) who)
    let sourcePrior := setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who
    let original := (independentProduct weights).bind fun plan => sourcePrior.map (Prod.mk plan)
    let family := fun memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    (((app).policyMixture original family).posterior (control.execution.recall who)).map
        (fun memory => (memory.1 (pool agent), memory.2 view)) =
      (weights (pool agent)).bind fun part =>
        (setup.commitRecoveryNonmissingSourcePolicy wellFormed assessment.strategy who view).map
          (Prod.mk part) := by
  have running : ¬ ((menu).protocol initial horizon scheduler).terminal (some control) := by
    change ¬ (control.remaining = 0 ∧ control.actor = none)
    rintro ⟨_, absent⟩
    rw [active] at absent
    cases absent
  have played := (N).mem_playedInformation (who := who)
    (history := ⟨some control, trace⟩) running
  have observed : (N).infoOf who trace =
      some (control.execution.recall who, control.execution.observe (app) who) :=
    ((menu).info initial horizon scheduler who trace).trans (by
      simp only [ReactiveApplication.observe, active, ite_true])
  rw [observed] at played
  refine ⟨played, ?_⟩
  intro agent view sourcePrior original family
  obtain ⟨remaining, factor⟩ := phaseTimingPlanPolicy_value_posterior_of_history setup mode runtime
    leaks bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed
      finite noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
        (independentProduct weights) who control trace clear event payload binding request unsent
  have poolLaw := phaseTimingPlanPolicy_pool_posterior setup mode runtime leaks bounds runtimePlan
    horizon scheduler bound fallback wellFormed
      (fun member => setup.commitRecoveryValueAssessment wellFormed assessment who member)
        sourcePrior weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded who (control.execution.recall who) (control.execution.observe (app) who)
            played
  let current := setup.commitRecoveryNonmissingSourcePolicy wellFormed assessment.strategy who view
  have marginal := congrArg (PMF.map fun pair => pair.2.1 (pool agent)) factor
  have remainingLaw : remaining.map (fun rest => rest.1 (pool agent)) = weights (pool agent) := by
    have equal : (((app).policyMixture original family).posterior
        (control.execution.recall who)).map (fun memory => memory.1 (pool agent)) =
          remaining.map (fun rest => rest.1 (pool agent)) := by
      simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, PMF.bind_const] using marginal
    exact equal.symm.trans poolLaw
  have joint := congrArg (PMF.map fun pair => (pair.2.1 (pool agent), pair.1)) factor
  have equal : (((app).policyMixture original family).posterior
      (control.execution.recall who)).map
      (fun memory => (memory.1 (pool agent), memory.2 view)) =
        current.bind (fun choice => remaining.map fun rest => (rest.1 (pool agent), choice)) := by
    simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def] using joint
  apply equal.trans
  calc
    _ = current.bind (fun choice => (weights (pool agent)).map fun part => (part, choice)) := by
      apply congrArg (PMF.bind current)
      funext choice
      rw [← remainingLaw]
      exact (PMF.map_comp (fun rest => rest.1 (pool agent)) remaining
        (fun part => (part, choice))).symm
    _ = _ := by
      exact PMF.bind_comm current (weights (pool agent))
        (fun choice part => PMF.pure (part, choice))

open Classical in
/-- With positive original RAW noise every fixed finite timing-plan member
supports the entire actual counted own recall. This includes arbitrary raw
preparations and aliases and supplies consistency rather than assuming it. -/
theorem phaseTimingPlanPolicy_consistent_of_history
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (positive : 0 < noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player) (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control)) :
    (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
      fallback wellFormed source noise positive.le noiseBounded slotWeight slotNonnegative
        slotBounded plan who).Consistent (control.execution.recall who) := by
  let policy := phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
    bound fallback wellFormed source noise positive.le noiseBounded slotWeight slotNonnegative
      slotBounded plan who
  have supported (earlier : List (app).PlayerEntry) (entry : (app).PlayerEntry)
      (recorded : earlier ++ [entry] <+: control.execution.recall who) :
      entry.action ∈ (policy earlier entry.beforeView).support := by
    obtain ⟨later, equal⟩ := recorded
    have recalled : control.execution.recall who = earlier ++ entry :: later := by
      simpa only [List.append_assoc, List.singleton_append] using equal.symm
    obtain ⟨before, prior, _prefix, active, pastEq, viewed, allowed⟩ :=
      (menu).recorded_response_at initial horizon scheduler control trace who earlier entry later
        recalled
    have running : ¬ ((menu).protocol initial horizon scheduler).terminal (some before) := by
      change ¬ (before.remaining = 0 ∧ before.actor = none)
      rintro ⟨_, absent⟩
      rw [active] at absent
      cases absent
    have played := (N).mem_playedInformation (who := who)
      (history := ⟨some before, prior⟩) running
    have observed : (N).infoOf who prior =
        some (before.execution.recall who, before.execution.observe (app) who) :=
      ((menu).info initial horizon scheduler who prior).trans (by
        simp only [ReactiveApplication.observe, active, ite_true])
    rw [observed, pastEq, ← viewed] at played
    rw [← viewed] at allowed
    let choice : (N).Choice who (some (earlier, entry.beforeView)) :=
      ⟨some entry.action, entry.action, allowed, rfl⟩
    let agent : Agent := ⟨who, ⟨some (earlier, entry.beforeView), played⟩⟩
    change entry.action ∈ (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source noise positive.le noiseBounded slotWeight
        slotNonnegative slotBounded plan who earlier entry.beforeView).support
    rw [phaseTimingPlanPolicy_apply, dite_eq_left played, PMF.support_map]
    refine ⟨choice, ?_, rfl⟩
    exact phaseTimingComponent_fullSupport setup mode runtime leaks bounds initial horizon scheduler
      bound wellFormed source noise positive noiseBounded slotWeight slotNonnegative slotBounded
        agent (plan (pool agent)) choice
  have consistent (past : List (app).PlayerEntry) :
      past <+: control.execution.recall who → policy.Consistent past := by
    induction past using List.reverseRecOn with
    | nil => intro _; exact .nil
    | append_singleton past entry ih =>
        intro inside
        exact .snoc entry (ih ((List.prefix_append past [entry]).trans inside))
          (supported past entry inside)
  exact consistent _ (List.prefix_refl _)

end Vegas
