/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueCallback
import GameTheoryExtensions.Analysis.Protocol.StoppedKernelComparison

/-! # Exact assembled stopped laws from original global private policies -/

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
/-- The SAME original global source-policy and per-owner timing-plan
implementations give exactly the assembled physical history law up to first
public exclusion. The entire original history and entry correlation remain. -/
theorem phaseTimingPlanPolicy_value_stopped_law
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (extra : ((menu).protocol initial horizon scheduler).History → Prop)
    (start : ((menu).protocol initial horizon scheduler).History) :
    let priors := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let members := fun who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let players := fun who => ((app).policyMixture (priors who) (members who)).policy
    let first := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let profile := (N).agentBehavior (N).playedInformation fallback (fun agent =>
      (weights (pool agent)).bind (phaseTimingComponent setup mode runtime leaks bounds initial
        horizon scheduler bound wellFormed assessment noise noiseNonnegative noiseBounded
          slotWeight slotNonnegative slotBounded agent))
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      extra history ∨ match history.state with
        | none => False
        | some current => current.execution.application.current.excluded ≠ ∅
    (N).runBehavioralUntil certificate first stopped start =
      (N).runBehavioralUntil certificate profile stopped start := by
  intro priors members players first profile stopped
  let target := (menu).decodeProfile initial horizon scheduler profile
  let second := fun who => (menu).restrictPolicy initial horizon scheduler who (target who)
  let E := (menu).protocol initial horizon scheduler
  have callbacks (history : E.History) (running : ¬ stopped history) (who : Player) :
      first who ((N).infoOf who history.trace) =
        second who ((N).infoOf who history.trace) := by
    rcases history with ⟨state, trace⟩
    cases state with
    | none =>
        have info := (menu).info initial horizon scheduler who trace
        change (N).infoOf who trace = none at info
        rw [info]
        rfl
    | some control =>
        have clear : control.execution.application.current.excluded = ∅ := by
          by_contra excluded
          exact running (Or.inr excluded)
        have observed := (menu).info initial horizon scheduler who trace
        change (N).infoOf who trace = (app).observe who (some control) at observed
        by_cases active : control.actor = some who
        · have info : (N).infoOf who trace = some (control.execution.recall who,
              control.execution.observe (app) who) := by
            simpa only [ReactiveApplication.observe, active, ite_true] using observed
          rw [info]
          have law := phaseTimingPlanPolicy_value_callback_of_history setup mode runtime leaks
            bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed
              finite weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative
                slotBounded who control trace active clear
          change players who (control.execution.recall who)
              (control.execution.observe (app) who) =
            target who (control.execution.recall who) (control.execution.observe (app) who) at law
          change (menu).restrictPolicy initial horizon scheduler who (players who)
              (some (control.execution.recall who, control.execution.observe (app) who)) =
            (menu).restrictPolicy initial horizon scheduler who (target who)
              (some (control.execution.recall who, control.execution.observe (app) who))
          have targetCovered := (menu).decode_embedPolicy_covered initial horizon scheduler who
            (profile who) (control.execution.recall who) (control.execution.observe (app) who)
          have firstCovered : ∀ action ∈ (players who (control.execution.recall who)
              (control.execution.observe (app) who)).support,
              action ∈ (menu).actions who (control.execution.recall who)
                (control.execution.observe (app) who) := by
            rw [law]
            exact targetCovered
          apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
          rw [(menu).restrictPolicy_map_val initial horizon scheduler who (players who) _ _
            firstCovered, (menu).restrictPolicy_map_val initial horizon scheduler who (target who)
              _ _ targetCovered]
          exact congrArg (PMF.map some) law
        · have info : (N).infoOf who trace = none := by
            simpa only [ReactiveApplication.observe, active, ite_false] using observed
          rw [info]
          rfl
  have step : ∀ left right : E.History, left = right → ¬ stopped left →
      ¬ E.terminal left.state →
      ∃ joint : PMF (E.History × E.History),
        joint.map Prod.fst = (N).runBehavioralFrom first 1 left ∧
        joint.map Prod.snd = (N).runBehavioralFrom second 1 right ∧
        ∀ next ∈ joint.support, next.1 = next.2 := by
    intro history _ equal running notTerminal
    subst equal
    have agreement := (N).behavioralJoint_congr history.trace notTerminal
      (callbacks history running)
    have laws : (N).runBehavioralFrom first 1 history =
        (N).runBehavioralFrom second 1 history := by
      rw [(N).runBehavioralFrom_succ_of_not_terminal first 0 notTerminal,
        (N).runBehavioralFrom_succ_of_not_terminal second 0 notTerminal, agreement]
      rfl
    refine ⟨((N).runBehavioralFrom first 1 history).map (fun next => (next, next)), ?_, ?_, ?_⟩
    · rw [PMF.map_comp]
      exact PMF.map_id _
    · rw [PMF.map_comp]
      exact (PMF.map_id _).trans laws
    · intro pair member
      obtain ⟨next, _actual, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
      rfl
  have result := (N).runBehavioralUntil_map_eq_of_paired_steps (N) certificate certificate
    first second stopped stopped id id Eq (by rintro _ _ rfl; rfl)
      (by rintro _ _ rfl _; rfl) step start start rfl
  have retract : second = profile := by
    funext who
    exact (menu).restrict_decode_embedPolicy initial horizon scheduler who (profile who)
  rw [← retract]
  simpa only [PMF.map_id] using result

end Vegas
