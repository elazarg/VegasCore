/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueRecall
import Vegas.Game.CommitRecoveryValuePlan
import Interaction.ReactiveMixtureAtoms
import Vegas.Game.PhaseSourceRecordedPosition
import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseBindingIdleMenu
import Interaction.ReactiveRecordedResponse

/-! # Actual own-recall posterior of the original global source policy -/

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

open Classical in
/-- At an actual clear unsent binding callback the current coordinate of the
ORIGINAL global source policy retains its source law independently of the
updated entire timing plan and every other source coordinate. Actual recalled
raw responses are retained; no independent per-entry source prior is drawn. -/
theorem phaseTimingPlanPolicy_value_posterior_of_history
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (planLaw : PMF ((p : Pool) → Parts p)) (who : Player)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩) :
    let view := phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe (app) who)
    let sourcePrior := setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who
    let original := planLaw.bind fun plan => sourcePrior.map (Prod.mk plan)
    let family := fun memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    ∃ remainder : PMF (((p : Pool) → Parts p) ×
        ((other : {other // other ≠ view}) → (setup.informationModel
          (CommitmentInterface.forfeiture setup.program)).Choice who other.val)),
      (((app).policyMixture original family).posterior (control.execution.recall who)).map
          (fun memory => (memory.2 view,
            (memory.1, fun other : {other // other ≠ view} => memory.2 other.val))) =
        (setup.commitRecoveryNonmissingSourcePolicy wellFormed assessment.strategy who view).bind
          (fun choice => remainder.map (Prod.mk choice)) := by
  intro view sourcePrior original family
  let choices := fun point : setup.ProtocolView who => (setup.informationModel
    (CommitmentInterface.forfeiture setup.program)).Choice who point
  let split := Equiv.piSplitAt view choices
  let otherLaw := sourcePrior.map fun member =>
    fun other : {other // other ≠ view} => member other.val
  let restLaw := planLaw.bind fun plan => otherLaw.map (Prod.mk plan)
  let current := setup.commitRecoveryNonmissingSourcePolicy wellFormed assessment.strategy who view
  let read := fun memory : ((p : Pool) → Parts p) × (∀ point, choices point) =>
    (memory.2 view, (memory.1, fun other : {other // other ≠ view} => memory.2 other.val))
  let restore := fun pair : choices view ×
      (((p : Pool) → Parts p) × ((other : {other // other ≠ view}) → choices other.val)) =>
    (pair.2.1, split.symm (pair.1, pair.2.2))
  let members := fun pair => family (restore pair)
  let default := current.support_nonempty.choose
  let remaining := fun rest => members (default, rest)
  have sourceTrace : ((app).protocol (setup.initialLaw.map fun draw =>
      PhaseRuntimeState.initial runtimePlan (encodeInputs draw)) horizon scheduler).Trace
        (some control) := by
    have initialEq : initial = setup.initialLaw.map (fun draw =>
        PhaseRuntimeState.initial runtimePlan (encodeInputs draw)) := PMF.map_comp ..
    exact initialEq ▸ (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨source, history, sourceClear, _generation, actor, same⟩ :=
    phase_ready_binding_sourceView setup mode runtime leaks runtimePlan maximal horizon scheduler
      sourceTrace who event payload binding request.2.2.1 clear
  have running : ¬ setup.commitRecoveryProtocol.terminal (some source) := by
    intro stopped
    have absent := ProtocolState.terminal_actor_none who setup.program source.point stopped
    rw [ProtocolState.actor_observe_eq, actor] at absent
    cases absent
  have sourceSplit := setup.commitRecoveryValuePlan_split finite wellFormed assessment.strategy
    ⟨some source, history⟩ sourceClear running who
  change view = setup.commitRecoveryPrivate who (some source) at same
  change (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map
      (Equiv.piSplitAt (setup.commitRecoveryPrivate who (some source)) choices) = _ at sourceSplit
  rw [← same] at sourceSplit
  have priorSplit : original.map read =
      current.bind (fun choice => restLaw.map (Prod.mk choice)) := by
    have row (plan : (p : Pool) → Parts p) :
        sourcePrior.map (fun member => read (plan, member)) =
          current.bind (fun choice => otherLaw.map fun rest => (choice, (plan, rest))) := by
      have transformed := congrArg (PMF.map fun pair => (pair.1, (plan, pair.2))) sourceSplit
      simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, read, split, current, otherLaw,
        sourcePrior, Equiv.piSplitAt, Equiv.coe_fn_mk] using transformed
    change (planLaw.bind fun plan => sourcePrior.map (Prod.mk plan)).map read = _
    calc
      _ = planLaw.bind (fun plan => sourcePrior.map fun member => read (plan, member)) := by
        rw [PMF.map_bind]
        apply congrArg (PMF.bind planLaw)
        funext plan
        exact PMF.map_comp ..
      _ = planLaw.bind (fun plan => current.bind fun choice =>
          otherLaw.map fun rest => (choice, (plan, rest))) := by
        apply congrArg (PMF.bind planLaw)
        funext plan
        exact row plan
      _ = current.bind (fun choice => planLaw.bind fun plan =>
          otherLaw.map fun rest => (choice, (plan, rest))) := PMF.bind_comm ..
      _ = _ := by
        apply congrArg (PMF.bind current)
        funext choice
        change _ = (planLaw.bind fun plan => otherLaw.map (Prod.mk plan)).map (Prod.mk choice)
        rw [PMF.map_bind]
        apply congrArg (PMF.bind planLaw)
        funext plan
        exact (PMF.map_comp ..).symm
  have restored (memory : ((p : Pool) → Parts p) × (∀ point, choices point)) :
      restore (read memory) = memory := by
    apply Prod.ext
    · rfl
    · change split.symm (split memory.2) = memory.2
      exact split.symm_apply_apply _
  have familyEq : (fun memory => members (read memory)) = family := by
    funext memory
    exact congrArg family (restored memory)
  have transported := (app).policyMixture_posterior_map original read members
    (control.execution.recall who)
  have samePosterior := congrArg (fun policies =>
    ((app).policyMixture original policies).posterior (control.execution.recall who) |>.map read)
      familyEq
  have samePrior := congrArg (fun prior =>
    ((app).policyMixture prior members).posterior (control.execution.recall who)) priorSplit
  have transported := samePosterior.symm.trans (transported.trans samePrior)
  refine ⟨((app).policyMixture restLaw remaining).posterior (control.execution.recall who), ?_⟩
  change (((app).policyMixture original family).posterior (control.execution.recall who)).map
    read = current.bind (fun choice =>
      (((app).policyMixture restLaw remaining).posterior (control.execution.recall who)).map
        (Prod.mk choice))
  apply transported.trans
  apply (app).policyMixture_posterior_independent_left_atoms current restLaw members remaining
    (control.execution.recall who)
  intro earlier entry recorded value rest
  have agree : ∀ point, point ≠ view →
      (split.symm (value, rest.2)) point = (split.symm (default, rest.2)) point := by
    intro point different
    simp [split, Equiv.piSplitAt, different]
  exact phaseTimingPlanPolicy_source_coordinate_unread setup mode runtime leaks bounds runtimePlan
    horizon scheduler bound maximal fallback wellFormed assessment mixed noise noiseNonnegative
      noiseBounded slotWeight slotNonnegative slotBounded rest.1 who _ _ control trace clear event
        payload binding request unsent agree earlier entry recorded

end Vegas
