/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingCanonicalRecipe
import Vegas.Game.PhaseTimingCompletion
import Vegas.Game.PhaseSourceCompletionLaw
import Vegas.Game.PhaseCanonicalSafety

/-! # Initialized history laws of the same operational timing completion -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
  (sourceSequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
  (sourceLimit : setup.commitRecoveryModel.BehavioralAssessment)
  (sourceConvergence : BehavioralAssessmentConvergesPointwise sourceSequence sourceLimit)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source sourceLimit.strategy)
  (continuing : ∀ who (site : setup.commitRecoveryModel.InformationSite who),
    ∀ choice ∈ (sourceLimit.strategy who site.1).support,
      setup.CommitRecoveryContinues who site.1 choice.1)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat)
  (scheduler : (phaseApplication (serviceRuntime setup mode deadline) leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)
  (delay bound : (serviceGraph setup mode).EventId → Nat)

local notation "R" => serviceRuntime setup mode deadline
local notation "app" => phaseApplication R leaks
local notation "start" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu R leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu R leaks bounds) (start) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu R leaks bounds) (start) horizon scheduler
local notation "parts" => PhaseTimingPart setup mode R leaks bounds start horizon scheduler bound
local notation "pools" => phaseTimingPool setup mode R leaks bounds start horizon scheduler bound
local notation "canonical" => phaseSourceStrategy setup mode R leaks bounds wellFormed
  sourceLimit (start) horizon scheduler


include sourceConvergence copies continuing maximal capacity

/-- The actual timing-completed sequence and its own convergent limit preserve
the entire canonical initialized history law at every fuel. No prescription is
imposed at other clear callbacks, and no incentive conclusion is assumed. -/
theorem phaseTimingAssessment_run_eq_canonical
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)]
  (asyncService : PhaseService.AsyncContract R leaks
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler delay bound)
  (timely : (R).AsyncTimely delay bound)
  (values : ∀ event owner payload,
    ((serviceGraph setup mode).outputLayout event = .binding owner payload ∨
      (serviceGraph setup mode).outputLayout event = .publication payload) →
    ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
  (noise : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ noise n) (bounded : ∀ n, noise n ≤ 1)
  (vanishes : Tendsto noise atTop (nhds 0))
  (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
  (slotBounded : ∀ n, slotWeight n ≤ 1)
  (slotVanishes : Tendsto slotWeight atTop (nhds 0))
  (weights : ℕ → ∀ p, PMF (parts p))
  (fallback : ∀ who, (N).Policy who)
  (sequence : ℕ → (N).BehavioralAssessment) (limit : (N).BehavioralAssessment)
  (index : ℕ → ℕ) (increasing : StrictMono index)
  (converges : BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit)
  (assembled : ∀ n, (sequence n).strategy = (N).agentBehavior (N).playedInformation fallback
    fun agent => (weights n (pools agent)).bind
      (phaseTimingComponent setup mode R leaks bounds start horizon scheduler bound wellFormed
        (sourceSequence n) (noise n) (nonnegative n) (bounded n) (slotWeight n)
          (slotNonnegative n) (slotBounded n) agent))
    (fuel : Nat) :
    (N).runBehavioralFrom limit.strategy fuel (E).initHistory =
      (N).runBehavioralFrom canonical fuel (E).initHistory := by
  classical
  have initialEq : (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan) =
      (start) := PMF.map_comp encodeInputs setup.initialLaw (PhaseRuntimeState.initial plan)
  have safe : ∀ (current : (app).Control) (_trace : (E).Trace (some current)),
      (∀ who, (phaseSourcePolicy setup mode R leaks bounds wellFormed sourceLimit who).Consistent
        (current.execution.recall who)) → current.execution.application.current.excluded = ∅ := by
    have law := phaseSourcePolicy_clear_history setup mode deadline leaks source bounds wellFormed
      sourceLimit copies continuing plan (serviceGraph_revealRelaxedOrdered setup mode) maximal
        horizon scheduler capacity delay bound asyncService.opportunity asyncService.inclusion
          timely values
    rw [initialEq] at law
    exact law
  apply phaseSourceAssessment_run_eq_canonical setup mode R leaks bounds wellFormed plan maximal
    horizon scheduler sourceSequence sourceLimit sourceConvergence noise nonnegative bounded
      vanishes slotWeight slotNonnegative slotBounded slotVanishes sequence limit index increasing
        converges ?_ safe fuel
  rintro n who site ⟨current, trace, acting, atSite, consistent⟩ _unflagged
  have clear := safe current trace consistent
  rw [assembled n]
  change (N).agentBehavior (N).playedInformation fallback _ ((N).agentAt site).1
    ((N).agentAt site).2.1 = _
  rw [(N).agentBehavior_at (N).playedInformation fallback _ ((N).agentAt site)]
  have componentEq : phaseTimingComponent setup mode R leaks bounds start horizon scheduler bound
      wellFormed (sourceSequence n) (noise n) (nonnegative n) (bounded n) (slotWeight n)
        (slotNonnegative n) (slotBounded n) ((N).agentAt site) = fun _ =>
      phaseSourcePerturbedStrategy setup mode R leaks bounds start horizon scheduler wellFormed
        (sourceSequence n) (noise n) (nonnegative n) (bounded n) (slotWeight n)
          (slotNonnegative n) (slotBounded n) who site.1 := by
    funext part
    apply phaseTimingComponent_eq_source_of_canonical_callback setup mode R leaks bounds wellFormed
      source sourceLimit copies continuing plan maximal horizon scheduler capacity delay bound
        ?_ timely values (sourceSequence n) (noise n) (nonnegative n) (bounded n) (slotWeight n)
          (slotNonnegative n) (slotBounded n) ((N).agentAt site) current trace acting atSite clear
            consistent part
    rw [← initialEq]
    exact asyncService.opportunity
  rw [componentEq, PMF.bind_const]

/-- The same timing assessment has the full canonical terminal history law,
including all private setup and runtime data retained in that history. -/
theorem phaseTimingAssessment_terminal_run_eq_canonical
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)]
  (asyncService : PhaseService.AsyncContract R leaks
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler delay bound)
  (timely : (R).AsyncTimely delay bound)
  (values : ∀ event owner payload,
    ((serviceGraph setup mode).outputLayout event = .binding owner payload ∨
      (serviceGraph setup mode).outputLayout event = .publication payload) →
    ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
  (noise : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ noise n) (bounded : ∀ n, noise n ≤ 1)
  (vanishes : Tendsto noise atTop (nhds 0))
  (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
  (slotBounded : ∀ n, slotWeight n ≤ 1)
  (slotVanishes : Tendsto slotWeight atTop (nhds 0))
  (weights : ℕ → ∀ p, PMF (parts p))
  (fallback : ∀ who, (N).Policy who)
  (sequence : ℕ → (N).BehavioralAssessment) (limit : (N).BehavioralAssessment)
  (index : ℕ → ℕ) (increasing : StrictMono index)
  (converges : BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit)
  (assembled : ∀ n, (sequence n).strategy = (N).agentBehavior (N).playedInformation fallback
    fun agent => (weights n (pools agent)).bind
      (phaseTimingComponent setup mode R leaks bounds start horizon scheduler bound wellFormed
        (sourceSequence n) (noise n) (nonnegative n) (bounded n) (slotWeight n)
          (slotNonnegative n) (slotBounded n) agent))
    (certificate : (E).WellFoundedHistories) :
    (N).runBehavioralTerminalFrom certificate limit.strategy (E).initHistory =
      (N).runBehavioralTerminalFrom certificate canonical (E).initHistory := by
  rw [(N).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
    ((menu).bounded (start) horizon scheduler),
    (N).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
      ((menu).bounded (start) horizon scheduler)]
  exact phaseTimingAssessment_run_eq_canonical setup mode deadline leaks bounds wellFormed source
    sourceSequence sourceLimit sourceConvergence copies continuing plan maximal horizon scheduler
      capacity delay bound asyncService timely values noise nonnegative bounded vanishes slotWeight
        slotNonnegative slotBounded slotVanishes weights fallback sequence limit index increasing
          converges assembled _

end Vegas
