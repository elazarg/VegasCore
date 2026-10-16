/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryTimingWordStoppedRealization
import Interaction.ReactiveStoppedProfileMixture
import Vegas.Game.CommitPrefixPlanJoint
import Interaction.ReactiveMixtureSupport
import GameTheoryExtensions.Analysis.Protocol.StoppedKernelComparison
import Vegas.Pending.PhaseClearHistory
import Vegas.Pending.PhaseBindingMemoryCallback
import Interaction.ReactiveAnchoredMixture
import Vegas.Game.RecoveryFixedCommitGeometry
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseBindingReadiness

/-! # Original owner plans and source words jointly with actual stopped histories -/

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
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial runtimePlan)
variable [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).InfoState who)]

local notation "N" => ReactiveApplication.ResponseMenu.information (menu) initial horizon scheduler
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

local instance timingWordStoppedJointPoolFintype :
    Fintype (FreeKeyedPool isFree isKeyed poolKey) := Fintype.ofFinite _

open Classical in
/-- The original complete private member profile is retained jointly with the
actual zero-RAW stopped physical history. Plans are sampled separately for
each owner and keep all their coordinates; the focal intervention ignores
its sampled member. No equality with a factual updated plan tag is asserted. -/
theorem RecoverySourceCheckpoint.timing_word_anchored_stopped_joint
    {anchor : (app).Control}
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (clearEntry : anchor.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode anchor.execution.application)
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (residual : SourceProgram.BehavioralProfile checkpoint.residual.tail)
    (raw : ∀ owner point,
      (residual owner).protocolAction checkpoint.residual.tail
          (ProtocolState.observe owner checkpoint.residual.tail point) =
        (setup.commitRecoveryNonmissingProfile assessment.strategy owner
          (setup.commitRecoveryClearInformation wellFormed owner
            (some (ProtocolState.observe owner setup.program
              (checkpoint.residual.lift point))))).map
                (fun choice => CommitRecoveryMove.underlying choice.1))
    {Ξ : SourceCtx Player L} {Q : Finset VarId}
    (block : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (reconstruct : block.prepend suffix = checkpoint.residual.tail)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : anchor.execution.application.phases = phase :: remaining)
    (positive : 0 < block.length) (boundary : IsCommitBoundary suffix)
    (fallback : (who : Player) → (N).Policy who)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (capacity : horizon ≤ bounds.candidateCount)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (entryFresh : ∀ owner, ∀ record ∈ anchor.execution.recall owner,
      record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt)
    (focal : Player) (intervention : (N).BehavioralPolicy focal)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (extra : ((menu).protocol initial horizon scheduler).History → Prop) :
    let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
    let wordLaw := block.prefixLaw suffix typed checkpoint.source
    let priors := fun owner => (independentProduct weights).bind fun plan =>
      (wordLaw.map (SourceProgram.Config.view owner)).map (Prod.mk plan)
    let members := fun owner (memory : ((p : Pool) → Parts p) × DecisionView owner Ξ) =>
      ReactiveApplication.anchoredPolicy anchor.execution
        (fun _ => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
          scheduler
          bound fallback wellFormed assessment block anchor.execution.application.attempt.phase
            anchor.execution.application.generation slotWeight slotNonnegative slotBounded
              memory.1 owner memory.2) owner
    let profile := (N).agentBehavior (N).playedInformation fallback (fun agent =>
      (weights (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound
        agent)).bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon
          scheduler bound wellFormed assessment 0 le_rfl (by norm_num) slotWeight slotNonnegative
            slotBounded agent))
    let focalPolicy := (app).decodePolicy ((menu).embedPolicy initial horizon scheduler focal
      intervention)
    let family := fun owner memory =>
      if owner = focal then focalPolicy else members owner memory
    let posterior := fun state => independentProduct (fun owner =>
      ((app).policyMixture (priors owner) (family owner)).posterior
        ((app).recallAt owner state))
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      extra history ∨ match history.state with
        | none => True
        | some current => current.execution.application.current.excluded ≠ ∅ ∨
            current.execution.application.phases ≠ phase :: remaining
    (independentProduct priors).bind (fun memories =>
      ((N).runBehavioralUntil certificate (fun who =>
        (menu).restrictPolicy initial horizon scheduler who (family who (memories who)))
          stopped ⟨some anchor, anchorTrace⟩).map (fun final => (final, memories))) =
    ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) profile focal intervention) stopped
        ⟨some anchor, anchorTrace⟩).bind fun final =>
          (posterior final.state).map (Prod.mk final) := by
  intro typed wordLaw priors members profile focalPolicy family posterior stopped
  let players := Function.update (fun who => ((app).policyMixture (priors who)
    (members who)).policy) focal focalPolicy
  have membersCovered (who : Player) (memory : ((p : Pool) → Parts p) × DecisionView who Ξ) :
      ∀ past view action, action ∈ (members who memory past view).support →
        action ∈ (menu).actions who past view := by
    exact (menu).anchoredPolicy_covered initial horizon scheduler anchor anchorTrace _ who
      (fun past view action supported => (menu).decode_embedPolicy_covered initial horizon
        scheduler who _ past view action supported)
  have familyCovered : ∀ who memory past view action,
      action ∈ (family who memory past view).support →
        action ∈ (menu).actions who past view := by
    intro who memory past view action supported
    by_cases own : who = focal
    · simp only [family, ite_eq_left own] at supported
      subst who
      exact (menu).decode_embedPolicy_covered initial horizon scheduler focal intervention
        past view action supported
    · simp only [family, ite_eq_right own] at supported
      exact membersCovered who memory past view action supported
  have entryPosterior : posterior (some anchor) = independentProduct priors := by
    apply congrArg independentProduct
    funext who
    change ((app).policyMixture (priors who) (family who)).posterior
      (anchor.execution.recall who) = priors who
    by_cases own : who = focal
    · have independent : family who = fun _ => focalPolicy := by
        funext memory past view
        simp only [family, ite_eq_left own]
      rw [independent]
      exact (app).policyMixture_posterior_of_agree (priors who) _ focalPolicy _
        (fun _ _ _ _ => rfl)
    · have unchanged : family who = members who := by
        funext memory past view
        simp only [family, ite_eq_right own]
      rw [unchanged]
      exact ReactiveApplication.anchoredPolicy_mixture_posterior (priors who) anchor.execution
        _ who
  have policies : (fun who => ((app).policyMixture (priors who) (family who)).policy) =
      players := by
    funext who past view
    by_cases own : who = focal
    · subst who
      simp only [family, players, Function.update_self,
        ReactiveApplication.policyMixture_policy, ite_true, PMF.bind_const]
    · have unchanged : family who = members who := by
        funext memory past view
        simp only [family, ite_eq_right own]
      simp only [unchanged, players, Function.update_of_ne own]
  have joint := (menu).runUntil_policyMixtures_joint initial horizon scheduler certificate
    priors family familyCovered stopped ⟨some anchor, anchorTrace⟩
  change (posterior (some anchor)).bind (fun memories =>
    ((N).runBehavioralUntil certificate (fun who => (menu).restrictPolicy initial horizon
      scheduler who (family who (memories who))) stopped ⟨some anchor, anchorTrace⟩).map
        (fun final => (final, memories))) = _ at joint
  rw [entryPosterior] at joint
  have finitePolicies : (fun who => (menu).restrictPolicy initial horizon scheduler who
      (((app).policyMixture (priors who) (family who)).policy)) =
      fun who => (menu).restrictPolicy initial horizon scheduler who (players who) := by
    funext who
    exact congrArg ((menu).restrictPolicy initial horizon scheduler who) (congrFun policies who)
  rw [finitePolicies] at joint
  have physical := RecoverySourceCheckpoint.timing_word_anchored_stopped_law setup mode runtime
    leaks bounds runtimePlan inputs horizon scheduler bound anchorTrace maximal clearEntry
      checkpoint wellFormed assessment residual raw block suffix reconstruct phase remaining
        installed positive boundary fallback slotWeight slotNonnegative slotBounded weights
          capacity values entryFresh focal intervention certificate extra
  change (N).runBehavioralUntil certificate (fun who =>
    (menu).restrictPolicy initial horizon scheduler who (players who)) stopped
      ⟨some anchor, anchorTrace⟩ = _ at physical
  rw [physical] at joint
  exact joint

end Vegas
