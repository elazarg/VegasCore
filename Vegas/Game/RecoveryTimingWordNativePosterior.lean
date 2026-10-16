/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryTimingWordStoppedConfig
import GameTheory.Math.Probability.ConditionalObservation
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

local instance timingWordNativePosteriorPoolFintype :
    Fintype (FreeKeyedPool isFree isKeyed poolKey) := Fintype.ofFinite _

open Classical in
/-- Conditioning the SAME original immutable Config/owner-plan joint on a
genuine full native input gives actual own-recall memory weights followed by
ORIGINAL Config fibers. This retains the entire source Config and full plans;
it does not replace those weights by a source belief or remove entry tilt. -/
theorem RecoverySourceCheckpoint.timing_word_anchored_native_posterior
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
    (extra : ((menu).protocol initial horizon scheduler).History → Prop)
    (observer : Player) (observed : (N).InfoState observer) :
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
    let run := fun memories => (N).runBehavioralUntil certificate (fun who =>
      (menu).restrictPolicy initial horizon scheduler who (family who (memories who))) stopped
        ⟨some anchor, anchorTrace⟩
    let read := fun (plans : Player → ((p : Pool) → Parts p))
      (complete : SourceProgram.Config Player L Ξ) =>
        fun owner => (plans owner, complete.view owner)
    let words := fun complete : SourceProgram.Config Player L Ξ =>
      fun owner => complete.view owner
    let native := (N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) profile focal intervention) stopped
        ⟨some anchor, anchorTrace⟩
    let original := (independentProduct (fun _ : Player => independentProduct weights)).bind
      fun plans => wordLaw.bind fun complete => (run (read plans complete)).map
        (fun final => (final, plans, complete))
    let implementation := native.bind fun final =>
      (posterior final.state).map (Prod.mk final)
    let nativeInput := fun final : ((menu).protocol initial horizon scheduler).History =>
      (N).infoOf observer final.trace
    observed ∈ (native.map nativeInput).support →
    (fiberPosterior original (fun row => nativeInput row.1) observed).map Prod.snd =
      (fiberPosterior implementation (fun row => nativeInput row.1) observed).bind fun row =>
        (fiberPosterior wordLaw words (fun owner => (row.2 owner).2)).map
          (fun complete => ((fun owner => (row.2 owner).1), complete)) := by
  intro typed wordLaw priors members profile focalPolicy family posterior stopped run read words
    native original implementation nativeInput present
  let reattach := fun pair : ((menu).protocol initial horizon scheduler).History ×
      ((owner : Player) → ((p : Pool) → Parts p) × DecisionView owner Ξ) =>
    (fiberPosterior wordLaw words (fun owner => (pair.2 owner).2)).map
      (fun complete => (pair.1, (fun owner => (pair.2 owner).1), complete))
  have physical := RecoverySourceCheckpoint.timing_word_anchored_stopped_config_joint setup mode
    runtime leaks bounds runtimePlan inputs horizon scheduler bound anchorTrace maximal clearEntry
      checkpoint wellFormed assessment residual raw block suffix reconstruct phase remaining
        installed positive boundary fallback slotWeight slotNonnegative slotBounded weights
          capacity values entryFresh focal intervention certificate extra
  change original = native.bind (fun final => (posterior final.state).bind fun memories =>
    reattach (final, memories)) at physical
  have joint : original = implementation.bind reattach := by
    rw [physical]
    simp only [implementation, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  have marginal : implementation.map (fun row => nativeInput row.1) =
      native.map nativeInput := by
    simp only [implementation, PMF.map_bind, PMF.map_comp, Function.comp_def]
    calc
      _ = native.bind (fun final => PMF.pure (nativeInput final)) := by
        apply bind_congr_on_support
        intro final _
        exact PMF.map_const _ _
      _ = _ := PMF.bind_pure_comp _ _
  have observedImplementation : observed ∈
      (implementation.map (fun row => nativeInput row.1)).support := by
    rw [marginal]
    exact present
  have compatible : ∀ row ∈ implementation.support, ∀ next ∈ (reattach row).support,
      nativeInput next.1 = nativeInput row.1 := by
    intro row _ next supported
    obtain ⟨complete, _, rfl⟩ := PMF.support_map .. ▸ supported
    rfl
  have conditioned := fiberPosterior_bind_of_observation implementation reattach
    (fun row => nativeInput row.1) (fun row => nativeInput row.1) compatible observed
      observedImplementation
  rw [joint, conditioned, PMF.map_bind]
  apply bind_congr_on_support
  intro row _
  rw [PMF.map_comp]
  rfl

end Vegas
