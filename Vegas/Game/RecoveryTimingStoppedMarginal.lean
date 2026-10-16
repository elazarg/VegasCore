/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryTimingInitialJoint
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

/-! # Stopped immutable joint under equal initialized state laws -/

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
  (inputs : PMF (serviceGraph setup mode).Inputs)
  (initialLaw : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => initialLaw
variable [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    initialLaw horizon scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    initialLaw horizon scheduler).InfoState who)]

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

local instance timingWordStoppedMarginalPoolFintype :
    Fintype (FreeKeyedPool isFree isKeyed poolKey) := Fintype.ofFinite _

open Classical in
/-- The literal assembled zero-noise strategy is the physical marginal of the
original immutable Config and separate owner plans at the same full anchor. -/
theorem RecoverySourceCheckpoint.timing_word_anchored_stopped_marginal
    (initialEq : initialLaw = inputs.map (PhaseRuntimeState.initial runtimePlan))
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
    (stopped : ((menu).protocol initial horizon scheduler).History → Prop)
    (stoppedEq : stopped = fun history => extra history ∨ match history.state with
      | none => True
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.phases ≠ phase :: remaining) :
    let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
    let wordLaw := block.prefixLaw suffix typed checkpoint.source
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
    let run := fun memories => (N).runBehavioralUntil certificate (fun who =>
      (menu).restrictPolicy initial horizon scheduler who (family who (memories who))) stopped
        ⟨some anchor, anchorTrace⟩
    let read := fun (plans : Player → ((p : Pool) → Parts p))
      (complete : SourceProgram.Config Player L Ξ) =>
        fun owner => (plans owner, complete.view owner)
    ((independentProduct (fun _ : Player => independentProduct weights)).bind fun plans =>
      wordLaw.bind fun complete => run (read plans complete)) =
    (N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) profile focal intervention) stopped
        ⟨some anchor, anchorTrace⟩ := by
  rw [stoppedEq]
  intro typed wordLaw members profile focalPolicy family run read
  have joint :=
    RecoverySourceCheckpoint.timing_word_anchored_stopped_config_joint_of_initial setup mode runtime
      leaks bounds runtimePlan inputs initialLaw horizon scheduler bound initialEq anchorTrace
        maximal clearEntry checkpoint wellFormed assessment residual raw block suffix reconstruct
          phase remaining installed positive boundary fallback slotWeight slotNonnegative
            slotBounded weights capacity values entryFresh focal intervention certificate extra
  dsimp only at joint
  have marginal := congrArg (PMF.map Prod.fst) joint
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at marginal
  have mapIdentity (law : PMF ((menu).protocol initial horizon scheduler).History) :
      law.map (fun final => final) = law := PMF.map_id law
  have mapConstant {A : Type} (law : PMF A)
      (final : ((menu).protocol initial horizon scheduler).History) :
      law.map (fun _ => final) = PMF.pure final := PMF.map_const _ _
  have bindConstant {A : Type} (law : PMF A)
      (final : ((menu).protocol initial horizon scheduler).History) :
      law.bind (fun _ => PMF.pure final) = PMF.pure final := PMF.bind_const _ _
  have bindIdentity (law : PMF ((menu).protocol initial horizon scheduler).History) :
      law.bind (fun final => PMF.pure final) = law := PMF.bind_pure law
  simp only [mapIdentity, mapConstant, bindConstant, bindIdentity] at marginal
  convert! marginal using 1

end Vegas
