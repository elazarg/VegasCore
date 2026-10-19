/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOriginalResetPayoff

/-! # Actual selected reset endpoints and their complete payoff laws -/

noncomputable section

namespace VegasTests

open Vegas SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime

/-- This consumes the original first-exit pair, including its selected retry
points, words and history extensions. Both full witnesses are packaged at those
literal endpoints; properness is inherited from the restored saved cells. -/
example
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : horizon ≤ bounds.candidateCount)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (anchor : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some anchor))
    (witness : RecoverySourceWitness setup mode plan anchor.execution.application)
    (archived : witness.checkpoint.ArchivedProposals anchor.execution.network.inputs)
    (oldProper : ∀ who, who ∉ anchor.execution.application.current.excluded →
      witness.checkpoint.source.BindingsHoldValues who)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : anchor.execution.application.phases = phase :: remaining)
    (kind : phase.kind = .commitment)
    (before ending : Bool → (app).Control)
    (priors : ∀ side, ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some (before side)))
    (traces : ∀ side, ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some (ending side)))
    (kept : ∀ side, TracePrefix anchorTrace (priors side))
    (same : ∀ side, (before side).execution.application.attempt =
      anchor.execution.application.attempt)
    (idle : ∀ side, (ending side).actor = none)
    (changed : ∀ side, (ending side).execution.application.attempt ≠
      (before side).execution.application.attempt)
    (raw : Bool → RecoveryState (serviceGraph setup mode))
    (effects : ∀ side, PhaseClosingEffect runtime leaks (before side).execution
      (ending side).execution (raw side))
    (normalized : ∀ side, (ending side).execution.application =
      ({ (before side).execution.application with current := raw side } :
        PhaseRuntimeState (serviceGraph setup mode)).normalize)
    (finished : ∀ side, phase.Finished (phase.drain (raw side)))
    (missed : ∀ side, (((phase.drain (raw side)).excluded \
      (before side).execution.application.entry.excluded) ∩ phase.owners).Nonempty)
    (survives : ∀ side, (phase.owners \ (phase.drain (raw side)).excluded).Nonempty)
    (inherited : ∀ side, anchor.execution.application.current.excluded ⊆
      (ending side).execution.application.current.excluded)
    (archive : PhaseProposal.sourceArchive (ending false).execution.network.inputs =
      PhaseProposal.sourceArchive (ending true).execution.network.inputs)
    (paired : PairedBindingResetSources witness.checkpoint
      (ending false).execution.application (ending true).execution.application
        (phase.drain (raw false)) (phase.drain (raw true))) :
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let model := (menu).information initial horizon scheduler
    let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    let profile := fun side who => (menu).restrictPolicy initial horizon scheduler who
      (ReactiveApplication.anchoredPolicy (ending side).execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    ∀ who, (model.runBehavioralTerminalFrom certificate (profile false)
        ⟨some (ending false), traces false⟩).map
          (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            final.state who) =
      (model.runBehavioralTerminalFrom certificate (profile true)
        ⟨some (ending true), traces true⟩).map
          (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            final.state who) := by
  exact phaseProposal_original_reset_payoff_law_eq setup mode runtime leaks bounds plan complete
    covered maximal values fullValues tape activationGap processingGap gaps margin capacity utility
      excludedPayoff anchor anchorTrace witness archived oldProper phase remaining installed kind
        before ending priors traces kept same idle changed raw effects normalized finished missed
          survives inherited archive paired

end VegasTests
