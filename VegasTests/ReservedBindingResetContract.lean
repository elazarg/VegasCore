/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochBindingReset
import Vegas.Game.PhaseProposalResetPayoff

/-! # Original stopped available-SEND binding reset contract -/

noncomputable section

namespace VegasTests

open Vegas Vegas.SourceProgram Vegas.EventGraph Vegas.EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable [Fintype Player]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "nativeInitial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)

open scoped Classical in
example
    (complete : leaks = MessageNetwork.completePendingObservation)
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (remaining : Nat) (active : (app).Execution) (actor : Player)
    (leftResponse rightResponse : (app).Action)
    (activeTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some ⟨remaining, some actor, active⟩))
    (leftAvailable : leftResponse ∈ (menu).actions actor
      (active.recall actor) (active.observe app actor))
    (rightAvailable : rightResponse ∈ (menu).actions actor
      (active.recall actor) (active.observe app actor))
    (leftSends : leftResponse.transmission ≠ none)
    (phase : RuntimePhase graph) (installed : phase ∈ active.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (checkpoint : RecoverySourceCheckpoint setup mode active.application) :
    let initial := (inputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let anchor := fun response : (app).Action => active.respond app actor response
    ∃ leftTrace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, anchor leftResponse⟩),
    ∃ rightTrace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, anchor rightResponse⟩),
    TracePrefix activeTrace leftTrace ∧ TracePrefix activeTrace rightTrace ∧
    let law := fun response (trace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, anchor response⟩)) =>
      let players := ReactiveApplication.anchoredPolicy (anchor response)
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
      let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
      let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
        match history.state with
        | none => False
        | some control =>
            control.execution.application.attempt ≠ (anchor response).application.attempt
      ((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, anchor response⟩, trace⟩
    ∀ leftFinal ∈ (law leftResponse leftTrace).support,
    ∀ rightFinal ∈ (law rightResponse rightTrace).support,
      ∃ (leftEnding rightEnding leftBefore rightBefore : (app).Control)
        (leftPrior : ((menu).protocol initial horizon scheduler).Trace (some leftBefore))
        (rightPrior : ((menu).protocol initial horizon scheduler).Trace (some rightBefore))
        (leftJoint rightJoint : Player → Option (app).Action)
        (leftLegal : ((menu).protocol initial horizon scheduler).Legal (some leftBefore) leftJoint)
        (rightLegal : ((menu).protocol initial horizon scheduler).Legal
          (some rightBefore) rightJoint)
        (leftRealized : some leftEnding ∈ ((app).transition initial horizon scheduler
          (some leftBefore) leftJoint).support)
        (rightRealized : some rightEnding ∈ ((app).transition initial horizon scheduler
          (some rightBefore) rightJoint).support)
        (leftRaw rightRaw : RecoveryState graph),
        leftFinal.state = some leftEnding ∧ rightFinal.state = some rightEnding ∧
        TracePrefix leftTrace leftPrior ∧ TracePrefix rightTrace rightPrior ∧
        TracePrefix (leftPrior.extend leftJoint leftLegal leftRealized) leftFinal.trace ∧
        TracePrefix (rightPrior.extend rightJoint rightLegal rightRealized) rightFinal.trace ∧
        leftBefore.execution.application.attempt = active.application.attempt ∧
        rightBefore.execution.application.attempt = active.application.attempt ∧
        PhaseClosingEffect runtime leaks leftBefore.execution leftEnding.execution leftRaw ∧
        PhaseClosingEffect runtime leaks rightBefore.execution rightEnding.execution rightRaw ∧
        phase ∈ leftBefore.execution.application.phases.head? ∧
        phase ∈ rightBefore.execution.application.phases.head? ∧
        phase.Finished (phase.drain leftRaw) ∧ phase.Finished (phase.drain rightRaw) ∧
        leftEnding.actor = none ∧ rightEnding.actor = none ∧
        leftEnding.execution.application.attempt ≠ active.application.attempt ∧
        rightEnding.execution.application.attempt ≠ active.application.attempt ∧
        leftEnding.execution.application =
          ({ leftBefore.execution.application with current := leftRaw } :
            PhaseRuntimeState graph).normalize ∧
        rightEnding.execution.application =
          ({ rightBefore.execution.application with current := rightRaw } :
            PhaseRuntimeState graph).normalize ∧
        (phase.drain leftRaw).FailureCoverage ∧
        (phase.drain rightRaw).FailureCoverage ∧
        (phase.drain leftRaw).excluded = leftEnding.execution.application.current.excluded ∧
        (phase.drain rightRaw).excluded = rightEnding.execution.application.current.excluded ∧
        PhaseProposal.sourceArchive leftEnding.execution.network.inputs =
          PhaseProposal.sourceArchive rightEnding.execution.network.inputs ∧
        (∀ event ∈ phase.events, ∀ owner payload,
          (graph).outputLayout event = .binding owner payload →
          (leftRaw.native.accepted (.inr event) ≠ none ↔
            ReservedEpoch.ownedAcceptanceWord runtime leaks tape
              (anchor leftResponse) owner event)) ∧
        (∀ event ∈ phase.events, ∀ owner payload,
          (graph).outputLayout event = .binding owner payload →
          (rightRaw.native.accepted (.inr event) ≠ none ↔
            ReservedEpoch.ownedAcceptanceWord runtime leaks tape
              (anchor rightResponse) owner event)) ∧
        (∀ event ∈ phase.events, ∀ owner payload, owner ≠ actor →
          (graph).outputLayout event = .binding owner payload →
          (leftRaw.native.accepted (.inr event) ≠ none ↔
            rightRaw.native.accepted (.inr event) ≠ none)) ∧
        (actor ∉ rightEnding.execution.application.current.excluded →
          actor ∉ leftEnding.execution.application.current.excluded ∧
          (∀ event ∈ phase.events, ∀ payload,
            (graph).outputLayout event = .binding actor payload →
            rightRaw.native.accepted (.inr event) ≠ none) ∧
          (∀ event ∈ phase.events, ∀ payload,
            (graph).outputLayout event = .binding actor payload →
            leftRaw.native.accepted (.inr event) ≠ none) ∧
          (phase.drain leftRaw).native.sourceFailureFootprint =
            (phase.drain rightRaw).native.sourceFailureFootprint ∧
          (phase.drain leftRaw).excluded = (phase.drain rightRaw).excluded ∧
          PhaseRuntimeState.sourceControlRecords leftEnding.execution.application.retired =
            PhaseRuntimeState.sourceControlRecords rightEnding.execution.application.retired ∧
          (((phase.drain rightRaw).excluded \ active.application.entry.excluded).Nonempty →
            PairedBindingResetSources checkpoint leftEnding.execution.application
              rightEnding.execution.application)) := by
  exact phaseProposalUnflagged_available_send_reset_boundary setup mode runtime leaks bounds plan
    complete coveredValues maximal ordered values fullValues tape activationGap processingGap
    gaps margin capacity remaining active actor leftResponse rightResponse activeTrace
    leftAvailable rightAvailable leftSends phase installed commitment checkpoint

end VegasTests

namespace VegasTests

open Vegas Vegas.SourceProgram Vegas.EventGraph Vegas.EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime

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
    (anchor : Bool → (app).Control) (idle : ∀ side, (anchor side).actor = none)
    (traces : ∀ side, ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some (anchor side)))
    (entryExcluded : ∀ side, (anchor side).execution.application.entry.excluded =
      (anchor side).execution.application.current.excluded)
    (fresh : ∀ side who, ∀ record ∈ (anchor side).execution.recall who,
      record.beforeView.application.2.attempt ≠ (anchor side).execution.application.attempt)
    (witness : ∀ side, RecoverySourceWitness setup mode plan (anchor side).execution.application)
    (archived : ∀ side, (witness side).checkpoint.ArchivedProposals
      (anchor side).execution.network.inputs)
    (proper : ∀ side who, who ∉ (anchor side).execution.application.current.excluded →
      (witness side).checkpoint.source.BindingsHoldValues who)
    (same : setup.proposalRecoveryErasedHistory
        ⟨_, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup
            (PhaseProposal.sourceArchive (anchor false).execution.network.inputs))
              (witness false).checkpoint.trace⟩ =
      setup.proposalRecoveryErasedHistory
        ⟨_, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup
            (PhaseProposal.sourceArchive (anchor true).execution.network.inputs))
              (witness true).checkpoint.trace⟩) :
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let model := (menu).information initial horizon scheduler
    let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    let profile := fun side who => (menu).restrictPolicy initial horizon scheduler who
      (ReactiveApplication.anchoredPolicy (anchor side).execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    ∀ who, (model.runBehavioralTerminalFrom certificate (profile false)
        ⟨some (anchor false), traces false⟩).map
          (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            final.state who) =
      (model.runBehavioralTerminalFrom certificate (profile true)
        ⟨some (anchor true), traces true⟩).map
          (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            final.state who) := by
  exact phaseProposal_fresh_payoff_law_eq_of_erased_source setup mode runtime leaks bounds plan
    complete covered maximal values fullValues tape activationGap processingGap gaps margin capacity
      utility excludedPayoff anchor idle traces entryExcluded fresh witness archived proper same

end VegasTests
