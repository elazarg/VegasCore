/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseAttemptControls
import Vegas.Game.PhaseProposalEmissionResponse
import Vegas.Game.PhaseProposalBindingResponse
import Vegas.Game.PhaseProposalBindingWord
import Vegas.Pending.PhaseBindingResponseWitness
import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseSemanticProgress
import Vegas.Game.PhaseCommitmentProposalArchive
import Vegas.Game.ReservedEpochStoppedImage
import Vegas.Game.ReservedEpochOriginalWord
import Interaction.ReactiveLocalContinuation
import Interaction.ReactiveAnchoredMixture
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryInvariant

/-! # The original emission frontier throughout an actual binding phase

The frontier below is the deterministic readout of the original signed trace.
Its pending values are retained before admission. Automatic coordinates of
inherited excluded owners are completed by the original phase drain.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- Geometric and signed-meaning facts about the literal emitted ideal.
There is no probability-law or physical-admission premise in this predicate. -/
structure PhaseProposalBindingPhaseInvariant
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (execution : (app).Execution) (frontier : (graph).Config) : Prop where
  within : frontier.cut.Within phase.low phase.high
  quiet : ∀ event ∈ phase.events, frontier.cut.Ready event →
    ∀ owner ∈ anchor.application.current.excluded, (graph).actor? event ≠ some owner
  emissions : PhaseProposalEmittedBindings runtime leaks execution phase frontier

omit [Fintype Player] in
private theorem frontier_drain_geometry
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (frontier : (graph).Config)
    (within : frontier.cut.Within phase.low phase.high) :
    let after := phaseProposalBindingFrontierDrain setup mode runtime leaks anchor phase frontier
    after.cut.Within phase.low phase.high ∧
      ∀ event ∈ phase.events, after.cut.Ready event →
        ∀ owner ∈ anchor.application.current.excluded, (graph).actor? event ≠ some owner := by
  let state : RecoveryState (graph) :=
    ⟨{ anchor.application.current.native with config := frontier },
      anchor.application.current.excluded⟩
  refine ⟨phase.drain_within state within, ?_⟩
  intro event inside ready owner excluded acting
  apply phase.drain_quiescent state event
  refine ⟨inside, ready, ?_⟩
  rw [acting, phase.drain_excluded]
  exact excluded

omit [Fintype Player] in
private theorem frontier_advance_geometry
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (frontier : (graph).Config)
    (before : (app).ProtocolState) (joint : Player → Option (app).Action)
    (within : frontier.cut.Within phase.low phase.high)
    (quiet : ∀ event ∈ phase.events, frontier.cut.Ready event →
      ∀ owner ∈ anchor.application.current.excluded, (graph).actor? event ≠ some owner) :
    let after := phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor phase
      frontier before joint
    after.cut.Within phase.low phase.high ∧
      ∀ event ∈ phase.events, after.cut.Ready event →
        ∀ owner ∈ anchor.application.current.excluded, (graph).actor? event ≠ some owner := by
  cases before with
  | none => exact ⟨within, quiet⟩
  | some control =>
    by_cases attempted : control.execution.application.attempt = anchor.application.attempt
    · cases actor : control.actor with
      | none =>
        simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor]
          using And.intro within quiet
      | some who =>
        cases sent : ((joint who).getD ⟨none⟩).transmission with
        | none =>
          simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor, sent]
            using And.intro within quiet
        | some material =>
          cases packet : material.call.packet with
          | opening =>
            simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor,
              sent, packet] using And.intro within quiet
          | malformed =>
            simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor,
              sent, packet] using And.intro within quiet
          | commitment event candidate =>
            by_cases inside : event ∈ phase.events
            · cases node : nodeView (graph) event with
              | bind owner payload binding code =>
                by_cases same : owner = who
                · by_cases ready : frontier.cut.Ready event
                  · simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte,
                      actor, sent, packet, inside, node, same, ready, dite_true, dite_false] using
                      (frontier_drain_geometry setup mode runtime leaks anchor phase
                        (frontier.complete event ready _ _)
                        (within.complete event ready ((phase.mem_events event).mp inside).2))
                  · simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte,
                      actor, sent, packet, inside, node, same, ready, dite_true, dite_false]
                        using And.intro within quiet
                · simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte,
                    actor, sent, packet, inside, node, same] using And.intro within quiet
              | resolve =>
                simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor,
                  sent, packet, inside, node] using And.intro within quiet
              | sample =>
                simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor,
                  sent, packet, inside, node] using And.intro within quiet
            · simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor,
                sent, packet, inside] using And.intro within quiet
    · simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte]
        using And.intro within quiet

omit [Fintype Player] in
/-- Geometry is retained on the original raw trace, even before an emitted
packet is included. This theorem makes no assumption about the sender law. -/
theorem phaseProposalEmissionFrontier_geometry
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (anchorLength : Nat)
    (first : (graph).Config) (within : first.cut.Within phase.low phase.high)
    (quiet : ∀ event ∈ phase.events, first.cut.Ready event →
      ∀ owner ∈ anchor.application.current.excluded, (graph).actor? event ≠ some owner) :
    ∀ {state : (app).ProtocolState}
      (trace : ((app).protocol initial horizon scheduler).Trace state),
      let frontier := phaseProposalEmissionFrontier setup mode runtime leaks anchor phase
        anchorLength first initial horizon scheduler trace
      frontier.cut.Within phase.low phase.high ∧
        ∀ event ∈ phase.events, frontier.cut.Ready event →
          ∀ owner ∈ anchor.application.current.excluded, (graph).actor? event ≠ some owner
  | _, .start => ⟨within, quiet⟩
  | _, .extend prior joint legal realized => by
    have previous := phaseProposalEmissionFrontier_geometry anchor phase anchorLength first
      within quiet prior
    rw [phaseProposalEmissionFrontier]
    split
    · exact frontier_advance_geometry setup mode runtime leaks anchor phase _ _ joint
        previous.1 previous.2
    · exact previous

/-- A genuine offered nonsilent response in the installed commitment interval
has the actual typed binding shape at its requested coordinate. -/
private theorem nonsilent_binding_request
    (phase : RuntimePhase (graph)) (commitment : phase.kind = .commitment)
    (remaining : Nat) (who : Player) (execution : (app).Execution)
    (trace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (installed : execution.application.phases.head? = some phase)
    (material : WitnessedSubmission (graph))
    (offered : (⟨some material⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds who (execution.recall who)
        (execution.observe (app) who)) :
    ∃ (event : (graph).EventId) (payload : L.Ty)
      (binding : (graph).outputLayout event = .binding who payload),
      cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) =
        .bind who payload ∧ event ∈ phase.events ∧
          execution.application.SeedRequest who ⟨execution.application.attempt, event⟩ := by
  obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks bounds
    plan inputs horizon scheduler remaining who execution trace material offered
  have inside : coordinate.event ∈ phase.events := by
    obtain ⟨actual, actualInstalled, member⟩ := request.2.1
    have equal : actual = phase := Option.some.inj ((Option.mem_def.mp actualInstalled).symm.trans
      installed)
    simpa only [equal] using member
  have fields := phase.fields coordinate.event ((phase.mem_events _).mp inside).1
    ((phase.mem_events _).mp inside).2
  rw [commitment] at fields
  obtain ⟨owner, payload, binding⟩ := fields
  cases node : nodeView (graph) coordinate.event with
  | bind actor kind typed code =>
    obtain ⟨rfl, rfl⟩ := EventField.binding.inj (typed.symm.trans binding)
    have actorEq : (graph).actor? coordinate.event = some actor :=
      (EventCode.actor_cast typed ((graph).nodes coordinate.event)).symm.trans
        (congrArg EventCode.actor code)
    have equal : actor = who := Option.some.inj (actorEq.symm.trans request.2.2.2.1)
    subst actor
    refine ⟨coordinate.event, kind, typed, code, inside, ?_⟩
    simpa only [← request.1] using request
  | resolve actor kind source checks typed code => cases typed.symm.trans binding
  | sample kind law typed code => cases typed.symm.trans binding

/-- Every actual counted prefix in the original, exclusion-stable attempt
retains its signed meanings at the SAME emitted frontier. Stability of the
namespace and E is explicit: the fresh-service application discharges it,
whereas an old unsafe anchor is not silently treated as fresh. -/
theorem phaseProposalEmissionFrontier_traceInvariant
    (anchorControl : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchorControl))
    (phase : RuntimePhase (graph))
    (installed : anchorControl.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (first : (graph).Config)
    (within : first.cut.Within phase.low phase.high)
    (quiet : ∀ event ∈ phase.events, first.cut.Ready event →
      ∀ owner ∈ anchorControl.execution.application.current.excluded,
        (graph).actor? event ≠ some owner)
    (entryExcluded : anchorControl.execution.application.entry.excluded =
      anchorControl.execution.application.current.excluded)
    (initialOrigins : ∀ event ∈ first.cut.completed, event.val < phase.low ∨
      ∃ owner ∈ anchorControl.execution.application.current.excluded,
        (graph).actor? event = some owner)
    (initialPrior : ∀ event : (graph).EventId, event.val < phase.low →
      anchorControl.execution.application.entry.native.config.outputs event = first.outputs event)
    (emissions : PhaseProposalEmittedBindings runtime leaks anchorControl.execution phase first)
    (final : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some final))
    (retained : TracePrefix anchorTrace trace)
    (sameAttempt : final.execution.application.attempt =
      anchorControl.execution.application.attempt)
    (sameExcluded : final.execution.application.current.excluded =
      anchorControl.execution.application.current.excluded) :
    PhaseProposalBindingPhaseInvariant setup mode runtime leaks anchorControl.execution phase
      final.execution (phaseProposalEmissionFrontier setup mode runtime leaks
        anchorControl.execution phase anchorTrace.length first initial horizon scheduler
          ((menu).toRawTrace initial horizon scheduler trace)) := by
  let ordered := serviceGraph_revealRelaxedOrdered setup mode
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized ((menu).toRawTrace initial horizon scheduler anchorTrace)
  have anchorFrontier : phaseProposalEmissionFrontier setup mode runtime leaks
      anchorControl.execution phase anchorTrace.length first initial horizon scheduler
        ((menu).toRawTrace initial horizon scheduler anchorTrace) = first := by
    apply phaseProposalEmissionFrontier_before_anchor
    rw [(menu).toRawTrace_length]
  have along : ∀ {target}
      (last : ((menu).protocol initial horizon scheduler).Trace target),
      TracePrefix anchorTrace last → ∃ next : (app).Control, target = some next ∧
        next.execution.application.Ordered ∧
        anchorControl.execution.application.attempt.generation ≤
          next.execution.application.attempt.generation ∧
        anchorControl.execution.application.attempt.phase ≤
          next.execution.application.attempt.phase ∧
        anchorControl.execution.application.current.excluded ⊆
          next.execution.application.current.excluded ∧
        (next.execution.application.attempt = anchorControl.execution.application.attempt →
          next.execution.application.phases = anchorControl.execution.application.phases ∧
          next.execution.application.entry = anchorControl.execution.application.entry ∧
          (next.execution.application.current.excluded =
            anchorControl.execution.application.current.excluded →
            PhaseProposalBindingPhaseInvariant setup mode runtime leaks anchorControl.execution
              phase next.execution (phaseProposalEmissionFrontier setup mode runtime leaks
                anchorControl.execution phase anchorTrace.length first initial horizon scheduler
                  ((menu).toRawTrace initial horizon scheduler last)))) := by
    intro target last kept
    induction kept with
    | refl =>
      refine ⟨anchorControl, rfl, firstOrdered, le_rfl, le_rfl, Finset.Subset.refl _, ?_⟩
      intro _
      refine ⟨rfl, rfl, fun _ => ?_⟩
      rw [anchorFrontier]
      exact ⟨within, quiet, emissions⟩
    | @extend source target earlier kept joint legal reached ih =>
      obtain ⟨middle, rfl, middleOrdered, lowerGen, lowerPhase, lowerE, previous⟩ := ih
      have actual : target ∈ ((app).transition initial horizon scheduler (some middle)
          joint).support := reached
      obtain ⟨next, rfl, _recall⟩ := (app).transition_recall_prefix initial horizon scheduler
        middle target joint actual
      have nextOrdered := (phaseApplication_seedOrder runtime leaks).transition initial horizon
        scheduler initialized (some middle) (some next) joint middleOrdered actual
      have progress := (phaseApplication_namespace_progress runtime leaks).transition initial
        horizon scheduler middle next joint actual middleOrdered
      have excluded := (phaseApplication_exclusion_monotone runtime leaks).transition initial
        horizon scheduler middle next joint actual
      refine ⟨next, rfl, nextOrdered, lowerGen.trans progress.1, lowerPhase.trans progress.2,
        lowerE.trans excluded, ?_⟩
      intro nextSame
      have middleSame : middle.execution.application.attempt =
          anchorControl.execution.application.attempt := by
        have generation := congrArg CommitAttemptId.generation nextSame
        have phaseRank := congrArg CommitAttemptId.phase nextSame
        cases left : middle.execution.application.attempt with
        | mk leftPhase leftGeneration =>
          cases right : anchorControl.execution.application.attempt with
          | mk rightPhase rightGeneration =>
            simp only [left, right] at lowerGen lowerPhase progress generation phaseRank ⊢
            congr 1 <;> omega
      obtain ⟨middlePhases, middleEntry, invariant⟩ := previous middleSame
      have stepSame := middleSame.trans nextSame.symm
      have nextPhases := ((phaseApplication_sameAttempt_controls runtime leaks).transition initial
        horizon scheduler middle next joint actual middleOrdered stepSame).1.trans middlePhases
      have nextEntry := ((phaseApplication_sameAttempt_entry runtime leaks).transition initial
        horizon scheduler middle next joint actual middleOrdered stepSame).trans middleEntry
      refine ⟨nextPhases, nextEntry, ?_⟩
      intro nextE
      have middleE : middle.execution.application.current.excluded =
          anchorControl.execution.application.current.excluded :=
        Finset.Subset.antisymm (by simpa only [nextE] using excluded) lowerE
      have holds := invariant middleE
      let frontier := phaseProposalEmissionFrontier setup mode runtime leaks
        anchorControl.execution phase anchorTrace.length first initial horizon scheduler
          ((menu).toRawTrace initial horizon scheduler earlier)
      have rawKept : TracePrefix
          ((menu).toRawTrace initial horizon scheduler anchorTrace)
          ((menu).toRawTrace initial horizon scheduler earlier) :=
        ((menu).reaches_raw initial horizon scheduler kept.reachesWithin).tracePrefix
      have prior : ∀ event : (graph).EventId, event.val < phase.low →
          middle.execution.application.entry.native.config.outputs event = frontier.outputs event :=
        by
        intro event below
        obtain ⟨value, written⟩ := Option.isSome_iff_exists.mp
          ((first.output_available event).mpr (within.1 event below))
        have stored : (phaseProposalEmissionFrontier setup mode runtime leaks
            anchorControl.execution phase anchorTrace.length first initial horizon scheduler
              ((menu).toRawTrace initial horizon scheduler anchorTrace)).store (.inr event) =
              some value := by simpa only [anchorFrontier, Config.store_output] using written
        have held := phaseProposalEmissionFrontier_prefix_preserves setup mode runtime leaks
          anchorControl.execution phase anchorTrace.length first initial horizon scheduler
            (.inr event) value stored rawKept
        exact (congrArg (fun entry => entry.native.config.outputs event) middleEntry).trans
          ((initialPrior event below).trans (written.trans held.symm))
      have geometry := phaseProposalEmissionFrontier_geometry setup mode runtime leaks plan inputs
        horizon scheduler anchorControl.execution phase anchorTrace.length first within quiet
          ((menu).toRawTrace initial horizon scheduler (earlier.extend joint legal reached))
      refine ⟨geometry.1, geometry.2, ?_⟩
      have installedMiddle : middle.execution.application.phases.head? = some phase := by
        rw [middlePhases]
        exact installed
      have entryEMiddle : middle.execution.application.entry.excluded =
          anchorControl.execution.application.current.excluded := by
        rw [middleEntry]
        exact entryExcluded
      rcases middle with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
        have present : (joint who).isSome := by
          cases selected : joint who with
          | none =>
            have inactive := legal.2 who
            rw [selected] at inactive
            exact (inactive (by rfl)).elim
          | some response => rfl
        obtain ⟨response, selected⟩ := Option.isSome_iff_exists.mp present
        have nextEq : next = ⟨remaining, none, execution.respond (app) who response⟩ := by
          apply Option.some.inj
          have pure := (PMF.mem_support_pure_iff _ _).mp actual
          simpa only [ReactiveApplication.transition, selected, Option.getD_some] using pure
        subst next
        cases transmitted : response.transmission with
        | none =>
          have responseEq : response = ⟨none⟩ := by cases response; cases transmitted; rfl
          have unchanged : (execution.respond (app) who response).application =
              execution.application := by rw [responseEq]; rfl
          have sameInputs : (execution.respond (app) who response).network.inputs =
              execution.network.inputs := by rw [responseEq]; rfl
          have stepF : phaseProposalEmissionFrontier setup mode runtime leaks
              anchorControl.execution phase anchorTrace.length first initial horizon scheduler
                ((menu).toRawTrace initial horizon scheduler
                  (earlier.extend joint legal reached)) = frontier := by
            rw [ReactiveApplication.ResponseMenu.toRawTrace, phaseProposalEmissionFrontier,
              ite_eq_left (by simpa only [(menu).toRawTrace_length] using kept.length_le)]
            simp only [phaseProposalBindingFrontierAdvance, middleSame, ↓reduceIte,
              selected, Option.getD_some, transmitted]
            rfl
          rw [stepF]
          simpa only [PhaseProposalEmittedBindings, unchanged, sameInputs] using holds.emissions
        | some material =>
          have offered : (⟨some material⟩ : (app).Action) ∈
              PhaseCount.onePacketActions runtime leaks bounds who (execution.recall who)
                (execution.observe (app) who) := by
            have allowed := legal.2 who
            rw [selected] at allowed
            have equal : response = ⟨some material⟩ := by
              cases response; cases transmitted; rfl
            have member := allowed.2
            change response ∈ PhaseCount.onePacketActions runtime leaks bounds who
              (execution.recall who) (execution.observe (app) who) at member
            simpa only [equal] using member
          obtain ⟨event, payload, binding, code, inside, request⟩ := nonsilent_binding_request
            setup mode runtime leaks bounds plan inputs horizon scheduler phase commitment remaining
              who execution earlier installedMiddle material offered
          have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds plan ordered inputs
            horizon scheduler remaining who execution earlier _ request material offered
          have ready := phaseProposalEmissionFrontier_ready setup mode runtime leaks bounds plan
            inputs horizon scheduler anchorControl.execution phase anchorTrace.length first
              ⟨remaining, some who, execution⟩ earlier installedMiddle commitment middleSame middleE
                entryEMiddle initialOrigins prior holds.emissions
                  (by simpa only [← entryEMiddle] using holds.quiet) holds.within.2 who event
                    request.2.2.1 request.2.2.2.1 request.2.2.2.2 unsent
          exact phaseProposalEmissionFrontier_binding_step setup mode runtime leaks bounds plan
            inputs horizon scheduler anchorControl.execution phase anchorTrace.length first
              remaining
              who execution earlier joint legal response selected reached material transmitted event
                payload binding code request inside middleSame kept.length_le holds.emissions
                  ready.1
      | none =>
        have stepF : phaseProposalEmissionFrontier setup mode runtime leaks
            anchorControl.execution phase anchorTrace.length first initial horizon scheduler
              ((menu).toRawTrace initial horizon scheduler (earlier.extend joint legal reached)) =
              frontier := by
          rw [ReactiveApplication.ResponseMenu.toRawTrace, phaseProposalEmissionFrontier,
            ite_eq_left (by simpa only [(menu).toRawTrace_length] using kept.length_le)]
          exact phaseProposalBindingFrontierAdvance_idle setup mode runtime leaks _ _ _ _ _ joint
        rw [stepF]
        cases remaining with
        | zero =>
          have equal := (PMF.mem_support_pure_iff _ _).mp actual
          cases Option.some.inj equal
          exact holds.emissions
        | succ remaining =>
          rw [ReactiveApplication.transition, PMF.mem_support_bind_iff] at actual
          obtain ⟨command, _chosen, moved⟩ := actual
          obtain ⟨after, moved, equality⟩ := PMF.support_map .. ▸ moved
          have sameExecution : next.execution = after :=
            congrArg ReactiveApplication.Control.execution (Option.some.inj equality.symm)
          rw [sameExecution]
          exact phaseProposalEmittedBindings_environment runtime leaks bounds plan inputs horizon
            scheduler ⟨remaining + 1, none, execution⟩ earlier after command moved phase frontier
              frontier holds.emissions (by simpa only [sameExecution] using stepSame)
                (fun _ _ written => written)
  obtain ⟨next, equal, _ordered, _generation, _phase, _excluded, result⟩ := along trace retained
  cases Option.some.inj equal
  exact (result sameAttempt).2.2 sameExcluded

private theorem frontier_one_response
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (anchorLength : Nat)
    (first : (graph).Config)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (profile : ∀ who, ((menu).information initial horizon scheduler).BehavioralPolicy who)
    (remaining : Nat) (who : Player) (execution : (app).Execution)
    (trace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (later : anchorLength ≤ trace.length) :
    let potential := fun history : ((menu).protocol initial horizon scheduler).History =>
      (graph).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values)
        (phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength first
          initial horizon scheduler ((menu).toRawTrace initial horizon scheduler history.trace))
    let frontier := phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength
      first initial horizon scheduler ((menu).toRawTrace initial horizon scheduler trace)
    (((menu).information initial horizon scheduler).runBehavioralFrom profile 1
      ⟨some ⟨remaining, some who, execution⟩, trace⟩).bind potential =
      ((menu).decodeProfile initial horizon scheduler profile who (execution.recall who)
        (execution.observe (app) who)).bind fun response =>
          (graph).canonicalContinuation
            (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values)
            (phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor phase frontier
              (some ⟨remaining, some who, execution⟩)
              (Function.update (fun _ => none) who (some response))) := by
  intro potential frontier
  let model := (menu).information initial horizon scheduler
  let history : ((menu).protocol initial horizon scheduler).History :=
    ⟨some ⟨remaining, some who, execution⟩, trace⟩
  have running : ¬ ((menu).protocol initial horizon scheduler).terminal history.state := by
    simp only [history, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal,
      reduceCtorEq, and_false, not_false_eq_true]
  have draw : model.behavioralJoint profile trace running =
      (profile who (model.infoOf who trace)).map
        (model.jointOfChoice ((app).singleMover initial horizon scheduler) history running who
          (by rfl)) := by
    have unique : ∀ other, ((menu).protocol initial horizon scheduler).active history.state other →
        other = who := by
      intro other active
      exact (Option.some.inj active).symm
    rw [model.behavioralJoint_eq_map_of_at_most_one_active profile trace running who unique]
    apply congrArg (fun f => (profile who (model.infoOf who trace)).map f)
    funext choice
    apply Subtype.ext
    rfl
  rw [model.runBehavioralFrom_succ_of_not_terminal profile 0 running, PMF.bind_bind, draw,
    PMF.bind_map]
  simp only [InformationModel.runBehavioralFrom, runRandomizedFor_zero]
  have expansion : ∀ choice : model.Choice who (model.infoOf who trace),
      (((menu).protocol initial horizon scheduler).step history.state
        (model.jointOfChoice ((app).singleMover initial horizon scheduler) history running who
          (by rfl) choice)).bindOnSupport (fun _ realized =>
            potential (history.extend _ realized)) =
      (graph).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values)
        (phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor phase frontier
          history.state (Function.update (fun _ => none) who choice.1)) := by
    intro choice
    have joints : (model.jointOfChoice ((app).singleMover initial horizon scheduler) history
        running who (by rfl) choice).1 = Function.update (fun _ => none) who choice.1 := by
      funext other
      by_cases same : other = who
      · subst other
        simp [InformationModel.jointOfChoice, singletonJoint]
      · simp [InformationModel.jointOfChoice, singletonJoint, same]
    rw [bindOnSupport_eq_bind_of_eq_on_support _ (g := fun _ =>
      (graph).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values)
        (phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor phase frontier
          history.state (Function.update (fun _ => none) who choice.1))) (by
            intro target realized
            dsimp only [potential, History.extend,
              ReactiveApplication.ResponseMenu.toRawTrace]
            rw [phaseProposalEmissionFrontier]
            have laterRaw : anchorLength ≤ ((menu).toRawTrace initial horizon scheduler
                history.trace).length := by
              change anchorLength ≤ ((menu).toRawTrace initial horizon scheduler trace).length
              rw [(menu).toRawTrace_length]
              exact later
            rw [ite_eq_left laterRaw]
            change (graph).canonicalContinuation _
              (phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor phase frontier
                history.state (((menu).protocol initial horizon scheduler).singletonJoint
                  who choice.1)) = _
            rw [show ((menu).protocol initial horizon scheduler).singletonJoint who choice.1 =
                Function.update (fun _ => none) who choice.1 from by
                  funext other
                  by_cases same : other = who
                  · subst other
                    simp only [singletonJoint, dite_true, Function.update_self]
                  · simp only [singletonJoint, same, dite_false,
                      Function.update_of_ne same]] )]
    exact PMF.bind_const _ _
  calc
    _ = (profile who (model.infoOf who trace)).bind (fun choice =>
        (graph).canonicalContinuation
          (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values)
          (phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor phase frontier
            history.state (Function.update (fun _ => none) who choice.1))) := by
      apply bind_congr_on_support
      intro choice _supported
      dsimp only [Function.comp_apply]
      rw [bindOnSupport_bind]
      simpa only [PMF.pure_bind] using expansion choice
    _ = _ := ?_
  have available : ∀ choice : model.Choice who (model.infoOf who trace),
      choice.1 = some (choice.1.getD ⟨none⟩) := by
    intro choice
    have legal := (model.menu_adequate who trace choice.1).mp choice.2
    cases selected : choice.1 with
    | none =>
      rw [selected] at legal
      exact (legal (by rfl)).elim
    | some response => rfl
  conv_lhs =>
    arg 2
    ext choice
    rw [available choice]
  let project := fun choice : model.Choice who (model.infoOf who trace) =>
    choice.1.getD (⟨none⟩ : (app).Action)
  let responseKernel := fun response : (app).Action =>
    (graph).canonicalContinuation
      (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values)
      (phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor phase frontier
        history.state (Function.update (fun _ => none) who (some response)))
  have observed : model.infoOf who trace =
      some (execution.recall who, execution.observe (app) who) :=
    ((menu).info initial horizon scheduler who trace).trans (ite_eq_left rfl)
  let responseAt := fun info : model.InfoState who =>
    (profile who info).map (fun choice => choice.1.getD (⟨none⟩ : (app).Action))
  have responseLaw : (profile who (model.infoOf who trace)).map project =
      (menu).decodeProfile initial horizon scheduler profile who (execution.recall who)
        (execution.observe (app) who) := by
    calc
      _ = responseAt (model.infoOf who trace) := rfl
      _ = responseAt (some (execution.recall who, execution.observe (app) who)) :=
        congrArg responseAt observed
      _ = _ := by
        unfold ReactiveApplication.ResponseMenu.decodeProfile ReactiveApplication.decodePolicy
          ReactiveApplication.ResponseMenu.embedPolicy
        rw [PMF.map_comp]
        apply congrArg (fun f => (profile who
          (some (execution.recall who, execution.observe (app) who))).map f)
        funext choice
        rfl
  change ((profile who (model.infoOf who trace)).bind (responseKernel ∘ project)) = _
  rw [← PMF.bind_map, responseLaw]


private theorem frontier_one_environment
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (anchorLength : Nat)
    (first : (graph).Config)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (profile : ∀ who, ((menu).information initial horizon scheduler).BehavioralPolicy who)
    (remaining : Nat) (execution : (app).Execution)
    (trace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩)) :
    let potential := fun history : ((menu).protocol initial horizon scheduler).History =>
      (graph).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values)
        (phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength first
          initial horizon scheduler ((menu).toRawTrace initial horizon scheduler history.trace))
    (((menu).information initial horizon scheduler).runBehavioralFrom profile 1
      ⟨some ⟨remaining, none, execution⟩, trace⟩).bind potential =
      potential ⟨some ⟨remaining, none, execution⟩, trace⟩ := by
  intro potential
  let model := (menu).information initial horizon scheduler
  let history : ((menu).protocol initial horizon scheduler).History :=
    ⟨some ⟨remaining, none, execution⟩, trace⟩
  by_cases ended : ((menu).protocol initial horizon scheduler).terminal history.state
  · rw [model.runBehavioralFrom_of_terminal profile 1 ended, PMF.pure_bind]
  rw [model.runBehavioralFrom_succ_of_not_terminal profile 0 ended, PMF.bind_bind]
  simp only [InformationModel.runBehavioralFrom, runRandomizedFor_zero]
  have constant : ∀ draw,
      (((menu).protocol initial horizon scheduler).step history.state draw).bindOnSupport
        (fun _ realized => potential (history.extend draw.2 realized)) = potential history := by
    intro draw
    rw [bindOnSupport_eq_bind_of_eq_on_support _ (g := fun _ => potential history) (by
      intro target realized
      dsimp only [potential, History.extend]
      rw [ReactiveApplication.ResponseMenu.toRawTrace, phaseProposalEmissionFrontier]
      split
      · rw [phaseProposalBindingFrontierAdvance_idle]
      · rfl)]
    exact PMF.bind_const _ _
  calc
    _ = (model.behavioralJoint profile history.trace ended).bind
        (fun _ => potential history) := by
      apply bind_congr_on_support
      intro draw _supported
      rw [bindOnSupport_bind]
      simpa only [PMF.pure_bind] using constant draw
    _ = _ := PMF.bind_const _ _

/-- Binding fields completed automatically for inherited exclusions contain
literal failure. This statement concerns the emitted graph ideal only. -/
def PhaseProposalAutomaticBindingValues (phase : RuntimePhase (graph)) (excluded : Finset Player)
    (frontier : (graph).Config) : Prop :=
  ∀ event ∈ phase.events, ∀ owner ∈ excluded,
    ∀ payload (binding : (graph).outputLayout event = .binding owner payload),
      event ∈ frontier.cut.completed →
        (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
          frontier.store = some .failure

omit [Fintype Player] in
private theorem frontier_drain_failures
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (frontier : (graph).Config)
    (automatic : ∀ event ∈ phase.events, ∀ owner ∈ anchor.application.current.excluded,
      ∀ payload (binding : (graph).outputLayout event = .binding owner payload),
        event ∈ frontier.cut.completed →
          (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
            frontier.store = some .failure) :
    let after := phaseProposalBindingFrontierDrain setup mode runtime leaks anchor phase frontier
    ∀ event ∈ phase.events, ∀ owner ∈ anchor.application.current.excluded,
      ∀ payload (binding : (graph).outputLayout event = .binding owner payload),
        event ∈ after.cut.completed →
          (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
            after.store = some .failure := by
  let state : RecoveryState (graph) :=
    ⟨{ anchor.application.current.native with config := frontier },
      anchor.application.current.excluded⟩
  have preserve : ∀ after, Relation.ReflTransGen phase.AutomaticStep state after →
      ∀ event ∈ phase.events, ∀ owner ∈ anchor.application.current.excluded,
        ∀ payload (binding : (graph).outputLayout event = .binding owner payload),
          event ∈ after.native.config.cut.completed →
            (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
              after.native.config.store = some .failure := by
    intro after path
    induction path with
    | refl => exact automatic
    | @tail middle after path step ih =>
      obtain ⟨selected, eligible, rfl⟩ := step
      intro event inside owner excluded payload binding completed
      obtain ⟨action, supported⟩ := middle.completeAutomatic_step selected eligible.2
      rw [middle.native.config.step_cut selected eligible.2.1 action _ supported,
        EventOrder.Cut.mem_complete] at completed
      rcases completed with same | old
      · subst event
        cases node : nodeView (graph) selected with
        | bind actor ty typed code =>
          obtain ⟨rfl, rfl⟩ := EventField.binding.inj (typed.symm.trans binding)
          change cast (congrArg (fun field : EventField Player L => Option field.Value) typed)
            ((middle.native.completeFailure selected eligible.2.1).config.outputs selected) =
              some PublicationResult.failure
          rw [State.completeFailure, node]
          change cast (congrArg (fun field : EventField Player L => Option field.Value) typed)
            ((middle.native.config.complete selected eligible.2.1 _ _).outputs selected) = _
          rw [Config.complete_output_same]
          have cancel {A B : Type} (equal : A = B) (value : B) :
              cast (congrArg Option equal) (some (cast equal.symm value)) = some value := by
            cases equal
            rfl
          exact cancel (congrArg EventField.Value typed) PublicationResult.failure
        | resolve actor ty source checks typed code => cases typed.symm.trans binding
        | sample ty law typed code => cases typed.symm.trans binding
      · exact (⟨.inr event, binding⟩ :
          FieldRef (graph).layout (.binding owner payload)).get?_preserved
          middle.native.config.store
            (middle.completeAutomatic selected eligible.2).native.config.store
            (middle.native.config.step_store_of_some _ selected eligible.2.1 action supported)
              .failure (ih event inside owner excluded payload binding old)
  exact preserve _ (phase.drain_trace state)

omit [Fintype Player] in
private theorem frontier_complete_failures
    (phase : RuntimePhase (graph)) (excluded : Finset Player) (frontier : (graph).Config)
    (automatic : PhaseProposalAutomaticBindingValues setup mode phase excluded frontier)
    (event : (graph).EventId) (ready : frontier.cut.Ready event)
    (action : (graph).Action event) (value : ((graph).outputLayout event).Value)
    (owner : Player) (acting : (graph).actor? event = some owner) (active : owner ∉ excluded) :
    PhaseProposalAutomaticBindingValues setup mode phase excluded
      (frontier.complete event ready action value) := by
  intro query inside who inherited payload binding completed
  rw [Config.complete_cut, EventOrder.Cut.mem_complete] at completed
  rcases completed with same | old
  · subst query
    have sameOwner : who = owner := Option.some.inj
      (((graph).actor?_of_outputLayout_binding binding).symm.trans acting)
    exact (active (sameOwner ▸ inherited)).elim
  · exact (⟨.inr query, binding⟩ : FieldRef (graph).layout (.binding who payload)).get?_preserved
      frontier.store (frontier.complete event ready action value).store
        (frontier.complete_store_of_some event ready action value) .failure
          (automatic query inside who inherited payload binding old)

omit [Fintype Player] in
private theorem frontier_advance_failures
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (frontier : (graph).Config)
    (before : (app).ProtocolState) (joint : Player → Option (app).Action)
    (quiet : ∀ event ∈ phase.events, frontier.cut.Ready event →
      ∀ owner ∈ anchor.application.current.excluded, (graph).actor? event ≠ some owner)
    (automatic : PhaseProposalAutomaticBindingValues setup mode phase
      anchor.application.current.excluded frontier) :
    PhaseProposalAutomaticBindingValues setup mode phase anchor.application.current.excluded
      (phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor phase frontier
        before joint) := by
  cases before with
  | none => exact automatic
  | some control =>
    by_cases attempted : control.execution.application.attempt = anchor.application.attempt
    · cases actor : control.actor with
      | none =>
        simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor]
          using automatic
      | some who =>
        cases sent : ((joint who).getD ⟨none⟩).transmission with
        | none =>
          simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor, sent]
            using automatic
        | some material =>
          cases packet : material.call.packet with
          | opening =>
            simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor,
              sent, packet] using automatic
          | malformed =>
            simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor,
              sent, packet] using automatic
          | commitment event candidate =>
            by_cases inside : event ∈ phase.events
            · cases node : nodeView (graph) event with
              | bind owner payload binding code =>
                by_cases same : owner = who
                · by_cases ready : frontier.cut.Ready event
                  · have acting : (graph).actor? event = some owner :=
                      (graph).actor?_of_outputLayout_binding binding
                    have active : owner ∉ anchor.application.current.excluded :=
                      fun excluded => quiet event inside ready owner excluded acting
                    let result :=
                      ((((joint who).getD ⟨none⟩).transmission.bind
                        PhaseProposal.bindingPreparation).bind (fun raw => raw.as? payload)).elim
                          PublicationResult.failure PublicationResult.success
                    let action := cast (congrArg EventField.Action binding.symm) result
                    let value := cast (congrArg EventField.Value binding.symm) result
                    have completed := frontier_complete_failures setup mode phase
                      anchor.application.current.excluded frontier automatic event ready action
                        value owner acting active
                    have drained := frontier_drain_failures setup mode runtime leaks anchor phase
                      (frontier.complete event ready action value) completed
                    simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte,
                      actor, sent, packet, inside, node, same, ready, dite_true, dite_false,
                      action, value, result, PhaseProposalAutomaticBindingValues] using drained
                  · simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte,
                      actor, sent, packet, inside, node, same, ready, dite_true, dite_false]
                        using automatic
                · simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte,
                    actor, sent, packet, inside, node, same] using automatic
              | resolve =>
                simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor,
                  sent, packet, inside, node] using automatic
              | sample =>
                simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor,
                  sent, packet, inside, node] using automatic
            · simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor,
                sent, packet, inside] using automatic
    · simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte]
        using automatic

omit [Fintype Player] in
/-- The SAME signed trace cannot turn an inherited automatic failure into a
hidden usable value. Quietness rules out a forged active completion of E. -/
theorem phaseProposalEmissionFrontier_automatic_values
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (anchorLength : Nat)
    (first : (graph).Config) (within : first.cut.Within phase.low phase.high)
    (quiet : ∀ event ∈ phase.events, first.cut.Ready event →
      ∀ owner ∈ anchor.application.current.excluded, (graph).actor? event ≠ some owner)
    (automatic : PhaseProposalAutomaticBindingValues setup mode phase
      anchor.application.current.excluded first) :
    ∀ {state : (app).ProtocolState}
      (trace : ((app).protocol initial horizon scheduler).Trace state),
      PhaseProposalAutomaticBindingValues setup mode phase anchor.application.current.excluded
        (phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength first
          initial horizon scheduler trace)
  | _, .start => automatic
  | _, .extend prior joint legal realized => by
    have previous := phaseProposalEmissionFrontier_automatic_values anchor phase anchorLength
      first within quiet automatic prior
    have geometry := phaseProposalEmissionFrontier_geometry setup mode runtime leaks plan inputs
      horizon scheduler anchor phase anchorLength first within quiet prior
    rw [phaseProposalEmissionFrontier]
    split
    · exact frontier_advance_failures setup mode runtime leaks anchor phase _ _ joint
        geometry.2 previous
    · exact previous

/-- The callback frame contains only literal operational readouts. In
particular it assumes neither a source law nor independence of pending values.
The trace invariant supplies its emission/domain components before the
stopping law is evaluated. -/
structure PhaseProposalBindingCallbackFrame
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (execution : (app).Execution) (frontier : (graph).Config)
    (actor : Option Player) : Prop where
  installed : execution.application.phases.head? = some phase
  excluded : execution.application.current.excluded = anchor.application.current.excluded
  retired : execution.application.retired = anchor.application.retired
  failures : ∀ rank ≤ execution.application.attempt.phase,
    execution.application.current.native.publicView.sourceFailureFootprint.1 rank =
      anchor.application.current.native.publicView.sourceFailureFootprint.1 rank
  agreement : execution.application.current.native.config.CompletedOutputAgreement frontier
  inputs : execution.application.current.native.config.inputs = frontier.inputs
  archive : ∀ who, actor = some who →
    PhaseProposal.observedSourceArchive runtime leaks (execution.recall who)
        (execution.observe (app) who) =
      PhaseProposal.observedSourceArchive runtime leaks (anchor.recall who)
        (phaseProposalBindingGraphView setup mode runtime leaks anchor who
          ((graph).playerObserve who execution.application.current.native.config))
  hidden : ∀ who event, execution.application.current.native.config.cut.Ready event →
    (graph).actor? event = some who → who ∉ execution.application.current.excluded →
    (∀ message ∈ (app).outputs (execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩) →
    ∀ pending ∈ frontier.cut.completed,
      pending ∉ execution.application.current.native.config.cut.completed →
        ¬ (graph).fieldVisibleTo who (.inr pending)
  within : frontier.cut.Within phase.low phase.high
  quiet : ∀ event ∈ phase.events, frontier.cut.Ready event →
    ∀ owner ∈ anchor.application.current.excluded, (graph).actor? event ≠ some owner
  emissions : PhaseProposalEmittedBindings runtime leaks execution phase frontier

/-- Physical completed-store agreement, fresh-drawer concealment and the full
entry archive are consequences of the same signed emission fold. The only
exclusion equality used here is a factual property of the actual prefix. -/
theorem phaseProposalEmissionFrontier_callback_frame
    (complete : leaks = MessageNetwork.completePendingObservation)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (anchor : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (phase : RuntimePhase (graph))
    (installed : anchor.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (entryExcluded : anchor.execution.application.entry.excluded =
      anchor.execution.application.current.excluded)
    (initialOrigins : ∀ event ∈ anchor.execution.application.current.native.config.cut.completed,
      event.val < phase.low ∨ ∃ owner ∈ anchor.execution.application.current.excluded,
        (graph).actor? event = some owner)
    (emissions : PhaseProposalEmittedBindings runtime leaks anchor.execution phase
      anchor.execution.application.current.native.config)
    (current : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some current))
    (kept : TracePrefix anchorTrace trace)
    (sameAttempt : current.execution.application.attempt =
      anchor.execution.application.attempt)
    (sameExcluded : current.execution.application.current.excluded =
      anchor.execution.application.current.excluded) :
    PhaseProposalBindingCallbackFrame setup mode runtime leaks anchor.execution phase
      current.execution (phaseProposalEmissionFrontier setup mode runtime leaks anchor.execution
        phase anchorTrace.length anchor.execution.application.current.native.config initial horizon
          scheduler ((menu).toRawTrace initial horizon scheduler trace)) current.actor := by
  let first := anchor.execution.application.current.native.config
  let frontier := phaseProposalEmissionFrontier setup mode runtime leaks anchor.execution phase
    anchorTrace.length first initial horizon scheduler
      ((menu).toRawTrace initial horizon scheduler trace)
  let raw := (menu).toRawTrace initial horizon scheduler trace
  let anchorRaw := (menu).toRawTrace initial horizon scheduler anchorTrace
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have anchorOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler initialized anchorRaw
  have currentOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler initialized raw
  have metadata := phase_attempt_metadata_of_prefix runtime leaks menu initial initialized horizon
    scheduler anchor current anchorTrace trace kept anchorOrdered sameAttempt.symm
  have currentPhase : current.execution.application.phases.head? = some phase :=
    (congrArg (fun phases => phases.head?) (congrArg Prod.fst metadata)).symm.trans installed
  have progress := phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
    scheduler anchor current anchorTrace trace kept anchorOrdered
  have currentEntry : current.execution.application.entry = anchor.execution.application.entry :=
    (progress.2.2 sameAttempt.symm).symm
  have receipts := phaseReceiptRecord_history runtime leaks
    (serviceGraph_revealRelaxedOrdered setup mode) plan inputs horizon scheduler anchorRaw
  have position : anchor.execution.application.entry.native.config.cut.IsPrefix phase.low ∧
      first.cut.Within phase.low phase.high := by
    have positioned := receipts.exclusion.frontier.positioned
    cases phases : anchor.execution.application.phases with
    | nil => simp only [phases, List.head?_nil, reduceCtorEq] at installed
    | cons head rest =>
      have same : head = phase := by
        simpa only [phases, List.head?_cons, Option.some.injEq] using installed
      subst head
      simpa only [PhaseRuntimeState.Positioned, phases, first] using positioned
  have quiet : ∀ event ∈ phase.events, first.cut.Ready event →
      ∀ owner ∈ anchor.execution.application.current.excluded,
        (graph).actor? event ≠ some owner := by
    intro event _inside ready owner excluded acting
    have quiescent := (phaseApplication_quiescent runtime leaks
      (serviceGraph_revealRelaxedOrdered setup mode)).history initial horizon scheduler (by
        intro state supported
        obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
        exact phaseApplication_initial_quiescent plan
          (serviceGraph_revealRelaxedOrdered setup mode) maximal draw) anchorRaw
    exact quiescent.2.2 event ⟨ready, by rwa [acting]⟩
  have initialPrior : ∀ event : (graph).EventId, event.val < phase.low →
      anchor.execution.application.entry.native.config.outputs event = first.outputs event := by
    intro event below
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
      ((anchor.execution.application.entry.native.config.output_available event).mpr
        ((position.1.2 event).mpr below))
    exact stored.trans
      ((phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler anchorRaw)
        (.inr event) value stored).symm
  have invariant := phaseProposalEmissionFrontier_traceInvariant setup mode runtime leaks bounds
    plan inputs horizon scheduler anchor anchorTrace phase installed commitment first position.2
      quiet entryExcluded initialOrigins initialPrior emissions current trace kept sameAttempt
        sameExcluded
  have rawKept := ((menu).reaches_raw initial horizon scheduler kept.reachesWithin).tracePrefix
  have atAnchor : phaseProposalEmissionFrontier setup mode runtime leaks anchor.execution phase
      anchorTrace.length first initial horizon scheduler anchorRaw = first := by
    apply phaseProposalEmissionFrontier_before_anchor
    rw [(menu).toRawTrace_length]
  have prior : ∀ event : (graph).EventId, event.val < phase.low →
      current.execution.application.entry.native.config.outputs event = frontier.outputs event := by
    intro event below
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
      ((first.output_available event).mpr (position.2.1 event below))
    have priorStore : (phaseProposalEmissionFrontier setup mode runtime leaks anchor.execution phase
        anchorTrace.length first initial horizon scheduler anchorRaw).store (.inr event) =
          some value := by simpa only [atAnchor, Config.store_output] using stored
    have held := phaseProposalEmissionFrontier_prefix_preserves setup mode runtime leaks
      anchor.execution phase anchorTrace.length first initial horizon scheduler (.inr event) value
        priorStore rawKept
    exact (congrArg (fun entry => entry.native.config.outputs event) currentEntry).trans
      ((initialPrior event below).trans (stored.trans held.symm))
  have entryE : current.execution.application.entry.excluded =
      anchor.execution.application.current.excluded := by rw [currentEntry]; exact entryExcluded
  have sameE : current.execution.application.current.excluded =
      current.execution.application.entry.excluded := sameExcluded.trans entryE.symm
  have silent : ∀ event ∈ phase.events, frontier.cut.Ready event →
      ∀ owner ∈ current.execution.application.entry.excluded,
        (graph).actor? event ≠ some owner := by simpa only [entryE] using invariant.quiet
  have domain := phaseProposalBinding_settled_domain runtime leaks bounds plan inputs horizon
    scheduler (serviceGraph_revealRelaxedOrdered setup mode) current trace phase currentPhase
      commitment frontier sameE prior invariant.emissions silent
  have initialAutomatic : PhaseProposalAutomaticBindingValues setup mode phase
      anchor.execution.application.current.excluded first := by
    intro event inside owner excluded payload binding completed
    exact phaseProposal_completed_inherited_binding runtime leaks bounds plan inputs horizon
      scheduler (serviceGraph_revealRelaxedOrdered setup mode) anchor anchorTrace phase
        (Option.mem_def.mpr installed) commitment owner event payload binding inside completed
          (entryExcluded.symm ▸ excluded)
  have automatic := phaseProposalEmissionFrontier_automatic_values setup mode runtime leaks plan
    inputs horizon scheduler anchor.execution phase anchorTrace.length first position.2 quiet
      initialAutomatic raw
  have agreement := phaseProposalBinding_completed_agreement runtime leaks bounds plan inputs
    horizon scheduler (serviceGraph_revealRelaxedOrdered setup mode) current trace phase
      currentPhase commitment frontier sameE domain prior invariant.emissions (by
        intro event completed inside owner excluded payload binding
        exact automatic event inside owner (entryE ▸ excluded) payload binding completed)
  have storeExtension := (phase_prefix_semantic_extension runtime leaks menu initial horizon
    scheduler anchor current anchorTrace trace kept anchorOrdered sameAttempt.symm).1
  have inputEq : current.execution.application.current.native.config.inputs = frontier.inputs := by
    funext index
    have originalStore : (phaseProposalEmissionFrontier setup mode runtime leaks anchor.execution
        phase anchorTrace.length first initial horizon scheduler anchorRaw).store (.inl index) =
          some (first.inputs index) := by simp only [atAnchor, Config.store_input]
    have held := phaseProposalEmissionFrontier_prefix_preserves setup mode runtime leaks
      anchor.execution phase anchorTrace.length first initial horizon scheduler (.inl index)
        (first.inputs index) originalStore rawKept
    have physical := storeExtension (.inl index) (first.inputs index) (by rfl)
    exact (Option.some.inj physical).trans (Option.some.inj held).symm
  refine ⟨currentPhase, sameExcluded, (congrArg Prod.snd metadata).symm, ?_, agreement,
    inputEq, ?_, ?_, invariant.within, invariant.quiet, invariant.emissions⟩
  · intro rank bounded
    have address : current.execution.application.attempt.phase = phase.low := by
      simp only [PhaseRuntimeState.attempt, currentPhase, Option.map_some, Option.getD_some]
    have currentFailure := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
      scheduler raw
    have anchorFailure := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
      scheduler anchorRaw
    rw [State.sourceFailureFootprint_read, State.sourceFailureFootprint_read]
    exact (currentFailure.failureOwnersBefore_eq_below phase.low
      (fun event below => by rw [currentEntry]; exact (position.1.2 event).mpr below) rank
        (address ▸ bounded)).symm.trans
          ((congrArg (fun entry => entry.native.failureOwnersBefore rank) currentEntry).trans
            (anchorFailure.failureOwnersBefore_eq_below phase.low
              (fun event below => (position.1.2 event).mpr below) rank (address ▸ bounded)))
  · intro who active
    rw [PhaseProposal.observedSourceArchive_eq_submitted runtime leaks complete initial horizon
      scheduler current raw who active,
      phaseProposalBindingGraphView_archive setup mode runtime leaks initial horizon scheduler
        anchor anchorRaw who]
    obtain ⟨ending, endingEq, archived⟩ := PhaseProposal.phase_commitment_prefix_sourceArchive
      runtime leaks bounds plan (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon
        scheduler anchor anchorTrace phase (Option.mem_def.mpr installed) commitment trace kept (by
          intro middle prefixTrace after before _shorter
          have middleOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
            scheduler initialized ((menu).toRawTrace initial horizon scheduler prefixTrace)
          have lower := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
            horizon scheduler anchor middle anchorTrace prefixTrace after anchorOrdered
          have upper := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
            horizon scheduler middle current prefixTrace trace before middleOrdered
          have gen := congrArg CommitAttemptId.generation sameAttempt
          have phaseRank := congrArg CommitAttemptId.phase sameAttempt
          cases left : middle.execution.application.attempt with
          | mk leftPhase leftGeneration =>
            cases right : anchor.execution.application.attempt with
            | mk rightPhase rightGeneration =>
              simp only [left, right] at lower upper gen phaseRank ⊢
              congr 1 <;> omega)
    cases Option.some.inj endingEq
    exact archived
  · intro who event ready actor active unsent
    exact (phaseProposalEmissionFrontier_ready setup mode runtime leaks bounds plan inputs horizon
      scheduler anchor.execution phase anchorTrace.length first current trace currentPhase
        commitment sameAttempt sameExcluded entryE initialOrigins prior invariant.emissions silent
          invariant.within.2 who event ready actor active unsent).2

/-- The actual stopped runner preserves the frozen-entry canonical potential.
The literal start may already contain emissions, while the frozen original
entry supplies the query potential. Their attempt is the same. Structural
frames refer to actual running prefixes and retain all pending assignments. -/
theorem phaseProposalUnflagged_stopped_potential_of_callback_frames
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (capacity : horizon ≤ bounds.candidateCount)
    (original : inputs = setup.initialLaw.map encodeInputs)
    (anchor : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (origin : (app).Execution)
    (originAttempt : origin.application.attempt = anchor.execution.application.attempt)
    (phase : RuntimePhase (graph)) (commitment : phase.kind = .commitment)
    (first : (graph).Config)
    (frames : ∀ (current : (app).Control)
      (trace : ((menu).protocol initial horizon scheduler).Trace (some current)),
      (∃ fuel, ⟨some current, trace⟩ ∈
        (((menu).information initial horizon scheduler).runBehavioralFrom
          (fun who => (menu).restrictPolicy initial horizon scheduler who
            (ReactiveApplication.anchoredPolicy anchor.execution
              (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who))
          fuel ⟨some anchor, anchorTrace⟩).support) →
      (∀ ending ∈ (((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories
        (fun who => (menu).restrictPolicy initial horizon scheduler who
          (ReactiveApplication.anchoredPolicy anchor.execution
            (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who))
        (fun history => match history.state with
          | none => False
          | some control => control.execution.application.attempt ≠
            anchor.execution.application.attempt) ⟨some current, trace⟩).support,
        ending ∈ (((menu).information initial horizon scheduler).runBehavioralUntil
          ((menu).bounded initial horizon scheduler).wellFoundedHistories
          (fun who => (menu).restrictPolicy initial horizon scheduler who
            (ReactiveApplication.anchoredPolicy anchor.execution
              (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who))
          (fun history => match history.state with
            | none => False
            | some control => control.execution.application.attempt ≠
              anchor.execution.application.attempt) ⟨some anchor, anchorTrace⟩).support) →
      TracePrefix anchorTrace trace →
      current.execution.application.attempt = anchor.execution.application.attempt →
      PhaseProposalBindingCallbackFrame setup mode runtime leaks origin phase
        current.execution (phaseProposalEmissionFrontier setup mode runtime leaks origin
          phase anchorTrace.length first initial horizon scheduler
            ((menu).toRawTrace initial horizon scheduler trace)) current.actor) :
    let model := (menu).information initial horizon scheduler
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who
      (ReactiveApplication.anchoredPolicy anchor.execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some current => current.execution.application.attempt ≠ anchor.execution.application.attempt
    let potential := fun history : ((menu).protocol initial horizon scheduler).History =>
      (graph).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup mode runtime leaks plan origin phase
          values)
        (phaseProposalEmissionFrontier setup mode runtime leaks origin phase
          anchorTrace.length first initial horizon scheduler
            ((menu).toRawTrace initial horizon scheduler history.trace))
    (model.runBehavioralUntil ((menu).bounded initial horizon scheduler).wellFoundedHistories
      profile stopped ⟨some anchor, anchorTrace⟩).bind potential =
        (graph).canonicalContinuation
          (phaseProposalBindingPotentialProfile setup mode runtime leaks plan origin phase
            values) first := by
  intro model profile stopped potential
  let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
  have decoded : (menu).decodeProfile initial horizon scheduler profile =
      ReactiveApplication.anchoredPolicy anchor.execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) := by
    funext who
    exact (menu).decode_restrictPolicy_of_covered initial horizon scheduler who _
      ((menu).anchoredPolicy_covered initial horizon scheduler anchor anchorTrace
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who
          (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values who))
  have oneStep : ∀ (history : ((menu).protocol initial horizon scheduler).History),
      TracePrefix anchorTrace history.trace →
      (∃ fuel, history ∈ (model.runBehavioralFrom profile fuel
        ⟨some anchor, anchorTrace⟩).support) →
      (∀ ending ∈ (model.runBehavioralUntil certificate profile stopped history).support,
        ending ∈ (model.runBehavioralUntil certificate profile stopped
          ⟨some anchor, anchorTrace⟩).support) →
      (∃ current : (app).Control, history.state = some current) →
      ¬ stopped history → ¬ ((menu).protocol initial horizon scheduler).terminal history.state →
      (model.runBehavioralFrom profile 1 history).bind potential = potential history := by
    intro history kept supported context existsControl going _running
    obtain ⟨current, currentEq⟩ := existsControl
    rcases history with ⟨state, trace⟩
    dsimp only at currentEq
    subst state
    have same : current.execution.application.attempt = anchor.execution.application.attempt :=
      Classical.not_not.mp going
    have sameOrigin : current.execution.application.attempt = origin.application.attempt :=
      same.trans originAttempt.symm
    have frame := frames current trace supported context kept same
    rcases current with ⟨remaining, actor, execution⟩
    cases actor with
    | none =>
      exact frontier_one_environment setup mode runtime leaks bounds plan inputs horizon scheduler
        origin phase anchorTrace.length first values profile remaining execution trace
    | some who =>
      rw [frontier_one_response setup mode runtime leaks bounds plan inputs horizon scheduler
        origin phase anchorTrace.length first values profile remaining who execution trace
          kept.length_le, decoded]
      have recalledPrefix : anchor.execution.recall who <+: execution.recall who :=
        (app).reaches_recall_prefix initial horizon scheduler
          ((menu).reaches_raw initial horizon scheduler kept.reachesWithin) anchor
            ⟨remaining, some who, execution⟩ rfl rfl who
      rw [ReactiveApplication.anchoredPolicy_of_extends anchor.execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who
          (execution.recall who) (execution.observe (app) who) recalledPrefix]
      by_cases offered : ∃ material : WitnessedSubmission (graph),
          (⟨some material⟩ : (app).Action) ∈
            PhaseCount.onePacketActions runtime leaks bounds who (execution.recall who)
              (execution.observe (app) who)
      · obtain ⟨material, allowed⟩ := offered
        obtain ⟨event, payload, binding, code, inside, request⟩ := nonsilent_binding_request
          setup mode runtime leaks bounds plan inputs horizon scheduler phase commitment remaining
            who execution trace frame.installed material allowed
        have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds plan
          (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who
            execution trace _ request material allowed
        have sourceTrace : ((menu).protocol
            (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
              horizon scheduler).Trace (some ⟨remaining, some who, execution⟩) := by
          rw [original, PMF.map_comp] at trace
          exact trace
        exact phaseProposalUnflagged_binding_response_harmonic setup mode runtime leaks bounds plan
          complete covered maximal values fullValues horizon scheduler capacity remaining who
            execution origin sourceTrace phase commitment event payload binding code
              inside
              (by simpa only [← frame.excluded] using request.2.2.2.2) request unsent sameOrigin
                frame.retired frame.failures (frame.archive who rfl) _ frame.agreement frame.inputs
                  (frame.hidden who event request.2.2.1 request.2.2.2.1 request.2.2.2.2 unsent)
      · have onlyWait : ∀ response ∈ PhaseCount.onePacketActions runtime leaks bounds who
            (execution.recall who) (execution.observe (app) who), response = ⟨none⟩ := by
          intro response member
          cases response with
          | mk transmission =>
            cases transmission with
            | none => rfl
            | some material => exact (offered ⟨material, member⟩).elim
        rw [phaseProposalUnflaggedPolicy_forced_wait setup mode runtime leaks bounds plan values
          who (execution.recall who) (execution.observe (app) who) onlyWait, PMF.pure_bind]
        simp only [phaseProposalBindingFrontierAdvance, sameOrigin, ↓reduceIte,
          Function.update_self, Option.getD_some]
        rfl
  have stoppedLaw : ∀ history : ((menu).protocol initial horizon scheduler).History,
      TracePrefix anchorTrace history.trace →
      (∃ fuel, history ∈ (model.runBehavioralFrom profile fuel
        ⟨some anchor, anchorTrace⟩).support) →
      (∀ ending ∈ (model.runBehavioralUntil certificate profile stopped history).support,
        ending ∈ (model.runBehavioralUntil certificate profile stopped
          ⟨some anchor, anchorTrace⟩).support) →
      (∃ current : (app).Control, history.state = some current) →
      (model.runBehavioralUntil certificate profile stopped history).bind potential =
        potential history := by
    intro history
    induction history using certificate.induction with
    | _ history ih =>
      intro kept priorSupport context existsControl
      by_cases halt : stopped history
      · rw [model.runBehavioralUntil_of_stopped certificate profile halt, PMF.pure_bind]
      by_cases ended : ((menu).protocol initial horizon scheduler).terminal history.state
      · rw [model.runBehavioralUntil_of_terminal certificate profile ended, PMF.pure_bind]
      rw [model.runBehavioralUntil_of_running certificate profile halt ended, PMF.bind_bind]
      calc
        _ = (model.runBehavioralFrom profile 1 history).bind potential := by
          apply bind_congr_on_support
          intro next supported
          obtain ⟨⟨joint, legal, realized⟩, _future⟩ :=
            model.mem_support_runBehavioralFrom_one profile ended supported
          have retained : TracePrefix history.trace next.trace :=
            (model.runBehavioralFrom_reachesWithin profile 1 history next supported).tracePrefix
          have nextControl : ∃ current : (app).Control, next.state = some current := by
            obtain ⟨current, state⟩ := existsControl
            have reached : next.state ∈ ((app).transition initial horizon scheduler history.state
                joint).support := realized
            rw [state] at reached
            obtain ⟨after, equality, _recall⟩ := (app).transition_recall_prefix initial horizon
              scheduler current next.state joint reached
            exact ⟨after, equality⟩
          have nextSupport : ∃ fuel, next ∈ (model.runBehavioralFrom profile fuel
              ⟨some anchor, anchorTrace⟩).support := by
            obtain ⟨fuel, previous⟩ := priorSupport
            refine ⟨fuel + 1, ?_⟩
            rw [model.runBehavioralFrom_add profile fuel 1, PMF.mem_support_bind_iff]
            exact ⟨history, previous, supported⟩
          have nextContext : ∀ ending ∈
              (model.runBehavioralUntil certificate profile stopped next).support,
              ending ∈ (model.runBehavioralUntil certificate profile stopped
                ⟨some anchor, anchorTrace⟩).support := by
            intro ending continuation
            apply context ending
            rw [model.runBehavioralUntil_of_running certificate profile halt ended,
              PMF.mem_support_bind_iff]
            exact ⟨next, supported, continuation⟩
          exact ih next ⟨joint, legal, realized⟩ (kept.trans retained) nextSupport nextContext
            nextControl
        _ = potential history := oneStep history kept priorSupport context existsControl halt ended
  have initially : ∃ fuel, (⟨some anchor, anchorTrace⟩ :
      ((menu).protocol initial horizon scheduler).History) ∈
        (model.runBehavioralFrom profile fuel ⟨some anchor, anchorTrace⟩).support :=
    ⟨0, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
  have result := stoppedLaw ⟨some anchor, anchorTrace⟩ .refl initially (fun _ member => member)
    ⟨anchor, rfl⟩
  have originalFrontier : phaseProposalEmissionFrontier setup mode runtime leaks origin
      phase anchorTrace.length first initial horizon scheduler
        ((menu).toRawTrace initial horizon scheduler anchorTrace) = first := by
    apply phaseProposalEmissionFrontier_before_anchor
    rw [(menu).toRawTrace_length]
  simpa only [potential, originalFrontier] using result

variable {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

omit [Fintype Player] in
private theorem completed_word_canonical
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (excluded : Finset Player)
    (entry : SourceProgram.Config Player L Γ)
    (profile : (graph).BehavioralProfile) (config : (graph).Config)
    (completed : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      embedding.event index ∈ config.cut.completed) :
    ((graph).canonicalContinuation profile config).map (fun key =>
      phaseProposalBindingWord setup.program block suffix embedding excluded key.2.1 entry) =
        PMF.pure (phaseProposalBindingWord setup.program block suffix embedding excluded
          config.store entry) := by
  have actual := phaseProposalBindingWord_runPlan setup.program mode block suffix embedding
    excluded entry ((graph).policyPlan ((graph).normalizeProfile profile)
      (graph).canonicalScheduler) config.remaining config completed
  simpa only [canonicalContinuation, canonicalSemanticLaw, PMF.map_comp, Function.comp_def,
    semanticKey, storeRecall, serviceGraph, Setup.eventGraph] using actual

/-- Once the original interval is complete, the stopped potential identity
is the actual emitted binding-word law. Completion is tested on the SAME
retained frontier, not on a synthetic future graph prefix. -/
theorem phaseProposalUnflagged_stopped_word_of_callback_frames
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (capacity : horizon ≤ bounds.candidateCount)
    (original : inputs = setup.initialLaw.map encodeInputs)
    (anchor : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (phase : RuntimePhase (graph)) (commitment : phase.kind = .commitment)
    (first : (graph).Config)
    (frames : ∀ (current : (app).Control)
      (trace : ((menu).protocol initial horizon scheduler).Trace (some current)),
      (∃ fuel, ⟨some current, trace⟩ ∈
        (((menu).information initial horizon scheduler).runBehavioralFrom
          (fun who => (menu).restrictPolicy initial horizon scheduler who
            (ReactiveApplication.anchoredPolicy anchor.execution
              (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who))
          fuel ⟨some anchor, anchorTrace⟩).support) →
      (∀ ending ∈ (((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories
        (fun who => (menu).restrictPolicy initial horizon scheduler who
          (ReactiveApplication.anchoredPolicy anchor.execution
            (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who))
        (fun history => match history.state with
          | none => False
          | some control => control.execution.application.attempt ≠
            anchor.execution.application.attempt) ⟨some current, trace⟩).support,
        ending ∈ (((menu).information initial horizon scheduler).runBehavioralUntil
          ((menu).bounded initial horizon scheduler).wellFoundedHistories
          (fun who => (menu).restrictPolicy initial horizon scheduler who
            (ReactiveApplication.anchoredPolicy anchor.execution
              (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who))
          (fun history => match history.state with
            | none => False
            | some control => control.execution.application.attempt ≠
              anchor.execution.application.attempt) ⟨some anchor, anchorTrace⟩).support) →
      TracePrefix anchorTrace trace →
      current.execution.application.attempt = anchor.execution.application.attempt →
      PhaseProposalBindingCallbackFrame setup mode runtime leaks anchor.execution phase
        current.execution (phaseProposalEmissionFrontier setup mode runtime leaks anchor.execution
          phase anchorTrace.length first initial horizon scheduler
            ((menu).toRawTrace initial horizon scheduler trace)) current.actor)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (entry : SourceProgram.Config Player L Γ) :
    let model := (menu).information initial horizon scheduler
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who
      (ReactiveApplication.anchoredPolicy anchor.execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some current => current.execution.application.attempt ≠ anchor.execution.application.attempt
    let stoppedLaw := model.runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories
        profile stopped ⟨some anchor, anchorTrace⟩
    let frontier := fun history : ((menu).protocol initial horizon scheduler).History =>
      phaseProposalEmissionFrontier setup mode runtime leaks anchor.execution phase
        anchorTrace.length first initial horizon scheduler
          ((menu).toRawTrace initial horizon scheduler history.trace)
    (∀ final ∈ stoppedLaw.support,
      ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
        embedding.event index ∈ (frontier final).cut.completed) →
    stoppedLaw.map (fun final => phaseProposalBindingWord setup.program block suffix embedding
        anchor.execution.application.current.excluded (frontier final).store entry) =
      ((graph).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor.execution phase
          values) first).map (fun key => phaseProposalBindingWord setup.program block suffix
            embedding anchor.execution.application.current.excluded key.2.1 entry) := by
  intro model profile stopped stoppedLaw frontier completed
  let graphProfile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan
    anchor.execution phase values
  let read := fun key : (graph).SemanticKey => phaseProposalBindingWord setup.program block suffix
    embedding anchor.execution.application.current.excluded key.2.1 entry
  have potential := phaseProposalUnflagged_stopped_potential_of_callback_frames setup mode runtime
    leaks bounds plan inputs horizon scheduler complete covered maximal values fullValues capacity
      original anchor anchorTrace anchor.execution rfl phase commitment first frames
  have projected := congrArg (fun law => law.map read) potential
  rw [PMF.map_bind] at projected
  have endpoints : (stoppedLaw.bind fun final =>
      ((graph).canonicalContinuation graphProfile (frontier final)).map read) =
      stoppedLaw.map (fun final => phaseProposalBindingWord setup.program block suffix embedding
        anchor.execution.application.current.excluded (frontier final).store entry) := by
    calc
      _ = stoppedLaw.bind (fun final => PMF.pure
          (phaseProposalBindingWord setup.program block suffix embedding
            anchor.execution.application.current.excluded (frontier final).store entry)) := by
        apply bind_congr_on_support
        intro final supported
        exact completed_word_canonical setup mode block suffix embedding
          anchor.execution.application.current.excluded entry graphProfile (frontier final)
            (completed final supported)
      _ = _ := PMF.bind_pure_comp _ _
  exact endpoints.symm.trans projected

private theorem closing_raw_bindings
    (before ending : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (raw : RecoveryState (graph))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt) :
    BindingStamp (fun who => (app).outputs (before.execution.recall who))
        before.execution.application.attempt raw.native ∧
      (∀ candidate payload, raw.native.bindingResult candidate payload =
        before.execution.application.current.native.bindingResult candidate payload) := by
  let trace := (menu).toRawTrace initial horizon scheduler prior
  have stamp := phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler trace
  rcases effect with ⟨id, message, native, found, moved, accepted, rfl⟩ |
      ⟨command, native, moved, supported, rfl⟩
  · have selected : ending.execution.application =
        ((app).handle before.execution.application message).getD before.execution.application := by
      have exactMove := moved
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at exactMove
      have stateEq := congrArg (fun execution : (app).Execution => execution.application)
        ((PMF.mem_support_pure_iff _ _).mp exactMove)
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found] using stateEq
    have wrapped : (before.execution.application.handle runtime message).isSome := by
      cases handler : before.execution.application.handle runtime message with
      | some next => rfl
      | none =>
        have sameApplication : ending.execution.application = before.execution.application := by
          simpa only [show (app).handle before.execution.application message = none from handler,
            Option.getD_none] using selected
        exact (changed (congrArg PhaseRuntimeState.attempt sameApplication)).elim
    have allowed : (message.payload.tokenValid before.execution.application.attempt &&
        before.execution.application.allows message.payload.packet.call &&
          (!(before.execution.application.current.excludedCall message.payload.packet.call))) =
            true := by
      by_contra invalid
      have absent : before.execution.application.handle runtime message = none := by
        simp only [PhaseRuntimeState.handle, ite_eq_right invalid]
      rw [absent] at wrapped
      cases wrapped
    have authorized := (Bool.and_eq_true_iff.mp allowed).1
    have packetValid := (Bool.and_eq_true_iff.mp authorized).1
    have addressed : message.payload.attempt = before.execution.application.attempt := by
      exact decide_eq_true_eq.mp (Bool.and_eq_true_iff.mp packetValid).1
    refine ⟨raw_handle_bindingStamp runtime leaks before.execution native message stamp
      ((app).history_provenance initial horizon scheduler trace |>.lookup id message found)
        addressed accepted, ?_⟩
    · intro candidate payload
      exact raw_handle_bindingResult runtime _ native _ accepted candidate payload
  · refine ⟨stamp.copy (environmentStep_tables runtime _ native command supported).1, ?_⟩
    intro candidate payload
    change native.bindingResult candidate payload = _
    unfold State.bindingResult
    rw [(environmentStep_tables runtime _ native command supported).2]

/-- The original closing image completes the literal emitted frontier.
This comparison uses its exact signed accepted candidates before normalization. -/
private theorem closing_image_frontier
    (before : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (phase : RuntimePhase (graph))
    (installed : before.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (frontier : (graph).Config)
    (within : frontier.cut.Within phase.low phase.high)
    (quiet : ∀ event ∈ phase.events, frontier.cut.Ready event →
      ∀ owner ∈ before.execution.application.entry.excluded,
        (graph).actor? event ≠ some owner)
    (emissions : PhaseProposalEmittedBindings runtime leaks before.execution phase frontier)
    (raw : RecoveryState (graph))
    (stamp : BindingStamp (fun who => (app).outputs (before.execution.recall who))
      before.execution.application.attempt raw.native)
    (meanings : ∀ candidate payload, raw.native.bindingResult candidate payload =
      before.execution.application.current.native.bindingResult candidate payload)
    (finished : phase.Finished (phase.drain raw))
    (bindingInvariant : (phase.drain raw).native.BindingInvariant)
    (coverage : (phase.drain raw).FailureCoverage)
    (excluded : (phase.drain raw).excluded = before.execution.application.entry.excluded) :
    (∀ event ∈ phase.events, event ∈ frontier.cut.completed) ∧
      ∀ event ∈ phase.events, ∀ owner ∉ before.execution.application.entry.excluded,
        ∀ payload (binding : (graph).outputLayout event = .binding owner payload),
          (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
              (phase.drain raw).native.config.store =
            (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
              frontier.store := by
  have tables := phase.drain_tables raw
  have address : before.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some]
  have readback : ∀ event ∈ phase.events,
      ∀ owner ∉ before.execution.application.entry.excluded,
        ∀ payload (binding : (graph).outputLayout event = .binding owner payload),
          (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
              (phase.drain raw).native.config.store =
            (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
              frontier.store ∧ event ∈ frontier.cut.completed := by
    intro event inside owner active payload binding
    have present : (phase.drain raw).native.accepted (.inr event) ≠ none := by
      intro missing
      have failed := ((phase.drain raw).native.publicView_missedBinding event owner payload
        binding).mpr ⟨finished inside, missing⟩
      exact active (excluded ▸ coverage.covered event owner
        (actor?_of_outputLayout_binding (graph) binding) (Or.inl failed))
    obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
    have rawAccepted : raw.native.accepted (.inr event) = some candidate := by
      rwa [tables.1] at accepted
    obtain ⟨message, authored, _sender, named, attempted⟩ :
        ∃ message ∈ (app).outputs (before.execution.recall candidate.1),
          message.sender = candidate.1 ∧
            message.payload.packet.call = .commitment event candidate ∧
              message.payload.attempt = before.execution.application.attempt := by
      rcases stamp event candidate rawAccepted with earlier | signed
      · have lower := ((phase.mem_events event).mp inside).1
        omega
      · exact signed
    have member : message ∈ before.execution.network.inputs := by
      rw [← (app).history_inputRecall initial horizon scheduler
        ((menu).toRawTrace initial horizon scheduler prior) candidate.1] at authored
      exact (List.mem_filter.mp authored).1
    have emitted := emissions message member attempted event inside candidate named owner payload
      binding
    have sameMeaning : (phase.drain raw).native.bindingResult candidate payload =
        before.execution.application.current.native.bindingResult candidate payload := by
      unfold State.bindingResult
      rw [tables.2.1]
      exact meanings candidate payload
    have field := bindingInvariant.binding_read
      (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)) event rfl
        (finished inside)
    rw [accepted, Option.elim_some, sameMeaning] at field
    refine ⟨field.trans emitted.symm, ?_⟩
    apply (frontier.output_available event).mp
    have available {first second : Type} (same : first = second) (item : Option first) :
        (cast (congrArg Option same) item).isSome = item.isSome := by
      cases same
      rfl
    change (frontier.store (.inr event)).isSome = true
    rw [← available (congrArg EventField.Value binding) (frontier.store (.inr event))]
    change ((⟨.inr event, binding⟩ : FieldRef (graph).layout
      (.binding owner payload)).get? frontier.store).isSome = true
    rw [emitted]
    rfl
  refine ⟨?_, fun event inside owner active payload binding =>
    (readback event inside owner active payload binding).1⟩
  have domain : ∀ rank, ∀ event : (graph).EventId, event.val = rank →
      event.val < phase.high → event ∈ (phase.drain raw).native.config.cut.completed →
        event ∈ frontier.cut.completed := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro event indexed bounded completed
      by_cases earlier : event.val < phase.low
      · exact within.1 event earlier
      have inside : event ∈ phase.events := (phase.mem_events event).mpr ⟨by omega, bounded⟩
      obtain ⟨owner, payload, binding⟩ := commitment ▸ phase.fields event
        ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
      by_cases inherited : owner ∈ before.execution.application.entry.excluded
      · by_contra absent
        have ready : frontier.cut.Ready event := ⟨absent, fun predecessor member =>
          ih predecessor.val (by have lower := (graph).order.predecessor_lt member; omega)
            predecessor rfl (by have lower := (graph).order.predecessor_lt member; omega)
              ((phase.drain raw).native.config.cut.predecessor_closed completed member)⟩
        exact quiet event inside ready owner inherited
          (actor?_of_outputLayout_binding (graph) binding)
      · exact (readback event inside owner inherited payload binding).2
  intro event inside
  exact domain event.val event rfl ((phase.mem_events event).mp inside).2 (finished inside)

theorem phaseProposal_fresh_entry_binding_origins
    (anchor : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (phase : RuntimePhase (graph))
    (installed : anchor.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (fresh : ∀ who, ∀ record ∈ anchor.execution.recall who,
      record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt) :
    (∀ message ∈ anchor.execution.network.inputs,
      message.payload.attempt ≠ anchor.execution.application.attempt) ∧
      PhaseProposalEmittedBindings runtime leaks anchor.execution phase
        anchor.execution.application.current.native.config ∧
      ∀ event ∈ anchor.execution.application.current.native.config.cut.completed,
        event.val < phase.low ∨ ∃ owner ∈ anchor.execution.application.current.excluded,
          (graph).actor? event = some owner := by
  let rawTrace := (menu).toRawTrace (initial) horizon scheduler anchorTrace
  have noInputs : ∀ message ∈ anchor.execution.network.inputs,
      message.payload.attempt ≠ anchor.execution.application.attempt := by
    intro message member attempted
    have own : message ∈ (app).outputs (anchor.execution.recall message.sender) := by
      rw [← (app).history_inputRecall (initial) horizon scheduler rawTrace message.sender]
      exact List.mem_filter.mpr ⟨member, by simp only [decide_true]⟩
    obtain ⟨record, recorded, emitted⟩ := List.mem_filterMap.mp own
    have original := phase_recalled_emission_attempt runtime leaks (initial) horizon scheduler
      rawTrace message.sender record recorded message emitted
    exact fresh message.sender record recorded (original.symm.trans attempted)
  have emissions : PhaseProposalEmittedBindings runtime leaks anchor.execution phase
      anchor.execution.application.current.native.config := by
    intro message member same
    exact (noInputs message member same).elim
  have position : anchor.execution.application.entry.native.config.cut.IsPrefix phase.low ∧
      anchor.execution.application.current.native.config.cut.Within phase.low phase.high := by
    have positioned := (phaseReceiptRecord_history runtime leaks
      (serviceGraph_revealRelaxedOrdered setup mode) plan inputs
        horizon scheduler rawTrace).exclusion.frontier.positioned
    cases phases : anchor.execution.application.phases with
    | nil => simp only [phases, List.head?_nil, reduceCtorEq] at installed
    | cons head rest =>
      have same : head = phase := by
        simpa only [phases, List.head?_cons, Option.some.injEq] using installed
      subst head
      simpa only [PhaseRuntimeState.Positioned, phases] using positioned
  have initialOrigins : ∀ event ∈ anchor.execution.application.current.native.config.cut.completed,
      event.val < phase.low ∨ ∃ owner ∈ anchor.execution.application.current.excluded,
        (graph).actor? event = some owner := by
    intro event completed
    by_cases below : event.val < phase.low
    · exact Or.inl below
    have inside : event ∈ phase.events := (phase.mem_events event).mpr
      ⟨by omega, position.2.2 event completed⟩
    obtain ⟨owner, payload, binding⟩ := commitment ▸ phase.fields event
      ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
    by_cases excluded : owner ∈ anchor.execution.application.current.excluded
    · exact Or.inr ⟨owner, excluded, actor?_of_outputLayout_binding (graph) binding⟩
    have missing : anchor.execution.application.current.native.accepted (.inr event) = none := by
      by_contra present
      obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
      have stamp := phaseLiveBindingStamp_history runtime leaks plan
        inputs horizon scheduler rawTrace
      rcases stamp event candidate accepted with past |
          ⟨message, authored, _sender, _named, attempted⟩
      · have address : anchor.execution.application.attempt.phase = phase.low := by
          simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some]
        omega
      · have member : message ∈ anchor.execution.network.inputs := by
          change message ∈ (app).outputs (anchor.execution.recall candidate.1) at authored
          rw [← (app).history_inputRecall (initial) horizon scheduler rawTrace candidate.1]
            at authored
          exact (List.mem_filter.mp authored).1
        exact noInputs message member attempted
    have coverage := (phaseFailureCoverage_history runtime leaks plan
      inputs horizon scheduler rawTrace).active
    exact (excluded (coverage.covered event owner (actor?_of_outputLayout_binding (graph) binding)
      (Or.inl ((anchor.execution.application.current.native.publicView_missedBinding event owner
        payload binding).mpr ⟨completed, missing⟩)))).elim
  exact ⟨noInputs, emissions, initialOrigins⟩

private theorem excluded_prefix_grows : ∀ (first last : (app).Control)
    (prior : ((menu).protocol (initial) horizon scheduler).Trace (some first))
    (trace : ((menu).protocol (initial) horizon scheduler).Trace (some last)),
    TracePrefix prior trace → first.execution.application.current.excluded ⊆
      last.execution.application.current.excluded := by
  intro first last prior trace kept
  let monotone := phaseApplication_exclusion_monotone runtime leaks
  let property : (app).State → Prop := fun state =>
    first.execution.application.current.excluded ⊆ state.current.excluded
  have invariant : (app).Invariant property := {
    submit := fun state who submission before =>
      before.trans (monotone.submit state who submission)
    handle := fun state message after before accepted =>
      before.trans (monotone.handle state message after accepted)
    environment := fun state command after before reached =>
      before.trans (monotone.environment state command after reached) }
  exact invariant.tracePrefix menu (initial) horizon scheduler first last prior trace kept
    (Finset.Subset.refl _)

/-- At an actual fresh reserved entry the operational frame is derived,
including survival of every inherited active owner. No future callback frame,
conditional source law or endpoint readout identity is supplied. -/
theorem phaseProposalUnflagged_stopped_potential_of_fresh_entry
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (anchor : (app).Control) (idle : anchor.actor = none)
    (anchorTrace : ((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some anchor))
    (phase : RuntimePhase (graph))
    (installed : anchor.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (entryExcluded : anchor.execution.application.entry.excluded =
      anchor.execution.application.current.excluded)
    (fresh : ∀ who, ∀ record ∈ anchor.execution.recall who,
      record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt) :
    let startLaw := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let model := (menu).information startLaw horizon scheduler
    let profile := fun who => (menu).restrictPolicy startLaw horizon scheduler who
      (ReactiveApplication.anchoredPolicy anchor.execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    let stopped := fun history : ((menu).protocol startLaw horizon scheduler).History =>
      match history.state with
      | none => False
      | some current => current.execution.application.attempt ≠ anchor.execution.application.attempt
    let potential := fun history : ((menu).protocol startLaw horizon scheduler).History =>
      (graph).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor.execution phase
          values)
        (phaseProposalEmissionFrontier setup mode runtime leaks anchor.execution phase
          anchorTrace.length anchor.execution.application.current.native.config startLaw horizon
            scheduler ((menu).toRawTrace startLaw horizon scheduler history.trace))
    (model.runBehavioralUntil ((menu).bounded startLaw horizon scheduler).wellFoundedHistories
      profile stopped ⟨some anchor, anchorTrace⟩).bind potential =
        (graph).canonicalContinuation
          (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor.execution phase
            values) anchor.execution.application.current.native.config := by
  classical
  intro startLaw horizon scheduler model profile stopped potential
  have initialized : ∀ state ∈ startLaw.support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  obtain ⟨_noInputs, emissions, initialOrigins⟩ :=
    phaseProposal_fresh_entry_binding_origins setup mode runtime
    leaks bounds plan (setup.initialLaw.map encodeInputs) horizon scheduler anchor anchorTrace phase
      installed
      commitment fresh
  have result := phaseProposalUnflagged_stopped_potential_of_callback_frames setup mode runtime
    leaks bounds
    plan (setup.initialLaw.map encodeInputs) horizon scheduler complete covered maximal values
      fullValues capacity rfl anchor anchorTrace anchor.execution rfl phase commitment
        anchor.execution.application.current.native.config (by
    intro current trace _supported context kept same
    obtain ⟨last, continuation⟩ :=
      (model.runBehavioralUntil ((menu).bounded startLaw horizon scheduler).wellFoundedHistories
        profile stopped ⟨some current, trace⟩).support_nonempty
    have rootMember := context last (by
      convert continuation using 1
      congr 3
      funext history
      dsimp only [stopped]
      cases history.state <;> rfl)
    dsimp only [horizon, scheduler] at rootMember
    rcases anchor with ⟨remaining, actor, execution⟩
    change actor = none at idle
    subst actor
    obtain ⟨ending, before, prior, joint, legal, realized, native, stateEq, _rest⟩ :=
      phaseProposalUnflagged_stopped_binding_image setup mode runtime leaks bounds plan complete
        covered maximal (serviceGraph_revealRelaxedOrdered setup mode) values fullValues tape
          activationGap processingGap gaps margin capacity remaining execution anchorTrace phase
            (Option.mem_def.mpr installed) commitment last (by
              convert rootMember using 1
              congr 3
              funext history
              cases history.state <;> rfl)
    have toLast := model.runBehavioralUntil_support_prefix
      ((menu).bounded startLaw horizon scheduler).wellFoundedHistories profile stopped
        ⟨some current, trace⟩ last continuation
    let lastTrace : ((menu).protocol startLaw horizon scheduler).Trace (some ending) :=
      stateEq ▸ last.trace
    have through : TracePrefix trace lastTrace := by
      dsimp only [lastTrace]
      cases last
      cases stateEq
      exact toLast
    have currentE : current.execution.application.current.excluded =
        execution.application.current.excluded := by
      apply Finset.Subset.antisymm
      · intro owner excluded
        by_contra originallyActive
        have finalActive := phaseProposalUnflagged_stopped_survival_of_fresh setup mode runtime
          leaks bounds plan complete covered maximal (serviceGraph_revealRelaxedOrdered setup mode)
            values fullValues tape activationGap processingGap gaps margin capacity remaining
              execution anchorTrace phase (Option.mem_def.mpr installed) commitment owner
                originallyActive (by
                  intro event request
                  rintro ⟨record, member, requested⟩
                  exact fresh owner record member requested.1.symm) last (by
                  convert rootMember using 1
                  congr 3
                  funext history
                  cases history.state <;> rfl) ending stateEq
        exact finalActive ((excluded_prefix_grows setup mode runtime leaks bounds plan
            (setup.initialLaw.map encodeInputs) horizon scheduler current ending trace lastTrace
              through) excluded)
      · exact excluded_prefix_grows setup mode runtime leaks bounds plan
          (setup.initialLaw.map encodeInputs) horizon scheduler
            ⟨remaining, none, execution⟩ current anchorTrace trace kept
    exact phaseProposalEmissionFrontier_callback_frame setup mode runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon scheduler complete maximal
        ⟨remaining, none, execution⟩ anchorTrace phase installed commitment entryExcluded
          initialOrigins emissions current trace kept same currentE
  )
  convert result using 1
  congr 3
  funext history
  dsimp only [stopped]
  cases history.state <;> rfl

/-- From an actual retained entry, the admitted original tape preserves the
causal emitted-frontier potential after a literal mid-block response. Every
callback frame and every prefix exclusion equality is derived from the actual
trace and acceptance word, including already pending owned bindings. -/
theorem phaseProposalUnflagged_stopped_potential_from_retained_entry
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (anchor : (app).Control) (idle : anchor.actor = none)
    (anchorTrace : ((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some anchor))
    (phase : RuntimePhase (graph))
    (installed : anchor.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (origin : (app).Control)
    (originTrace : ((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some origin))
    (retained : TracePrefix originTrace anchorTrace)
    (sameAttempt : origin.execution.application.attempt = anchor.execution.application.attempt)
    (originInstalled : origin.execution.application.phases.head? = some phase)
    (entryExcluded : origin.execution.application.entry.excluded =
      origin.execution.application.current.excluded)
    (fresh : ∀ who, ∀ record ∈ origin.execution.recall who,
      record.beforeView.application.2.attempt ≠ origin.execution.application.attempt)
    (clean : anchor.execution.application.current.excluded =
      origin.execution.application.current.excluded)
    (afterProcessing : ReservedEpoch.packetCapacity runtime ≤
      anchor.execution.environmentRecall.length %
        ReservedEpoch.cycleWidth («graph» := graph) (ReservedEpoch.packetCapacity runtime))
    (admitted : ∀ owner, owner ∉ anchor.execution.application.current.excluded →
      ∀ event ∈ phase.events, ∀ payload,
      (graph).outputLayout event = .binding owner payload →
      ReservedEpoch.ownedAcceptanceWord runtime leaks tape anchor.execution owner event) :
    let startLaw := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let model := (menu).information startLaw horizon scheduler
    let profile := fun who => (menu).restrictPolicy startLaw horizon scheduler who
      (ReactiveApplication.anchoredPolicy anchor.execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    let stopped := fun history : ((menu).protocol startLaw horizon scheduler).History =>
      match history.state with
      | none => False
      | some current => current.execution.application.attempt ≠ anchor.execution.application.attempt
    let frontier := fun history : ((menu).protocol startLaw horizon scheduler).History =>
      phaseProposalEmissionFrontier setup mode runtime leaks origin.execution phase
        originTrace.length origin.execution.application.current.native.config startLaw horizon
          scheduler ((menu).toRawTrace startLaw horizon scheduler history.trace)
    let potential := fun history : ((menu).protocol startLaw horizon scheduler).History =>
      (graph).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup mode runtime leaks plan origin.execution phase
          values) (frontier history)
    (model.runBehavioralUntil ((menu).bounded startLaw horizon scheduler).wellFoundedHistories
      profile stopped ⟨some anchor, anchorTrace⟩).bind potential =
        (graph).canonicalContinuation
          (phaseProposalBindingPotentialProfile setup mode runtime leaks plan origin.execution phase
            values) (frontier ⟨some anchor, anchorTrace⟩) := by
  classical
  intro startLaw horizon scheduler model profile stopped frontier potential
  let first := frontier ⟨some anchor, anchorTrace⟩
  have restart {state} (trace : ((menu).protocol startLaw horizon scheduler).Trace state)
      (kept : TracePrefix anchorTrace trace) :
      frontier ⟨state, trace⟩ = phaseProposalEmissionFrontier setup mode runtime leaks
        origin.execution phase anchorTrace.length first startLaw horizon scheduler
          ((menu).toRawTrace startLaw horizon scheduler trace) := by
    have rawKept := ((menu).reaches_raw startLaw horizon scheduler kept.reachesWithin).tracePrefix
    have equation := phaseProposalEmissionFrontier_restart setup mode runtime leaks startLaw
      horizon scheduler origin.execution phase originTrace.length
        origin.execution.application.current.native.config
        ((menu).toRawTrace startLaw horizon scheduler anchorTrace)
        (by rw [(menu).toRawTrace_length]; exact retained.length_le)
        ((menu).toRawTrace startLaw horizon scheduler trace) rawKept
    simpa only [(menu).toRawTrace_length, frontier, first] using equation
  obtain ⟨_noInputs, emissions, initialOrigins⟩ :=
    phaseProposal_fresh_entry_binding_origins setup mode runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon scheduler origin originTrace phase
        originInstalled commitment fresh
  have result := phaseProposalUnflagged_stopped_potential_of_callback_frames setup mode runtime
    leaks bounds plan (setup.initialLaw.map encodeInputs) horizon scheduler complete covered maximal
      values fullValues capacity rfl anchor anchorTrace origin.execution sameAttempt phase
        commitment
        first (by
    intro current trace _supported context kept same
    obtain ⟨last, continuation⟩ :=
      (model.runBehavioralUntil ((menu).bounded startLaw horizon scheduler).wellFoundedHistories
        profile stopped ⟨some current, trace⟩).support_nonempty
    have rootMember := context last (by
      convert continuation using 1
      congr 3
      funext history
      dsimp only [stopped]
      cases history.state <;> rfl)
    rcases anchor with ⟨remaining, actor, execution⟩
    change actor = none at idle
    subst actor
    obtain ⟨ending, before, prior, joint, legal, realized, raw, stateEq, _idle, _changed,
      _fromStart, _toFinal, _same, _installed, _effect, _finished, _normalized, _coverage,
      _excluded, _tables, _candidates, _archive, _retiredBefore, _retiredAfter, _word,
      survives, _footprint⟩ :=
      phaseProposalUnflagged_stopped_acceptance_word setup mode runtime leaks bounds plan complete
        covered maximal (serviceGraph_revealRelaxedOrdered setup mode) values fullValues tape
          activationGap processingGap gaps margin capacity remaining execution anchorTrace phase
            (Option.mem_def.mpr installed) commitment afterProcessing last (by
              convert rootMember using 1
              congr 3
              funext history
              dsimp only [stopped]
              cases history.state <;> rfl)
    have toLast := model.runBehavioralUntil_support_prefix
      ((menu).bounded startLaw horizon scheduler).wellFoundedHistories profile stopped
        ⟨some current, trace⟩ last continuation
    let lastTrace : ((menu).protocol startLaw horizon scheduler).Trace (some ending) :=
      stateEq ▸ last.trace
    have through : TracePrefix trace lastTrace := by
      dsimp only [lastTrace]
      cases last
      cases stateEq
      exact toLast
    have currentE : current.execution.application.current.excluded =
        execution.application.current.excluded := by
      apply Finset.Subset.antisymm
      · intro owner excluded
        by_contra active
        exact survives owner active (admitted owner active)
          ((excluded_prefix_grows setup mode runtime leaks bounds plan
            (setup.initialLaw.map encodeInputs) horizon scheduler current ending trace lastTrace
              through) excluded)
      · exact excluded_prefix_grows setup mode runtime leaks bounds plan
          (setup.initialLaw.map encodeInputs) horizon scheduler
            ⟨remaining, none, execution⟩ current anchorTrace trace kept
    have frame := phaseProposalEmissionFrontier_callback_frame setup mode runtime leaks bounds
      plan
      (setup.initialLaw.map encodeInputs) horizon scheduler complete maximal origin originTrace
        phase
        originInstalled commitment entryExcluded initialOrigins emissions current trace
          (retained.trans kept) (same.trans sameAttempt.symm) (currentE.trans clean)
    change PhaseProposalBindingCallbackFrame setup mode runtime leaks origin.execution phase
      current.execution (frontier ⟨some current, trace⟩) current.actor at frame
    rw [restart trace kept] at frame
    exact frame)
  calc
    _ = (model.runBehavioralUntil ((menu).bounded startLaw horizon scheduler).wellFoundedHistories
        profile stopped ⟨some anchor, anchorTrace⟩).bind (fun history =>
          (graph).canonicalContinuation
            (phaseProposalBindingPotentialProfile setup mode runtime leaks plan origin.execution
              phase values)
            (phaseProposalEmissionFrontier setup mode runtime leaks origin.execution phase
              anchorTrace.length first startLaw horizon scheduler
                ((menu).toRawTrace startLaw horizon scheduler history.trace))) := by
      apply bind_congr_on_support
      intro history supported
      have kept := model.runBehavioralUntil_support_prefix
        ((menu).bounded startLaw horizon scheduler).wellFoundedHistories profile stopped
          ⟨some anchor, anchorTrace⟩ history supported
      dsimp only [potential]
      rw [restart history.trace kept]
    _ = _ := by
      convert result using 1
      congr 3
      funext history
      dsimp only [stopped]
      cases history.state <;> rfl

/-- The original drained image has the emitted addressed word law. -/
theorem phaseProposalUnflagged_stopped_binding_word
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (anchor : (app).Control) (idle : anchor.actor = none)
    (anchorTrace : ((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some anchor))
    (phase : RuntimePhase (graph))
    (installed : anchor.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (entryExcluded : anchor.execution.application.entry.excluded =
      anchor.execution.application.current.excluded)
    (fresh : ∀ who, ∀ record ∈ anchor.execution.recall who,
      record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (entry : SourceProgram.Config Player L Γ)
    (locations : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      embedding.event index ∈ phase.events) :
    let startLaw := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let model := (menu).information startLaw horizon scheduler
    let profile := fun who => (menu).restrictPolicy startLaw horizon scheduler who
      (ReactiveApplication.anchoredPolicy anchor.execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    let stopped := fun history : ((menu).protocol startLaw horizon scheduler).History =>
      match history.state with
      | none => False
      | some current => current.execution.application.attempt ≠ anchor.execution.application.attempt
    let law := model.runBehavioralUntil
      ((menu).bounded startLaw horizon scheduler).wellFoundedHistories profile stopped
        ⟨some anchor, anchorTrace⟩
    ∃ image : ((menu).protocol startLaw horizon scheduler).History → RecoveryState (graph),
      (∀ final ∈ law.support,
        ∃ (ending before : (app).Control)
          (prior : ((menu).protocol startLaw horizon scheduler).Trace (some before))
          (joint : Player → Option (app).Action)
          (legal : ((menu).protocol startLaw horizon scheduler).Legal (some before) joint)
          (realized : some ending ∈ ((app).transition startLaw horizon scheduler
            (some before) joint).support) (raw : RecoveryState (graph)),
          final.state = some ending ∧ TracePrefix anchorTrace prior ∧
            TracePrefix (prior.extend joint legal realized) final.trace ∧
            PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
            image final = phase.drain raw ∧ phase.Finished (image final) ∧
            (image final).excluded = anchor.execution.application.current.excluded ∧
            PhaseProposal.sourceArchive ending.execution.network.inputs =
              PhaseProposal.sourceArchive anchor.execution.network.inputs ∧
            before.execution.application.attempt = anchor.execution.application.attempt ∧
            phase ∈ before.execution.application.phases.head? ∧
            ending.execution.application =
              ({ before.execution.application with current := raw } :
                PhaseRuntimeState graph).normalize ∧
            (image final).native.BindingInvariant ∧ (image final).FailureCoverage) ∧
      law.map (fun final => phaseProposalBindingWord setup.program block suffix embedding
        anchor.execution.application.current.excluded (image final).native.config.store entry) =
          ((graph).canonicalContinuation
            (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor.execution
              phase values) anchor.execution.application.current.native.config).map
                (fun key => phaseProposalBindingWord setup.program block suffix embedding
                  anchor.execution.application.current.excluded key.2.1 entry) := by
  classical
  intro startLaw horizon scheduler model profile stopped law
  let frontier := fun history : ((menu).protocol startLaw horizon scheduler).History =>
    phaseProposalEmissionFrontier setup mode runtime leaks anchor.execution phase anchorTrace.length
      anchor.execution.application.current.native.config startLaw horizon scheduler
        ((menu).toRawTrace startLaw horizon scheduler history.trace)
  obtain ⟨_noInputs, emissions, initialOrigins⟩ :=
    phaseProposal_fresh_entry_binding_origins setup mode runtime
    leaks bounds plan (setup.initialLaw.map encodeInputs) horizon scheduler anchor anchorTrace phase
      installed
      commitment fresh
  have initialized : ∀ state ∈ startLaw.support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have anchorOrdered := (phaseApplication_seedOrder runtime leaks).history startLaw horizon
    scheduler initialized ((menu).toRawTrace startLaw horizon scheduler anchorTrace)
  have endpoint : ∀ final ∈ law.support,
      ∃ (ending before : (app).Control)
        (prior : ((menu).protocol startLaw horizon scheduler).Trace (some before))
        (joint : Player → Option (app).Action)
        (legal : ((menu).protocol startLaw horizon scheduler).Legal (some before) joint)
        (realized : some ending ∈ ((app).transition startLaw horizon scheduler
          (some before) joint).support) (raw : RecoveryState (graph)),
        final.state = some ending ∧ TracePrefix anchorTrace prior ∧
          TracePrefix (prior.extend joint legal realized) final.trace ∧
          PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
          phase.Finished (phase.drain raw) ∧
          (phase.drain raw).excluded = anchor.execution.application.current.excluded ∧
          PhaseProposal.sourceArchive ending.execution.network.inputs =
            PhaseProposal.sourceArchive anchor.execution.network.inputs ∧
          (∀ event ∈ phase.events, event ∈ (frontier final).cut.completed) ∧
          (∀ event ∈ phase.events, ∀ owner ∉ anchor.execution.application.current.excluded,
            ∀ payload (binding : (graph).outputLayout event = .binding owner payload),
              (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
                  (phase.drain raw).native.config.store =
                (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
                  (frontier final).store) ∧
          before.execution.application.attempt = anchor.execution.application.attempt ∧
          phase ∈ before.execution.application.phases.head? ∧
          ending.execution.application =
            ({ before.execution.application with current := raw } :
              PhaseRuntimeState graph).normalize ∧
          (phase.drain raw).native.BindingInvariant ∧ (phase.drain raw).FailureCoverage := by
    intro final supported
    rcases anchor with ⟨remaining, actor, execution⟩
    change actor = none at idle
    subst actor
    obtain ⟨ending, before, prior, joint, legal, realized, raw, stateEq, _idleEnd, changed,
        fromAnchor, toFinal, sameAttempt, beforeInstalled, normalized, effect, finished,
        bindingInvariant, coverage, snapshotE, _accepted, _candidates, oldArchive, _tail⟩ :=
      phaseProposalUnflagged_stopped_binding_image setup mode runtime leaks bounds plan complete
        covered maximal (serviceGraph_revealRelaxedOrdered setup mode) values fullValues tape
          activationGap processingGap gaps margin capacity remaining execution anchorTrace phase
            (Option.mem_def.mpr installed) commitment final (by
              convert supported using 1
              congr 3
              funext history
              dsimp only [stopped]
              cases history.state <;> rfl)
    let endingTrace : ((menu).protocol startLaw horizon scheduler).Trace (some ending) :=
      stateEq ▸ final.trace
    have wholePrefix : TracePrefix anchorTrace endingTrace := by
      dsimp only [endingTrace]
      cases final
      cases stateEq
      exact fromAnchor.trans ((TracePrefix.extend .refl joint legal realized).trans toFinal)
    have finalE : ending.execution.application.current.excluded =
        execution.application.current.excluded := by
      apply Finset.Subset.antisymm
      · intro owner excluded
        by_contra active
        have survival := phaseProposalUnflagged_stopped_survival_of_fresh setup mode runtime leaks
          bounds plan complete covered maximal (serviceGraph_revealRelaxedOrdered setup mode)
            values fullValues tape activationGap processingGap gaps margin capacity remaining
              execution anchorTrace phase (Option.mem_def.mpr installed) commitment owner active
                (by
                  intro event request
                  rintro ⟨record, member, requested⟩
                  exact fresh owner record member requested.1.symm) final (by
                    convert supported using 1
                    congr 3
                    funext history
                    dsimp only [stopped]
                    cases history.state <;> rfl) ending stateEq
        exact survival excluded
      · exact excluded_prefix_grows setup mode runtime leaks bounds plan
          (setup.initialLaw.map encodeInputs) horizon scheduler
            ⟨remaining, none, execution⟩ ending anchorTrace endingTrace wholePrefix
    have beforeE : before.execution.application.current.excluded =
        execution.application.current.excluded :=
      Finset.Subset.antisymm (by
        have tailPrefix : TracePrefix prior endingTrace := by
          dsimp only [endingTrace]
          cases final
          cases stateEq
          exact (TracePrefix.extend .refl joint legal realized).trans toFinal
        simpa only [finalE] using excluded_prefix_grows setup mode runtime leaks bounds plan
          (setup.initialLaw.map encodeInputs) horizon scheduler before ending prior endingTrace
            tailPrefix) (excluded_prefix_grows setup mode runtime leaks bounds plan
              (setup.initialLaw.map encodeInputs) horizon scheduler
                ⟨remaining, none, execution⟩ before anchorTrace prior fromAnchor)
    have frame := phaseProposalEmissionFrontier_callback_frame setup mode runtime leaks bounds
      plan
      (setup.initialLaw.map encodeInputs) horizon scheduler complete maximal
        ⟨remaining, none, execution⟩ anchorTrace phase installed commitment entryExcluded
          initialOrigins emissions before prior fromAnchor sameAttempt beforeE
    have entryEq := phase_attempt_progress_of_prefix runtime leaks menu startLaw initialized horizon
      scheduler ⟨remaining, none, execution⟩ before anchorTrace prior fromAnchor anchorOrdered
    have entryE : before.execution.application.entry.excluded =
        execution.application.current.excluded :=
      (congrArg (fun entry => entry.excluded)
        (entryEq.2.2 sameAttempt.symm).symm).trans entryExcluded
    have rawFields := closing_raw_bindings setup mode runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon scheduler before ending prior raw effect
        (by intro equal; exact changed (equal.trans sameAttempt))
    have scalar := closing_image_frontier setup mode runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon scheduler before prior phase
        (Option.mem_def.mp beforeInstalled) commitment _ frame.within (by
          simpa only [entryE] using frame.quiet) frame.emissions raw rawFields.1 rawFields.2
            finished
            bindingInvariant coverage (snapshotE.trans (finalE.trans entryE.symm))
    have beforeIdle : before.actor = none := by
      cases acting : before.actor with
      | none => rfl
      | some owner =>
        have literal := realized
        simp only [ReactiveApplication.transition, acting, PMF.mem_support_pure_iff] at literal
        have target := Option.some.inj literal
        have equal : ending.execution.application.attempt =
            before.execution.application.attempt := by
          apply (congrArg (fun control : (app).Control =>
            control.execution.application.attempt) target).trans
          generalize (joint owner).getD ⟨none⟩ = response
          rcases response with ⟨_ | material⟩ <;> rfl
        exact (changed (equal.trans sameAttempt)).elim
    have finalExact : (⟨some ending, prior.extend joint legal realized⟩ :
        ((menu).protocol startLaw horizon scheduler).History) = final := by
      apply toFinal.eq_of_length
      have upper := toFinal.length_le
      by_contra unequal
      have shorter : (prior.extend joint legal realized).length < final.trace.length := by omega
      have first := model.runBehavioralUntil_support_first
        ((menu).bounded startLaw horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, execution⟩, anchorTrace⟩ final supported
          ⟨some ending, prior.extend joint legal realized⟩
          (.extend fromAnchor joint legal realized) toFinal shorter
      exact first changed
    have frontierEq : frontier final = phaseProposalEmissionFrontier setup mode runtime leaks
        execution phase anchorTrace.length execution.application.current.native.config startLaw
          horizon scheduler ((menu).toRawTrace startLaw horizon scheduler prior) := by
      rw [← finalExact]
      dsimp only [frontier]
      rw [ReactiveApplication.ResponseMenu.toRawTrace, phaseProposalEmissionFrontier,
        ite_eq_left (by simpa only [(menu).toRawTrace_length] using fromAnchor.length_le)]
      simp only [phaseProposalBindingFrontierAdvance, sameAttempt, ↓reduceIte, beforeIdle]
    refine ⟨ending, before, prior, joint, legal, realized, raw, stateEq, fromAnchor, toFinal,
      effect, finished, snapshotE.trans finalE, oldArchive, ?_, ?_, sameAttempt,
      beforeInstalled, normalized, bindingInvariant, coverage⟩
    · simpa only [frontierEq] using scalar.1
    · simpa only [entryE, frontierEq] using scalar.2
  choose ending before prior joint legal realized raw facts using endpoint
  let image := fun final : ((menu).protocol startLaw horizon scheduler).History =>
    if member : final ∈ law.support then phase.drain (raw final member)
    else anchor.execution.application.current
  have imageEq : ∀ final (member : final ∈ law.support),
      image final = phase.drain (raw final member) := by
    intro final member
    simp only [image, dite_eq_left member]
  refine ⟨image, ?_, ?_⟩
  · intro final member
    obtain ⟨stateEq, fromAnchor, toFinal, effect, finished, imageE, oldArchive,
      _completed, _scalar, sameAttempt, beforeInstalled, normalized, valid, coverage⟩ :=
        facts final member
    exact ⟨ending final member, before final member, prior final member, joint final member,
      legal final member, realized final member, raw final member, stateEq, fromAnchor, toFinal,
      effect, imageEq final member, (imageEq final member).symm ▸ finished,
      (congrArg RecoveryState.excluded (imageEq final member)).trans imageE, oldArchive,
      sameAttempt, beforeInstalled, normalized, (imageEq final member).symm ▸ valid,
      (imageEq final member).symm ▸ coverage⟩
  let graphProfile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan
    anchor.execution phase values
  let read := fun key : (graph).SemanticKey => phaseProposalBindingWord setup.program block suffix
    embedding anchor.execution.application.current.excluded key.2.1 entry
  have imageWord : ∀ final ∈ law.support,
      phaseProposalBindingWord setup.program block suffix embedding
          anchor.execution.application.current.excluded (image final).native.config.store entry =
        phaseProposalBindingWord setup.program block suffix embedding
          anchor.execution.application.current.excluded (frontier final).store entry := by
    intro final member
    obtain ⟨_stateEq, _fromAnchor, _toFinal, _effect, _finished, _imageE, _oldArchive,
      _completed, same, _sameAttempt, _beforeInstalled, _normalized, _valid, _coverage⟩ :=
        facts final member
    rw [imageEq final member]
    apply phaseProposalBindingWord_congr setup.program block suffix embedding
    intro who active index inside owned
    obtain ⟨owner, payload, _member, layout⟩ := block.binding_before_length suffix index inside
    have ownerEq : owner = who := Option.some.inj
      (((eventOwner?_eq_actor (block.prepend suffix) index).trans
        (EventGraph.actor?_of_outputLayout_binding _ layout)).symm.trans owned)
    subst owner
    have binding : (graph).outputLayout (embedding.event index) = .binding who payload :=
      (embedding.layout_eq index).trans layout
    have scalar := same (embedding.event index) (locations index inside) who active payload binding
    have outputEq : (phase.drain (raw final member)).native.config.outputs
        (embedding.event index) = (frontier final).outputs (embedding.event index) := by
      apply (cast_inj (congrArg (fun field : EventField Player L => Option field.Value) binding)).mp
      exact scalar
    change cast _ ((phase.drain (raw final member)).native.config.outputs (embedding.event index)) =
      cast _ ((frontier final).outputs (embedding.event index))
    rw [outputEq]
  have harmonic := phaseProposalUnflagged_stopped_potential_of_fresh_entry setup mode runtime leaks
    bounds plan complete covered maximal values fullValues tape activationGap processingGap gaps
      margin capacity anchor idle anchorTrace phase installed commitment entryExcluded fresh
  have projected := congrArg (fun distribution => distribution.map read) harmonic
  rw [PMF.map_bind] at projected
  have images : (law.bind fun final =>
      ((graph).canonicalContinuation graphProfile (frontier final)).map read) =
      law.map (fun final => phaseProposalBindingWord setup.program block suffix embedding
        anchor.execution.application.current.excluded (image final).native.config.store entry) := by
    calc
      _ = law.bind (fun final => PMF.pure (phaseProposalBindingWord setup.program block suffix
          embedding anchor.execution.application.current.excluded
            (image final).native.config.store entry)) := by
        apply bind_congr_on_support
        intro final member
        have completed := (facts final member).2.2.2.2.2.2.2.1
        have pointmass := completed_word_canonical setup mode block suffix embedding
          anchor.execution.application.current.excluded entry graphProfile (frontier final)
            (fun index inside => completed (embedding.event index) (locations index inside))
        exact pointmass.trans (congrArg PMF.pure (imageWord final member).symm)
      _ = _ := PMF.bind_pure_comp _ _
  exact images.symm.trans projected

/-- The admitted original attempt closes with the actual pending-and-emitted
word law from its retained entry, even when the continuation starts mid-block. -/
theorem phaseProposalUnflagged_stopped_binding_word_from_retained_entry
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (anchor : (app).Control) (idle : anchor.actor = none)
    (anchorTrace : ((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some anchor))
    (phase : RuntimePhase (graph))
    (installed : anchor.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (origin : (app).Control)
    (originTrace : ((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some origin))
    (retained : TracePrefix originTrace anchorTrace)
    (originAttempt : origin.execution.application.attempt = anchor.execution.application.attempt)
    (originInstalled : origin.execution.application.phases.head? = some phase)
    (entryExcluded : origin.execution.application.entry.excluded =
      origin.execution.application.current.excluded)
    (fresh : ∀ who, ∀ record ∈ origin.execution.recall who,
      record.beforeView.application.2.attempt ≠ origin.execution.application.attempt)
    (clean : anchor.execution.application.current.excluded =
      origin.execution.application.current.excluded)
    (afterProcessing : ReservedEpoch.packetCapacity runtime ≤
      anchor.execution.environmentRecall.length %
        ReservedEpoch.cycleWidth («graph» := graph) (ReservedEpoch.packetCapacity runtime))
    (admitted : ∀ owner, owner ∉ anchor.execution.application.current.excluded →
      ∀ event ∈ phase.events, ∀ payload,
      (graph).outputLayout event = .binding owner payload →
      ReservedEpoch.ownedAcceptanceWord runtime leaks tape anchor.execution owner event)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (entry : SourceProgram.Config Player L Γ)
    (locations : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      embedding.event index ∈ phase.events) :
    let startLaw := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let model := (menu).information startLaw horizon scheduler
    let profile := fun who => (menu).restrictPolicy startLaw horizon scheduler who
      (ReactiveApplication.anchoredPolicy anchor.execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    let stopped := fun history : ((menu).protocol startLaw horizon scheduler).History =>
      match history.state with
      | none => False
      | some current => current.execution.application.attempt ≠ anchor.execution.application.attempt
    let law := model.runBehavioralUntil
      ((menu).bounded startLaw horizon scheduler).wellFoundedHistories profile stopped
        ⟨some anchor, anchorTrace⟩
    ∃ image : ((menu).protocol startLaw horizon scheduler).History → RecoveryState (graph),
      (∀ final ∈ law.support,
        ∃ (ending before : (app).Control)
          (prior : ((menu).protocol startLaw horizon scheduler).Trace (some before))
          (joint : Player → Option (app).Action)
          (legal : ((menu).protocol startLaw horizon scheduler).Legal (some before) joint)
          (realized : some ending ∈ ((app).transition startLaw horizon scheduler
            (some before) joint).support) (raw : RecoveryState (graph)),
          final.state = some ending ∧ TracePrefix anchorTrace prior ∧
            TracePrefix (prior.extend joint legal realized) final.trace ∧
            PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
            image final = phase.drain raw ∧ phase.Finished (image final) ∧
            (image final).excluded = anchor.execution.application.current.excluded ∧
            PhaseProposal.sourceArchive ending.execution.network.inputs =
              PhaseProposal.sourceArchive anchor.execution.network.inputs ∧
            before.execution.application.attempt = anchor.execution.application.attempt ∧
            phase ∈ before.execution.application.phases.head? ∧
            ending.execution.application =
              ({ before.execution.application with current := raw } :
                PhaseRuntimeState graph).normalize ∧
            (image final).native.BindingInvariant ∧ (image final).FailureCoverage) ∧
      law.map (fun final => phaseProposalBindingWord setup.program block suffix embedding
        anchor.execution.application.current.excluded (image final).native.config.store entry) =
          ((graph).canonicalContinuation
            (phaseProposalBindingPotentialProfile setup mode runtime leaks plan origin.execution
              phase values) (phaseProposalEmissionFrontier setup mode runtime leaks origin.execution
                phase originTrace.length origin.execution.application.current.native.config startLaw
                  horizon scheduler ((menu).toRawTrace startLaw horizon scheduler anchorTrace))).map
                (fun key => phaseProposalBindingWord setup.program block suffix embedding
                  anchor.execution.application.current.excluded key.2.1 entry) := by
  classical
  intro startLaw horizon scheduler model profile stopped law
  let frontier := fun history : ((menu).protocol startLaw horizon scheduler).History =>
    phaseProposalEmissionFrontier setup mode runtime leaks origin.execution phase originTrace.length
      origin.execution.application.current.native.config startLaw horizon scheduler
        ((menu).toRawTrace startLaw horizon scheduler history.trace)
  obtain ⟨_noInputs, emissions, initialOrigins⟩ :=
    phaseProposal_fresh_entry_binding_origins setup mode runtime
    leaks bounds plan (setup.initialLaw.map encodeInputs) horizon scheduler origin originTrace phase
      originInstalled commitment fresh
  have initialized : ∀ state ∈ startLaw.support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have originOrdered := (phaseApplication_seedOrder runtime leaks).history startLaw horizon
    scheduler initialized ((menu).toRawTrace startLaw horizon scheduler originTrace)
  have endpoint : ∀ final ∈ law.support,
      ∃ (ending before : (app).Control)
        (prior : ((menu).protocol startLaw horizon scheduler).Trace (some before))
        (joint : Player → Option (app).Action)
        (legal : ((menu).protocol startLaw horizon scheduler).Legal (some before) joint)
        (realized : some ending ∈ ((app).transition startLaw horizon scheduler
          (some before) joint).support) (raw : RecoveryState (graph)),
        final.state = some ending ∧ TracePrefix anchorTrace prior ∧
          TracePrefix (prior.extend joint legal realized) final.trace ∧
          PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
          phase.Finished (phase.drain raw) ∧
          (phase.drain raw).excluded = anchor.execution.application.current.excluded ∧
          PhaseProposal.sourceArchive ending.execution.network.inputs =
            PhaseProposal.sourceArchive anchor.execution.network.inputs ∧
          (∀ event ∈ phase.events, event ∈ (frontier final).cut.completed) ∧
          (∀ event ∈ phase.events, ∀ owner ∉ anchor.execution.application.current.excluded,
            ∀ payload (binding : (graph).outputLayout event = .binding owner payload),
              (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
                  (phase.drain raw).native.config.store =
                (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding owner payload)).get?
                  (frontier final).store) ∧
          before.execution.application.attempt = anchor.execution.application.attempt ∧
          phase ∈ before.execution.application.phases.head? ∧
          ending.execution.application =
            ({ before.execution.application with current := raw } :
              PhaseRuntimeState graph).normalize ∧
          (phase.drain raw).native.BindingInvariant ∧ (phase.drain raw).FailureCoverage := by
    intro final supported
    rcases anchor with ⟨remaining, actor, execution⟩
    change actor = none at idle
    subst actor
    obtain ⟨ending, before, prior, joint, legal, realized, raw, stateEq, _idleEnd, changed,
        fromAnchor, toFinal, sameAttempt, beforeInstalled, normalized, effect, finished,
        bindingInvariant, coverage, snapshotE, _accepted, _candidates, oldArchive, _tail⟩ :=
      phaseProposalUnflagged_stopped_binding_image setup mode runtime leaks bounds plan complete
        covered maximal (serviceGraph_revealRelaxedOrdered setup mode) values fullValues tape
          activationGap processingGap gaps margin capacity remaining execution anchorTrace phase
            (Option.mem_def.mpr installed) commitment final (by
              convert supported using 1
              congr 3
              funext history
              dsimp only [stopped]
              cases history.state <;> rfl)
    let endingTrace : ((menu).protocol startLaw horizon scheduler).Trace (some ending) :=
      stateEq ▸ final.trace
    have wholePrefix : TracePrefix anchorTrace endingTrace := by
      dsimp only [endingTrace]
      cases final
      cases stateEq
      exact fromAnchor.trans ((TracePrefix.extend .refl joint legal realized).trans toFinal)
    have finalE : ending.execution.application.current.excluded =
        execution.application.current.excluded := by
      apply Finset.Subset.antisymm
      · intro owner excluded
        by_contra active
        obtain ⟨actualEnding, _before, _prior, _joint, _legal, _realized, _raw,
          actualState, _idle, _changed, _from, _to, _same, _installed, _effect, _finished,
          _normalized, _coverage, _excluded, _tables, _candidates, _archive, _retired,
          _retiredAfter, _word, survives, _footprint⟩ :=
          phaseProposalUnflagged_stopped_acceptance_word setup mode runtime leaks bounds plan
            complete covered maximal (serviceGraph_revealRelaxedOrdered setup mode) values
              fullValues tape activationGap processingGap gaps margin capacity remaining execution
                anchorTrace phase (Option.mem_def.mpr installed) commitment afterProcessing
                  final (by
                  convert supported using 1
                  congr 3
                  funext history
                  dsimp only [stopped]
                  cases history.state <;> rfl)
        have endingEq : actualEnding = ending := Option.some.inj (actualState.symm.trans stateEq)
        subst actualEnding
        exact survives owner active (admitted owner active) excluded
      · exact excluded_prefix_grows setup mode runtime leaks bounds plan
          (setup.initialLaw.map encodeInputs) horizon scheduler
            ⟨remaining, none, execution⟩ ending anchorTrace endingTrace wholePrefix
    have beforeE : before.execution.application.current.excluded =
        execution.application.current.excluded :=
      Finset.Subset.antisymm (by
        have tailPrefix : TracePrefix prior endingTrace := by
          dsimp only [endingTrace]
          cases final
          cases stateEq
          exact (TracePrefix.extend .refl joint legal realized).trans toFinal
        simpa only [finalE] using excluded_prefix_grows setup mode runtime leaks bounds plan
          (setup.initialLaw.map encodeInputs) horizon scheduler before ending prior endingTrace
            tailPrefix) (excluded_prefix_grows setup mode runtime leaks bounds plan
              (setup.initialLaw.map encodeInputs) horizon scheduler
                ⟨remaining, none, execution⟩ before anchorTrace prior fromAnchor)
    have sameOrigin : before.execution.application.attempt =
        origin.execution.application.attempt := sameAttempt.trans originAttempt.symm
    have frame := phaseProposalEmissionFrontier_callback_frame setup mode runtime leaks bounds
      plan
      (setup.initialLaw.map encodeInputs) horizon scheduler complete maximal origin originTrace
        phase
        originInstalled commitment entryExcluded initialOrigins emissions before prior
          (retained.trans fromAnchor) sameOrigin (beforeE.trans clean)
    have entryEq := phase_attempt_progress_of_prefix runtime leaks menu startLaw initialized horizon
      scheduler origin before originTrace prior (retained.trans fromAnchor) originOrdered
    have entryE : before.execution.application.entry.excluded =
        execution.application.current.excluded :=
      (congrArg (fun entry => entry.excluded)
        (entryEq.2.2 sameOrigin.symm).symm).trans (entryExcluded.trans clean.symm)
    have rawFields := closing_raw_bindings setup mode runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon scheduler before ending prior raw effect
        (by intro equal; exact changed (equal.trans sameAttempt))
    have scalar := closing_image_frontier setup mode runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon scheduler before prior phase
        (Option.mem_def.mp beforeInstalled) commitment _ frame.within (by
          simpa only [entryE, ← clean] using frame.quiet) frame.emissions raw
            rawFields.1 rawFields.2
            finished
            bindingInvariant coverage (snapshotE.trans (finalE.trans entryE.symm))
    have beforeIdle : before.actor = none := by
      cases acting : before.actor with
      | none => rfl
      | some owner =>
        have literal := realized
        simp only [ReactiveApplication.transition, acting, PMF.mem_support_pure_iff] at literal
        have target := Option.some.inj literal
        have equal : ending.execution.application.attempt =
            before.execution.application.attempt := by
          apply (congrArg (fun control : (app).Control =>
            control.execution.application.attempt) target).trans
          generalize (joint owner).getD ⟨none⟩ = response
          rcases response with ⟨_ | material⟩ <;> rfl
        exact (changed (equal.trans sameAttempt)).elim
    have finalExact : (⟨some ending, prior.extend joint legal realized⟩ :
        ((menu).protocol startLaw horizon scheduler).History) = final := by
      apply toFinal.eq_of_length
      have upper := toFinal.length_le
      by_contra unequal
      have shorter : (prior.extend joint legal realized).length < final.trace.length := by omega
      have first := model.runBehavioralUntil_support_first
        ((menu).bounded startLaw horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, execution⟩, anchorTrace⟩ final supported
          ⟨some ending, prior.extend joint legal realized⟩
          (.extend fromAnchor joint legal realized) toFinal shorter
      exact first changed
    have frontierEq : frontier final = phaseProposalEmissionFrontier setup mode runtime leaks
        origin.execution phase originTrace.length
          origin.execution.application.current.native.config startLaw
          horizon scheduler ((menu).toRawTrace startLaw horizon scheduler prior) := by
      rw [← finalExact]
      dsimp only [frontier]
      rw [ReactiveApplication.ResponseMenu.toRawTrace, phaseProposalEmissionFrontier,
        ite_eq_left (by
          simpa only [(menu).toRawTrace_length] using (retained.trans fromAnchor).length_le)]
      simp only [phaseProposalBindingFrontierAdvance, sameOrigin, ↓reduceIte, beforeIdle]
    refine ⟨ending, before, prior, joint, legal, realized, raw, stateEq, fromAnchor, toFinal,
      effect, finished, snapshotE.trans finalE, oldArchive, ?_, ?_, sameAttempt,
      beforeInstalled, normalized, bindingInvariant, coverage⟩
    · simpa only [frontierEq] using scalar.1
    · simpa only [entryE, frontierEq] using scalar.2
  choose ending before prior joint legal realized raw facts using endpoint
  let image := fun final : ((menu).protocol startLaw horizon scheduler).History =>
    if member : final ∈ law.support then phase.drain (raw final member)
    else anchor.execution.application.current
  have imageEq : ∀ final (member : final ∈ law.support),
      image final = phase.drain (raw final member) := by
    intro final member
    simp only [image, dite_eq_left member]
  refine ⟨image, ?_, ?_⟩
  · intro final member
    obtain ⟨stateEq, fromAnchor, toFinal, effect, finished, imageE, oldArchive,
      _completed, _scalar, sameAttempt, beforeInstalled, normalized, valid, coverage⟩ :=
        facts final member
    exact ⟨ending final member, before final member, prior final member, joint final member,
      legal final member, realized final member, raw final member, stateEq, fromAnchor, toFinal,
      effect, imageEq final member, (imageEq final member).symm ▸ finished,
      (congrArg RecoveryState.excluded (imageEq final member)).trans imageE, oldArchive,
      sameAttempt, beforeInstalled, normalized, (imageEq final member).symm ▸ valid,
      (imageEq final member).symm ▸ coverage⟩
  let graphProfile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan
    origin.execution phase values
  let read := fun key : (graph).SemanticKey => phaseProposalBindingWord setup.program block suffix
    embedding anchor.execution.application.current.excluded key.2.1 entry
  have imageWord : ∀ final ∈ law.support,
      phaseProposalBindingWord setup.program block suffix embedding
          anchor.execution.application.current.excluded (image final).native.config.store entry =
        phaseProposalBindingWord setup.program block suffix embedding
          anchor.execution.application.current.excluded (frontier final).store entry := by
    intro final member
    obtain ⟨_stateEq, _fromAnchor, _toFinal, _effect, _finished, _imageE, _oldArchive,
      _completed, same, _sameAttempt, _beforeInstalled, _normalized, _valid, _coverage⟩ :=
        facts final member
    rw [imageEq final member]
    apply phaseProposalBindingWord_congr setup.program block suffix embedding
    intro who active index inside owned
    obtain ⟨owner, payload, _member, layout⟩ := block.binding_before_length suffix index inside
    have ownerEq : owner = who := Option.some.inj
      (((eventOwner?_eq_actor (block.prepend suffix) index).trans
        (EventGraph.actor?_of_outputLayout_binding _ layout)).symm.trans owned)
    subst owner
    have binding : (graph).outputLayout (embedding.event index) = .binding who payload :=
      (embedding.layout_eq index).trans layout
    have scalar := same (embedding.event index) (locations index inside) who active payload binding
    have outputEq : (phase.drain (raw final member)).native.config.outputs
        (embedding.event index) = (frontier final).outputs (embedding.event index) := by
      apply (cast_inj (congrArg (fun field : EventField Player L => Option field.Value) binding)).mp
      exact scalar
    change cast _ ((phase.drain (raw final member)).native.config.outputs (embedding.event index)) =
      cast _ ((frontier final).outputs (embedding.event index))
    rw [outputEq]
  have harmonic := phaseProposalUnflagged_stopped_potential_from_retained_entry setup mode runtime
    leaks
    bounds plan complete covered maximal values fullValues tape activationGap processingGap gaps
      margin capacity anchor idle anchorTrace phase installed commitment origin originTrace retained
        originAttempt originInstalled entryExcluded fresh clean afterProcessing admitted
  have projected := congrArg (fun distribution => distribution.map read) harmonic
  rw [PMF.map_bind] at projected
  have images : (law.bind fun final =>
      ((graph).canonicalContinuation graphProfile (frontier final)).map read) =
      law.map (fun final => phaseProposalBindingWord setup.program block suffix embedding
        anchor.execution.application.current.excluded (image final).native.config.store entry) := by
    calc
      _ = law.bind (fun final => PMF.pure (phaseProposalBindingWord setup.program block suffix
          embedding anchor.execution.application.current.excluded
            (image final).native.config.store entry)) := by
        apply bind_congr_on_support
        intro final member
        have completed := (facts final member).2.2.2.2.2.2.2.1
        have pointmass := completed_word_canonical setup mode block suffix embedding
          anchor.execution.application.current.excluded entry graphProfile (frontier final)
            (fun index inside => completed (embedding.event index) (locations index inside))
        exact pointmass.trans (congrArg PMF.pure (imageWord final member).symm)
      _ = _ := PMF.bind_pure_comp _ _
  exact images.symm.trans projected

end Vegas
