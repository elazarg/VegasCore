/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalEmissionOrigin
import Vegas.Game.PhaseProposalBindingPending
import Vegas.Game.PhaseProposalBindingSettlement

/-! # Actual readiness at the retained emitted binding frontier -/

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

/-- Forward signed meanings and the derived inverse SEND witnesses identify
actual readiness at the SAME trace frontier. Inherited-E automatic nodes are
retained explicitly; no synthetic own response history is used. -/
theorem phaseProposalEmissionFrontier_ready
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (anchorLength : Nat)
    (initialFrontier : (graph).Config)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (installed : control.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (sameAttempt : control.execution.application.attempt = anchor.application.attempt)
    (sameExcluded : control.execution.application.current.excluded =
      anchor.application.current.excluded)
    (entryExcluded : control.execution.application.entry.excluded =
      anchor.application.current.excluded)
    (initialOrigins : ∀ query ∈ initialFrontier.cut.completed,
      query.val < phase.low ∨
        ∃ owner ∈ anchor.application.current.excluded, (graph).actor? query = some owner) :
    let frontier := phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength
      initialFrontier initial horizon scheduler ((menu).toRawTrace initial horizon scheduler trace)
    (∀ query : (graph).EventId, query.val < phase.low →
      control.execution.application.entry.native.config.outputs query = frontier.outputs query) →
    PhaseProposalEmittedBindings runtime leaks control.execution phase frontier →
    (∀ query ∈ phase.events, frontier.cut.Ready query →
      ∀ owner ∈ control.execution.application.entry.excluded,
        (graph).actor? query ≠ some owner) →
    (∀ query ∈ frontier.cut.completed, query.val < phase.high) →
    ∀ who (event : (graph).EventId),
      control.execution.application.current.native.config.cut.Ready event →
      (graph).actor? event = some who →
      who ∉ control.execution.application.current.excluded →
      (∀ message ∈ (app).outputs (control.execution.recall who),
        PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩) →
      frontier.cut.Ready event ∧
        (∀ pending ∈ frontier.cut.completed,
          pending ∉ control.execution.application.current.native.config.cut.completed →
            ¬ (graph).fieldVisibleTo who (.inr pending)) := by
  intro frontier prior emissions quiet bounded who event ready actor active unsent
  let raw := (menu).toRawTrace initial horizon scheduler trace
  have excluded : control.execution.application.current.excluded =
      control.execution.application.entry.excluded := sameExcluded.trans entryExcluded.symm
  have domain := phaseProposalBinding_settled_domain runtime leaks bounds plan inputs horizon
    scheduler (serviceGraph_revealRelaxedOrdered setup mode) control trace phase installed
      commitment
      frontier excluded prior emissions quiet
  have earlier : ∀ query : (graph).EventId, query.val < phase.low →
      query ∈ control.execution.application.current.native.config.cut.completed := by
    have receipts := phaseReceiptRecord_history runtime leaks
      (serviceGraph_revealRelaxedOrdered setup mode) plan inputs horizon scheduler raw
    have positioned := receipts.exclusion.frontier.positioned
    cases phases : control.execution.application.phases with
    | nil => simp only [phases, List.head?_nil, reduceCtorEq] at installed
    | cons first rest =>
        have same : first = phase := by simpa only [phases, List.head?_cons, Option.some.injEq]
          using installed
        subst first
        have position :
            control.execution.application.current.native.config.cut.Within phase.low phase.high :=
          (show control.execution.application.entry.native.config.cut.IsPrefix phase.low ∧
            control.execution.application.current.native.config.cut.Within phase.low phase.high
              from by simpa only [PhaseRuntimeState.Positioned, phases] using positioned).2
        exact position.1
  have origins : ∀ query ∈ frontier.cut.completed,
      query ∉ control.execution.application.current.native.config.cut.completed →
      query ∈ phase.events → (∃ message ∈ control.execution.network.inputs,
        message.payload.attempt = control.execution.application.attempt ∧
        message.payload.packet.call.event? (graph) = some query ∧
        (graph).actor? query = some message.sender) ∨
      ∃ owner ∈ control.execution.application.current.excluded,
        (graph).actor? query = some owner := by
    intro query completed missing _inside
    rcases phaseProposalEmissionFrontier_origin setup mode runtime leaks anchor phase anchorLength
        initialFrontier initial horizon scheduler query raw completed with old | automatic | sent
    · rcases initialOrigins query old with below | excluded
      · exact (missing (earlier query below)).elim
      · exact Or.inr (by simpa only [sameExcluded] using excluded)
    · exact Or.inr (by simpa only [sameExcluded] using automatic)
    · obtain ⟨before, after, first, joint, legal, realized, kept, _later, emitted⟩ := sent
      obtain ⟨message, member, attempt, named, sender⟩ := phaseProposalBindingEmissionAt_input
        setup mode runtime leaks anchor initial horizon scheduler first joint legal realized
          control raw kept query emitted
      exact Or.inl ⟨message, member, attempt.trans sameAttempt.symm, named, sender⟩
  have hidden := phaseProposalBinding_pending_hidden runtime leaks bounds plan inputs horizon
    scheduler (serviceGraph_revealRelaxedOrdered setup mode) control trace phase commitment frontier
      earlier bounded origins who event ready actor active unsent
  refine ⟨⟨?_, fun predecessor member => domain (ready.2 member)⟩, hidden⟩
  intro completed
  exact hidden event completed ready.1
    (EventCode.output_visible_of_actor ((graph).nodes event) who actor)

end Vegas
