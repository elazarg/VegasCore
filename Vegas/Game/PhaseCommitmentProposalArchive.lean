/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalSourceArchive
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseCommitmentExclusionOrigin
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryInvariant

/-! # An opaque commitment attempt preserves every old opening proposal -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
private theorem commitment_response_archive (execution : (app).Execution) (who : Player)
    (material : WitnessedSubmission graph) (event : graph.EventId) (candidate : Handle graph)
    (call : material.call.packet = .commitment event candidate) :
    sourceArchive (execution.respond app who ⟨some material⟩).network.inputs =
      sourceArchive execution.network.inputs := by
  let message : Message Player (app).Payload :=
    ⟨(who, execution.network.nextSerial who),
      (execution.application.submit who material).emit who (execution.network.known who) material⟩
  have absent : packetProposal? message.payload = none := by
    dsimp only [message]
    unfold packetProposal?
    rw [phase_emit_call, call]
  have raw : archive (execution.respond app who ⟨some material⟩).network.inputs =
      archive execution.network.inputs := by
    change archive (execution.network.inputs ++ [message]) = _
    rw [archive_append]
    simp only [archive, List.filterMap_cons, absent, List.filterMap_nil, List.toFinset_nil,
      Finset.union_empty]
  unfold sourceArchive
  rw [raw]

/-- No counted callback can emit an opening while its original commitment
descriptor is installed. The existing stopped evaluator therefore retains the
ENTIRE typed proposal archive at its first namespace exit, including previously
failed or negative-receipt disclosures. No publication plaintext is erased. -/
theorem phase_attempt_stopped_sourceArchive
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler)
    (profile : ∀ who, ((PhaseCount.onePacketMenu runtime leaks bounds).information
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).BehavioralPolicy who)
    (start : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some start))
    (phase : RuntimePhase graph) (installed : phase ∈ start.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) :
    let menu := PhaseCount.onePacketMenu runtime leaks bounds
    let initial := inputs.map (PhaseRuntimeState.initial plan)
    let stopped := fun history : (menu.protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ start.execution.application.attempt
    ∀ final ∈ ((menu.information initial horizon scheduler).runBehavioralUntil
        (menu.bounded initial horizon scheduler).wellFoundedHistories profile stopped
          ⟨some start, trace⟩).support,
      ∃ ending : (app).Control, final.state = some ending ∧
        sourceArchive ending.execution.network.inputs =
          sourceArchive start.execution.network.inputs := by
  classical
  intro menu initial stopped
  let E := menu.protocol initial horizon scheduler
  let model := menu.information initial horizon scheduler
  let property := fun history : E.History =>
    ∃ current : (app).Control, history.state = some current ∧
      current.execution.application.Ordered ∧
      (current.execution.application.attempt = start.execution.application.attempt →
        current.execution.application.phases = start.execution.application.phases) ∧
      sourceArchive current.execution.network.inputs = sourceArchive start.execution.network.inputs
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state positive
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ positive
    exact PhaseRuntimeState.initial_ordered plan draw
  have startOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized (menu.toRawTrace initial horizon scheduler trace)
  have holds : property ⟨some start, trace⟩ :=
    ⟨start, rfl, startOrdered, fun _ => rfl, rfl⟩
  have preserved : ∀ history, ¬ stopped history → ¬ E.terminal history.state →
      property history → ∀ next ∈ (model.runBehavioralFrom profile 1 history).support,
        property next := by
    intro history going running valid next supported
    obtain ⟨current, currentEq, currentOrdered, phasesKept, archiveEq⟩ := valid
    have same : current.execution.application.attempt = start.execution.application.attempt := by
      by_contra changed
      exact going (by simp only [stopped, currentEq]; exact changed)
    obtain ⟨⟨joint, legal, realized⟩, _later⟩ :=
      model.mem_support_runBehavioralFrom_one profile running supported
    have moved : next.state ∈ ((app).transition initial horizon scheduler
        (some current) joint).support := by
      change next.state ∈ ((app).transition initial horizon scheduler history.state joint).support
        at realized
      rwa [currentEq] at realized
    obtain ⟨updated, nextEq, _recall⟩ := (app).transition_recall_prefix initial horizon scheduler
      current next.state joint moved
    have afterMoved : some updated ∈ ((app).transition initial horizon scheduler
        (some current) joint).support := by rwa [nextEq] at moved
    have nextOrdered := (phaseApplication_seedOrder runtime leaks).transition initial horizon
      scheduler initialized (some current) (some updated) joint currentOrdered afterMoved
    refine ⟨updated, nextEq, nextOrdered, ?_, ?_⟩
    · intro sameNext
      exact ((phaseApplication_sameAttempt_phases runtime leaks).transition initial horizon
        scheduler current updated joint afterMoved currentOrdered (same.trans sameNext.symm)).trans
          (phasesKept same)
    · have installedNow : phase ∈ current.execution.application.phases.head? := by
        simpa only [phasesKept same] using installed
      have prior : E.Trace (some current) := currentEq ▸ history.trace
      have legalNow : E.Legal (some current) joint := currentEq ▸ legal
      rcases current with ⟨remaining, actor, execution⟩
      cases actor with
      | some owner =>
          obtain ⟨response, chosen⟩ := LegalOption.exists_eq_some_of_active
            (E := E) (joint owner) (E.legalOption_of_legal legalNow owner) rfl
          have offered : response ∈ PhaseCount.onePacketActions runtime leaks bounds owner
              (execution.recall owner) (execution.observe app owner) := by
            have allowed := legalNow.2 owner
            rw [chosen] at allowed
            exact allowed.2
          simp only [ReactiveApplication.transition, chosen, Option.getD_some] at afterMoved
          cases (PMF.mem_support_pure_iff _ _).mp afterMoved
          apply Eq.trans ?_ archiveEq
          rcases response with ⟨transmission⟩
          cases transmission with
          | none => rfl
          | some material =>
              obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent
                runtime leaks bounds plan inputs horizon scheduler remaining owner execution
                  prior material offered
              obtain ⟨actualPhase, actualInstalled, inside⟩ := request.2.1
              have phaseEq : actualPhase = phase := Option.some.inj
                ((Option.mem_def.mp actualInstalled).symm.trans (Option.mem_def.mp installedNow))
              subst actualPhase
              obtain ⟨who, payload, binding⟩ := commitment ▸ phase.fields coordinate.event
                ((phase.mem_events coordinate.event).mp inside).1
                ((phase.mem_events coordinate.event).mp inside).2
              have ownerEq : who = owner := Option.some.inj
                ((graph.actor?_of_outputLayout_binding binding).symm.trans request.2.2.2.1)
              subst who
              obtain ⟨serial, preparation, evidence, materialEq, _bounded, _fresh⟩ :=
                PhaseCount.onePacket_binding_shape runtime leaks bounds plan ordered inputs horizon
                  scheduler remaining owner execution prior coordinate.event payload binding
                    (by exact ⟨rfl, request.2⟩) material offered
              exact commitment_response_archive runtime leaks execution owner material
                coordinate.event (owner, .prepared serial) (by rw [materialEq])
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp afterMoved
              exact archiveEq
          | succ remaining =>
              obtain ⟨command, _selected, actual⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterMoved)
              obtain ⟨after, stepped, equal⟩ := PMF.support_map .. ▸ actual
              cases Option.some.inj equal
              have kept := sourceArchive_environmentStep runtime leaks execution after command
                stepped
              exact kept.trans archiveEq
  intro final supported
  obtain ⟨ending, stateEq, _ordered, _phases, archiveEq⟩ :=
    model.runBehavioralUntil_support_history_closed
      (menu.bounded initial horizon scheduler).wellFoundedHistories profile stopped property
        preserved ⟨some start, trace⟩ holds final supported
  exact ⟨ending, stateEq, archiveEq⟩

end Vegas.EventGraphRuntime.PhaseProposal
