/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalEmissionFrontier
import Vegas.Pending.PhaseOwnCommitments
import Interaction.ReactiveHistory

/-! # Original SEND provenance of the current emission frontier -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

/-- An actual response at this original namespace supplies an owned binding
packet. This retains the original raw joint and material, not a new draw. -/
def PhaseProposalBindingEmissionAt (anchor : (app).Execution)
    (before : (app).ProtocolState) (joint : Player → Option (app).Action)
    (event : (graph).EventId) : Prop :=
  ∃ who, (graph).actor? event = some who ∧
    ∃ remaining execution, before = some ⟨remaining, some who, execution⟩ ∧
      execution.application.attempt = anchor.application.attempt ∧
      ∃ response material candidate, joint who = some response ∧
        response.transmission = some material ∧
        material.call.packet = .commitment event candidate

/-- The existing deterministic closure creates only inherited-E events.
The proof follows its existing native automatic path; it does not reimplement
that closure or fabricate physical responses. -/
theorem phaseProposalBindingFrontierDrain_origin
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (frontier : (graph).Config)
    (event : (graph).EventId)
    (completed : event ∈
      (phaseProposalBindingFrontierDrain setup mode runtime leaks anchor phase
        frontier).cut.completed) :
    event ∈ frontier.cut.completed ∨
      ∃ owner ∈ anchor.application.current.excluded, (graph).actor? event = some owner := by
  let state : RecoveryState (graph) :=
    ⟨{ anchor.application.current.native with config := frontier },
      anchor.application.current.excluded⟩
  have preserve : ∀ after, Relation.ReflTransGen phase.AutomaticStep state after →
      after.excluded = state.excluded ∧
        ∀ query ∈ after.native.config.cut.completed,
          query ∈ frontier.cut.completed ∨
            ∃ owner ∈ state.excluded, (graph).actor? query = some owner := by
    intro after path
    induction path with
    | refl => exact ⟨rfl, fun _ member => Or.inl member⟩
    | @tail middle after path step ih =>
        obtain ⟨selected, eligible, rfl⟩ := step
        refine ⟨ih.1, ?_⟩
        intro query member
        obtain ⟨action, supported⟩ := middle.completeAutomatic_step selected eligible.2
        rw [middle.native.config.step_cut _ eligible.2.1 action _ supported] at member
        rcases Finset.mem_insert.mp member with same | previous
        · subst query
          obtain ⟨owner, acting, excluded⟩ := eligible.2.owned
          exact Or.inr ⟨owner, ih.1 ▸ excluded, acting⟩
        · exact ih.2 query previous
  exact (preserve _ (phase.drain_trace state)).2 event completed

/-- Every new frontier coordinate is either a literal current SEND or an
inherited excluded completion. Totalization branches cannot invent a third
origin. The actual original joint is retained in the SEND alternative. -/
theorem phaseProposalBindingFrontierAdvance_origin
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (frontier : (graph).Config)
    (before : (app).ProtocolState) (joint : Player → Option (app).Action)
    (query : (graph).EventId)
    (completed : query ∈ (phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor
      phase frontier before joint).cut.completed) :
    query ∈ frontier.cut.completed ∨
      (∃ owner ∈ anchor.application.current.excluded, (graph).actor? query = some owner) ∨
        PhaseProposalBindingEmissionAt setup mode runtime leaks anchor before joint query := by
  cases before with
  | none => exact Or.inl completed
  | some control =>
      by_cases attempted : control.execution.application.attempt = anchor.application.attempt
      · cases actor : control.actor with
        | none => exact Or.inl (by
            simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor]
              using completed)
        | some who =>
            cases sent : ((joint who).getD ⟨none⟩).transmission with
            | none => exact Or.inl (by
                simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte,
                  actor, sent] using completed)
            | some material =>
                cases packet : material.call.packet with
                | opening => exact Or.inl (by
                    simpa only [phaseProposalBindingFrontierAdvance, attempted,
                      ↓reduceIte, actor, sent, packet] using completed)
                | malformed => exact Or.inl (by
                    simpa only [phaseProposalBindingFrontierAdvance, attempted,
                      ↓reduceIte, actor, sent, packet] using completed)
                | commitment event candidate =>
                    by_cases inside : event ∈ phase.events
                    · cases node : nodeView (graph) event with
                      | bind owner payload binding code =>
                          by_cases same : owner = who
                          · by_cases ready : frontier.cut.Ready event
                            · let result :=
                                (((((joint who).getD ⟨none⟩).transmission.bind
                                  PhaseProposal.bindingPreparation).bind
                                    (fun raw => raw.as? payload)).elim PublicationResult.failure
                                      PublicationResult.success)
                              let next := frontier.complete event ready
                                (cast (congrArg EventField.Action binding.symm) result)
                                (cast (congrArg EventField.Value binding.symm) result)
                              have after : query ∈ (phaseProposalBindingFrontierDrain setup mode
                                  runtime leaks anchor phase next).cut.completed := by
                                simpa only [phaseProposalBindingFrontierAdvance, attempted,
                                  ↓reduceIte, actor, sent, packet, inside, node, same, ready,
                                  dite_true, next, result] using completed
                              rcases phaseProposalBindingFrontierDrain_origin setup mode runtime
                                  leaks anchor phase next query after with old | automatic
                              · change query ∈ insert event frontier.cut.completed at old
                                rcases Finset.mem_insert.mp old with equal | previous
                                · subst query
                                  refine Or.inr (Or.inr ⟨who, ?_, control.remaining,
                                    control.execution, ?_, attempted, ?_⟩)
                                  · rw [← same]
                                    exact nodeView_bind_actor binding code
                                  · cases control
                                    cases actor
                                    rfl
                                  · cases selected : joint who with
                                    | none => simp only [selected, Option.getD_none] at sent
                                              cases sent
                                    | some response => exact ⟨response, material, candidate,
                                        rfl, by
                                          simpa only [selected, Option.getD_some] using sent,
                                          packet⟩
                                · exact Or.inl previous
                              · exact Or.inr (Or.inl automatic)
                            · exact Or.inl (by
                                simpa only [phaseProposalBindingFrontierAdvance, attempted,
                                  ↓reduceIte, actor, sent, packet, inside, node, same, ready,
                                  dite_false] using completed)
                          · exact Or.inl (by
                              simpa only [phaseProposalBindingFrontierAdvance, attempted,
                                ↓reduceIte, actor, sent, packet, inside, node, same]
                                  using completed)
                      | resolve => exact Or.inl (by
                          simpa only [phaseProposalBindingFrontierAdvance, attempted,
                            ↓reduceIte, actor, sent, packet, inside, node] using completed)
                      | sample => exact Or.inl (by
                          simpa only [phaseProposalBindingFrontierAdvance, attempted,
                            ↓reduceIte, actor, sent, packet, inside, node] using completed)
                    · exact Or.inl (by
                        simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte,
                          actor, sent, packet, inside] using completed)
      · exact Or.inl (by
          simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte] using completed)

/-- A new nonexcluded assignment in the frontier has a literal original
native response prefix. The initial frontier alternative is explicit, so an
arbitrary anchor cannot silently forget an already pending assignment. -/
theorem phaseProposalEmissionFrontier_origin
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (anchorLength : Nat)
    (initialFrontier : (graph).Config) (initial : PMF (app).State)
    (horizon : Nat) (scheduler : (app).Scheduler) (query : (graph).EventId) :
    ∀ {state : (app).ProtocolState}
      (trace : ((app).protocol initial horizon scheduler).Trace state),
      query ∈ (phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength
        initialFrontier initial horizon scheduler trace).cut.completed →
      query ∈ initialFrontier.cut.completed ∨
        (∃ owner ∈ anchor.application.current.excluded, (graph).actor? query = some owner) ∨
          ∃ (before after : (app).ProtocolState)
            (prior : ((app).protocol initial horizon scheduler).Trace before)
            (joint : Player → Option (app).Action)
            (legal : ((app).protocol initial horizon scheduler).Legal before joint)
            (realized : after ∈ (((app).protocol initial horizon scheduler).step before
              ⟨joint, legal⟩).support),
            TracePrefix (prior.extend joint legal realized) trace ∧
              anchorLength ≤ prior.length ∧
                PhaseProposalBindingEmissionAt setup mode runtime leaks anchor before joint query
  | _, .start, completed => Or.inl completed
  | _, .extend prior joint legal realized, completed => by
      have extendOrigin :
          (query ∈ initialFrontier.cut.completed ∨
            (∃ owner ∈ anchor.application.current.excluded,
              (graph).actor? query = some owner) ∨
              ∃ (before after : (app).ProtocolState)
                (first : ((app).protocol initial horizon scheduler).Trace before)
                (selected : Player → Option (app).Action)
                (allowed : ((app).protocol initial horizon scheduler).Legal before selected)
                (supported : after ∈ (((app).protocol initial horizon scheduler).step before
                  ⟨selected, allowed⟩).support),
                TracePrefix (first.extend selected allowed supported) prior ∧
                  anchorLength ≤ first.length ∧
                    PhaseProposalBindingEmissionAt setup mode runtime leaks anchor before selected
                      query) →
          query ∈ initialFrontier.cut.completed ∨
            (∃ owner ∈ anchor.application.current.excluded,
              (graph).actor? query = some owner) ∨
              ∃ (before after : (app).ProtocolState)
                (first : ((app).protocol initial horizon scheduler).Trace before)
                (selected : Player → Option (app).Action)
                (allowed : ((app).protocol initial horizon scheduler).Legal before selected)
                (supported : after ∈ (((app).protocol initial horizon scheduler).step before
                  ⟨selected, allowed⟩).support),
                TracePrefix (first.extend selected allowed supported)
                    (prior.extend joint legal realized) ∧
                  anchorLength ≤ first.length ∧
                    PhaseProposalBindingEmissionAt setup mode runtime leaks anchor before selected
                      query := by
        rintro (old | automatic | ⟨before, after, first, selected, allowed, supported, kept,
          later, emitted⟩)
        · exact Or.inl old
        · exact Or.inr (Or.inl automatic)
        · exact Or.inr (Or.inr ⟨before, after, first, selected, allowed, supported,
            .extend kept joint legal realized, later, emitted⟩)
      by_cases later : anchorLength ≤ prior.length
      · rw [phaseProposalEmissionFrontier, ite_eq_left later] at completed
        rcases phaseProposalBindingFrontierAdvance_origin setup mode runtime leaks anchor phase
            _ _ joint query completed with old | automatic | emitted
        · exact extendOrigin (phaseProposalEmissionFrontier_origin anchor phase anchorLength
            initialFrontier initial horizon scheduler query prior old)
        · exact Or.inr (Or.inl automatic)
        · exact Or.inr (Or.inr ⟨_, _, prior, joint, legal, realized, .refl, later, emitted⟩)
      · rw [phaseProposalEmissionFrontier, ite_eq_right later] at completed
        exact extendOrigin (phaseProposalEmissionFrontier_origin anchor phase anchorLength
          initialFrontier initial horizon scheduler query prior completed)

/-- A retained original SEND prefix supplies an actual immutable signed input
at the endpoint. This joins the ghost's inverse witness to the real network;
no admission or counterfactual input support is postulated. -/
theorem phaseProposalBindingEmissionAt_input
    (anchor : (app).Execution) (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) {before after : (app).ProtocolState}
    (prior : ((app).protocol initial horizon scheduler).Trace before)
    (joint : Player → Option (app).Action)
    (legal : ((app).protocol initial horizon scheduler).Legal before joint)
    (realized : after ∈ (((app).protocol initial horizon scheduler).step before
      ⟨joint, legal⟩).support)
    (control : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (kept : TracePrefix (prior.extend joint legal realized) trace)
    (event : (graph).EventId)
    (emitted : PhaseProposalBindingEmissionAt setup mode runtime leaks anchor before joint event) :
    ∃ message ∈ control.execution.network.inputs,
      message.payload.attempt = anchor.application.attempt ∧
      message.payload.packet.call.event? (graph) = some event ∧
      (graph).actor? event = some message.sender := by
  obtain ⟨who, actor, remaining, execution, state, attempt, response, material, candidate,
    selected, transmitted, packet⟩ := emitted
  subst before
  change after ∈ (PMF.pure (some ⟨remaining, none,
    execution.respond (app) who ((joint who).getD ⟨none⟩)⟩)).support at realized
  rw [selected, Option.getD_some] at realized
  cases (PMF.mem_support_pure_iff _ _).mp realized
  let message := (execution.network.submit who ((app).packet
    ((app).submit execution.application who material) who (execution.network.known who)
      material)).1
  have responseEq : response = ⟨some material⟩ := by
    cases response
    cases transmitted
    rfl
  have output : message ∈ (app).outputs ((execution.respond (app) who response).recall who) := by
    simp [responseEq, ReactiveApplication.Execution.respond, MessageNetwork.submit,
      ReactiveApplication.outputs, message]
  have retained := (app).reaches_recall_prefix initial horizon scheduler kept.reachesWithin
    ⟨remaining, none, execution.respond (app) who response⟩ control rfl rfl who
  have laterOutput : message ∈ (app).outputs (control.execution.recall who) := by
    obtain ⟨entry, member, emittedEq⟩ := List.mem_filterMap.mp output
    exact List.mem_filterMap.mpr ⟨entry, retained.subset member, emittedEq⟩
  have recalled := (app).history_inputRecall initial horizon scheduler trace
  rw [← recalled who] at laterOutput
  refine ⟨message, (List.mem_filter.mp laterOutput).1, ?_, ?_, actor⟩
  · exact attempt
  · change ((execution.application.submit who material).emit who
      (execution.network.known who) material).packet.call.event? (graph) = some event
    rw [phase_emit_call, packet]
    rfl

end Vegas
