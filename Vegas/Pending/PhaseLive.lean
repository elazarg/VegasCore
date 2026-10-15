/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseReadiness

/-! # Actual normalized phases always expose live work -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- An installed descriptor always has a genuinely unfinished event. -/
def Live (state : PhaseRuntimeState graph) : Prop :=
  ∀ phase ∈ state.phases.head?, ¬ phase.Finished state.current

theorem normalize_live (state : PhaseRuntimeState graph) (frontier : state.Frontier) :
    state.normalize.Live :=
  settle_unfinished _ _ _ _ _ frontier

theorem initial_live (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).Live :=
  settle_unfinished _ _ _ _ _ (initial_checkpoint_frontier plan inputs)

theorem submit_live (state : PhaseRuntimeState graph) (live : state.Live) (who : Player)
    (submission : WitnessedSubmission graph) : (state.submit who submission).Live := by
  intro phase member
  change ¬ phase.events ⊆
    (submitStep (submission.call.register state.current.native who) who
      submission.call.packet).config.cut.completed
  rw [submitStep_config, (submission.call.register_facts who state.current.native).1]
  exact live phase member

theorem handle_live (runtime : EventGraphRuntime graph) (state next : PhaseRuntimeState graph)
    (frontier : state.Frontier) (message : Message Player (CommitAttemptPacket graph))
    (accepted : state.handle runtime message = some next) : next.Live := by
  unfold handle at accepted
  split at accepted
  · rename_i allowed
    obtain ⟨native, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
    have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
    obtain ⟨phase, member, event, named, inside⟩ := allows_event state _ authorized
    obtain ⟨actual, actualNamed, ready, action, supported⟩ :=
      handle_config_mem_step runtime state.current.native native _ rawAccepted
    have same : actual = event := Option.some.inj (actualNamed.symm.trans named)
    subst actual
    exact normalize_live _ (frontier.after_effect
      (state.current.inclusionResult message.payload.packet.call native)
      (Or.inr ⟨phase, member, event, inside, ready, action, supported⟩))
  · cases accepted

theorem environment_live (runtime : EventGraphRuntime graph) (state next : PhaseRuntimeState graph)
    (frontier : state.Frontier) (live : state.Live) (command : EnvironmentCommand graph)
    (supported : next ∈ (state.environment runtime command).support) : next.Live := by
  unfold environment at supported
  split at supported
  · rename_i allowed
    obtain ⟨native, rawSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact normalize_live _ (frontier.after_effect (state.current.environmentResult command native)
      (state.command_effect runtime command native allowed rawSupported))
  · rw [PMF.mem_support_pure_iff] at supported
    subst next
    exact live

omit [DecidableEq Player] in
/-- A nonempty live phase exposes an actual surviving owner request or its
ready singleton sample. Choosing a least unfinished rank needs no scheduling,
source-state, graph-order or maximum-delay hypothesis. -/
theorem request_or_sample (state : PhaseRuntimeState graph) (frontier : state.Frontier)
    (live : state.Live) (quiescent : ∀ event, ¬ state.current.AutomaticReady event)
    (nonempty : state.phases ≠ []) :
    (∃ owner event, state.SeedRequest owner ⟨state.attempt, event⟩) ∨
      ∃ phase event, state.phases.head? = some phase ∧ phase.kind = .sample ∧
        event.val = phase.low ∧ state.current.native.config.cut.Ready event ∧
          graph.actor? event = none := by
  classical
  cases phases : state.phases with
  | nil => exact (nonempty phases).elim
  | cons phase remaining =>
      have head : phase ∈ state.phases.head? := by
        simp only [phases, List.head?_cons, Option.mem_some_iff]
      have missing : ∃ event ∈ phase.events,
          event ∉ state.current.native.config.cut.completed := by
        by_contra absent
        apply live phase head
        intro event inside
        by_contra unfinished
        exact absent ⟨event, inside, unfinished⟩
      obtain ⟨missingEvent, inside, unfinished⟩ := missing
      obtain ⟨event, ready, before⟩ :=
        state.current.native.config.cut.exists_ready_le_of_unfinished missingEvent unfinished
      have position := frontier.positioned
      rw [phases] at position
      have lower : phase.low ≤ event.val := by
        by_contra outside
        exact ready.1 (position.2.1 event (by omega))
      have upper : event.val < phase.high :=
        before.trans_lt ((phase.mem_events missingEvent).mp inside).2
      have member := (phase.mem_events event).mpr ⟨lower, upper⟩
      cases actor : graph.actor? event with
      | some owner =>
          left
          refine ⟨owner, event, rfl, ⟨phase, head, member⟩, ready, actor, ?_⟩
          intro excluded
          apply quiescent event
          refine ⟨ready, ?_⟩
          simpa only [actor] using excluded
      | none =>
          right
          have publicOutput := EventCode.output_public_of_actor_none (graph.nodes event) actor
          have notPublication := EventCode.not_publication_of_actor_none (graph.nodes event) actor
          have typed := phase.fields event lower upper
          have kind : phase.kind = .sample := by
            cases kind : phase.kind with
            | sample => rfl
            | commitment =>
                rw [kind] at typed
                obtain ⟨owner, payload, shape⟩ := typed
                rw [shape] at publicOutput
                exact publicOutput.elim
            | reveal =>
                rw [kind] at typed
                obtain ⟨payload, shape⟩ := typed
                exact (notPublication (by rw [shape]; trivial)).elim
          refine ⟨phase, event, ?_, kind, ?_, ready, actor⟩
          · rfl
          · have singleton := phase.sample_singleton kind
            omega

end PhaseRuntimeState

theorem phaseApplication_live (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant
      (fun state => state.Frontier ∧ state.Live) where
  submit state who submission valid :=
    ⟨state.submit_frontier who submission valid.1, state.submit_live valid.2 who submission⟩
  handle state message next valid accepted :=
    ⟨state.handle_frontier runtime next message valid.1 accepted,
      state.handle_live runtime next valid.1 message accepted⟩
  environment state command next valid supported :=
    ⟨state.environment_frontier runtime next command valid.1 supported,
      state.environment_live runtime next valid.1 valid.2 command supported⟩

end Vegas.EventGraphRuntime
