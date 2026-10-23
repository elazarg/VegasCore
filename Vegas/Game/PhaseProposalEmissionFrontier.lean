/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalBindingEmission

/-! # Retain actual binding emissions along the original native history

This is a deterministic readout of the existing actual trace, not a new play
runner. The initial frontier is supplied literally, so an arbitrary anchor
cannot replace an already emitted pending value by a new source draw.
-/

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

/-- Close only the original interval's already excluded logical coordinates.
The native metadata here is not a counterfactual runtime execution; the
automatic operation uses its literal graph action and the fixed entry E. -/
def phaseProposalBindingFrontierDrain (anchor : (app).Execution)
    (phase : RuntimePhase (graph)) (frontier : (graph).Config) : (graph).Config :=
  (phase.drain
    (⟨{ anchor.application.current.native with config := frontier },
      anchor.application.current.excluded⟩ : RecoveryState (graph))).native.config

/-- The existing excluded closure retains every literal earlier emitted value. -/
theorem phaseProposalBindingFrontierDrain_preserves
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (frontier : (graph).Config)
    (field : (graph).Field) (value : ((graph).layout field).Value)
    (stored : frontier.store field = some value) :
    (phaseProposalBindingFrontierDrain setup mode runtime leaks anchor phase frontier).store field =
      some value :=
  phase.drain_keepsStore
    (⟨{ anchor.application.current.native with config := frontier },
      anchor.application.current.excluded⟩ : RecoveryState (graph)) field value stored

/-- Add exactly the prepared action carried by this actual response. All
environment microsteps, WAITs, other namespaces and nonbinding traffic leave
the emitted assignment fixed. Readiness is totalized only outside the genuine
frontier invariant; no graph action is sampled by this map. -/
def phaseProposalBindingFrontierAdvance (anchor : (app).Execution)
    (phase : RuntimePhase (graph)) (frontier : (graph).Config)
    (before : (app).ProtocolState) (joint : Player → Option (app).Action) : (graph).Config :=
  match before with
  | none => frontier
  | some control =>
      if control.execution.application.attempt = anchor.application.attempt then
        match control.actor with
        | none => frontier
        | some who =>
            let response := (joint who).getD ⟨none⟩
            match response.transmission with
            | none => frontier
            | some material =>
                match material.call.packet with
                | .commitment event _ =>
                    if event ∈ phase.events then
                      match nodeView (graph) event with
                      | .bind owner payload binding _code =>
                          if owner = who then
                            if ready : frontier.cut.Ready event then
                              let result :=
                                ((response.transmission.bind PhaseProposal.bindingPreparation).bind
                                  (fun raw => raw.as? payload)).elim PublicationResult.failure
                                    PublicationResult.success
                              let next := frontier.complete event ready
                                (cast (congrArg EventField.Action binding.symm) result)
                                (cast (congrArg EventField.Value binding.symm) result)
                              phaseProposalBindingFrontierDrain setup mode runtime leaks anchor
                                phase next
                            else frontier
                          else frontier
                      | .resolve .. | .sample .. => frontier
                    else frontier
                | .opening .. | .malformed .. => frontier
      else frontier

/-- Every actual-history update only retains additional binding assignments.
It cannot rewrite an earlier pending value, even at a totalized raw history. -/
theorem phaseProposalBindingFrontierAdvance_preserves
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (frontier : (graph).Config)
    (before : (app).ProtocolState) (joint : Player → Option (app).Action)
    (field : (graph).Field) (value : ((graph).layout field).Value)
    (stored : frontier.store field = some value) :
    (phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor phase frontier before
      joint).store field = some value := by
  cases before with
  | none => exact stored
  | some control =>
      by_cases attempted : control.execution.application.attempt = anchor.application.attempt
      · cases actor : control.actor with
        | none => simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte, actor]
            using stored
        | some who =>
            cases sent : ((joint who).getD ⟨none⟩).transmission with
            | none => simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte,
                actor, sent] using stored
            | some material =>
                cases packet : material.call.packet with
                | opening => simpa only [phaseProposalBindingFrontierAdvance, attempted,
                    ↓reduceIte, actor, sent, packet] using stored
                | malformed => simpa only [phaseProposalBindingFrontierAdvance, attempted,
                    ↓reduceIte, actor, sent, packet] using stored
                | commitment event candidate =>
                    by_cases inside : event ∈ phase.events
                    · cases node : nodeView (graph) event with
                      | bind owner payload binding code =>
                          by_cases same : owner = who
                          · by_cases ready : frontier.cut.Ready event
                            · simpa only [phaseProposalBindingFrontierAdvance, attempted,
                                ↓reduceIte, actor, sent, packet, inside, node, same, ready,
                                dite_true, dite_false] using
                                (phaseProposalBindingFrontierDrain_preserves setup mode runtime
                                  leaks anchor phase (frontier.complete event ready _ _) field
                                    value (frontier.complete_store_of_some _ _ _ _ field value
                                      stored))
                            · simpa only [phaseProposalBindingFrontierAdvance, attempted,
                                ↓reduceIte, actor, sent, packet, inside, node, same, ready,
                                dite_true, dite_false]
                                  using stored
                          · simpa only [phaseProposalBindingFrontierAdvance, attempted,
                              ↓reduceIte, actor, sent, packet, inside, node, same] using stored
                      | resolve => simpa only [phaseProposalBindingFrontierAdvance, attempted,
                          ↓reduceIte, actor, sent, packet, inside, node] using stored
                      | sample => simpa only [phaseProposalBindingFrontierAdvance, attempted,
                          ↓reduceIte, actor, sent, packet, inside, node] using stored
                    · simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte,
                        actor, sent, packet, inside] using stored
      · simpa only [phaseProposalBindingFrontierAdvance, attempted, ↓reduceIte] using stored

/-- The original actual chronological trace determines its emitted ideal.
Only events after the supplied anchor prefix are interpreted. The SAME actual
joint response, native source control and chance-selected trace are retained. -/
def phaseProposalEmissionFrontier (anchor : (app).Execution)
    (phase : RuntimePhase (graph)) (anchorLength : Nat) (initialFrontier : (graph).Config)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler) :
    {state : (app).ProtocolState} → ((app).protocol initial horizon scheduler).Trace state →
      (graph).Config
  | _, .start => initialFrontier
  | _, @GameTheory.Protocol.ExecutionProtocol.Trace.extend _ _ before _ prior joint _ _ =>
      let frontier := phaseProposalEmissionFrontier anchor phase anchorLength initialFrontier
        initial horizon scheduler prior
      if anchorLength ≤ prior.length then
        phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor phase frontier before
          joint
      else frontier

/-- The old source/traffic prefix is never replayed with invented choices. -/
theorem phaseProposalEmissionFrontier_before_anchor
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (anchorLength : Nat)
    (initialFrontier : (graph).Config) (initial : PMF (app).State)
    (horizon : Nat) (scheduler : (app).Scheduler) :
    ∀ {state : (app).ProtocolState}
      (trace : ((app).protocol initial horizon scheduler).Trace state),
      trace.length ≤ anchorLength →
      phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength
        initialFrontier initial horizon scheduler trace = initialFrontier
  | _, .start, _earlier => rfl
  | _, .extend prior joint legal supported, earlier => by
      have priorBound : prior.length ≤ anchorLength := by
        simp only [ExecutionProtocol.Trace.length] at earlier
        omega
      have notLater : ¬ anchorLength ≤ prior.length := by
        simp only [ExecutionProtocol.Trace.length] at earlier
        omega
      simp only [phaseProposalEmissionFrontier, ite_eq_right notLater]
      exact phaseProposalEmissionFrontier_before_anchor anchor phase anchorLength initialFrontier
        initial horizon scheduler prior priorBound

/-- Actual environment service does not resample any pending source value. -/
theorem phaseProposalBindingFrontierAdvance_idle
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (frontier : (graph).Config)
    (remaining : Nat) (execution : (app).Execution)
    (joint : Player → Option (app).Action) :
    phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor phase frontier
      (some ⟨remaining, none, execution⟩) joint = frontier := by
  simp only [phaseProposalBindingFrontierAdvance]
  split <;> rfl

/-- The frontier update retains the literal material of this actual binding
response before any physical inclusion. The candidate name and private alias
remain in the original trace; only their already prepared typed graph value
is added to the semantic frontier. -/
theorem phaseProposalBindingFrontierAdvance_binding
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (frontier : (graph).Config)
    (remaining : Nat) (who : Player) (execution : (app).Execution)
    (joint : Player → Option (app).Action) (response : (app).Action)
    (selected : joint who = some response)
    (material : WitnessedSubmission (graph)) (transmitted : response.transmission = some material)
    (event : (graph).EventId) (candidate : Handle (graph))
    (packet : material.call.packet = .commitment event candidate)
    (payload : L.Ty) (binding : (graph).outputLayout event = .binding who payload)
    (code : cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) =
      .bind who payload)
    (attempt : execution.application.attempt = anchor.application.attempt)
    (inside : event ∈ phase.events) (ready : frontier.cut.Ready event) :
    phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor phase frontier
        (some ⟨remaining, some who, execution⟩) joint =
      phaseProposalBindingFrontierDrain setup mode runtime leaks anchor phase
        (frontier.complete event ready
          (phaseProposalPreparedBindingAction setup mode runtime leaks event who payload binding
            response)
          (cast (congrArg EventField.Value binding.symm)
            (((response.transmission.bind PhaseProposal.bindingPreparation).bind
              (fun raw => raw.as? payload)).elim PublicationResult.failure
                PublicationResult.success))) := by
  simp only [phaseProposalBindingFrontierAdvance, attempt, ↓reduceIte, selected, Option.getD_some,
    transmitted, packet, inside, nodeView_eq_bind binding code, ready,
    phaseProposalPreparedBindingAction]
  rw [dite_eq_left True.intro]

/-- The emitted binding update is exactly one deterministic instance of the
existing graph evaluator, even before its physical packet is admitted. -/
theorem phaseProposalPreparedBindingAction_step
    (frontier : (graph).Config) (event : (graph).EventId) (who : Player) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (code : cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) =
      .bind who payload)
    (response : (app).Action) (ready : frontier.cut.Ready event) :
    frontier.step event ready
        (phaseProposalPreparedBindingAction setup mode runtime leaks event who payload binding
          response) =
      PMF.pure (frontier.complete event ready
        (phaseProposalPreparedBindingAction setup mode runtime leaks event who payload binding
          response)
        (cast (congrArg EventField.Value binding.symm)
          (((response.transmission.bind PhaseProposal.bindingPreparation).bind
            (fun raw => raw.as? payload)).elim PublicationResult.failure
              PublicationResult.success))) := by
  unfold phaseProposalPreparedBindingAction
  rw [frontier.step_eq_map_of_code event ready binding (.bind who payload) code _
    (PMF.pure _) rfl, PMF.pure_map]

/-- The SAME actual trace prefix carries every emitted assignment to every
later prefix. No history support is reconditioned, and no hidden value is
chosen again when its packet is eventually delivered. -/
theorem phaseProposalEmissionFrontier_prefix_preserves
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (anchorLength : Nat)
    (initialFrontier : (graph).Config) (initial : PMF (app).State)
    (horizon : Nat) (scheduler : (app).Scheduler)
    {before : (app).ProtocolState}
    {prior : ((app).protocol initial horizon scheduler).Trace before}
    (field : (graph).Field) (value : ((graph).layout field).Value)
    (stored : (phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength
      initialFrontier initial horizon scheduler prior).store field = some value) :
    ∀ {after : (app).ProtocolState}
      {trace : ((app).protocol initial horizon scheduler).Trace after},
      TracePrefix prior trace →
      (phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength
        initialFrontier initial horizon scheduler trace).store field = some value
  | _, _, .refl => stored
  | _, _, .extend earlier joint legal supported => by
      have ih := phaseProposalEmissionFrontier_prefix_preserves anchor phase anchorLength
        initialFrontier initial horizon scheduler field value stored earlier
      rw [phaseProposalEmissionFrontier]
      split
      · exact phaseProposalBindingFrontierAdvance_preserves setup mode runtime leaks anchor phase
          _ _ joint field value ih
      · exact ih

/-- The prepared value of an actual SEND is retained by every later prefix of
that SAME native trace. Delivery, waiting, and later emissions cannot replace
this ghost assignment or redraw its typed value. -/
theorem phaseProposalEmissionFrontier_binding_recorded
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (anchorLength : Nat)
    (initialFrontier : (graph).Config) (initial : PMF (app).State)
    (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (who : Player) (execution : (app).Execution)
    (prior : ((app).protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (joint : Player → Option (app).Action)
    (legal : ((app).protocol initial horizon scheduler).Legal
      (some ⟨remaining, some who, execution⟩) joint)
    (target : (app).ProtocolState)
    (realized : target ∈ (((app).protocol initial horizon scheduler).step
      (some ⟨remaining, some who, execution⟩) ⟨joint, legal⟩).support)
    (response : (app).Action) (selected : joint who = some response)
    (material : WitnessedSubmission (graph)) (transmitted : response.transmission = some material)
    (event : (graph).EventId) (candidate : Handle (graph))
    (packet : material.call.packet = .commitment event candidate)
    (payload : L.Ty) (binding : (graph).outputLayout event = .binding who payload)
    (code : cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) =
      .bind who payload)
    (attempt : execution.application.attempt = anchor.application.attempt)
    (inside : event ∈ phase.events) (later : anchorLength ≤ prior.length)
    (ready : (phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength
      initialFrontier initial horizon scheduler prior).cut.Ready event)
    {final : (app).ProtocolState}
    (trace : ((app).protocol initial horizon scheduler).Trace final)
    (kept : TracePrefix (prior.extend joint legal realized) trace) :
    (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding who payload)).get?
        (phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength
          initialFrontier initial horizon scheduler trace).store =
      some (((response.transmission.bind PhaseProposal.bindingPreparation).bind
        (fun raw => raw.as? payload)).elim PublicationResult.failure
          PublicationResult.success) := by
  let frontier := phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength
    initialFrontier initial horizon scheduler prior
  let result := (((response.transmission.bind PhaseProposal.bindingPreparation).bind
    (fun raw => raw.as? payload)).elim PublicationResult.failure PublicationResult.success)
  let value := cast (congrArg EventField.Value binding.symm) result
  have next : (phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength
      initialFrontier initial horizon scheduler (prior.extend joint legal realized)).store
        (.inr event) = some value := by
    rw [phaseProposalEmissionFrontier, ite_eq_left later]
    rw [phaseProposalBindingFrontierAdvance_binding setup mode runtime leaks anchor phase frontier
      remaining who execution joint response selected material transmitted event candidate packet
        payload binding code attempt inside ready]
    apply phaseProposalBindingFrontierDrain_preserves setup mode runtime leaks anchor phase
    exact frontier.complete_output_same event ready _ value
  have retained := phaseProposalEmissionFrontier_prefix_preserves setup mode runtime leaks
    anchor phase anchorLength initialFrontier initial horizon scheduler (.inr event) value next kept
  change cast (congrArg (fun field : EventField Player L => Option field.Value) binding)
    ((phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength
      initialFrontier initial horizon scheduler trace).store (.inr event)) = some result
  rw [retained]
  have cancel {first second : Type} (same : first = second) (item : second) :
      cast (congrArg Option same) (some (cast same.symm item)) = some item := by
    cases same
    rfl
  exact cancel (congrArg EventField.Value binding) result

/-- Restart the emitted ideal at an actual retained prefix, keeping every
already emitted value in the initial ideal of the remaining raw trace. -/
theorem phaseProposalEmissionFrontier_restart
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (anchor : (app).Execution) (phase : RuntimePhase (serviceGraph setup mode))
    (anchorLength : Nat) (first : (serviceGraph setup mode).Config)
    {before : (app).ProtocolState}
    (past : ((app).protocol initial horizon scheduler).Trace before)
    (afterAnchor : anchorLength ≤ past.length) :
    ∀ {after : (app).ProtocolState}
      (trace : ((app).protocol initial horizon scheduler).Trace after),
      TracePrefix past trace →
      phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength first
          initial horizon scheduler trace =
        phaseProposalEmissionFrontier setup mode runtime leaks anchor phase past.length
          (phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength first
            initial horizon scheduler past) initial horizon scheduler trace
  | _, _, .refl =>
      (phaseProposalEmissionFrontier_before_anchor setup mode runtime leaks anchor phase past.length
        (phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength first
          initial horizon scheduler past) initial horizon scheduler past (Nat.le_refl _)).symm
  | _, _, .extend kept joint legal realized => by
      have previous := phaseProposalEmissionFrontier_restart initial horizon scheduler anchor
        phase anchorLength first past afterAnchor _ kept
      rw [phaseProposalEmissionFrontier, phaseProposalEmissionFrontier,
        ite_eq_left (afterAnchor.trans kept.length_le), ite_eq_left kept.length_le, previous]

end Vegas
