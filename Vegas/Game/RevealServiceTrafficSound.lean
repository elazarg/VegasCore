/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceTraffic
import Vegas.Game.RevealServiceWatcherSupport
import Interaction.ReactiveTrafficState

/-! # Sound traffic audits on every retained native history

Canonical openings and published replay aliases satisfy the public checker.
The retained watcher is silent, and service commands emit no traffic. The
result applies to every legal prefix, independently of policies or utilities.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

omit [Fintype Player] in
private theorem prefix_current_service (initial : State L setup.context) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graph setup).layout Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event))
      (offset count : Nat) (source : ProtocolState program)
      (execution : (application setup leaks).Execution),
      PrefixCheckpoint setup leaks initial program refs revelations outputs
        offset count source execution →
      ∀ event : (graph setup).EventId, event.val = offset + count →
      ((graph setup).actor? event).isSome = true →
      execution.application.config.cut.Ready event ∧
        execution.application.WithinDeadline (runtime setup) event := by
  intro Γ openNames program refs revelations outputs offset count
  induction count generalizing Γ openNames program refs revelations outputs offset with
  | zero =>
      intro source execution related event rank strategic
      simp only [Nat.add_zero] at rank
      have fromCheckpoint {Γ : SourceCtx Player L} (source : Config Player L Γ)
          (refs : ContextRefs (graph setup).layout Γ)
          (checkpoint : Checkpoint setup leaks initial source refs offset execution) :
          execution.application.config.cut.Ready event ∧
            execution.application.WithinDeadline (runtime setup) event := by
        have inside : offset < (graph setup).order.eventCount := rank ▸ event.isLt
        have same : (⟨offset, inside⟩ : (graph setup).EventId) = event := Fin.ext rank.symm
        exact ⟨same ▸ checkpoint.ordered.ready inside, checkpoint.timely event rank strategic⟩
      cases program <;>
        obtain ⟨source, _state, _revelations, checkpoint⟩ := related <;>
        exact fromCheckpoint source _ checkpoint
  | succ count ih =>
      intro source execution related event rank strategic
      cases program with
      | ret payoffs => exact related.elim
      | sample name fresh law next => exact related.elim
      | commit name owner fresh guard next => exact related.elim
      | reveal published owner name fresh selected unresolved next =>
          cases source with
          | inl source => exact related.elim
          | inr source =>
              exact ih next _ _ _ (offset + 1) source execution related event (by omega) strategic

theorem retained_owner_response_traffic (bounds : MessageBounds (graph setup))
    (watcher who : Player) (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (ordinary : who ≠ watcher) (history : (protocol setup leaks bounds watcher).History)
    (control : (application setup leaks).Control) (state : history.state = some control)
    (active : control.actor = some who) (response : (application setup leaks).Action)
    (allowed : response ∈ ordinaryActions setup leaks bounds who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)) :
    ∀ record ∈ (application setup leaks).trafficStep (some control)
      (some ⟨control.remaining, none,
        control.execution.respond (application setup leaks) who response⟩),
      permittedTraffic setup leaks watcher record = true := by
  let responses := menu setup leaks bounds watcher
  let reference := responses.uniformPolicy (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)
  have acts : (protocol setup leaks bounds watcher).active history.state who := by
    change (application setup leaks).actor history.state = some who
    rw [state]
    exact active
  obtain ⟨event, owned, _depth, supported⟩ := owner_history_supported setup leaks bounds
    watcher who reveals ordinary history acts
  obtain ⟨boundary, _boundarySupport, stateEq, initial, _initialSupport, source,
      _before, related, _decoded⟩ := owner_supported setup leaks bounds watcher who reveals
        observer openable reference event owned history supported
  have same := Option.some.inj (state.symm.trans stateEq)
  subst control
  let execution := ownerOpportunity setup leaks event who boundary
  have recalled : execution.InputRecall (application setup leaks) :=
    PrefixCheckpoint.runtime_fact (fun next => next.InputRecall (application setup leaks))
      (fun _ _ _ _ checkpoint => checkpoint.recall) _ _ _ _ _ _ _ _ related
  have binding : execution.application.BindingInvariant :=
    PrefixCheckpoint.runtime_fact (fun next => next.application.BindingInvariant)
      (fun _ _ _ _ checkpoint => checkpoint.binding) _ _ _ _ _ _ _ _ related
  have strategic : ((graph setup).actor? event).isSome = true := by rw [owned]; rfl
  have service := prefix_current_service setup leaks initial _ _ _ _ 0 event.val source
    execution related event (by omega) strategic
  apply ordinary_response_traffic setup leaks bounds execution watcher who ordinary _
    recalled binding ?_ ?_ response allowed
  · intro other granted
    have equal : event = other := Option.some.inj granted
    exact equal ▸ service.1
  · intro other granted
    have equal : event = other := Option.some.inj granted
    exact equal ▸ service.2

/-- Every actual retained transition emits only permitted traffic. -/
theorem retained_step_traffic (bounds : MessageBounds (graph setup))
    (watcher : Player) (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (history : (protocol setup leaks bounds watcher).History)
    (joint : Player → Option (application setup leaks).Action)
    (legal : (protocol setup leaks bounds watcher).Legal history.state joint)
    (next : (application setup leaks).ProtocolState)
    (reached : next ∈ ((protocol setup leaks bounds watcher).step history.state
      ⟨joint, legal⟩).support) :
    ∀ record ∈ (application setup leaks).trafficStep history.state next,
      permittedTraffic setup leaks watcher record = true := by
  let app := application setup leaks
  change next ∈ (app.transition (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) history.state joint).support at reached
  cases state : history.state with
  | none => simp only [ReactiveApplication.trafficStep, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  | some control =>
      rw [state] at reached
      cases actor : control.actor with
      | some who =>
          have chosen := legal.2 who
          rw [state] at chosen
          cases selected : joint who with
          | none =>
              rw [selected] at chosen
              exact (chosen actor).elim
          | some response =>
              rw [selected] at chosen
              have allowed := chosen.2
              change response ∈ (menu setup leaks bounds watcher).actions who
                (control.execution.recall who) (control.execution.observe app who) at allowed
              simp only [ReactiveApplication.transition, actor, selected,
                Option.getD_some, PMF.mem_support_pure_iff _ _] at reached
              subst next
              by_cases same : who = watcher
              · subst who
                have quiet := watcher_history_silent setup leaks bounds watcher reveals
                  observer openable history control state actor
                simp only [menu, ↓reduceIte, Set.Finite.mem_toFinset] at allowed
                rw [quiet, PMF.mem_support_pure_iff _ _] at allowed
                subst response
                cases control with
                | mk remaining owner execution =>
                    simp only at actor
                    subst owner
                    dsimp only [app]
                    simp only [ReactiveApplication.trafficStep_silent, List.not_mem_nil,
                      IsEmpty.forall_iff, implies_true]
              · have ordinary : response ∈ ordinaryActions setup leaks bounds who
                    (control.execution.recall who) (control.execution.observe app who) := by
                  simpa only [menu, same, ↓reduceIte] using allowed
                exact retained_owner_response_traffic setup leaks bounds watcher who reveals
                  observer
                  openable same history control state actor response ordinary
      | none =>
          cases countEq : control.remaining with
          | zero =>
              apply (legal.1 _).elim
              rw [state]
              exact ⟨countEq, actor⟩
          | succ remaining =>
              simp only [ReactiveApplication.transition, actor, countEq,
                PMF.support_bind] at reached
              obtain ⟨command, _selected, moved⟩ := Set.mem_iUnion₂.mp reached
              obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
              have noneTraffic := app.trafficStep_environment control.execution updated command
                supported remaining
              cases control with
              | mk count owner execution =>
                  simp only at actor countEq
                  subst count owner
                  rw [noneTraffic]
                  simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]

/-- The complete actual audit is conforming at every retained prefix. -/
theorem retained_history_traffic (bounds : MessageBounds (graph setup))
    (watcher : Player) (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (history : (protocol setup leaks bounds watcher).History) :
    ∀ record ∈ (application setup leaks).stateTraffic history.state,
      permittedTraffic setup leaks watcher record = true := by
  let responses := menu setup leaks bounds watcher
  rw [← responses.trafficAudit_eq_stateTraffic (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher) history]
  rcases history with ⟨state, trace⟩
  induction trace with
  | start => simp only [ReactiveApplication.ResponseMenu.trafficAudit,
      ReactiveApplication.ResponseMenu.toRawTrace, ReactiveApplication.trafficAudit,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | @extend source target prior joint legal realized ih =>
      change ∀ record ∈ responses.trafficAudit (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) ⟨source, prior⟩ ++
          (application setup leaks).trafficStep source target, _
      intro record member
      rcases List.mem_append.mp member with previous | added
      · exact ih record previous
      · exact retained_step_traffic setup leaks bounds watcher reveals observer openable
          ⟨source, prior⟩ joint legal target realized record added

/-- A sound partial audit cannot charge any player on any retained prefix. -/
theorem retained_traffic_clear (bounds : MessageBounds (graph setup))
    (watcher : Player) (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (history : (protocol setup leaks bounds watcher).History) (who : Player)
    (records : List (application setup leaks).TrafficRecord)
    (authentic : records ⊆ (application setup leaks).stateTraffic history.state) :
    (application setup leaks).trafficViolation (permittedTraffic setup leaks watcher)
      who records = false := by
  apply (application setup leaks).trafficViolation_clear
  intro record member _owner
  exact retained_history_traffic setup leaks bounds watcher reveals observer openable
    history record (authentic member)

end Vegas
