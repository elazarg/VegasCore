/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceInclusion
import Vegas.Pending.PhaseResolutionPersistence

/-! # Survival identifies the actual wait replies of timed local service rules -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Genuine tick draining cannot silently consume a rejected selected packet
in the clean game: if the selected physical request survives a nonactivation
reply, that reply was wait. Foreign and malformed raw traffic remains outside
this precise service-domain statement. -/
theorem nonactivation_wait_or_resolved (priority : RestSeed → List (app).EnvironmentEntry →
  (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (timed : DeadlineExpiry runtime decideLocal)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (remaining : Nat) (execution next : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
        ((controller runtime leaks priority decideLocal).family seeds)).Trace
        (some ⟨remaining, none, execution⟩))
    (coordinate : PhaseSeedAddress graph)
    (selected : PhaseSeedCalendar.selectedAt runtime leaks priority seeds.1 execution = some
      coordinate)
    (command : (app).Command)
    (chosen : command ∈ ((controller runtime leaks priority decideLocal).family seeds
      execution.environmentRecall (execution.observeEnvironment app)).support)
    (reached : next ∈ (execution.environmentStep app command).support)
    (idle : (command.actor? app).isNone = true) :
    command = .wait ∨ coordinate.1.Resolved next.application := by
  let scheduler := (controller runtime leaks priority decideLocal).family seeds
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨input, valid, namespaces, _⟩ :=
    currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler raw
  obtain ⟨owner, request⟩ := PhaseSeedCalendar.selected_request runtime leaks priority seeds.1
    execution valid
    coordinate selected
  have progress := (phaseApplication_namespace_progress runtime leaks).environmentStep execution
    next command reached namespaces.ordered
  have chosenEq := (PMF.mem_support_pure_iff _ _).mp chosen
  have actualReply : reply runtime leaks decideLocal coordinate (seeds.2 coordinate)
      (queryAt runtime leaks execution coordinate owner) = command :=
    (choose_of_selected runtime leaks priority decideLocal seeds execution coordinate selected owner
      request.2.2.2.1).symm.trans chosenEq.symm
  cases decided : decideLocal coordinate (seeds.2 coordinate)
      (queryAt runtime leaks execution coordinate owner) with
  | activation =>
      have commandEq : command = .activate owner := by
        simpa only [reply, decided, request.2.2.2.1, Option.map_some, Option.getD_some] using
          actualReply.symm
      rw [commandEq] at idle
      cases idle
  | wait => exact Or.inl (by simpa only [reply, decided] using actualReply.symm)
  | inclusion index =>
      cases indexed : (queryAt runtime leaks execution coordinate owner).emissions[index]? with
      | none =>
          exact Or.inl (by
            simpa only [reply, decided, indexed, Option.map_none, Option.getD_none] using
              actualReply.symm)
      | some emission =>
          have commandEq : command = .include emission.identifier := by
            simpa only [reply, decided, indexed, Option.map_some, Option.getD_some] using
              actualReply.symm
          have moved := reached
          rw [commandEq] at moved
          have included := actualReply.trans commandEq
          have resolves := inclusion_resolves_of_trace runtime leaks decideLocal timed bounds plan
            ordered
            maximal inputs horizon scheduler remaining execution next trace coordinate owner request
            (seeds.2 coordinate) emission.identifier included moved
          exact Or.inr (CommitAttemptEvent.Resolved.of_step coordinate.1 execution.application
            next.application request.1 progress resolves)
  | expiry =>
      have commandEq : command = .application (.expire coordinate.1.event) := by
        simpa only [reply, decided] using actualReply.symm
      have moved := reached
      rw [commandEq] at moved
      obtain ⟨updated, changed, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
      have due := (timed coordinate (seeds.2 coordinate)
        (queryAt runtime leaks execution coordinate owner)).mp decided
      have resolves := PhaseRuntimeState.expire_resolves_of_request runtime execution.application
        state valid namespaces.ordered request due nativeMoved
      exact Or.inr (CommitAttemptEvent.Resolved.of_step coordinate.1 execution.application
        state request.1 progress resolves)

/-- Once a physical coordinate has resolved it cannot return, even through later retries.
Thus every earlier selected nonactivation at a currently surviving coordinate was wait. -/
theorem nonactivation_wait_of_future_request (priority : RestSeed → List (app).EnvironmentEntry →
  (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (timed : DeadlineExpiry runtime decideLocal)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (remaining : Nat) (execution next : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
        ((controller runtime leaks priority decideLocal).family seeds)).Trace
        (some ⟨remaining, none, execution⟩))
    (coordinate : PhaseSeedAddress graph)
    (selected : PhaseSeedCalendar.selectedAt runtime leaks priority seeds.1 execution = some
      coordinate)
    (command : (app).Command)
    (chosen : command ∈ ((controller runtime leaks priority decideLocal).family seeds
      execution.environmentRecall (execution.observeEnvironment app)).support)
    (reached : next ∈ (execution.environmentStep app command).support)
    (futureScheduler : (app).Scheduler) (players : Player → (app).Policy)
    (count : Nat) (final : (app).Execution)
    (continued : final ∈ ((app).runRounds futureScheduler players count next).support)
    (owner : Player) (survives : final.application.SeedRequest owner coordinate.1)
    (idle : (command.actor? app).isNone = true) : command = .wait := by
  rcases nonactivation_wait_or_resolved runtime leaks priority decideLocal timed seeds bounds plan
      ordered maximal inputs horizon remaining execution next trace coordinate selected command
      chosen
      reached idle with waiting | resolved
  · exact waiting
  · let scheduler := (controller runtime leaks priority decideLocal).family seeds
    have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
    obtain ⟨input, valid, namespaces, _⟩ :=
      currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler raw
    have validNext := (phaseApplication_invariant runtime leaks input).environmentStep execution
      next command valid reached
    have orderedNext := (phaseApplication_seedOrder runtime leaks).environmentStep execution next
      command namespaces.ordered reached
    exact (CommitAttemptEvent.Resolved.no_request_runRounds runtime leaks coordinate.1
      futureScheduler players count next final validNext orderedNext resolved continued owner
      survives).elim

end Vegas.EventGraphRuntime.PhaseServiceScheduler
