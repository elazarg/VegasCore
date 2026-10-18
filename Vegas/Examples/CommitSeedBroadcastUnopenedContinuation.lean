/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastRealization
import Vegas.Examples.CommitSeedBroadcastService
import Vegas.Examples.CommitSeedBroadcastPayoffs
import Vegas.Pending.PhaseCountVerdict
import Vegas.Pending.PhaseTimelyResolution
import Vegas.Pending.PhaseExpiryExclusion
import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveTrafficIdentity

/-! # Exclusion when a surviving publication is left unsubmitted -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private abbrev originalInputs : graph.Inputs :=
  encodeInputs (Env.empty (CellVal simpleExpr))

def NoOwnReveal (owner : Player) (coordinate : CommitAttemptEvent graph)
    (message : Message Player (CommitAttemptPacket graph)) : Prop :=
  message.sender = owner → PhaseCount.event? message.payload ≠ some coordinate

private theorem network_environment_safe (owner : Player) (coordinate : CommitAttemptEvent graph)
    (execution next : app.Execution) (command : app.Command)
    (safe : execution.network.Satisfies (NoOwnReveal owner coordinate))
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.network.Satisfies (NoOwnReveal owner coordinate) := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact safe
  | activate actor =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact safe.learn actor selected
  | «include» identifier =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      have kept := safe.includePending identifier
      cases found : execution.network.lookup identifier <;>
        simpa only [ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, found] using kept
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact safe

private theorem expiry_request_or_excluded
    (state next : PhaseRuntimeState graph) (owner : Player)
    (coordinate : CommitAttemptEvent graph) (valid : state.Invariant originalInputs)
    (request : state.SeedRequest owner coordinate)
    (reached : next ∈ (state.environment runtime (.expire coordinate.event)).support) :
    owner ∈ next.current.excluded ∨ next.SeedRequest owner coordinate := by
  have available := (valid.active.activated_iff coordinate.event).mpr
    ⟨request.2.2.1, by rw [request.2.2.2.1]; rfl⟩
  obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp available
  by_cases due : runtime.deadline coordinate.event ≤ state.current.native.clock - entered
  · exact Or.inl (PhaseRuntimeState.expire_excludes_of_request runtime state next owner
      coordinate request entered stamp due reached)
  · have timely : state.current.native.WithinDeadline runtime coordinate.event := by
      simpa only [State.WithinDeadline, stamp] using Nat.lt_of_not_ge due
    exact Or.inr (PhaseRuntimeState.expiry_request_before_deadline runtime state next owner
      coordinate request timely reached)

def Unopened (owner : Player) (coordinate : CommitAttemptEvent graph)
    (execution : app.Execution) : Prop :=
  execution.application.Invariant originalInputs ∧
    execution.network.Satisfies (NoOwnReveal owner coordinate) ∧
    (owner ∈ execution.application.current.excluded ∨
      execution.application.SeedRequest owner coordinate)

/-- Arbitrary foreign responses preserve a still-unsubmitted owned coordinate. -/
theorem unopened_respond_other (owner : Player) (coordinate : CommitAttemptEvent graph)
    (execution : app.Execution) (actor : Player) (action : app.Action)
    (different : actor ≠ owner) (valid : Unopened owner coordinate execution) :
    Unopened owner coordinate (execution.respond app actor action) := by
  refine ⟨(phaseApplication_invariant runtime leaks originalInputs).respond execution actor
    action valid.1, ?_, ?_⟩
  · rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact valid.2.1
    | some submission =>
        exact valid.2.1.submit actor _ (fun equal => (different equal).elim)
  · rcases valid.2.2 with excluded | requested
    · exact Or.inl ((phaseApplication_exclusion_monotone runtime leaks).respond execution
        actor action excluded)
    · exact Or.inr (respond_request runtime leaks execution actor action owner coordinate
        requested)

/-- A native environment operation either retains the unsubmitted request or
excludes its owner. This statement concerns the actual pending network. -/
theorem unopened_environment (owner : Player) (coordinate : CommitAttemptEvent graph)
    (execution next : app.Execution) (command : app.Command)
    (valid : Unopened owner coordinate execution)
    (reached : next ∈ (execution.environmentStep app command).support) :
    Unopened owner coordinate next := by
  refine ⟨(phaseApplication_invariant runtime leaks originalInputs).environmentStep execution
    next command valid.1 reached, network_environment_safe owner coordinate execution next command
      valid.2.1 reached, ?_⟩
  rcases valid.2.2 with excluded | requested
  · exact Or.inl ((phaseApplication_exclusion_monotone runtime leaks).environmentStep execution
      next command reached excluded)
  · rcases environment_request_or_own_resolution runtime leaks
      (serviceGraph_revealRelaxedOrdered setup .concurrentReveals) execution next valid.1
        owner coordinate requested command reached with retained | expiry | included
    · exact Or.inr retained
    · rw [expiry] at reached
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
      obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact expiry_request_or_excluded execution.application state owner coordinate
        valid.1 requested supported
    · obtain ⟨identifier, message, _native, _ready, _action, selected, lookup, sender,
        named, _handled, _step, _normalized⟩ := included
      by_cases sameAttempt : message.payload.attempt = coordinate.attempt
      · have addressed : PhaseCount.event? message.payload = some coordinate := by
          simp only [PhaseCount.event?, named, Option.map_some, sameAttempt]
        exact ((valid.2.1.lookup identifier message lookup) sender addressed).elim
      · have rejected : app.handle execution.application message = none :=
          PhaseRuntimeState.handle_retired runtime execution.application message
            (fun equal => sameAttempt (equal.trans requested.1.symm))
        have unchanged : next.application = execution.application := by
          rw [selected] at reached
          simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
          cases (PMF.mem_support_pure_iff _ _).mp reached
          simp only [ReactiveApplication.Execution.includePending,
            MessageNetwork.includePending, lookup, rejected, Option.getD_none]
        exact Or.inr (by rwa [unchanged])

private theorem unopened_policyInvariant (players : Player → app.Policy) (owner : Player)
    (coordinate : CommitAttemptEvent graph)
    (silent : players owner = app.silentPolicy) :
    app.PolicyInvariant players (Unopened owner coordinate) where
  respond execution actor action valid supported := by
    by_cases same : actor = owner
    · subst actor
      rw [silent] at supported
      cases app.mem_silentPolicy_support.mp supported
      exact valid
    · exact unopened_respond_other owner coordinate execution actor action same valid
  environment execution next command valid reached :=
    unopened_environment owner coordinate execution next command valid reached

/-- A genuine surviving ready publication which has never been submitted
cannot be rescued by arbitrary foreign raw traffic after its owner stays
silent. The original horizon completes it and therefore excludes the owner. -/
theorem silent_unsubmitted_publication_excluded
    (players : Player → app.Policy) (remaining : Nat) (before after : app.Execution)
    (trace : (app.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, before⟩))
    (owner : Player) (silent : players owner = app.silentPolicy)
    (request : before.application.SeedRequest owner
      ⟨before.application.attempt, revealEvent owner⟩)
    (unsubmitted : ∀ message ∈ before.network.inputs, message.sender = owner →
      PhaseCount.event? message.payload ≠
        some ⟨before.application.attempt, revealEvent owner⟩)
    (supported : after ∈ (app.runRounds scheduler players remaining before).support) :
    owner ∈ after.application.current.excluded := by
  have retained := app.retained_envelopes_mem_inputs before
    (app.history_provenance initial horizon scheduler trace)
    (app.history_inputRecall initial horizon scheduler trace)
  have safe : before.network.Satisfies
      (NoOwnReveal owner ⟨before.application.attempt, revealEvent owner⟩) :=
    retained.mono (fun message member => unsubmitted message member)
  have valid := raw_native_valid scheduler ⟨remaining, none, before⟩ trace
  have final := (unopened_policyInvariant players owner
    ⟨before.application.attempt, revealEvent owner⟩ silent).runRounds scheduler remaining
      before after ⟨valid, safe, Or.inr request⟩ supported
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial horizon scheduler players 0 remaining
    before after (by simpa only [Nat.zero_add] using trace) supported
  have complete := scheduler_completesPlay ⟨0, none, after⟩ finalTrace ⟨rfl, rfl⟩
  rcases final.2.2 with excluded | stillReady
  · exact excluded
  · exfalso
    apply stillReady.2.2.1.1
    rw [complete]
    exact Finset.mem_univ _

end Vegas.Examples.CommitSeedBroadcast
