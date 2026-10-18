/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingPrivateCalendar
import Vegas.Pending.PhaseBindingReceiptResolution
import Interaction.ReactiveTrafficIdentity

/-! # Actual acceptance at a first nonexpiry loss of a request -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- Without an accepting receipt after the actual command, a genuine request
can disappear only through its own expiry. This retains raw submissions and
the exact old coordinate when the command normalizes or retires the attempt. -/
theorem unaccepted_request_retained_or_expiry (seeds : Seeds) (remaining : Nat)
    (execution next : app.Execution)
    (trace : (app.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate)
    (command : app.Command) (moved : next ∈ (execution.environmentStep app command).support)
    (unaccepted : ¬ PhaseService.BindingAccepted runtime leaks coordinate owner next) :
    next.application.SeedRequest owner coordinate ∨
      command = .application (.expire coordinate.event) := by
  classical
  have valid := raw_native_valid (family seeds) _ trace
  rcases environment_request_or_own_resolution runtime leaks
      (serviceGraph_revealRelaxedOrdered setup .concurrentReveals) execution next valid owner
      coordinate request command moved with retained | expiry | included
  · exact Or.inl retained
  · exact Or.inr expiry
  · by_cases retained : next.application.SeedRequest owner coordinate
    · exact Or.inl retained
    obtain ⟨identifier, message, _native, _ready, _action, selected, found, authored, named,
      _handled, _stepped, _normalized⟩ := included
    have pending : message ∈ execution.network.pending := List.mem_of_find?_eq_some found
    have namedIdentifier := List.find?_some found
    have identifierEq : message.id = identifier := by
      change decide (message.id = identifier) = true at namedIdentifier
      exact of_decide_eq_true namedIdentifier
    have input := (app.retained_envelopes_mem_inputs execution
      (app.history_provenance initial horizon (family seeds) trace)
      (app.history_inputRecall initial horizon (family seeds) trace)).pending message pending
    rw [selected] at moved
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
    cases (PMF.mem_support_pure_iff _ _).mp moved
    cases accepted : app.handle execution.application message with
    | none =>
        have unchanged : (execution.includePending app identifier).application =
            execution.application := by
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found, accepted, Option.getD_none]
        exact (retained (unchanged.symm ▸ request)).elim
    | some target =>
        apply False.elim
        apply unaccepted
        have actual : execution.application.handle runtime message = some target := accepted
        have tag := PhaseRuntimeState.handle_attempt_eq runtime execution.application target message
          actual
        refine ⟨message, ?_, authored, tag.trans request.1.symm, named, ?_⟩
        · simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found, accepted] using input
        · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found, accepted, Option.isSome_some]
          rw [identifierEq]
          exact List.mem_append_right _ (List.mem_singleton_self _)

end Vegas.Examples.CommitSeedSignalling
