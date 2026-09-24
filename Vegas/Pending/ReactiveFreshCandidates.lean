/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveInvariant
import Vegas.Pending.ReactivePolicy
import Vegas.Pending.EventFreshCandidates

/-! # Fresh commitment material under arbitrary reactive behavior

A finite reactive history cannot exhaust fresh candidates. In particular,
the graph-policy compiler's allocation branch succeeds at every initialized
activation. This provides material, not a guarantee of winning inclusion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveFreshInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).Invariant State.FreshCandidates where
  submit state who submission fresh := by
    apply submitStep_freshCandidates
    rw [submission.call.register_eq]
    cases submission.call.registrationCommand who with
    | none => exact fresh
    | some command => exact privateStep_freshCandidates state who command fresh
  handle state message next fresh accepted :=
    handle_freshCandidates runtime state next ⟨message.id, message.payload.call⟩ fresh accepted
  environment state command next fresh supported := by
    have tables := environmentStep_tables runtime state next command supported
    simpa only [State.FreshCandidates, State.HandleUnused, tables.1, tables.2] using fresh

theorem reactive_history_fresh (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : FinDist graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {state} (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace state) :
    ReactiveApplication.stateInvariant State.FreshCandidates state := by
  apply (runtime.reactiveFreshInvariant leaks).history (inputs.map State.initial) horizon
    scheduler _ trace
  intro state supported
  obtain ⟨input, _, rfl⟩ := FinDist.support_map .. ▸ supported
  exact State.initial_freshCandidates input

/-- Allocation uses only the owner's actual view and cannot fail because of
earlier submissions by that player or its opponents. -/
theorem reactiveFreshSlot_available (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (fresh : execution.application.FreshCandidates) :
    ∃ serial, reactiveFreshSlot
      (execution.observe (runtime.reactiveApplication leaks) who).application = some serial := by
  obtain ⟨serial, _, fresh, _⟩ := fresh.exists_prepared who 0
  unfold reactiveFreshSlot
  split
  · exact ⟨_, rfl⟩
  · rename_i impossible
    exact False.elim (impossible ⟨serial, fresh⟩)

end Vegas.EventGraphRuntime
