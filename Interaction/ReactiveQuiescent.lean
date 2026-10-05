/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveApplication
import Interaction.MessagePublishedObservation

/-! # Passive observation without new pending information

An activation with no pending packets, or only already published packets, has
a deterministic effect under every observation rule. Sampling does not create
an extra private signal: only learned packets, rather than the sampled identifier
set itself, enter player views. Scheduler observations can still differ between
networks with different pending lists.
-/

namespace Interaction

open GameTheory.Math.Probability

variable {Principal Payload : Type} [DecidableEq Principal]

theorem MessageNetwork.learn_of_pending_nil
    (network : MessageNetwork Principal Payload) (who : Principal)
    (selected : Finset (MessageId Principal)) (empty : network.pending = []) :
    network.learn who selected = network := by
  apply MessageNetwork.learn_of_pending_known
  simp only [empty, List.not_mem_nil, IsEmpty.forall_iff, implies_true]

theorem ReactiveApplication.Execution.activate_of_pending_published
    (app : ReactiveApplication Principal) (execution : app.Execution) (who : Principal)
    (published : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id) :
    execution.environmentStep app (.activate who) =
      PMF.pure { execution with environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .activate who⟩] } := by
  simp only [ReactiveApplication.Execution.environmentStep,
    MessageNetwork.learn_of_pending_published _ _ _ published, PMF.map_comp, Function.comp_def]
  exact PMF.map_const _ _

theorem ReactiveApplication.Execution.activate_of_pending_nil
    (app : ReactiveApplication Principal) (execution : app.Execution) (who : Principal)
    (empty : execution.network.pending = []) :
    execution.environmentStep app (.activate who) =
      PMF.pure { execution with environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .activate who⟩] } := by
  simp only [ReactiveApplication.Execution.environmentStep,
    MessageNetwork.learn_of_pending_nil _ _ _ empty, PMF.map_comp, Function.comp_def]
  exact PMF.map_const _ _

end Interaction
