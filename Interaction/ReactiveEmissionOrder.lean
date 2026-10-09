/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSubmissionSerial

/-! # Envelope identifiers retain the order of actual own emissions

The sequence of identifiers in a player's remembered emitted packets is
exactly the allocated serial interval. Environment commands and silent
responses do not affect that sequence. No payload or conformance restriction
is imposed.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def Execution.EmissionOrder (execution : app.Execution) : Prop :=
  ∀ who, (app.outputs (execution.recall who)).map Message.id =
    (List.range (execution.network.nextSerial who)).map fun serial => (who, serial)

omit [DecidableEq Principal] in
theorem initial_emissionOrder (state : app.State) :
    (Execution.initial app state).EmissionOrder app := fun _ => rfl

theorem respond_emissionOrder (execution : app.Execution) (who : Principal)
    (action : app.Action) (valid : execution.EmissionOrder app) :
    (execution.respond app who action).EmissionOrder app := by
  intro observer
  have prior := valid observer
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      by_cases same : observer = who
      · subst observer
        simpa [Execution.respond, outputs] using prior
      · simpa [Execution.respond, same] using prior
  | some submission =>
      by_cases same : observer = who
      · subst observer
        simpa [Execution.respond, MessageNetwork.submit, outputs, List.range_succ]
          using congrArg (fun ids => ids ++ [(who, execution.network.nextSerial who)])
            prior
      · simpa [Execution.respond, MessageNetwork.submit, same] using prior

theorem environment_emissionOrder (execution next : app.Execution) (command : app.Command)
    (valid : execution.EmissionOrder app)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.EmissionOrder app := by
  intro who
  rw [app.environmentStep_recall execution next command reached,
    app.environmentStep_nextSerial execution next command reached]
  exact valid who

theorem emissionOrderInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (fun execution => execution.EmissionOrder app) where
  respond := app.respond_emissionOrder
  environment execution next command valid _ reached :=
    app.environment_emissionOrder execution next command valid reached

theorem emissionOrder_history (scheduler : app.Scheduler) (initial : PMF app.State)
    (horizon : Nat) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.EmissionOrder app) state :=
  (app.emissionOrderInvariant scheduler).history initial horizon
    (fun state _ => app.initial_emissionOrder state) trace

omit [DecidableEq Principal] in
/-- A packet's serial counts the remembered packets emitted before it,
including every malformed submission. -/
theorem emitted_serial_of_recall_split (execution : app.Execution)
    (valid : execution.EmissionOrder app) (who : Principal)
    (before after : List app.PlayerEntry) (entry : app.PlayerEntry)
    (recalled : execution.recall who = before ++ entry :: after)
    (message : Message Principal app.Payload) (emitted : entry.emitted = some message) :
    message.id = (who, (app.outputs before).length) := by
  have identifiers := valid who
  rw [recalled] at identifiers
  have lengths := congrArg List.length identifiers
  simp only [outputs, List.filterMap_append, List.filterMap_cons, emitted,
    List.length_map, List.length_append, List.length_cons, List.length_range] at lengths
  have selected := congrArg (fun ids => ids[(app.outputs before).length]?) identifiers
  simp only [outputs, List.filterMap_append, List.filterMap_cons, emitted,
    List.map_append, List.map_cons] at selected
  rw [List.getElem?_append_right (by simp), List.length_map, Nat.sub_self] at selected
  simp only [List.getElem?_cons_zero, List.getElem?_map] at selected
  rw [List.getElem?_range (by omega), Option.map_some] at selected
  exact Option.some.inj selected

omit [DecidableEq Principal] in
/-- Serial zero identifies the first actual emitted packet, rather than a
later retry after an unobserved malformed submission. -/
theorem emitted_zero_has_no_prior_outputs (execution : app.Execution)
    (valid : execution.EmissionOrder app) (who : Principal)
    (before after : List app.PlayerEntry) (entry : app.PlayerEntry)
    (recalled : execution.recall who = before ++ entry :: after)
    (message : Message Principal app.Payload) (emitted : entry.emitted = some message)
    (identified : message.id = (who, 0)) : app.outputs before = [] := by
  have serial := app.emitted_serial_of_recall_split execution valid who
    before after entry recalled message emitted
  rw [identified] at serial
  exact List.eq_nil_of_length_eq_zero (Prod.mk.inj serial).2.symm

end Interaction.ReactiveApplication
