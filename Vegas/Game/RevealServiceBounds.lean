/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService
import Vegas.Pending.ReactiveInitialValues

/-! # Finite alphabet coverage at initialized reveal checkpoints

The finite alphabet is extended using the actual source setup law. If a
checkpoint retains its initial accepted handles and candidate meanings, every
authentic opening found there belongs to that alphabet. This discharges local
response availability without making an infinite source value type finite or
discarding any previously admitted raw traffic.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The backend alphabet is chosen from the setup distribution before a source
equilibrium is selected. Preserving the initial tables suffices for coverage of
every authentic local opening, including normalized forwarding aliases. -/
theorem opening_available_of_initial_tables (bounds : MessageBounds (graph setup))
    (initial : State L setup.context) (supported : initial ∈ setup.initialLaw.support)
    (execution : (application setup leaks).Execution)
    (accepted : execution.application.accepted =
      (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted)
    (candidates : execution.application.candidates =
      (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs initial)).candidates)
    (field : (graph setup).Field) (candidate : Handle (graph setup))
    (associated : execution.application.accepted field = some candidate)
    (who : Player) (owned : candidate.1 = who) (raw : Raw L)
    (fixed : execution.application.candidates.lookup candidate = .openable raw)
    (event : (graph setup).EventId) :
    ((runtime setup).reactiveNormalization leaks).action who (execution.recall who)
        (execution.observe (application setup leaks) who)
        ((runtime setup).canonicalRevealResponse leaks event candidate raw true) ∈
      ((bounds.withInitialValues (initialLaw setup)).menu (runtime setup) leaks).actions who
        (execution.recall who) (execution.observe (application setup leaks) who) := by
  rw [accepted] at associated
  obtain ⟨input, owner, _payload, _field, _typed, same⟩ :=
    EventGraphRuntime.State.initial_accepted_eq_some (graph := graph setup)
      (setup.eventInputs initial) field candidate associated
  have ownerEq : owner = who := by simpa only [same] using owned
  subst owner
  rw [same, candidates] at fixed
  have initialized : EventGraphRuntime.State.initial (graph := graph setup)
      (setup.eventInputs initial) ∈
      (initialLaw setup).support := by
    rw [initialLaw, PMF.support_map]
    exact ⟨initial, supported, rfl⟩
  rw [same]
  exact bounds.initialized_opening_available (initialLaw setup)
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial))
    initialized who input raw fixed
    (runtime setup) leaks (execution.recall who)
    (execution.observe (application setup leaks) who) event

/-- Initial handle provenance supplies both components of raw opening coverage. -/
theorem opening_data_covered (bounds : MessageBounds (graph setup))
    (initial : State L setup.context) (supported : initial ∈ setup.initialLaw.support)
    (execution : (application setup leaks).Execution)
    (accepted : execution.application.accepted =
      (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted)
    (candidates : execution.application.candidates =
      (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs initial)).candidates)
    (field : (graph setup).Field) (candidate : Handle (graph setup))
    (associated : execution.application.accepted field = some candidate) (raw : Raw L)
    (fixed : execution.application.candidates.lookup candidate = .openable raw) :
    (bounds.withInitialValues (initialLaw setup)).AllowsHandle candidate ∧
      raw ∈ (bounds.withInitialValues (initialLaw setup)).values := by
  rw [accepted] at associated
  obtain ⟨input, owner, _payload, _field, _typed, same⟩ :=
    EventGraphRuntime.State.initial_accepted_eq_some (graph := graph setup)
      (setup.eventInputs initial) field candidate associated
  rw [same, candidates] at fixed
  rw [same]
  refine ⟨True.intro, ?_⟩
  apply bounds.initial_value_covered (initialLaw setup)
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial))
      _ owner input raw fixed
  rw [initialLaw, PMF.support_map]
  exact ⟨initial, supported, rfl⟩

end Vegas
