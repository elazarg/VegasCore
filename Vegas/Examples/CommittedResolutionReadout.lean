/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommittedResolutionService
import Vegas.Pending.ReactiveAssociationPersistence
import Vegas.Pending.ReactiveOpeningConformance
import Vegas.EventGraph.ResolutionProvenance
import Vegas.EventGraph.PrivateInputs

/-! # Immutable truthful disclosure in the concrete service

Bob's publication refers to an initialized binding with value TRUE. Arbitrary
RAW submissions, pending messages, and scheduler choices cannot change that
meaning. These are pointwise readout facts at every legal history, including
histories of the deterministic late-recovery scheduler. They do not assert
equilibrium preservation or that Bob's publication succeeds.
-/

noncomputable section

namespace Vegas.Examples.CommittedResolutionReadout

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability
open CommittedResolutionService

abbrev bobInput : nativeGraph.InputId := ⟨1, by decide⟩
abbrev bobCandidate : Handle nativeGraph := (bob, .initial bobInput)
abbrev bobBinding : FieldRef nativeGraph.layout (.binding bob .bool) :=
  ⟨.inl bobInput, rfl⟩

private theorem supported_source_initial (initial : Vegas.State simpleExpr initialCtx)
    (supported : initial ∈ setup.initialLaw.support) :
    initial = sourceInitial true ∨ initial = sourceInitial false := by
  have selected := support_mix_subset (1 / 4) (by norm_num) (by norm_num)
    (PMF.pure (sourceInitial true)) (PMF.pure (sourceInitial false)) supported
  simpa only [PMF.mem_support_pure_iff, Set.mem_union] using selected

private theorem initial_law_eq :
    (setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)) =
      initialLaw setup := by
  rw [PMF.map_comp]
  rfl

/-- The immutable source binding is TRUE for every supported initial setup. -/
theorem bob_input_true (input : nativeGraph.Inputs)
    (supported : input ∈ (setup.initialLaw.map setup.eventInputs).support) :
    input bobInput = .success true := by
  obtain ⟨initial, selected, rfl⟩ := PMF.support_map .. ▸ supported
  rcases supported_source_initial initial selected with rfl | rfl <;> rfl

/-- Every successful Bob publication is TRUE, under any observation-local
scheduler and arbitrary RAW responses. Publication failure remains possible. -/
theorem bob_success_true (scheduler : app.Scheduler) (horizon : Nat)
    (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (value : Bool)
    (published : control.execution.application.config.store (.inr bobEvent) =
      some (.success value)) : value = true := by
  have aligned : (app.protocol
      ((setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := nativeGraph)))
        horizon scheduler).Trace (some control) := by
    rwa [initial_law_eq]
  obtain ⟨input, supported, reachable⟩ := (runtime setup).reactive_history_graph_reachable
    leaks (setup.initialLaw.map setup.eventInputs) horizon scheduler aligned
  have stored := reachable.publication_binding bobEvent bob .bool bobBinding [] rfl rfl
    value published
  have inherited : bobBinding.get? control.execution.application.config.store =
      some (.success true) := by
    change some (control.execution.application.config.inputs bobInput) = _
    rw [reachable.inputs_eq, bob_input_true input supported]
  rw [inherited] at stored
  exact PublicationResult.success.inj (Option.some.inj stored).symm

/-- The initialized Bob handle and its meaning persist at every legal history. -/
theorem bob_binding_fixed (scheduler : app.Scheduler) (horizon : Nat)
    (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control)) :
    control.execution.application.accepted bobBinding.field = some bobCandidate ∧
      control.execution.application.candidates.lookup bobCandidate =
        .openable ⟨.bool, true⟩ := by
  have associated := ((runtime setup).reactiveAssociationInvariant leaks
    bobBinding.field bobCandidate).history (initialLaw setup) horizon scheduler (by
      intro state supported
      obtain ⟨initial, _selected, rfl⟩ := PMF.support_map .. ▸ supported
      refine ⟨EventGraphRuntime.State.initial_bindingInvariant _, ?_⟩
      exact EventGraphRuntime.State.initial_accepted_binding _ bobInput bob .bool rfl) trace
  have fixed := ((runtime setup).reactiveCandidateInvariant leaks bobCandidate
    ⟨.bool, true⟩).history (initialLaw setup) horizon scheduler (by
      intro state supported
      obtain ⟨initial, selected, rfl⟩ := PMF.support_map .. ▸ supported
      rcases supported_source_initial initial selected with rfl | rfl <;>
        exact EventGraphRuntime.State.initial_candidate_binding_success _ bobInput bob .bool
          rfl true rfl) trace
  exact ⟨associated.2, fixed⟩

/-- Acceptance at Bob's resolve node identifies the initialized TRUE opening;
fresh handles and arbitrary RAW opening claims cannot alter the publication. -/
theorem accepted_bob_opening_true (scheduler : app.Scheduler) (horizon : Nat)
    (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (next : EventGraphRuntime.State nativeGraph) (id : MessageId Player)
    (candidate : Handle nativeGraph) (raw : Raw simpleExpr)
    (accepted : (runtime setup).handle control.execution.application
      ⟨id, .opening bobEvent candidate raw⟩ = some next) :
    candidate = bobCandidate ∧ raw = ⟨.bool, true⟩ := by
  obtain ⟨associated, fixed⟩ := bob_binding_fixed scheduler horizon control trace
  exact (runtime setup).accepted_opening_identifies control.execution.application next bob
    bobEvent .bool bobBinding [] rfl rfl rfl bobCandidate ⟨.bool, true⟩ associated fixed
    id candidate raw accepted

end Vegas.Examples.CommittedResolutionReadout
