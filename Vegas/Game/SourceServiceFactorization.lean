/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRoster
import Vegas.Game.SourceServiceDisclosure
import Vegas.Pending.ReactiveOpeningLikelihood
import GameTheory.Math.Probability.ConditionalObservation
import Vegas.Source.ObservationRecall
import Vegas.Game.SourceServiceCheckpoint
import Vegas.Game.ServiceObservation
import Vegas.Pending.ReactiveBindingTranscript
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Source memory and actual service-channel factorization

The proof law retains both the effective source configuration and its original
private intentions. Only the former is decoded from the native execution.
Binding timing, passive sampling, silence, and inclusion use the existing
runtime evaluator. Their conditional likelihood is derived from those actual
operations, rather than supplied as an independent channel hypothesis.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Correlated initial draws with the same source view have identical native
traffic projections, including the genuine owned initial candidate catalogue. -/
theorem source_initial_traffic_eq
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (focal : Player) (left right : State L setup.context)
    (same : (setup.initialConfig left).view focal = (setup.initialConfig right).view focal) :
    (serviceRuntime setup mode deadline).bindingTraffic leaks focal
        (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
          (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
              (setup.eventInputs left))) =
      (serviceRuntime setup mode deadline).bindingTraffic leaks focal
        (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
          (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
              (setup.eventInputs right))) := by
  have first := SourceCheckpoint.initial (mode := mode) setup left
  have second := SourceCheckpoint.initial (mode := mode) setup right
  have observed := checkpoint_playerObservation_eq_of_order setup _ 0
    (ContextRefs.initial_coversPrefix setup.program) focal _ _ _ _ (by rfl) first.ordered
    second.ordered first.agrees second.agrees first.history second.history same
  have publics : (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
        (setup.eventInputs left)).publicView =
      (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
        (setup.eventInputs right)).publicView :=
    EventGraphRuntime.State.initial_publicView_eq_of_observation (graph := serviceGraph setup mode)
        focal (setup.eventInputs left) (setup.eventInputs right) observed
  have candidates := EventGraphRuntime.State.initial_candidates_eq_of_observation
    (graph := serviceGraph setup mode) focal (setup.eventInputs left)
    (setup.eventInputs right) observed
  have views : (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
        (setup.eventInputs left)).playerView focal =
      (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
        (setup.eventInputs right)).playerView focal := by
    unfold EventGraphRuntime.State.playerView
    rw [publics, observed, candidates]
  unfold EventGraphRuntime.bindingTraffic
  dsimp only [ReactiveApplication.Execution.initial]
  rw [views, publics]

/-- The induction starts from the actual supplied initial law. There is no
independence assumption on private types, and original and effective histories
are paired only at initialization, before any intention can be erased. -/
theorem source_initial_memory_factorization
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (focal : Player) :
    ∃ noise : DecisionView focal setup.context → PMF _,
      setup.initialLaw.map (fun initial =>
        ((setup.initialConfig initial, setup.initialConfig initial),
          (serviceRuntime setup mode deadline).bindingTraffic leaks focal
            (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
              (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
                (setup.eventInputs initial))))) =
      (setup.initialLaw.map fun initial =>
        (setup.initialConfig initial, setup.initialConfig initial)).bind fun pair =>
          (noise (pair.1.view focal)).map fun extra => (pair, extra) := by
  classical
  let read := fun initial : State L setup.context =>
    (serviceRuntime setup mode deadline).bindingTraffic leaks focal
      (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
        (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
            (setup.eventInputs initial)))
  let noise := fun view : DecisionView focal setup.context =>
    if present : ∃ initial ∈ setup.initialLaw.support,
        (setup.initialConfig initial).view focal = view then
      PMF.pure (read present.choose)
    else PMF.pure (read setup.initialLaw.support_nonempty.choose)
  refine ⟨noise, ?_⟩
  rw [PMF.bind_map]
  change setup.initialLaw.bind (fun initial => PMF.pure
      ((setup.initialConfig initial, setup.initialConfig initial), read initial)) = _
  apply bind_congr_on_support _
  intro initial supported
  have present : ∃ other ∈ setup.initialLaw.support,
      (setup.initialConfig other).view focal = (setup.initialConfig initial).view focal :=
    ⟨initial, supported, rfl⟩
  simp only [noise, Function.comp_apply, dite_eq_left present, PMF.pure_map]
  rw [show read initial = read present.choose from
    source_initial_traffic_eq setup leaks focal initial present.choose present.choose_spec.2.symm]

omit [IExpr.ResultTypes L] in
private theorem commit_view_reflects {Γ : SourceCtx Player L} {owner : Player}
    {payload : L.Ty} (focal : Player) (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (left right : Config Player L Γ)
    (first second : PublicationResult (L.Val payload))
    (same : (commitSuccessor name guard left first).view focal =
      (commitSuccessor name guard right second).view focal) :
    left.view focal = right.view focal := by
  have earlier := congrArg (DecisionView.back (decide (owner = focal))) same
  simpa only [back_commit_view] using earlier

end Vegas
