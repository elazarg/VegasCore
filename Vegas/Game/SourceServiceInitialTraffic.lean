/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefix
import Vegas.Game.ServiceObservation
import Vegas.Source.ObservationRecall
import Vegas.Pending.ReactiveBindingLikelihood

/-! # The actual initialized source and traffic law

Initial native traffic is determined by the focal source view, including the
owned initial candidate catalogue. The same correlated setup draw carries any
initial parameter and its decoded whole source prefix jointly.
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
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (focal : Player) (left right : State L setup.context)
    (same : (setup.initialConfig left).view focal = (setup.initialConfig right).view focal) :
    (runtime setup).bindingTraffic leaks focal
        (ReactiveApplication.Execution.initial (application setup leaks)
          (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs left))) =
      (runtime setup).bindingTraffic leaks focal
        (ReactiveApplication.Execution.initial (application setup leaks)
          (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs right))) := by
  have first := SourceCheckpoint.initial setup left
  have second := SourceCheckpoint.initial setup right
  have observed := checkpoint_playerObservation_eq setup _ 0
    (ContextRefs.initial_coversPrefix setup.program) focal _ _ _ _
      (EventGraphRuntime.State.initial_invariant
        (graph := graph setup) (setup.eventInputs left)).reachable
      (EventGraphRuntime.State.initial_invariant
        (graph := graph setup) (setup.eventInputs right)).reachable
      first.ordered second.ordered first.agrees second.agrees first.history second.history same
  have paired := NativeReplay.initial (runtime setup) focal
    (setup.eventInputs left) (setup.eventInputs right) observed
  have publics : (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs left)).publicView =
      (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs right)).publicView := paired.publicView
  have candidates := EventGraphRuntime.State.initial_candidates_eq_of_observation
    (graph := graph setup) focal (setup.eventInputs left) (setup.eventInputs right) observed
  have views : (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs left)).playerView focal =
      (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs right)).playerView focal := by
    unfold EventGraphRuntime.State.playerView
    rw [publics, observed, candidates]
    rfl
  unfold EventGraphRuntime.bindingTraffic
  dsimp only [ReactiveApplication.Execution.initial]
  rw [views, publics]

/-- The induction starts from the actual supplied initial law. There is no
independence assumption on private types, and original and effective histories
are paired only at initialization, before any intention can be erased. -/
theorem source_initial_memory_factorization
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (focal : Player) :
    ∃ noise : DecisionView focal setup.context → PMF _,
      setup.initialLaw.map (fun initial =>
        ((setup.initialConfig initial, setup.initialConfig initial),
          (runtime setup).bindingTraffic leaks focal
            (ReactiveApplication.Execution.initial (application setup leaks)
              (EventGraphRuntime.State.initial (graph := graph setup)
                (setup.eventInputs initial))))) =
      (setup.initialLaw.map fun initial =>
        (setup.initialConfig initial, setup.initialConfig initial)).bind fun pair =>
          (noise (pair.1.view focal)).map fun extra => (pair, extra) := by
  classical
  let read := fun initial : State L setup.context =>
    (runtime setup).bindingTraffic leaks focal
      (ReactiveApplication.Execution.initial (application setup leaks)
        (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)))
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


/-- The actual initial draw carries an arbitrary parameter, its decoded
typed whole source position and the same complete focal traffic together.
The channel reads only the whole source observation. No marginal or noise
law is supplied, and no independence of initial private types is needed. -/
theorem sourceService_initial_parameter_traffic_factorization {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (focal : Player) (parameter : State L setup.context → Parameter) :
    ∃ noise : SourceProgram.ProtocolView focal setup.program → PMF _,
      (∀ initial : State L setup.context,
        sourceServicePrefix? setup 0
            (ReactiveApplication.Execution.initial (application setup leaks)
              (EventGraphRuntime.State.initial (graph := graph setup)
                (setup.eventInputs initial))).application.config =
          some (ProtocolState.entry setup.program (setup.initialConfig initial))) ∧
      setup.initialLaw.map (fun initial =>
        ((parameter initial, ProtocolState.entry setup.program (setup.initialConfig initial)),
          (runtime setup).bindingTraffic leaks focal
            (ReactiveApplication.Execution.initial (application setup leaks)
              (EventGraphRuntime.State.initial (graph := graph setup)
                (setup.eventInputs initial))))) =
      ((setup.initialLaw.map fun initial =>
        (parameter initial, ProtocolState.entry setup.program (setup.initialConfig initial))).bind
          fun pair => (noise (ProtocolState.observe focal setup.program pair.2)).map
            fun extra => (pair, extra)) := by
  obtain ⟨sourceNoise, law⟩ := source_initial_memory_factorization setup leaks focal
  let noise := fun view : SourceProgram.ProtocolView focal setup.program =>
    sourceNoise (ProtocolView.entryView focal setup.program view)
  refine ⟨noise, fun initial => sourceServicePrefix?_initial setup initial, ?_⟩
  have lifted := congrArg (PMF.map fun pair =>
    ((parameter pair.1.1.state, ProtocolState.entry setup.program pair.1.1), pair.2)) law
  simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def,
    noise, ProtocolView.entryView_observe_entry, SourceProgram.Setup.initialConfig] using lifted

end Vegas
