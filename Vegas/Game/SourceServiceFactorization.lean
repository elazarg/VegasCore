module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveBindingLikelihood
public import Vegas.Game.SourceServiceCheckpoint
public import Vegas.Game.ServiceObservation
public import GameTheory.Math.Probability.Support
public import Vegas.Pending.EventInitialObservation

@[expose] public section

/-! # Initial source and native traffic factorization

The actual native initial traffic is determined by the focal player's source
view, even when initial private inputs are correlated. The joint law retains
one source configuration with its complete public default record.
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
    {duration : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (focal : Player) (left right : State L setup.context)
    (same : (Config.initial left).view focal = (Config.initial right).view focal) :
    (bindingTraffic (serviceTimeouts setup mode duration)) leaks focal
        (ReactiveApplication.Execution.initial (serviceApplication setup mode duration leaks)
          (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
              (setup.eventInputs left))) =
      (bindingTraffic (serviceTimeouts setup mode duration)) leaks focal
        (ReactiveApplication.Execution.initial (serviceApplication setup mode duration leaks)
          (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
              (setup.eventInputs right))) := by
  have first := SourceCheckpoint.initial (mode := mode) setup left
  have second := SourceCheckpoint.initial (mode := mode) setup right
  have observed := checkpoint_playerObservation_eq_of_order setup _ 0
    (ContextRefs.initial_coversPrefix setup.program) focal _ _ _ _
    EventGraph.Config.Reachable.initial EventGraph.Config.Reachable.initial
    (by change focal ∉ (∅ : Finset Player); simp)
    (by change focal ∉ (∅ : Finset Player); simp)
    (by rfl) first.ordered second.ordered first.agrees second.agrees first.history
    second.history (by rfl) (by rfl) same
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
    congr 1
  unfold EventGraphRuntime.bindingTraffic
  dsimp only [ReactiveApplication.Execution.initial]
  rw [views, publics]

/-- Initial native traffic factors through the focal source view for the
supplied initial law, without an independence assumption on private types. -/
theorem source_initial_traffic_factorization
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {duration : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (focal : Player) :
    ∃ noise : DecisionView focal setup.context → PMF _,
      setup.initialLaw.map (fun initial =>
        (Config.initial initial,
          (bindingTraffic (serviceTimeouts setup mode duration)) leaks focal
            (ReactiveApplication.Execution.initial (serviceApplication setup mode duration leaks)
              (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
                (setup.eventInputs initial))))) =
      (setup.initialLaw.map Config.initial).bind fun source =>
        (noise (source.view focal)).map fun extra => (source, extra) := by
  classical
  let read := fun initial : State L setup.context =>
    (bindingTraffic (serviceTimeouts setup mode duration)) leaks focal
      (ReactiveApplication.Execution.initial (serviceApplication setup mode duration leaks)
        (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
            (setup.eventInputs initial)))
  let noise := fun view : DecisionView focal setup.context =>
    if present : ∃ initial ∈ setup.initialLaw.support,
        (Config.initial initial).view focal = view then
      PMF.pure (read present.choose)
    else PMF.pure (read setup.initialLaw.support_nonempty.choose)
  refine ⟨noise, ?_⟩
  rw [PMF.bind_map]
  change setup.initialLaw.bind (fun initial => PMF.pure
      (Config.initial initial, read initial)) = _
  apply bind_congr_on_support _
  intro initial supported
  have present : ∃ other ∈ setup.initialLaw.support,
      (Config.initial other).view focal = (Config.initial initial).view focal :=
    ⟨initial, supported, rfl⟩
  simp only [noise, Function.comp_apply, dite_eq_left present, PMF.pure_map]
  rw [show read initial = read present.choose from
    source_initial_traffic_eq setup leaks focal initial present.choose present.choose_spec.2.symm]

end Vegas
