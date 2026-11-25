module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveBindingLikelihood
public import Vegas.Game.SourceServiceCheckpoint
public import Vegas.Game.ServiceObservation
public import GameTheory.Math.Probability.Support

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

/-- Equal source views give the same actual focal observation at graph initialization. -/
private theorem source_initial_playerObservation_eq
    (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
    (focal : Player) (left right : State L setup.context)
    (same : (Config.initial left).view focal = (Config.initial right).view focal) :
    (serviceGraph setup deps).playerObserve focal
        (EventGraph.Config.initial (setup.eventInputs left)) =
      (serviceGraph setup deps).playerObserve focal
        (EventGraph.Config.initial (setup.eventInputs right)) := by
  have first := SourceCheckpoint.initial (deps := deps) setup left
  have second := SourceCheckpoint.initial (deps := deps) setup right
  exact checkpoint_playerObservation_eq_of_order setup _ 0
    (ContextRefs.initial_coversPrefix setup.program) focal _ _ _ _
    EventGraph.Config.Reachable.initial EventGraph.Config.Reachable.initial
    (by change focal ∉ (∅ : Finset Player); simp)
    (by change focal ∉ (∅ : Finset Player); simp)
    (by rfl) first.ordered second.ordered first.agrees second.agrees first.history
    second.history (by rfl) (by rfl) same

/-- Correlated initial draws with the same source view have identical native
traffic projections, including the genuine owned initial candidate catalogue. -/
theorem source_initial_traffic_eq
    (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
    {duration : (serviceGraph setup deps).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (focal : Player) (left right : State L setup.context)
    (same : (Config.initial left).view focal = (Config.initial right).view focal) :
    (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
        (ReactiveApplication.Execution.initial (serviceApplication setup deps duration leaks)
          (EventGraphRuntime.State.initial (graph := serviceGraph setup deps)
              (setup.eventInputs left))) =
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
        (ReactiveApplication.Execution.initial (serviceApplication setup deps duration leaks)
          (EventGraphRuntime.State.initial (graph := serviceGraph setup deps)
              (setup.eventInputs right))) := by
  exact initial_bindingTraffic_eq_of_observation (serviceTimeouts setup deps duration)
    leaks focal _ _ (source_initial_playerObservation_eq setup focal left right same)

/-- Initial native traffic factors through the focal source view for the
supplied initial law, without an independence assumption on private types. -/
theorem source_initial_traffic_factorization
    (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
    {duration : (serviceGraph setup deps).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (focal : Player) :
    ∃ noise : DecisionView focal setup.context → PMF _,
      setup.initialLaw.map (fun initial =>
        (Config.initial initial,
          (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
            (ReactiveApplication.Execution.initial (serviceApplication setup deps duration leaks)
              (EventGraphRuntime.State.initial (graph := serviceGraph setup deps)
                (setup.eventInputs initial))))) =
      (setup.initialLaw.map Config.initial).bind fun source =>
        (noise (source.view focal)).map fun extra => (source, extra) := by
  exact initial_bindingTraffic_factorization_of_view (serviceTimeouts setup deps duration)
    leaks focal setup.initialLaw setup.eventInputs Config.initial (fun config => config.view focal)
    (fun left _ right _ same => source_initial_playerObservation_eq setup focal left right same)

end Vegas
