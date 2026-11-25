module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.EffectiveOpeningSimulation
public import Vegas.Pending.ReadyRosterService

@[expose] public section

/-! # Unilateral graph simulation on the ready owner roster -/

noncomputable section

namespace Vegas

open Interaction EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The ready owner roster realizes any unilateral raw deviation against the
effective-opening profile on every canonical prefix and at termination. -/
theorem readyRoster_effectiveOpening_deviation_config_law
    (graph : EventGraph Player L)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (network : (NetworkPolicy (rosterTimeouts graph)) leaks)
    (inputs : PMF graph.Inputs) (base : graph.sequentialize.BehavioralProfile)
    (focal : Player) (deviation : (rosterApplication graph leaks).Policy) :
    let reference := effectiveOpening base
    let scheduler := readyRosterScheduler graph leaks (ownerRoster graph) network
    let horizon := (rosterPlan graph (ownerRoster graph)).length
    let players := Function.update (turnPolicy (rosterTimeouts graph) leaks (fun _ => 0) 1
      (EventGraphRuntime.firstTurnTiming graph.sequentialize 1) reference) focal deviation
    let boundary := physicalPrefix (rosterTimeouts graph) leaks scheduler players inputs horizon
    ∃ policy : graph.sequentialize.BehavioralPolicy focal,
      (∀ rank, rank ≤ graph.sequentialize.order.eventCount →
        (boundary rank).map (fun execution => Config.rankPrefix rank execution.application.config) =
          inputs.bind fun seed => graph.sequentialize.runPlan
            (graph.sequentialize.policyPlan (Function.update reference focal policy)
              graph.sequentialize.canonicalScheduler)
            rank (Config.initial seed)) ∧
      ((rosterApplication graph leaks).roundsFrom (rosterInitialLaw graph inputs)
        scheduler players horizon).map (fun final => final.application.config) =
        inputs.bind (graph.sequentialize.runPolicies graph.sequentialize.canonicalScheduler
          (Function.update reference focal policy)) :=
  effectiveOpening_deviation_config_law (turns := 1) (rosterTimeouts graph) leaks
    (readyRosterScheduler graph leaks (ownerRoster graph) network)
    (fun event => event.val) (fun _ => 0) inputs base
    (readyRoster_owner_contract graph leaks inputs network)
    (rosterScheduler_asyncTimely graph) focal deviation

end Vegas
