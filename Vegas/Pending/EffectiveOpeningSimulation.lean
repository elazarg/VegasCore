module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.SingleOwnerSimulation
public import Vegas.Pending.ForeignPublicationPhase

@[expose] public section

/-! # Unilateral graph simulation for effective-opening clients -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (timeouts : EventTimeouts graph.sequentialize)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))

local notation "G" => graph.sequentialize
local notation "app" => reactiveApplication timeouts leaks

/-- One graph behavioral deviation realizes a raw ledger deviation at every
canonical prefix, and hence on the terminal configuration, when the other
players use first-turn clients for the effective-opening reference profile. -/
theorem effectiveOpening_deviation_config_law {horizon turns : Nat}
    (scheduler : (app).Scheduler) (delay bound : (G).EventId → Nat)
    (inputs : PMF (G).Inputs) (base : (G).BehavioralProfile)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (focal : Player) (deviation : (app).Policy) :
    let reference := effectiveOpening base
    let players := Function.update (turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming G turns) reference) focal deviation
    let boundary := physicalPrefix timeouts leaks scheduler players inputs horizon
    ∃ policy : (G).BehavioralPolicy focal,
      (∀ rank, rank ≤ (G).order.eventCount →
        (boundary rank).map (fun execution => Config.rankPrefix rank execution.application.config) =
          inputs.bind fun seed => (G).runPlan
            ((G).policyPlan (Function.update reference focal policy) (G).canonicalScheduler)
            rank (Config.initial seed)) ∧
      ((app).roundsFrom (inputs.map State.initial) scheduler players horizon).map
        (fun final => final.application.config) =
        inputs.bind ((G).runPolicies (G).canonicalScheduler
          (Function.update reference focal policy))
    := by
  intro reference players boundary
  apply physicalPrefix_policy_of_steps scheduler players inputs horizon reference focal
    contract.completes
  intro event
  have own (controlled : (G).actor? event = none ∨ (G).actor? event = some focal) :=
    physicalPrefix_policyStep_of_focal_or_chance timeouts leaks scheduler bound turns
      (EventGraphRuntime.firstTurnTiming G turns) reference focal deviation inputs horizon
      contract.completes event controlled
  cases node : nodeView (G) event with
  | sample payload law outputEq codeEq =>
    exact own (Or.inl (nodeView_sample_actor outputEq codeEq))
  | bind owner payload outputEq codeEq =>
    by_cases equal : owner = focal
    · subst owner
      exact own (Or.inr (nodeView_bind_actor outputEq codeEq))
    · exact physicalPrefix_foreign_binding_policyStep scheduler delay bound inputs reference
        contract timely focal owner deviation equal event outputEq codeEq node
  | resolve owner payload binding checks outputEq codeEq =>
    by_cases equal : owner = focal
    · subst owner
      exact own (Or.inr (nodeView_resolve_actor outputEq codeEq))
    · exact physicalPrefix_foreign_publication_policyStep scheduler delay bound inputs base
        contract timely focal owner deviation equal event binding checks outputEq codeEq node

end Vegas.EventGraphRuntime
