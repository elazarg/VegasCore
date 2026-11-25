module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.SingleOwnerSimulation
public import Vegas.Pending.ForeignPublicationPhase

@[expose] public section

/-! # Unilateral graph simulation under safe publications -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (timeouts : EventTimeouts graph.sequentialize)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))

local notation "G" => graph.sequentialize
local notation "app" => reactiveApplication timeouts leaks

/-- On a supported initial input, a foreign owner can disclose only if the
publication will succeed. Its policy may withhold at an accepted opening. -/
def SafeForeignPublications {g : Vegas.EventGraph Player L} (inputs : PMF g.Inputs)
    (reference : g.BehavioralProfile) (focal : Player) : Prop :=
  ∀ (event : g.EventId) (owner : Player), owner ≠ focal → ∀ {payload : L.Ty}
    (binding : FieldRef g.layout (.binding owner payload))
    (checks : List (GuardCheck g.layout payload))
    (outputEq : g.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode g.layout) outputEq) (g.nodes event) =
      .resolve owner payload binding checks),
    nodeView g event = .resolve owner payload binding checks outputEq codeEq →
    ∀ initial ∈ inputs.support, ∀ config : g.Config, config.Reachable initial →
      config.cut.Ready event → owner ∉ config.defaulted →
      ∀ action ∈ (actionLaw reference config event).support,
        (cast (congrArg EventField.Action outputEq) action : Bool) = true →
        openingAccepted event config.store = true

/-- If the other players disclose only accepted openings, every raw unilateral
ledger deviation has one behavioral graph policy with the same configuration
law at all canonical prefixes and at the terminal stop. -/
theorem safePublication_deviation_config_law {horizon turns : Nat}
    (scheduler : (app).Scheduler) (delay bound : (G).EventId → Nat)
    (inputs : PMF (G).Inputs) (reference : (G).BehavioralProfile)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (focal : Player) (deviation : (app).Policy)
    (safe : SafeForeignPublications inputs reference focal) :
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
  intro players boundary
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
    · exact physicalPrefix_foreign_safe_publication_policyStep scheduler delay bound inputs
        reference
        contract timely focal owner deviation equal event binding checks outputEq codeEq node
        (safe event owner equal binding checks outputEq codeEq node)

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
  apply safePublication_deviation_config_law timeouts leaks scheduler delay bound inputs
    (effectiveOpening base) contract timely focal deviation
  intro event owner foreign payload binding checks outputEq codeEq node initial supported
    config reachable ready active action chosen disclose
  exact (effectiveOpening_publication_disclosure_safe node base config action chosen disclose).2

end Vegas.EventGraphRuntime
