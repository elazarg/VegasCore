module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.PhysicalPrefixPolicy
public import Vegas.Pending.SingleOwnerPhase

@[expose] public section

/-! # Unilateral graph simulation across repeated decisions and public chance -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (timeouts : EventTimeouts graph.sequentialize)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))

local notation "G" => graph.sequentialize
local notation "app" => reactiveApplication timeouts leaks

/-- Every focal or chance event satisfies the policy assembly's one-rank law
at the actual native stopping distribution. -/
theorem physicalPrefix_policyStep_of_focal_or_chance
    (scheduler : (app).Scheduler) (bound : (G).EventId → Nat) (turns : Nat)
    (timing : EventGraphRuntime.TurnTiming G turns) (reference : (G).BehavioralProfile)
    (focal : Player) (deviation : (app).Policy) (inputs : PMF (G).Inputs) (horizon : Nat)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler)
    (event : (G).EventId) (owner : (G).actor? event = none ∨ (G).actor? event = some focal) :
    PhysicalPrefixPolicyStep scheduler
      (Function.update (turnPolicy timeouts leaks bound turns timing reference) focal deviation)
      inputs horizon reference focal event := by
  classical
  intro noise factor
  obtain ⟨rule, next, joint⟩ := physicalPrefix_singleOwner_phase timeouts leaks scheduler bound
    turns timing reference focal deviation inputs horizon completes event owner noise factor
  let policy : (G).BehavioralPolicy focal := fun other actor info active =>
    if eq : event = other then eq ▸ rule info else reference focal other actor info active
  let players := Function.update (turnPolicy timeouts leaks bound turns timing reference)
    focal deviation
  let prior := physicalPrefix timeouts leaks scheduler players inputs horizon event.val
  let checkpoint := fun execution : (app).Execution =>
    Config.rankPrefix event.val execution.application.config
  refine ⟨policy, next, joint.trans ?_⟩
  apply congrArg (fun law : PMF (G).Config => law.bind _)
  rw [PMF.bind_map]
  apply bind_congr_on_support _
  intro execution member
  obtain ⟨_, _, _, _, ordered, _⟩ := physicalPrefix_supported timeouts leaks scheduler players
    inputs horizon completes event.val event.isLt.le execution member
  let before := checkpoint execution
  have ready : before.cut.Ready event := ordered.ready event.isLt
  change (if h : before.cut.Ready event then
    (rule ((G).playerObserve focal before)).bind (before.step event h) else PMF.pure before) =
      (G).runPlan ((G).policyPlan (Function.update reference focal policy) (G).canonicalScheduler)
        1 before
  rw [dite_eq_left ready, runPlan_one_at_prefix _ before event ordered]
  unfold eventStep
  rcases owner with chance | owned
  · rw [actionDistribution_of_ownerless _ _ chance, PMF.pure_bind]
    refine Eq.trans ?_ (PMF.bind_const (rule ((G).playerObserve focal before)) _)
    apply bind_congr_on_support _
    intro chosen _
    rw [((G).nodes event).action_eq_of_actor_none chance chosen
      (EventCode.actionOfActorNone ((G).nodes event) chance)]
  · rw [actionDistribution_of_actor _ _ owned]
    by_cases inactive : focal ∈ before.defaulted
    · rw [dite_eq_left inactive, PMF.pure_bind]
      refine Eq.trans ?_ (PMF.bind_const (rule ((G).playerObserve focal before)) _)
      apply bind_congr_on_support _
      intro chosen _
      exact before.step_eq_of_defaulted event ready focal owned inactive chosen _
    · simp only [dite_eq_right inactive, Function.update_self, policy, dite_eq_left]

/-- If all strategic events belong to the deviating player, every raw ledger
policy is realized by one graph behavioral policy at every rank and at the
terminal configuration. Public samples, repeated decisions, arbitrary input
laws, timing policies, and observations are allowed. -/
theorem singleOwner_deviation_config_distribution
    (scheduler : (app).Scheduler) (bound : (G).EventId → Nat) (turns : Nat)
    (timing : EventGraphRuntime.TurnTiming G turns) (reference : (G).BehavioralProfile)
    (focal : Player) (deviation : (app).Policy) (inputs : PMF (G).Inputs) (horizon : Nat)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler)
    (events : ∀ event, (G).actor? event = none ∨ (G).actor? event = some focal) :
    let players := Function.update (turnPolicy timeouts leaks bound turns timing reference)
      focal deviation
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
  apply physicalPrefix_policy_of_steps scheduler players inputs horizon reference focal completes
  intro event
  exact physicalPrefix_policyStep_of_focal_or_chance timeouts leaks scheduler bound turns
    timing reference focal deviation inputs horizon completes event (events event)

end Vegas.EventGraphRuntime
