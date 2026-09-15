/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import InteractionTests.LogicalCommitmentNative
import Interaction.MessageApplicationPolicies

/-! # Policy execution for the two-decision commitment experiment

This bounded `MessageApplication.runPolicies` experiment has two owner
decisions: a Boolean preparation kernel and an optional-opening kernel. The
intervening commitment submission is fixed; the opening response recalls its
value from the owner's private-command history. The background opponent and
environment are fixed independently of both kernels. The opponent sends an
unauthenticated claim, not another compiled binding's secret disclosure.

Conditioning removes auxiliary owner metadata and the full native view from
the logical policy while preserving the terminal publication/timeout law.
This is a restricted two-decision interface, not arbitrary native policies,
adaptive delivery service, or a whole-graph strategic certificate.
-/

noncomputable section

namespace InteractionTests.LogicalCommitmentPolicyExecution

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

open InteractionTests.LogicalCommitmentNative

private def initialExecution : app.PolicyExecution :=
  PolicyExecution.initial app initial

private def recalledValue? : List app.PlayerEntry → Option Bool
  | ⟨_, .privateCommand ⟨(0, some value)⟩⟩ :: _ => some value
  | _ => none

/-- The owner wrapper contains exactly two arbitrary kernels.  On its middle
invocation it submits the commitment determined by its actual private recall. -/
private def ownerPolicy (info : Fin 2)
    (first : Fin 2 → FinDist Bool)
    (second : Fin 2 → Bool → app.View → FinDist (Option Bool)) : app.PlayerPolicy :=
  fun history view => match history with
  | [] => (first info).map fun value => .privateCommand ⟨(0, some value)⟩
  | [_] => FinDist.pure <| match recalledValue? history with
      | some _ => .submit commitment
      | none => .wait
  | _ => match recalledValue? history with
      | some value => (second info value view).map fun response => match response with
          | some claimed => .submit (ownerOpening claimed)
          | none => .wait
      | none => FinDist.pure .wait

private def opponentPolicy (disclosure : Disclosure) : app.PlayerPolicy :=
  fun _ _ => FinDist.pure (.submit (competingOpening disclosure.claimed))

private def players (info : Fin 2) (disclosure : Disclosure)
    (first : Fin 2 → FinDist Bool)
    (second : Fin 2 → Bool → app.View → FinDist (Option Bool)) :
    Bool → app.PlayerPolicy
  | false => ownerPolicy info first second
  | true => opponentPolicy disclosure

/-- The fixed environment uses its own invocation history as a phase counter.
It never inspects or captures either owner kernel. -/
private def environment (disclosure : Disclosure) : app.EnvironmentPolicy :=
  fun history _ => FinDist.pure <| match history.length with
  | 0 => .include (false, 0)
  | 1 => .deliver false (true, 0)
  | 2 => if disclosure.included then .include (true, 0) else .wait
  | 3 => .include (false, 1)
  | _ => .application ⟨()⟩

private def schedule : List (@Invocation Bool) :=
  [.player false, .player false, .environment, .player true,
    .environment, .environment, .player false, .environment, .environment]

private def executionOutcome (execution : app.PolicyExecution) : Outcome :=
  outcome execution.native

private def expected (value : Bool) (response : Option Bool) : Outcome :=
  if response = some value then (some (some value), false) else (some none, true)

private theorem environmentStep_clock (state : app.Application) :
    app.environmentStep state ⟨()⟩ = FinDist.pure (runtime.tick state) := rfl

/-- `first` and `second` are arbitrary finite-distribution kernels at the two
designated owner decisions.  All other owner commands, the opponent policy,
the environment policy, and the schedule are fixed independently of them.
The second kernel receives the actual owner view and the value recovered from
the owner's actual private-command history. -/
theorem runPolicies_two_decision_outcome
    (info : Fin 2) (disclosure : Disclosure)
    (first : Fin 2 → FinDist Bool)
    (second : Fin 2 → Bool → app.View → FinDist (Option Bool)) :
    (app.runPolicies (players info disclosure first second) (environment disclosure)
      schedule initialExecution).map executionOutcome =
    (first info).bind fun value =>
      (second info value (State.observe app (disclosedState value disclosure) false)).bind
        fun response => FinDist.pure (expected value response) := by
  rcases disclosure with ⟨claimed, included⟩
  let data : Disclosure := ⟨claimed, included⟩
  cases included <;>
  simp only [schedule, MessageApplication.runPolicies, MessageApplication.invoke,
    players, ownerPolicy, opponentPolicy, environment, initialExecution,
    MessageApplication.PolicyExecution.initial, recalledValue?,
    MessageApplication.playerStep, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, MessageApplication.PlayerCommand.toAction,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.bind_map, FinDist.map_bind, FinDist.pure_bind, FinDist.bind_pure,
    FinDist.bind_bind, FinDist.map_pure, if_true, if_false, List.nil_append,
    List.length_nil, List.length_cons, Bool.false_eq_true,
    Bool.true_eq_false, List.length_append, List.cons_append, Nat.reduceAdd] <;>
  all_goals apply FinDist.bind_congr
  all_goals
    intro value _
    apply FinDist.bind_congr
    intro response _
    have hsettled := congrArg FinDist.pure
      (LogicalCommitmentNative.settled_outcome value data response)
    cases response <;>
      simp only [FinDist.pure_bind, environmentStep_clock] <;>
      exact hsettled

/-- The actual native policy runner has the law of a logical policy retaining
the first action and pending-versus-included observation, but not auxiliary
owner metadata or the full native view. The background opponent, environment,
schedule and logical transition kernels are fixed before both arbitrary owner kernels.
The initial metadata law mixes owner policies only. -/
theorem runPolicies_logical_policy_law
    (metadata : FinDist (Fin 2)) (disclosure : Disclosure)
    (first : Fin 2 → FinDist Bool)
    (second : Fin 2 → Bool → app.View → FinDist (Option Bool)) :
    ∃ logicalFirst : Unit → FinDist Bool,
      ∃ logicalSecond : Unit × Bool × OpeningObservation → FinDist (Option Bool),
        (metadata.bind fun info =>
          (app.runPolicies (players info disclosure first second) (environment disclosure)
            schedule initialExecution).map executionOutcome) =
        ((metadata.map fun _ => ()).bind fun info =>
          (logicalFirst info).bind fun value =>
            (logicalNext (FinDist.pure disclosure) info value).bind fun later =>
              (logicalSecond (info, value, later)).bind
                (logicalFinish (info, value, later))) := by
  obtain ⟨logicalFirst, logicalSecond, hlaw⟩ :=
    candidate_two_decision_policy_law metadata (FinDist.pure disclosure) first
      (fun history => second history.1 history.2.1 history.2.2)
  refine ⟨logicalFirst, logicalSecond, ?_⟩
  calc
    _ = metadata.bind (fun info => (first info).bind fun value =>
        (second info value (State.observe app (disclosedState value disclosure) false)).bind
          fun response => FinDist.pure (expected value response)) :=
      FinDist.bind_congr (fun info _ =>
        runPolicies_two_decision_outcome info disclosure first second)
    _ = _ := by simpa only [FinDist.pure_bind, expected] using hlaw

end InteractionTests.LogicalCommitmentPolicyExecution

/-- info: 'InteractionTests.LogicalCommitmentPolicyExecution.runPolicies_logical_policy_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractionTests.LogicalCommitmentPolicyExecution.runPolicies_logical_policy_law
