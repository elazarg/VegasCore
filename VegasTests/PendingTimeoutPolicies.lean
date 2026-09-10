/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedTimeoutPolicyLaws
import VegasTests.PendingTimeout

/-! # Policy-level timeout ordering regression

The players and invocation schedule are identical in both games.  Only the
wire-observing environment's order for two already-pending calls differs.  In
particular, player 1 submits a valid opening in both games; expiration is an
inclusion-order outcome, not an encoding of that player's decision to quit.
-/

namespace VegasTests.PendingTimeoutPolicies

open GameTheory GameTheory.Math.Probability
open Interaction Interaction.MessageApplication
open VegasTests.PendingSource

noncomputable section

private abbrev application := VegasTests.PendingTimeout.timed.messageApplication
  (Value := VegasTests.PendingExecution.Value)

private def players : Player → application.PlayerPolicy
  | 0 => fun _ _ => FinDist.pure (.submit .expire)
  | 1 => fun _ _ => FinDist.pure (.submit (.protocol (.opening 3 (1, 1) (some true))))

private def openingFirst : application.EnvironmentPolicy := fun history _ =>
  FinDist.pure <| match history.length with
    | 0 => .application (ULift.up 11)
    | 1 => .deliver 0 (1, 1)
    | 2 => .include (1, 1)
    | _ => .include (0, 1)

private def expiryFirst : application.EnvironmentPolicy := fun history _ =>
  FinDist.pure <| match history.length with
    | 0 => .application (ULift.up 11)
    | 1 => .deliver 0 (1, 1)
    | 2 => .include (0, 1)
    | _ => .include (1, 1)

private def schedule : List (@Invocation Player) :=
  [.environment, .player 1, .player 0, .environment, .environment, .environment]

private def initial :=
  VegasTests.PendingTimeout.commitPrefix (some false) (some true)

private def openingFirstResult :=
  VegasTests.PendingTimeout.timed.run initial
    [.advance 11, .submit 1 (.protocol (.opening 3 (1, 1) (some true))),
     .submit 0 .expire, .deliver 0 (1, 1), .include (1, 1), .include (0, 1)]

private def expiryFirstResult :=
  VegasTests.PendingTimeout.timed.run initial
    [.advance 11, .submit 1 (.protocol (.opening 3 (1, 1) (some true))),
     .submit 0 .expire, .deliver 0 (1, 1), .include (0, 1), .include (1, 1)]

def openingFirstLaw :=
  (application.policyGame openingFirst schedule
    (VegasTests.PendingTimeout.timed.toSharedState initial)).play players

def expiryFirstLaw :=
  (application.policyGame expiryFirst schedule
    (VegasTests.PendingTimeout.timed.toSharedState initial)).play players

private theorem openingFirst_native :
    openingFirstLaw.map (fun outcome => outcome.native) =
      FinDist.pure (VegasTests.PendingTimeout.timed.toSharedState openingFirstResult) := by
  simp only [openingFirstLaw, policyGame, policySignature, schedule, runPolicies, invoke, players,
    openingFirst, FinDist.map_pure, FinDist.pure_bind, PolicyExecution.initial,
    environmentPolicyStep, playerStep, advance, EnvironmentPolicyCommand.toAction,
    PlayerCommand.toAction, List.nil_append, List.length_cons, List.length_nil,
    List.length_append, SealedTimeout.step_shared, SealedTimeout.fromSharedAction]
  rfl

private theorem expiryFirst_native :
    expiryFirstLaw.map (fun outcome => outcome.native) =
      FinDist.pure (VegasTests.PendingTimeout.timed.toSharedState expiryFirstResult) := by
  simp only [expiryFirstLaw, policyGame, policySignature, schedule, runPolicies, invoke, players,
    expiryFirst, FinDist.map_pure, FinDist.pure_bind, PolicyExecution.initial,
    environmentPolicyStep, playerStep, advance, EnvironmentPolicyCommand.toAction,
    PlayerCommand.toAction, List.nil_append, List.length_cons, List.length_nil,
    List.length_append, SealedTimeout.step_shared, SealedTimeout.fromSharedAction]
  rfl

theorem openingFirst_resolution :
    openingFirstLaw.map (fun outcome => outcome.native.application.application.resolution) =
      FinDist.pure .completed := by
  have h := congrArg (FinDist.map fun state => state.application.application.resolution)
    openingFirst_native
  rw [FinDist.map_comp, FinDist.map_pure] at h
  exact h

theorem expiryFirst_resolution :
    expiryFirstLaw.map (fun outcome => outcome.native.application.application.resolution) =
      FinDist.pure .expired := by
  have h := congrArg (FinDist.map fun state => state.application.application.resolution)
    expiryFirst_native
  rw [FinDist.map_comp, FinDist.map_pure] at h
  exact h

theorem same_players_deliver_opening :
    openingFirstLaw.map (fun outcome =>
      (outcome.native.pool.inbox 0).getLast?.map Message.id) =
        FinDist.pure (some (1, 1)) ∧
    expiryFirstLaw.map (fun outcome =>
      (outcome.native.pool.inbox 0).getLast?.map Message.id) =
        FinDist.pure (some (1, 1)) := by
  constructor
  · have h := congrArg (FinDist.map fun state =>
        (state.pool.inbox 0).getLast?.map Message.id) openingFirst_native
    rw [FinDist.map_comp, FinDist.map_pure] at h
    exact h
  · have h := congrArg (FinDist.map fun state =>
        (state.pool.inbox 0).getLast?.map Message.id) expiryFirst_native
    rw [FinDist.map_comp, FinDist.map_pure] at h
    exact h

end

end VegasTests.PendingTimeoutPolicies

/-- info: 'VegasTests.PendingTimeoutPolicies.openingFirst_resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingTimeoutPolicies.openingFirst_resolution

/-- info: 'VegasTests.PendingTimeoutPolicies.expiryFirst_resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingTimeoutPolicies.expiryFirst_resolution

/-- info: 'VegasTests.PendingTimeoutPolicies.same_players_deliver_opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingTimeoutPolicies.same_players_deliver_opening
