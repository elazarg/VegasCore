/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionReservations

/-! # Reserved inclusion still permits reactions to pending packets -/

noncomputable section

namespace InteractionTests.SealedResolutionService

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

private def runtime : SealedResolution Bool (Option Bool) :=
  ⟨⟨[⟨.commit false, []⟩]⟩, none, 10⟩

private def players : Bool → runtime.messageApplication.PlayerPolicy := fun who _ view =>
  FinDist.pure <| if who then
    if view.messages.inbox.isEmpty then .wait else .privateCommand ⟨(7, some false)⟩
  else .submit .malformed

/-- Four delivery opportunities in one round, four inclusion opportunities
in the next. The fifth environment call of each round is the driver's clock. -/
private def reserved (turn : Nat) : Bool := decide (5 ≤ turn % 10)

private def wire : runtime.messageApplication.WirePolicy :=
  runtime.messageApplication.reserveInclusion reserved
    (fun _ _ => FinDist.pure (.deliver true (false, 0)))

private def initial : runtime.messageApplication.PolicyExecution :=
  PolicyExecution.initial _ (State.initial _ runtime.initial)

private theorem malformed_rejected (state : SealedResolution.ApplicationState Bool (Option Bool))
    (id : Bool × Nat) : runtime.handle state ⟨id, .malformed⟩ = none := by
  simp [SealedResolution.handle, SealedResolution.validateMessage?, SealedProgram.Payload.node?,
    SealedProgram.validateMessage?]

theorem delayed_wire_has_reserved_service :
    runtime.messageApplication.InclusionService (fun turn => reserved turn = true)
      (runtime.messageApplication.wireEnvironment wire) :=
  runtime.messageApplication.reserveInclusion_service reserved _

/-- Four inclusions every second round suffice for the two-entry roster,
uniformly over arbitrary traffic and unreserved wire decisions. Completion
may stop the driver before the scheduled drain. -/
theorem arbitrary_players_have_nonempty_service_class
    (policies : Bool → runtime.messageApplication.PlayerPolicy)
    (base : runtime.messageApplication.WirePolicy)
    (next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈ (runtime.roundDriver.runRounds [false, true] 4 policies
      (runtime.messageApplication.reserveInclusion reserved base) 2 initial).support) :
    runtime.complete next.native.application.visible = true ∨ next.native.pool.pending = [] := by
  exact runtime.runRounds_complete_or_pending_empty
    (fun (service : IdealCommitments Bool Nat (Option Bool)) owner slot value =>
      (service.sealValue owner slot value).state) runtime.handle [false, true] 4 policies
    (runtime.messageApplication.reserveInclusion reserved base) reserved
    (runtime.messageApplication.reserveInclusion_service reserved base) 1 initial next
    (by decide) hnext

private def prepared : runtime.messageApplication.PolicyExecution :=
  { initial with native :=
    { initial.native with
      application.service := (initial.native.application.service.sealValue false 0
        (some true)).state
      pool := (initial.native.pool.submit false (.commitment 0 (false, 0))).2 } }

/-- Five inclusions at the end of the second round cover the initial canonical
packet and every possible arrival from two arbitrary roster polls. Earlier
wire actions may deliver packets and players may react before inclusion. -/
theorem delayed_service_completes_ready_commitment
    (policies : Bool → runtime.messageApplication.PlayerPolicy)
    (base : runtime.messageApplication.WirePolicy)
    (next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈ (runtime.roundDriver.runRounds [false, true] 5 policies
      (runtime.messageApplication.reserveInclusion (fun turn => decide (6 ≤ turn % 12)) base)
        2 prepared).support) :
    next.native.application.visible.completed 0 = true := by
  exact runtime.runRounds_ready_commitment_completed [false, true] 5 policies
    (runtime.messageApplication.reserveInclusion (fun turn => decide (6 ≤ turn % 12)) base)
    (fun turn => decide (6 ≤ turn % 12))
    (runtime.messageApplication.reserveInclusion_service _ base)
    1 prepared next (by decide) (by decide) false 0 0 [] (some true)
    rfl List.mem_cons_self rfl rfl hnext

/-- A player reacts in the second round to a packet delivered while the ledger
is still empty. Reserved inclusion then drains both rounds' submissions. -/
theorem pending_reaction_before_reserved_inclusion :
    ((runtime.roundDriver.round [false, true] 4 players wire initial).bind
      (runtime.roundDriver.round [false, true] 4 players wire)).map (fun execution =>
        (execution.native.pool.pending.length, execution.native.pool.ledger.length,
          (execution.principalHistory true).map (fun entry =>
            (entry.beforeView.messages.inbox.isEmpty, entry.beforeView.messages.ledger.isEmpty)),
          execution.native.application.service.lookup (true, 7))) =
      FinDist.pure (0, 2, [(true, true), (false, true)], some (some false)) := by
  unfold MessageApplication.RoundDriver.round
  simp only [List.map_cons, List.map_nil,
    List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
    runPolicies, invoke, players, wire, wireEnvironment, reserveInclusion, reserved,
    playerStep, environmentPolicyStep, advance, PlayerCommand.toAction,
    EnvironmentPolicyCommand.toAction, MessageApplication.step,
    SealedResolution.messageApplication, FinDist.map_pure, FinDist.pure_bind]
  dsimp [initial, PolicyExecution.initial, State.initial, State.observe, State.environmentView,
    MessagePool.observe, MessagePool.empty, MessagePool.submit, MessagePool.deliver,
    MessagePool.lookup]
  simp [WireCommand.toEnvironmentCommand, environmentPolicyStep,
    advance, EnvironmentPolicyCommand.toAction, MessageApplication.step,
    SealedResolution.messageApplication, State.environmentView,
    MessagePool.deliver, MessagePool.lookup, includePending, MessagePool.includeApplication,
    MessagePool.includePending, MessagePool.removeFirst, malformed_rejected,
    SealedResolution.initial, IdealCommitments.empty, IdealCommitments.sealValue,
    IdealCommitments.lookup]

/-- With period two, the first round remains unreserved and every service call
of the second round is reserved. -/
theorem period_two_delays_until_second_round :
    SealedResolution.periodicFinalReservation 4 2 0 = false ∧
      (List.range' 5 4).countP
        (SealedResolution.periodicFinalReservation 4 2) = 4 := by
  decide

end InteractionTests.SealedResolutionService
