/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryService
import VegasTests.WindowedSourceCoverage

/-! # Delivery and raw reaction in a generated windowed application

The checked persistent-disclosure runtime is used directly. Its first owner
registers an arbitrary Boolean privately and submits the generated opaque
binding handle. Delivery exposes that envelope to the other player before the
ordinary inclusion slot, so an unrestricted replacement can replay it during
the intervening reaction invocation.
-/

noncomputable section

namespace VegasTests.WindowedDelivery

open Vegas Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability
open VegasTests.GeneratedPersistentDisclosure
open VegasTests.WindowedSourceCoverage

abbrev Player := TestPlayer

def roster : List Player := [0, 1]

def recipients : List Player := [1]

def ownerBase (secret : Bool) : runtime.application.PlayerPolicy :=
  fun history _ => FinDist.pure <|
    match history with
    | [] => .privateCommand (.register 0 ⟨.bool, secret⟩)
    | _ => .submit (.binding 0 (0, 0))

/-- The raw observer waits through its two ordinary polls, then reacts to the
delivery by replaying the opaque envelope. -/
def observerReplacement : runtime.application.PlayerPolicy :=
  fun history view =>
    if history.length = 2 then
      match view.messages.known? (0, 0) with
      | some _ => FinDist.pure (.replay (0, 0))
      | none => FinDist.pure .wait
    else FinDist.pure .wait

def deliveryPlayers (secret : Bool) : Player → runtime.application.PlayerPolicy :=
  fun who => if who = 1 then observerReplacement
    else runtime.deliveryBlockPlayer who (ownerBase secret)

def environment : runtime.application.EnvironmentPolicy :=
  runtime.deliveryBlockEnvironment roster recipients

def reactionPrefix : List (@Invocation Player) :=
  [.player 0, .player 0, .player 1, .player 1, .environment, .player 0, .player 1]

def throughNormal : List (@Invocation Player) := reactionPrefix ++ [.environment]

theorem schedule_starts_with_reaction_prefix :
    WindowedApplication.deliveryBlockInvocations roster recipients =
      throughNormal ++
        [.environment, .player 0, .environment, .player 1, .environment] := rfl

def opaqueMessage : Message Player (ApplicationImage.Payload Player simpleExpr) :=
  ⟨(0, 0), .binding 0 (0, 0)⟩

private def afterPlayer (before : runtime.application.PolicyExecution) (who : Player)
    (command : runtime.application.PlayerCommand) (native : runtime.application.State) :
    runtime.application.PolicyExecution :=
  { before with
    native := native
    principalHistory := fun other => if other = who then
      before.principalHistory who ++ [⟨State.observe runtime.application before.native who,
        command⟩] else before.principalHistory other
    nativeTrace := before.nativeTrace ++ (command.toAction runtime.application who).toList }

private def registered (secret : Bool) : runtime.application.PolicyExecution :=
  afterPlayer initial 0 (.privateCommand (.register 0 ⟨.bool, secret⟩))
    { initial.native with
      application := runtime.application.privateStep initial.native.application 0
        (.register 0 ⟨.bool, secret⟩) }

private theorem register_step (secret : Bool) :
    runtime.application.playerStep 0 initial (.privateCommand (.register 0 ⟨.bool, secret⟩)) =
      FinDist.pure (registered secret) := by
  simp only [MessageApplication.playerStep, MessageApplication.advance,
    PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind]
  rfl

private def submitted (secret : Bool) : runtime.application.PolicyExecution :=
  afterPlayer (registered secret) 0 (.submit opaqueMessage.payload)
    { (registered secret).native with
      pool := ((registered secret).native.pool.submit 0 opaqueMessage.payload).2 }

private def waited (who : Player) (before : runtime.application.PolicyExecution) :
    runtime.application.PolicyExecution := afterPlayer before who .wait before.native

private def polled (secret : Bool) := waited 1 (waited 1 (submitted secret))

private theorem polling_law (secret : Bool) :
    runtime.application.runPolicies (deliveryPlayers secret) environment
      [.player 0, .player 0, .player 1, .player 1] initial =
        FinDist.pure (polled secret) := by
  have hfirst : deliveryPlayers secret 0 (initial.principalHistory 0)
      (State.observe runtime.application initial.native 0) =
        FinDist.pure (.privateCommand (.register 0 ⟨.bool, secret⟩)) := rfl
  have hsecond : deliveryPlayers secret 0 ((registered secret).principalHistory 0)
      (State.observe runtime.application (registered secret).native 0) =
        FinDist.pure (.submit opaqueMessage.payload) := by
    dsimp [deliveryPlayers, registered, afterPlayer, WindowedApplication.deliveryBlockPlayer,
      ownerBase, opaqueMessage, initial, ApplicationPlan.windowedInitialExecution,
      PolicyExecution.initial, State.observe, WindowedApplication.application]
    rfl
  have hsubmit : runtime.application.playerStep 0 (registered secret)
      (.submit opaqueMessage.payload) = FinDist.pure (submitted secret) := by
    simp only [MessageApplication.playerStep, MessageApplication.advance,
      PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind]
    rfl
  rw [MessageApplication.runPolicies, MessageApplication.invoke, hfirst, FinDist.pure_bind,
    register_step, FinDist.pure_bind, MessageApplication.runPolicies,
    MessageApplication.invoke, hsecond, FinDist.pure_bind, hsubmit, FinDist.pure_bind]
  simp +unfoldPartialApp only [MessageApplication.runPolicies, MessageApplication.invoke,
    MessageApplication.playerStep, MessageApplication.advance, PlayerCommand.toAction]
  repeat' erw [FinDist.pure_bind]
  rfl

private def delivered (secret : Bool) : runtime.application.PolicyExecution :=
  { polled secret with
    native := { (polled secret).native with
      pool := ((polled secret).native.pool.deliver 1 (0, 0)).state }
    environmentHistory := (polled secret).environmentHistory ++
      [⟨State.environmentView runtime.application (polled secret).native, .deliver 1 (0, 0)⟩]
    nativeTrace := (polled secret).nativeTrace ++ [.deliver 1 (0, 0)] }

private theorem delivery_law (secret : Bool) :
    runtime.application.invoke (deliveryPlayers secret) environment (polled secret)
      .environment = FinDist.pure (delivered secret) := by
  have hdeliver : environment (polled secret).environmentHistory
      (State.environmentView runtime.application (polled secret).native) =
        FinDist.pure (.deliver 1 (0, 0)) := by
    dsimp [environment, polled, waited, submitted, registered, afterPlayer]
    rfl
  rw [MessageApplication.invoke, hdeliver, FinDist.pure_bind]
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind]
  rfl

private def reacted (secret : Bool) : runtime.application.PolicyExecution :=
  let before := waited 0 (delivered secret)
  afterPlayer before 1 (.replay (0, 0))
    { before.native with pool := (before.native.pool.replay 1 (0, 0)).state }

private theorem reaction_law (secret : Bool) :
    runtime.application.runPolicies (deliveryPlayers secret) environment
      [.player 0, .player 1] (delivered secret) = FinDist.pure (reacted secret) := by
  have hwait : deliveryPlayers secret 0 ((delivered secret).principalHistory 0)
      (State.observe runtime.application (delivered secret).native 0) = FinDist.pure .wait := by
    dsimp [deliveryPlayers]
    exact runtime.deliveryBlockPlayer_reaction 0 (ownerBase secret) _ _ (by rfl)
  have hreplay : deliveryPlayers secret 1 ((waited 0 (delivered secret)).principalHistory 1)
      (State.observe runtime.application (waited 0 (delivered secret)).native 1) =
        FinDist.pure (.replay (0, 0)) := by
    dsimp [deliveryPlayers, observerReplacement, waited, delivered, polled, submitted,
      registered, afterPlayer]
    rfl
  rw [MessageApplication.runPolicies, MessageApplication.invoke, hwait, FinDist.pure_bind]
  have hwaited : runtime.application.playerStep 0 (delivered secret) .wait =
      FinDist.pure (waited 0 (delivered secret)) := runtime.application.playerStep_wait _ _
  rw [hwaited, FinDist.pure_bind, MessageApplication.runPolicies, MessageApplication.invoke,
    hreplay, FinDist.pure_bind]
  simp +unfoldPartialApp only [MessageApplication.runPolicies, FinDist.bind_pure,
    MessageApplication.playerStep, MessageApplication.advance,
    PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind]
  rfl

/-- Merely reaching the reaction coordinate does not trigger replay: without a
delivered or public copy of the envelope, the observation-driven replacement
waits. -/
theorem observer_waits_without_delivery :
    observerReplacement
      [⟨State.observe runtime.application initial.native 1, .wait⟩,
       ⟨State.observe runtime.application initial.native 1, .wait⟩]
      (State.observe runtime.application initial.native 1) = FinDist.pure .wait := by
  simp [observerReplacement, State.observe, initial,
    ApplicationPlan.windowedInitialExecution, MessageApplication.PolicyExecution.initial,
    MessageApplication.State.initial, MessagePool.observe, MessagePool.View.known?,
    MessagePool.empty]

/-- At the reaction boundary the observer has the pending opaque handle in its
local inbox, while nothing has entered the public ledger. Both facts are
independent of the privately registered Boolean. The recorded raw command is
the observer's replay of that handle. -/
theorem reaction_observes_only_opaque_handle (secret : Bool) :
    (runtime.application.runPolicies (deliveryPlayers secret) environment reactionPrefix
      initial).map (fun out =>
        (out.native.pool.inbox 1, out.native.pool.ledger,
          (out.principalHistory 1).getLast?.map (·.command))) =
      FinDist.pure ([opaqueMessage], [], some (.replay (0, 0))) := by
  change (runtime.application.runPolicies (deliveryPlayers secret) environment
    ([.player 0, .player 0, .player 1, .player 1] ++
      [.environment, .player 0, .player 1]) initial).map _ = _
  rw [MessageApplication.runPolicies_append, polling_law, FinDist.pure_bind]
  rw [MessageApplication.runPolicies, delivery_law, FinDist.pure_bind, reaction_law,
    FinDist.map_pure]
  rfl

/-- Normal head service still includes the owner's original pending envelope
after the observer's unrestricted replay. The replay remains pending as a
second copy, while the first copy becomes public. -/
theorem replay_before_normal_inclusion (secret : Bool) :
    (runtime.application.runPolicies (deliveryPlayers secret) environment throughNormal
      initial).map (fun out =>
        (out.native.pool.inbox 1, out.native.pool.ledger, out.native.pool.pending)) =
      FinDist.pure ([opaqueMessage], [opaqueMessage], [opaqueMessage]) := by
  change (runtime.application.runPolicies (deliveryPlayers secret) environment
    ([.player 0, .player 0, .player 1, .player 1] ++
      [.environment, .player 0, .player 1, .environment]) initial).map _ = _
  rw [MessageApplication.runPolicies_append, polling_law, FinDist.pure_bind]
  rw [MessageApplication.runPolicies, delivery_law, FinDist.pure_bind]
  change (runtime.application.runPolicies (deliveryPlayers secret) environment
    ([.player 0, .player 1] ++ [.environment]) (delivered secret)).map _ = _
  rw [MessageApplication.runPolicies_append, reaction_law, FinDist.pure_bind]
  have hinclude : environment (reacted secret).environmentHistory
      (State.environmentView runtime.application (reacted secret).native) =
        FinDist.pure (.include (0, 0)) := by
    cases secret <;> rfl
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, hinclude,
    FinDist.pure_bind, FinDist.bind_pure, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.map_pure]
  rfl

end VegasTests.WindowedDelivery

/-- info: 'VegasTests.WindowedDelivery.reaction_observes_only_opaque_handle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedDelivery.reaction_observes_only_opaque_handle

/-- info: 'VegasTests.WindowedDelivery.replay_before_normal_inclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedDelivery.replay_before_normal_inclusion
