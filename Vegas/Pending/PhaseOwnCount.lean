/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCountMenu
import Interaction.ReactivePolicyInvariant

/-! # One author's count soundness against arbitrary foreign policies -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

def OwnCountClean (owner : Player) (execution : (app).Execution) : Prop :=
  CountRecall runtime leaks execution ∧
    ∀ message ∈ execution.network.inputs, message.sender = owner →
      permits execution.network.inputs message = true

theorem ownCountClean_respond (owner actor : Player) (execution : (app).Execution)
    (action : (app).Action) (clean : OwnCountClean runtime leaks owner execution)
    (allowed : actor = owner → action.transmission = none ∨
      OnePacketResponse runtime leaks owner (execution.recall owner)
        (execution.observe app owner) action) :
    OwnCountClean runtime leaks owner (execution.respond app actor action) := by
  refine ⟨countRecall_respond runtime leaks execution clean.1 actor action, ?_⟩
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact clean.2
  | some material =>
      obtain ⟨inputs, fresh, kept⟩ := permits_respond runtime leaks execution clean.1 actor
        material
      intro message member authored
      rw [inputs] at member
      rcases List.mem_append.mp member with old | new
      · rw [kept message old]
        exact clean.2 message old authored
      · have actual := List.mem_singleton.mp new
        subst message
        have same : actor = owner := authored
        subst actor
        rcases allowed rfl with silent | ⟨other, sent, permitted⟩
        · cases silent
        · cases Option.some.inj sent
          rw [fresh]
          exact permitted

theorem ownCountClean_policyInvariant (owner : Player) (players : Player → (app).Policy)
    (covered : ∀ past view action, action ∈ (players owner past view).support →
      action.transmission = none ∨ OnePacketResponse runtime leaks owner past view action) :
    (app).PolicyInvariant players (OwnCountClean runtime leaks owner) where
  respond execution actor action clean supported := by
    apply ownCountClean_respond runtime leaks owner actor execution action clean
    intro same
    subst actor
    exact covered _ _ action supported
  environment execution next command clean moved := by
    refine ⟨⟨(app).environment_inputRecall execution next command clean.1.1 moved,
      (app).environment_serialRecall execution next command clean.1.2.1 moved, ?_⟩, ?_⟩
    · intro observer
      rw [(app).environmentStep_inputs execution next command moved,
        (app).environmentStep_nextSerial execution next command moved]
      exact clean.1.2.2 observer
    · rw [(app).environmentStep_inputs execution next command moved]
      exact clean.2

theorem ownCountClean_runRounds (owner : Player) (players : Player → (app).Policy)
    (covered : ∀ past view action, action ∈ (players owner past view).support →
      action.transmission = none ∨ OnePacketResponse runtime leaks owner past view action)
    (scheduler : (app).Scheduler) (count : Nat) (before after : (app).Execution)
    (clean : OwnCountClean runtime leaks owner before)
    (reached : after ∈ ((app).runRounds scheduler players count before).support) :
    OwnCountClean runtime leaks owner after :=
  (ownCountClean_policyInvariant runtime leaks owner players covered).runRounds scheduler count
    before after clean reached

end Vegas.EventGraphRuntime.PhaseCount
