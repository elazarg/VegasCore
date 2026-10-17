/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingInitializedHalf
import Interaction.ReactiveRecovery

/-! # Initialized quiet prefixes with the original continuation policies -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- Force only an owner's first callback to be silent. Every callback with
a previous own response uses the original full physical policy. -/
def quietFirstPolicy (policy : app.Policy) : app.Policy
  | [], _ => PMF.pure ⟨none⟩
  | entry :: past, view => policy (entry :: past) view

def quietAlicePlayers (players : Player → app.Policy) : Player → app.Policy :=
  Function.update players alice (quietFirstPolicy (players alice))

theorem quietAlicePlayers_aliceFirst (players : Player → app.Policy) :
    quietAlicePlayers players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩ := by
  rw [quietAlicePlayers, Function.update_self]
  rfl

theorem quietAlicePlayers_bob (players : Player → app.Policy) :
    quietAlicePlayers players bob = players bob :=
  Function.update_of_ne (by decide : bob ≠ alice) _ _

/-- The first-response override has no effect on any later raw continuation.
Own recall grows under every response and is retained by every scheduler step. -/
theorem quietAlicePlayers_run_after_response (selected : app.Scheduler)
    (players : Player → app.Policy) (count : Nat) (execution : app.Execution)
    (responded : 0 < (execution.recall alice).length) :
    app.runRounds selected (quietAlicePlayers players) count execution =
      app.runRounds selected players count execution := by
  have invariant : app.PolicyInvariant players
      (fun current => 0 < (current.recall alice).length) := by
    constructor
    · intro current actor response valid _chosen
      exact valid.trans_le (app.respond_recall_prefix current actor alice response).length_le
    · intro current next command valid moved
      rw [app.environmentStep_recall current next command moved]
      exact valid
  symm
  apply invariant.runRounds_congr (quietAlicePlayers players) _ selected count execution responded
  intro current valid who
  by_cases same : who = alice
  · subst who
    rw [quietAlicePlayers, Function.update_self]
    cases recalled : current.recall alice with
    | nil => simp only [recalled, List.length_nil] at valid
             omega
    | cons entry past => rfl
  · rw [quietAlicePlayers, Function.update_of_ne same]

theorem quietAfterTwo_alice_recall_nonempty : 0 < (quietAfterTwo.recall alice).length := by
  change 0 < (((bobFirst ⟨none⟩).respond app bob ⟨none⟩).recall alice).length
  rw [app.respond_recall_length]
  have recalled : ((bobFirst ⟨none⟩).recall alice).length = 1 := by
    change ((aliceFirst.respond app alice ⟨none⟩).recall alice).length = 1
    rw [app.respond_recall_length, aliceFirst_recall]
    simp only [List.length_nil, ite_true, Nat.zero_add]
  rw [recalled]
  omega

theorem quiet_first_two_rounds_integrated (players : Player → app.Policy)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩) :
    app.runRounds scheduler players 2 initialExecution = PMF.pure quietAfterTwo := by
  rw [four_seed_execution]
  have constant : (fun bits => app.runRounds (family (seedOfBits bits)) players 2
      initialExecution) = fun _ => PMF.pure quietAfterTwo := by
    funext bits
    exact quiet_first_two_rounds players (seedOfBits bits) aliceWait bobWait
  rw [constant]
  exact PMF.bind_const _ _

/-- Artificially initializing Alice with WAIT gives exactly the original
continuation from Bob's quiet prefix after Bob also waits. -/
theorem initialized_quietAlice_tail (players : Player → app.Policy)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (count : Nat) :
    app.runRounds scheduler (quietAlicePlayers players) (2 + count) initialExecution =
      app.runRounds scheduler players count quietAfterTwo := by
  rw [app.runRounds_add, quiet_first_two_rounds_integrated (quietAlicePlayers players)
    (quietAlicePlayers_aliceFirst players) (by rw [quietAlicePlayers_bob]; exact bobWait),
    PMF.pure_bind]
  exact quietAlicePlayers_run_after_response scheduler players count quietAfterTwo
    quietAfterTwo_alice_recall_nonempty

theorem quietAlicePlayers_counted
    (profile : ∀ who, countedModel.BehavioralPolicy who) (who : Player)
    (past : List app.PlayerEntry) (view : app.PlayerView) (response : app.Action)
    (supported : response ∈ (quietAlicePlayers
      (countedMenu.decodeProfile initial horizon scheduler profile) who past view).support) :
    response ∈ countedMenu.actions who past view := by
  by_cases same : who = alice
  · subst who
    rw [quietAlicePlayers, Function.update_self] at supported
    cases past with
    | nil =>
        change response ∈ (PMF.pure ⟨none⟩).support at supported
        cases (PMF.mem_support_pure_iff _ _).mp supported
        exact PhaseCount.silence_onePacket runtime leaks bounds alice [] view
    | cons entry past =>
        exact countedMenu.decode_embedPolicy_covered initial horizon scheduler alice
          (profile alice) (entry :: past) view response supported
  · rw [quietAlicePlayers, Function.update_of_ne same] at supported
    exact countedMenu.decode_embedPolicy_covered initial horizon scheduler who
      (profile who) past view response supported

def quietAliceCountedProfile (profile : ∀ who, countedModel.BehavioralPolicy who)
    (who : Player) : countedModel.BehavioralPolicy who :=
  countedMenu.restrictPolicy initial horizon scheduler who
    (quietAlicePlayers (countedMenu.decodeProfile initial horizon scheduler profile) who)

theorem decode_quietAliceCountedProfile (profile : ∀ who, countedModel.BehavioralPolicy who) :
    countedMenu.decodeProfile initial horizon scheduler (quietAliceCountedProfile profile) =
      quietAlicePlayers (countedMenu.decodeProfile initial horizon scheduler profile) := by
  funext who
  exact countedMenu.decode_restrictPolicy_of_covered initial horizon scheduler who _
    (quietAlicePlayers_counted profile who)

end Vegas.Examples.CommitSeedSignalling
