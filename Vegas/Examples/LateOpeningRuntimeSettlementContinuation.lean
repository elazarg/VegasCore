/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBindingObservation

/-! # Exact complete continuation after the sender inclusion lottery

The actual eighteen-command suffix first settles Alice's pending pool and
samples Bob's observation, then retains Bob's original current response and
every later raw policy. The singleton opening gives an exact mixture of
successful and failed publication continuations. Genuine private opening
representations preserve the whole payoff law after Alice's last callback;
their private recall remains present in the actual execution.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSettlementContinuation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLateAcceptance LateOpeningRuntimeLatePrefixKernel
  LateOpeningRuntimeLateResponseKernel LateOpeningRuntimeBindingObservation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def receiverCompletion (players : Player → app.Policy) (execution : app.Execution) :
    PMF app.Execution :=
  (app.invoke players bob execution).bind
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 14)

def settlementCompletion (players : Player → app.Policy) (execution : app.Execution) :
    PMF app.Execution :=
  (settlementKernel weight nonnegative execution).bind
    (receiverCompletion weight nonnegative players)

/-- The actual binding activation precedes the original receiver response
and its complete fourteen-command continuation. -/
theorem receiver_suffix (players : Player → app.Policy) (execution : app.Execution)
    (cursor : execution.environmentRecall.length = 11) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 15 execution =
      (execution.environmentStep app (.activate bob)).bind
        (receiverCompletion weight nonnegative players) := by
  rw [ReactiveApplication.runRounds, ReactiveApplication.round,
    LateOpeningRuntimeService.scheduler, cursor]
  change ((PMF.pure (.activate bob : app.Command)).bind
    (fun command => app.dispatch players command execution)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch, PMF.bind_bind]
  rfl

/-- This is the original whole runtime suffix for every raw pending pool. -/
theorem whole_suffix_law (players : Player → app.Policy) (execution : app.Execution)
    (cursor : execution.environmentRecall.length = 8) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18 execution =
      settlementCompletion weight nonnegative players execution := by
  rw [show 18 = 3 + 15 from rfl, app.runRounds_add]
  unfold settlementCompletion
  rw [← settlement_activation weight nonnegative players execution cursor, PMF.bind_bind]
  apply bind_congr_on_support
  intro before reached
  apply receiver_suffix weight nonnegative players before
  rw [app.runRounds_environmentRecall_length
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 3 execution before reached,
      cursor]

/-- The full execution mixture retains all current and future receiver
responses; it is not a replacement by a Safe-or-guess action abstraction. -/
theorem canonical_completion_law (players : Player → app.Policy)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    settlementCompletion weight nonnegative players (beforeLottery bit label slot seen) =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (receiverCompletion weight nonnegative players (answerDecision bit label slot seen))
        (mix (1 / 2) (by norm_num) (by norm_num)
          (receiverCompletion weight nonnegative players
            (failedAnswerDecision bit label slot seen true))
          (receiverCompletion weight nonnegative players
            (failedAnswerDecision bit label slot seen false))) := by
  unfold settlementCompletion settlementKernel
  rw [beforeLottery_pending]
  change ((MessageNetwork.chooseWithOutside weight nonnegative {(alice, 0)}).bind
    (branchLaw (beforeLottery bit label slot seen))).bind _ = _
  rw [MessageNetwork.chooseWithOutside]
  simp only [Finset.card_singleton]
  simp only [MessageNetwork.chooseUniform_singleton, mix_bind, PMF.pure_bind,
    included_branch_law, omitted_branch_law]

/-- After Alice's last response, private aliases preserve the exact
settlement payoff distribution against arbitrary original future policies. -/
theorem completion_payoff_law_eq (players : Player → app.Policy)
    (first second : app.Execution) (later : 8 ≤ first.environmentRecall.length)
    (same : first.eraseRecall app alice = second.eraseRecall app alice)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (who : Player) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18 first).map
      (fun final => LateOpeningRuntimeNash.payoff reward forfeit sample deposit
        (app.finished final) who) =
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18 second).map
      (fun final => LateOpeningRuntimeNash.payoff reward forfeit sample deposit
        (app.finished final) who) := by
  have laws := app.continuation_eq_of_erasedRecall_eq
    (LateOpeningRuntimeService.scheduler weight nonnegative) 8 alice
      (LateOpeningRuntimeAliceIncentive.alice_absent weight nonnegative) players 18
        first second later same
  have mapped := congrArg (fun law : PMF app.Execution => law.map
    (fun final => LateOpeningRuntimeNash.payoff reward forfeit sample deposit
      (app.finished final) who)) laws
  simpa only [PMF.map_comp, Function.comp_def,
    LateOpeningRuntimeAliceOpeningAliases.payoff_eraseRecall] using mapped

/-- A genuine first response and actual silent retry have the exact
canonical whole payoff law, allowing every private first-response alias. -/
theorem genuine_first_payoff_law (players : Player → app.Policy)
    (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) (seen : Bool)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (who : Player) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
      ((finalDecision bit label ⟨some submission⟩
        (if seen then {(alice, 0)} else ∅)).respond app alice ⟨none⟩)).map
          (fun final => LateOpeningRuntimeNash.payoff reward forfeit sample deposit
            (app.finished final) who) =
      (settlementCompletion weight nonnegative players (beforeLottery bit label 0 seen)).map
        (fun final => LateOpeningRuntimeNash.payoff reward forfeit sample deposit
          (app.finished final) who) := by
  rw [← whole_suffix_law weight nonnegative players _ (by rfl :
    (beforeLottery bit label 0 seen).environmentRecall.length = 8)]
  apply completion_payoff_law_eq weight nonnegative players
  · change 8 ≤ (finalDecision bit label ⟨some submission⟩
      (if seen then {(alice, 0)} else ∅)).environmentRecall.length
    rw [final_cursor]
  · exact genuine_retry_erased weight nonnegative bit label submission genuine seen

/-- Every genuine final opening after earlier silence also preserves the
canonical full payoff distribution against the original receiver policies. -/
theorem genuine_final_payoff_law (players : Player → app.Policy)
    (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceOpeningContinuation.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label)
        submission)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (who : Player) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
      ((finalDecision bit label ⟨none⟩ ∅).respond app alice ⟨some submission⟩)).map
        (fun final => LateOpeningRuntimeNash.payoff reward forfeit sample deposit
          (app.finished final) who) =
      (settlementCompletion weight nonnegative players (beforeLottery bit label 1 false)).map
        (fun final => LateOpeningRuntimeNash.payoff reward forfeit sample deposit
          (app.finished final) who) := by
  rw [← whole_suffix_law weight nonnegative players _ (by rfl :
    (beforeLottery bit label 1 false).environmentRecall.length = 8)]
  apply completion_payoff_law_eq weight nonnegative players
  · change 8 ≤ (finalDecision bit label ⟨none⟩ ∅).environmentRecall.length
    rw [final_cursor]
  · exact genuine_final_erased weight nonnegative bit label submission genuine

end Vegas.Examples.LateOpeningRuntimeSettlementContinuation
