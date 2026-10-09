/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeServiceContract
import Vegas.Examples.LateOpeningRuntimeUtility
import Vegas.Game.AsyncServiceRawNash

/-! # Exact Nash correspondence for the concrete partially public runtime

The initialized three-instruction program compiles to the public two-late
builder. Its full bounded raw menu admits malformed packets and both late
opening choices. No extra receipt, opportunity or payoff-range hypothesis is
assumed here: the concrete service and utility bounds supply them. These are
Nash results; they do not claim sequential equilibrium of the clients.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeNash

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeUtility

abbrev model (weight : ℝ) (nonnegative : 0 ≤ weight) :=
  rawMenu.information initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)

def payoff (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ) :=
  TerminalAudit.utility (nativeBaseUtility reward forfeit)
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks sample) deposit

def settlement (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ) :=
  TerminalAudit.settlement (nativeBaseUtility reward forfeit)
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks sample) deposit

def clients (weight : ℝ) (nonnegative : 0 ≤ weight)
    (admission : CommitmentInterface program)
    (source : Profile (setup.informationModel admission).behavioralSignature) :
    Profile (model weight nonnegative).behavioralSignature :=
  (service weight nonnegative).clientProfile admission rawMenu
    (firstTurnTiming setup 1 .sequential) source

theorem realized_payoff_bounds {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : ∀ who, 0 ≤ deposit who)
    (who : Player) (output : Option (State simpleExpr program.terminalCtx)) (charged : Bool) :
    -forfeit - deposit who ≤ output.elim 0 (fun terminal =>
      sourceUtility reward forfeit terminal who) - (if charged then deposit who else 0) ∧
    output.elim 0 (fun terminal => sourceUtility reward forfeit terminal who) -
      (if charged then deposit who else 0) ≤
        (-forfeit - deposit who) +
          (forfeit + reward + 1 + deposit alice + deposit bob) := by
  have aliceDeposit := depositNonnegative alice
  have bobDeposit := depositNonnegative bob
  have selectedDeposit := depositNonnegative who
  have depositBound : deposit who ≤ deposit alice + deposit bob := by
    fin_cases who
    · change deposit alice ≤ deposit alice + deposit bob
      linarith
    · change deposit bob ≤ deposit alice + deposit bob
      linarith
  have baseBounds : -forfeit ≤ output.elim 0 (fun terminal =>
      sourceUtility reward forfeit terminal who) ∧
      output.elim 0 (fun terminal => sourceUtility reward forfeit terminal who) ≤ reward + 1 := by
    cases output with
    | none => simp only [Option.elim_none]; constructor <;> linarith
    | some terminal =>
        fin_cases who
        · change -forfeit ≤ sourceUtility reward forfeit terminal alice ∧
            sourceUtility reward forfeit terminal alice ≤ reward + 1
          obtain ⟨lower, upper⟩ := sourceUtility_alice_bounds rewardNonnegative
            forfeitNonnegative terminal
          exact ⟨lower, by linarith⟩
        · change -forfeit ≤ sourceUtility reward forfeit terminal bob ∧
            sourceUtility reward forfeit terminal bob ≤ reward + 1
          obtain ⟨lower, upper⟩ := sourceUtility_bob_bounds forfeitNonnegative reward terminal
          exact ⟨lower, by linarith⟩
  obtain ⟨lower, upper⟩ := baseBounds
  cases charged <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith

/-- Every concrete lottery weight and every source admission interface has
exact same-error Nash preservation and reflection for the first-opportunity
clients, against the entire bounded native raw menu. -/
theorem first_opportunity_nash_iff (weight : ℝ) (nonnegative : 0 ≤ weight)
    {reward forfeit : ℝ} (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (depositNonnegative : ∀ who, 0 ≤ deposit who)
    (admission : CommitmentInterface program)
    (error : ℝ) (source : Profile (setup.informationModel admission).behavioralSignature) :
    IsεNash ((model weight nonnegative).toBehavioralGameForm 53)
      (fun history who => payoff reward forfeit sample deposit history.state who) error
      (clients weight nonnegative admission source) ↔
    IsεNash ((setup.informationModel admission).toBehavioralGameForm 4)
      (fun history who => (setup.protocolReadout history.state).elim 0
        (fun terminal => sourceUtility reward forfeit terminal who)) error source := by
  exact (service weight nonnegative).isεNash_firstTurnClientProfile_iff admission
    setup.eventGraph.sequentialize_barrierOrdered parameter
    (forfeitUtility program forfeit (grossUtility reward)) sample authentic deposit
    depositNonnegative 1 (fun who => -forfeit - deposit who)
    (forfeit + reward + 1 + deposit alice + deposit bob)
    (realized_payoff_bounds rewardNonnegative forfeitNonnegative deposit depositNonnegative)
    error source

/-- The concrete clients preserve the complete typed store and the vector
of realized net payoffs for every source profile and authentic sampler. -/
theorem first_opportunity_settlement_law (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (admission : CommitmentInterface program)
    (source : Profile (setup.informationModel admission).behavioralSignature) :
    (((model weight nonnegative).runBehavioral
      (clients weight nonnegative admission source) 53).bind fun final =>
        (settlement reward forfeit sample deposit final.state).map fun payoffs =>
          (serviceSourceReadout setup .sequential deadline leaks final.state, payoffs)) =
      (setup.run (setup.decodeBehavioralProfile admission source)).map
        (fun terminal => (some terminal, sourceUtility reward forfeit terminal)) := by
  exact (service weight nonnegative).firstTurnClientProfile_settlement_law admission
    setup.eventGraph.sequentialize_barrierOrdered parameter
    (forfeitUtility program forfeit (grossUtility reward)) sample authentic deposit 1 source

end Vegas.Examples.LateOpeningRuntimeNash
