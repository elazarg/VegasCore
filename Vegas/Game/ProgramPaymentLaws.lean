/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProgramPayoffs
import Vegas.Compile.EventGraphScheduling

/-! # Joint execution and monetary receipt laws

The retained data includes the actual initial draw, the complete typed terminal
state and its public result. The compiled reader obtains money from native
terminal payouts. Pointwise payout correspondence and the terminal-state law
then preserve this entire joint distribution under every public scheduler.
These laws concern the existing completed source and ideal event executions;
they introduce no additional failure or exit behavior.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}

/-- All original execution coordinates retained alongside monetary receipts. -/
abbrev PaymentOutcome (program : SourceProgram Player L Γ O) :=
  State L Γ × State L program.terminalCtx × PublicOutcome program

/-- Source execution readout, including the initial state actually sampled. -/
def paymentObservation (program : SourceProgram Player L Γ O) (initial : State L Γ)
    (terminal : State L program.terminalCtx) : PaymentOutcome program × (Player → ℝ) :=
  ((initial, terminal, program.publicOutcome terminal),
    program.publicTransfers (program.publicOutcome terminal))

/-- Compiled execution readout with native executable payouts, retaining the
same initial state, complete decoded terminal state and public result. -/
def compiledPaymentObservation (program : SourceProgram Player L Γ O)
    (initial : State L Γ)
    (terminal : {config : (toEventGraph program).Config // config.cut.Terminal}) :
    PaymentOutcome program × (Player → ℝ) :=
  ((initial, terminalState program terminal,
      program.publicOutcome (terminalState program terminal)),
    fun who => (transferAmount (terminalPayouts program terminal) who : ℝ))

/-- Native payouts agree pointwise with program-computed transfers, so the
comparison preserves their correlation with all execution data. -/
theorem compiledPaymentObservation_eq (program : SourceProgram Player L Γ O)
    (initial : State L Γ)
    (terminal : {config : (toEventGraph program).Config // config.cut.Terminal}) :
    compiledPaymentObservation program initial terminal =
      paymentObservation program initial (terminalState program terminal) := by
  unfold compiledPaymentObservation paymentObservation publicTransfers
  rw [terminalPayouts_eq_source]
  rfl

/-- Public scheduling preserves the full joint execution and receipt law,
rather than only the marginal payout law or expected receipts. -/
theorem scheduled_payment_law (program : SourceProgram Player L Γ O)
    (scheduler : (toEventGraph program).PublicScheduler)
    (profile : BehavioralProfile program) (initial : State L Γ) :
    ((toEventGraph program).terminalOutcomes scheduler
        (compileEventProfile program profile) (encodeInputs initial)).map
        (compiledPaymentObservation program initial) =
      (program.run profile initial).map (paymentObservation program initial) := by
  have law := congrArg
    (fun distribution => distribution.map (paymentObservation program initial))
    (Vegas.scheduled_terminalState_law program scheduler profile initial)
  simpa only [PMF.map_comp, Function.comp_def, ← compiledPaymentObservation_eq] using law

namespace Setup

/-- Draw the initial state once and retain it jointly with the complete terminal
state, public outcome and every player's program-computed monetary receipt. -/
def paymentRun (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    PMF (PaymentOutcome setup.program × (Player → ℝ)) :=
  setup.initialLaw.bind fun initial =>
    (setup.program.run profile initial).map (paymentObservation setup.program initial)

/-- The full joint monetary law is preserved for any initial distribution and
public scheduler, including correlated private initial data. -/
theorem scheduled_setup_payment_law (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (profile : BehavioralProfile setup.program) :
    (setup.initialLaw.bind fun initial =>
      (setup.eventGraph.terminalOutcomes scheduler
          (compileEventProfile setup.program profile) (setup.eventInputs initial)).map
        (compiledPaymentObservation setup.program initial)) =
      setup.paymentRun profile := by
  unfold paymentRun
  apply bind_congr_on_support _
  intro initial _
  exact scheduled_payment_law setup.program scheduler profile initial

/-- Arbitrary valuations of the retained execution data yield identical joint
utility laws; the receipt readout can recover the monetary law from either side. -/
theorem scheduled_setup_payment_utility_law (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (profile : BehavioralProfile setup.program)
    (valuation : PaymentOutcome setup.program → Player → ℝ) :
    (setup.initialLaw.bind fun initial =>
      (setup.eventGraph.terminalOutcomes scheduler
          (compileEventProfile setup.program profile) (setup.eventInputs initial)).map
        (utilityReadout valuation ∘ compiledPaymentObservation setup.program initial)) =
      (setup.paymentRun profile).map (utilityReadout valuation) := by
  rw [← scheduled_setup_payment_law setup scheduler profile, PMF.map_bind]
  simp only [PMF.map_comp]

end Setup
end Vegas.SourceProgram
