/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.Payoffs
import Vegas.Examples.MonitoredGuessing.NativePayoff

/-! # Native settlement readout for the source return-table family

The execution graph is shared; the terminal decoder is compiled from the
source's declared table. The initialized law below retains the private input,
public results and actual net payoff vector. It proves zero charge on that
law, without an equilibrium or escrow-implementation claim.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def nativeTableUtility (table : PayoffTable) (charge : ℝ) (who : Player)
    (state : nativeApp.ProtocolState) : ℝ :=
  state.elim 0 fun control =>
    (table (nativeResults control.execution.application.config) who : ℝ) -
      if who = alice ∧ rejectedAlice control.execution.receipts then charge else 0

def tableObservation (table : PayoffTable) (charge : ℝ)
    (observation : Bool × Results × Bool) : Bool × Results × (Player → ℝ) :=
  (observation.1, observation.2.1, fun who => (table observation.2.1 who : ℝ) -
    if who = alice ∧ observation.2.2 then charge else 0)

theorem tableObservation_guessing (table : PayoffTable) (charge : ℝ) (bit guess : Bool) :
    tableObservation table charge (guessingObservation bit guess) =
      (bit, ⟨.success bit, guessResult guess⟩,
        fun who => (table ⟨.success bit, guessResult guess⟩ who : ℝ)) := by
  simp only [tableObservation, guessingObservation, Bool.false_eq_true, and_false,
    ↓reduceIte, sub_zero]

/-- The prescribed native behavior pays the literal source table, with no
runtime charge, for every receiver mixture and every charge value. Rationality
of those choices is a separate property of the selected payoff table. -/
theorem native_initialized_table_payoffs (table : PayoffTable) (charge : ℝ)
    (profile : Profile nativeModel.behavioralSignature) (guesses : FinDist Bool)
    (alicePolicy : profile alice = nativeAliceBehavior)
    (watcherPolicy : profile watcher = nativeWatcherBehavior)
    (atQuiet : profile bob quietBobSite.1 = nativeGuessBehavior guesses quietBobSite.1) :
    (nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map
      (fun history => ((nativeObservation history.state).1,
        (nativeObservation history.state).2.1,
        fun who => nativeTableUtility table charge who history.state)) =
      (FinDist.uniformOfFintype (α := Bool)).bind (fun bit =>
        guesses.map (fun guess => (bit, ⟨.success bit, guessResult guess⟩,
          fun who => (table ⟨.success bit, guessResult guess⟩ who : ℝ)))) := by
  have law := native_initialized_observation profile guesses alicePolicy watcherPolicy atQuiet
  have same : (nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map
      (fun history => ((nativeObservation history.state).1,
        (nativeObservation history.state).2.1,
        fun who => nativeTableUtility table charge who history.state)) =
      (((nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map History.state).map
        nativeObservation).map (tableObservation table charge) := by
    simp only [FinDist.map_comp, Function.comp_def]
    apply FinDist.map_congr_of_eq_on_support
    intro history supported
    have stateSupported : history.state ∈
        ((nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map History.state).support :=
      FinDist.support_map .. ▸ ⟨history, supported, rfl⟩
    obtain ⟨control, stateEq⟩ := native_initialized_some profile history.state stateSupported
    rw [stateEq]
    rfl
  rw [same, law]
  simp only [FinDist.map_bind, FinDist.map_comp, Function.comp_def,
    tableObservation_guessing]

end Vegas.Examples.MonitoredGuessing
