/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeUtility

/-! # The concrete partially public late-opening game

The bounded raw information model and its audited payoff and settlement laws
share one concrete game owner, independent of equilibrium proof imports.
-/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeGame

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

end Vegas.Examples.LateOpeningRuntimeGame
