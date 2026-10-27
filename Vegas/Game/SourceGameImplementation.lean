/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ConcurrentRawSequentialPreservation

/-! # Finite target games with source readouts

These data express the conclusion of source sequential-equilibrium preservation:
a target assessment, the initialized joint law and clean settlement. They impose
no network or operational semantics. In particular, existence of such a game
does not assert blockchain implementation; under finite source histories, the
source game itself can qualify.

A concrete runtime theorem must derive its protocol, information and readers
from actual execution. The runtime design is in `docs/se-runtime-design.md`.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A finite target game with source-state readout and settlement flags.
These fields do not specify an operational implementation. -/
structure SourceGameImplementation (setup : Setup (Player := Player) (L := L)) where
  protocol : ExecutionProtocol.{0, 0, 0} Player
  model : InformationModel.{0, 0, 0, 0, 0, 0} protocol
  finiteHistories : Finite protocol.History
  horizon : Nat
  bounded : protocol.BoundedHorizon horizon
  decisionRecall : model.DecisionRecall
  readout : protocol.State → Option (State L setup.program.terminalCtx)
  excluded : protocol.State → Player → Prop
  charged : protocol.State → Player → Bool

namespace SourceGameImplementation

variable {setup : Setup (Player := Player) (L := L)}
  (implementation : SourceGameImplementation setup)

/-- Apply the exclusion override and the indicated deposit deduction. -/
def netPayoff (payoffs : ConcurrentPayoffs setup) (deposit : Player → ℝ)
    (state : implementation.protocol.State) (who : Player) : ℝ := by
  classical
  exact (if implementation.excluded state who then payoffs.excludedPayoff who
    else (implementation.readout state).elim 0 (fun terminal => payoffs.utility terminal who)) -
  if implementation.charged state who then deposit who else 0

def terminalLaw (target : implementation.model.BehavioralAssessment) :
    PMF implementation.protocol.History :=
  implementation.model.runBehavioralTerminalFrom implementation.bounded.wellFoundedHistories
    target.strategy implementation.protocol.initHistory

/-- The fixed source-defined reader retains initial inputs, the complete typed
terminal state, public results and the realized payoff vector jointly. -/
def jointLaw (payoffs : ConcurrentPayoffs setup) (deposit : Player → ℝ)
    (target : implementation.model.BehavioralAssessment) : PMF (TerminalObservation setup) :=
  (implementation.terminalLaw target).map fun final =>
    TerminalObservation.read setup (implementation.readout final.state)
      (implementation.netPayoff payoffs deposit final.state)

/-- Exact target conclusion, including clean settlement on every supported
terminal history of the implementing equilibrium. -/
structure PreservesAssessment (payoffs : ConcurrentPayoffs setup) (deposit : Player → ℝ)
    (source : setup.intendedModel.BehavioralAssessment)
    (target : implementation.model.BehavioralAssessment) : Prop where
  equilibrium : target.IsSequentialEquilibrium
    implementation.decisionRecall.decisionInformationAntichain
    implementation.bounded.wellFoundedHistories
    (fun who final => implementation.netPayoff payoffs deposit final.state who)
  jointLaw : payoffs.jointLaw source = implementation.jointLaw payoffs deposit target
  noExclusions : ∀ final ∈ (implementation.terminalLaw target).support, ∀ who,
    ¬ implementation.excluded final.state who
  noCharges : ∀ final ∈ (implementation.terminalLaw target).support, ∀ who,
    implementation.charged final.state who = false

end SourceGameImplementation

end Vegas
