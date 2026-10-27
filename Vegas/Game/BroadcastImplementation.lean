/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ConcurrentRawSequentialPreservation

/-! # Formalization target for a fully recording broadcast compiler

This file fixes proposed parameter types and a generic result carrier for an
existential implementation statement. It defines no compiler. The inbox
transition system, its source interpreter and its observation model still have
to be defined. The carrier alone does not enforce those semantics or connect
the game to the parameters; it is not yet a broadcast operational specification.

The mathematical specification is in
`docs/se-broadcast-runtime-mathematics.md`. Independent delay draws are made by
the compiler at first submission. Observations use current-namespace metadata
and selected wire bodies, never private commitment meanings or future service
coins. Old replay observations are a separate auxiliary coordinate.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Source-value-free metadata on which a pending-traffic observation may depend.
The class is fixed by the public slot, rather than by its private payload. -/
structure BroadcastMetadata (Player : Type) where
  author : Player
  attempt : Nat
  slot : Nat
  packetClass : Nat

/-- A finite observation of the current physical namespace. Selecting a wire
position reveals that wire body; the auxiliary signal also permits counts and
metadata-only observations. The compiler excludes discarded namespaces from
this input and samples the kernel independently of new-body service coins. -/
structure BroadcastObservation (Player : Type) where
  Signal : Player → Type
  finiteSignal : ∀ who, Finite (Signal who)
  sample : (who : Player) → (clock : Nat) →
    (pending : List (BroadcastMetadata Player)) →
    PMF (Signal who × Finset (Fin pending.length))

/-- Parameters fixed before selecting a source equilibrium. The delay kernel
returns an offset, so actual delay is one plus the sampled value. Distinct
first submissions use independent draws. The two traffic bounds are separate:
replay traffic cannot consume the current fresh-submission coordinate. -/
structure BroadcastParameters (Player : Type) where
  publicationDelay : Nat
  publicationDelay_positive : 0 < publicationDelay
  protectedBlocks : Nat
  protectedBlocks_positive : 0 < protectedBlocks
  freshPerBlock : Player → Nat
  freshPerBlock_positive : ∀ who, 0 < freshPerBlock who
  replayMultiplicity : Nat
  delay : Player → (window : Nat) → (submittedAt : Nat) → PMF (Fin publicationDelay)
  observation : BroadcastObservation Player

/-- Generic finite-game output carrier for the proposed broadcast compiler.
None of these fields asserts equilibrium preservation or enforces the intended
runtime semantics. Publication, audit and observation constraints must be
supplied by an operational specification before existentially quantifying over
this carrier expresses a blockchain implementation theorem. -/
structure BroadcastImplementation (setup : Setup (Player := Player) (L := L)) where
  protocol : ExecutionProtocol.{0, 0, 0} Player
  model : InformationModel.{0, 0, 0, 0, 0, 0} protocol
  finiteHistories : Finite protocol.History
  horizon : Nat
  bounded : protocol.BoundedHorizon horizon
  decisionRecall : model.DecisionRecall
  readout : protocol.State → Option (State L setup.program.terminalCtx)
  excluded : protocol.State → Player → Prop
  charged : protocol.State → Player → Bool

namespace BroadcastImplementation

variable {setup : Setup (Player := Player) (L := L)}
  (implementation : BroadcastImplementation setup)

/-- A deterministic final ledger audit deducts one refundable deposit. -/
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

end BroadcastImplementation

end Vegas
