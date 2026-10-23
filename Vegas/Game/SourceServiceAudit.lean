/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSettledSound
import Vegas.Game.SourceServiceLaw
import Vegas.Pending.ReactiveServiceAudit
import GameTheory.Analysis.Protocol.CounterfactualDecomposition

/-! # Actual settlement on full-source compiled executions

The fixed service samples authentic signed packets, judges each against the
contract's settled record, and checks the record's missed-binding obligations.
No verdict reads when a packet was sent. Every retained history has zero
collection probability, including intermediate histories and correlated
private inputs. Consequently the compiled profile preserves the original joint
terminal-state and realized-payoff law. Incentives for arbitrary raw deviations
remain the separate continuation-repair obligation.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Authenticated audit evidence: the contract's settled record and one signed
packet. Neither the broadcaster nor the time of transmission is part of it. -/
abbrev SettledEvidence (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode := .sequential) :=
  SettledRecord (serviceGraph setup mode) × Message Player (WitnessedPacket (serviceGraph setup
    mode))

/-- A terminal audit of signed packets against the settled record and of public
binding omissions. The sample is authenticated separately; the verdict denotes
an actually collected charge under the declared inclusion and escrow service
contract. -/
def serviceSourceAudit
    (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    (deadline : (serviceGraph setup mode).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode))) :=
  (serviceRuntime setup mode deadline).serviceAudit leaks fun record =>
    (serviceApplication setup mode deadline leaks).sampledTrafficAudit
      (fun traffic => (record, traffic.envelope))
      (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2) sample

end Vegas
