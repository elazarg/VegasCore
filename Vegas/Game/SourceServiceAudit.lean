module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealService
public import Vegas.Pending.ReactiveServiceAudit
public import Interaction.ReactiveAuditCollection

@[expose] public section

/-! # Protocol audits of compiled source executions

The service samples authentic signed traffic and checks each packet against the
native contract's settled record. The resulting audit charges protocol
violations. Source omissions and authentic openings whose public guards reject
retain the game payoff declared for their public default history.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Authenticated audit evidence: the contract's settled record and one signed
packet. Neither the broadcaster nor the time of transmission is part of it. -/
abbrev SettledEvidence (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies := setup.informationDependencies) :=
  SettledRecord (serviceGraph setup deps) × Message Player (WitnessedPacket (serviceGraph setup
    deps))

/-- A terminal audit of signed packets against the settled record. The sample is
authenticated separately; its verdict denotes an actually collected charge
under the declared inclusion and escrow service contract. -/
def serviceSourceAudit
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (sample : List (SettledEvidence setup deps) → PMF (List (SettledEvidence setup deps))) :=
  (serviceAudit (serviceTimeouts setup deps duration)) leaks fun record =>
    (serviceApplication setup deps duration leaks).sampledTrafficAudit
      (fun traffic => (record, traffic.envelope))
      (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2) sample

end Vegas
