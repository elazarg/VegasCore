/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRuntime
import Vegas.Pending.ReactiveServiceAudit

/-! # Actual final-record audit for compiled source execution

The runtime samples authentic signed packets and judges them against its
settled record. Its public missed-decision markers charge the owner directly.
These definitions apply to every scheduler; monitoring may be partial and
report delivery may depend on the observed evidence.
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
abbrev SettledEvidence (setup : Setup (Player := Player) (L := L)) :=
  SettledRecord (graph setup) × Message Player (WitnessedPacket (graph setup))

/-- A terminal audit of signed packets against the settled record and of public
missed decisions. The sample is authenticated separately; the verdict denotes
an actually collected charge under the declared inclusion and escrow service
contract. -/
def sourceServiceAudit
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup))) :=
  (runtime setup).serviceAudit leaks fun record =>
    (application setup leaks).sampledTrafficAudit
      (fun traffic => (record, traffic.envelope))
      (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2) sample

end Vegas
