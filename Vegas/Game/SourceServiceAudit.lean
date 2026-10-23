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

/-- The audit of the default runtime. -/
abbrev sourceServiceAudit
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup))) :=
  serviceSourceAudit setup .sequential (rankDeadline setup .sequential) leaks sample

omit [Fintype Player] in
/-- **The verdict reads only signed envelopes and the settled record.** Two
audit observations with the same settled record (final public view and
receipts) and the same sequence of signed envelopes receive the same verdict
law; the public view and ledger recorded at each transmission are never read. -/
theorem sourceServiceAudit_congr
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (left right : List (application setup leaks).TrafficRecord ×
      Option (SettledRecord (graph setup)))
    (records : left.2 = right.2)
    (envelopes : left.1.map ReactiveApplication.TrafficRecord.envelope =
      right.1.map ReactiveApplication.TrafficRecord.envelope) :
    sourceServiceAudit setup leaks sample left = sourceServiceAudit setup leaks sample right := by
  obtain ⟨leftTraffic, leftRecord⟩ := left
  obtain ⟨rightTraffic, rightRecord⟩ := right
  change leftRecord = rightRecord at records
  subst records
  change leftTraffic.map _ = rightTraffic.map _ at envelopes
  cases leftRecord with
  | none => rfl
  | some record =>
      have projected (traffic : List (application setup leaks).TrafficRecord) :
          traffic.map (fun entry => ((record, entry.envelope) : SettledEvidence setup)) =
            (traffic.map ReactiveApplication.TrafficRecord.envelope).map
              (fun envelope => ((record, envelope) : SettledEvidence setup)) := by
        rw [List.map_map]
        rfl
      simp only [sourceServiceAudit, serviceSourceAudit, serviceAudit,
        ReactiveApplication.sampledTrafficAudit]
      rw [projected leftTraffic, projected rightTraffic, envelopes]

end Vegas
