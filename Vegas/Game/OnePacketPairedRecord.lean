/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFactorization
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Operational records at paired history prefixes -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- The operational record retains the initial state as well as every step. -/
theorem operationalRecord_length
    {state : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state) :
    (operationalRecord setup leaks bounds horizon scheduler trace).length = trace.length + 1 := by
  induction trace with
  | start => rfl
  | extend prior _ _ _ ih =>
      change (operationalRecord setup leaks bounds horizon scheduler prior).length + 1 =
        (prior.length + 1) + 1
      rw [ih]

/-- A chronological prefix is recovered by dropping the later states from
the newest-first operational record. -/
theorem operationalRecord_eq_drop_of_tracePrefix
    {first final : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    {prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace first}
    {trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace final}
    (isPrefix : TracePrefix prior trace) :
    operationalRecord setup leaks bounds horizon scheduler prior =
      (operationalRecord setup leaks bounds horizon scheduler trace).drop
        (trace.length - prior.length) := by
  induction isPrefix with
  | refl => simp only [Nat.sub_self, List.drop_zero]
  | @extend source target earlier isEarlier joint legal realized ih =>
      have lengthBound := isEarlier.length_le
      have count : (earlier.extend joint legal realized).length - prior.length =
          (earlier.length - prior.length) + 1 := by
        change earlier.length + 1 - prior.length = _
        omega
      simpa only [operationalRecord, count, List.drop_succ_cons] using ih

/-- Equal complete operational records give equal records at any two actual
prefixes of the same length. No hidden-state correspondence is assumed. -/
theorem operationalRecord_eq_of_paired_prefixes
    {first final imageFirst imageFinal :
      (onePacketProtocol setup leaks bounds horizon scheduler).State}
    {prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace first}
    {trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace final}
    {imagePrior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace imageFirst}
    {imageTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace imageFinal}
    (isPrefix : TracePrefix prior trace) (imagePrefix : TracePrefix imagePrior imageTrace)
    (records : operationalRecord setup leaks bounds horizon scheduler trace =
      operationalRecord setup leaks bounds horizon scheduler imageTrace)
    (lengths : prior.length = imagePrior.length) :
    operationalRecord setup leaks bounds horizon scheduler prior =
      operationalRecord setup leaks bounds horizon scheduler imagePrior := by
  have topLengths : trace.length = imageTrace.length := by
    have counted := congrArg List.length records
    rw [operationalRecord_length, operationalRecord_length] at counted
    omega
  rw [operationalRecord_eq_drop_of_tracePrefix isPrefix,
    operationalRecord_eq_drop_of_tracePrefix imagePrefix, records, topLengths, lengths]

end Vegas
