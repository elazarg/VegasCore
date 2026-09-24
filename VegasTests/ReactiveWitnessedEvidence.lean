/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.ReactivePacketEvidence

/-! # Transferable opening evidence before and after a rejected native call

Alice holds an initial Boolean commitment. She attaches its opening to a call
that the application always rejects. Bob can receive a passive leak, verify the
candidate value, and forward the certificate in his own fresh envelope. Neither
forwarding nor certification gives Bob Alice's application-call authority.
-/

noncomputable section

namespace VegasTests.ReactiveWitnessedEvidence

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

private abbrev inputs : Fin 1 → EventGraph.EventField Bool simpleExpr :=
  fun _ => .binding false .bool

private abbrev outputs : Fin 0 → EventGraph.EventField Bool simpleExpr := Fin.elim0

private abbrev graph : EventGraph Bool simpleExpr where
  inputCount := 1
  order := {
    eventCount := 0
    predecessors := Fin.elim0
    predecessor_lt := by intro event; exact Fin.elim0 event }
  inputLayout := inputs
  outputLayout := outputs
  nodes event := nomatch event
  reads_available := by intro event; exact Fin.elim0 event
  payoffs := []

private def runtime : EventGraphRuntime graph where
  deadline event := nomatch event

private def leaks : MessageNetwork.ObservationRule Bool (WitnessedPacket graph) :=
  fun _ _ => FinDist.pure {(false, 0)}

private abbrev app := runtime.reactiveApplication leaks

private def fact (bit : Bool) : OpeningFact graph :=
  ⟨(false, .initial 0), ⟨.bool, bit⟩⟩

private def call : Submission graph := ⟨.malformed ⟨.bool, true⟩, none⟩

private def initial (bit : Bool) : app.Execution :=
  ReactiveApplication.Execution.initial app (State.initial (fun _ => .success bit))

private def submitted (bit : Bool) : app.Execution :=
  (initial bit).respond app false ⟨some (.submit ⟨call, .owned (fact true)⟩)⟩

private def leaked (bit : Bool) : app.Execution :=
  { submitted bit with network := (submitted bit).network.learn true {(false, 0)} }

theorem activation_is_passive (bit : Bool) :
    ((submitted bit).environmentStep app (.activate true)).map
      (fun next => next.observe app true) = FinDist.pure ((leaked bit).observe app true) := by
  simp only [ReactiveApplication.Execution.environmentStep, app, reactiveApplication, leaks,
    FinDist.map_pure]
  rfl

/-- The same visible raw claim carries a proof only when the claimed value is fixed. -/
theorem true_claim_certified :
    fact true ∈ (runtime.packetEvidence leaks).observe ((leaked true).observe app true) := by
  decide

theorem false_claim_uncertified :
    (runtime.packetEvidence leaks).observe ((leaked false).observe app true) = [] := by
  rfl

/-- There is no verification oracle for another player's unopened commitment. -/
theorem foreign_query_fails (bit : Bool) :
    ((initial bit).respond app true
      ⟨some (.submit ⟨call, .owned (fact true)⟩)⟩).network.pending =
        [⟨(true, 0), ⟨call.packet, none⟩⟩] := by
  rfl

private def forwarded : app.Execution :=
  (leaked true).respond app true ⟨some (.submit ⟨call, .forward (false, 0)⟩)⟩

/-- Forwarding creates Bob's own envelope and retains Alice's candidate evidence. -/
theorem forwarding_preserves_certificate :
    forwarded.network.lookup (true, 0) =
      some ⟨(true, 0), ⟨call.packet, some (fact true)⟩⟩ := by
  rfl

private def included : app.Execution := forwarded.includePending app (true, 0)

/-- Application rejection leaves the certificate in the public ledger. -/
theorem rejection_retains_evidence (who : Bool) :
    included.receipts = [((true, 0), false)] ∧
      included.application = (initial true).application ∧
      fact true ∈ (runtime.packetEvidence leaks).observe (included.observe app who) := by
  refine ⟨rfl, rfl, ?_⟩
  cases who <;> decide

end VegasTests.ReactiveWitnessedEvidence
