/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicy

/-! # Certificate shape discipline of the prescribed reactive compiler

The compiler attaches evidence only to ordinary opening calls, and that evidence
matches the call's candidate and value. This applies to every source choice,
including withholding and failure. No service grant means no prescribed traffic.

These are local emission properties, not a complete protocol-conformance test:
a packet alone does not establish when it was sent, and this shape check permits
an opening sent prematurely by an arbitrary native policy.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

def unsupportedEvidence (packet : WitnessedPacket graph) : Bool :=
  match packet.evidence with
  | none => false
  | some fact => match packet.call with
    | .opening _ candidate raw => decide (fact ≠ ⟨candidate, raw⟩)
    | .commitment .. | .withhold .. | .malformed .. => true

theorem no_evidence_permitted (call : Payload graph) :
    unsupportedEvidence (⟨call, none⟩ : WitnessedPacket graph) = false := rfl

theorem disclosure_submission_permitted (call : Payload graph) (state : State graph)
    (who : Player) (known : List (Message Player (WitnessedPacket graph))) :
    unsupportedEvidence ((disclosureSubmission call).emit state who known) = false := by
  cases call with
  | commitment => rfl
  | withhold => rfl
  | malformed => rfl
  | opening event candidate raw =>
      by_cases valid : candidate.1 = who ∧ state.candidates.verify candidate raw = true
      · simp [disclosureSubmission, WitnessedSubmission.emit, valid, unsupportedEvidence]
      · simp [disclosureSubmission, WitnessedSubmission.emit, valid, unsupportedEvidence]

/-- The test covers every graph action, including source deviations, and any
emission state and known packets; it is not restricted to an equilibrium path. -/
theorem reactive_decision_submission_permitted (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (action : graph.Action event)
    (view : ReactivePlayerView graph) (submission : WitnessedSubmission graph)
    (sent : (runtime.reactiveDecision leaks who event action view).transmission =
      some (.submit submission)) (state : State graph)
    (known : List (Message Player (WitnessedPacket graph))) :
    unsupportedEvidence (submission.emit state who known) = false := by
  unfold reactiveDecision at sent
  cases node : nodeView graph event with
  | bind =>
      simp only [node] at sent
      cases fresh : reactiveFreshSlot view with
      | none => simp [fresh] at sent
      | some serial =>
          simp only [fresh, Option.map_some, Option.some.injEq] at sent
          cases sent
          rfl
  | resolve =>
      simp only [node, Option.some.injEq] at sent
      cases sent
      exact disclosure_submission_permitted _ state who known
  | sample =>
      simp [node] at sent

/-- No service grant means the prescribed compiler transmits nothing,
independently of the source strategy, prior intentions, or private values. -/
theorem no_grant_no_transmission (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (noGrant : view.application.publicView.serviceGrant = none) :
    runtime.prescribedReactiveResponse leaks who policy history intentions view =
      FinDist.pure (⟨none⟩, none) := by
  simp [prescribedReactiveResponse, noGrant]

end Vegas.EventGraphRuntime
