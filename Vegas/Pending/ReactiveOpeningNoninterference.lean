/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOpeningContinuation

/-! # Foreign replay choices leave the protected disclosure result unchanged

Other players may observe and replay the pending opening. Their response changes
the network and their own recall, but preserves the eventual application law of
the owner's scheduled disclosure policy. No equality of foreign observations or
restriction on the passive sampling rule is assumed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- At an already activated foreign visit, silence and replay have exactly
the same final protected-inclusion application law. Complete network traces
and the foreign player's recall are deliberately retained by both executions. -/
theorem openingWindowMixture_foreign_waiting_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (choices : FinDist (Option (Fin slots))) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (serials : initial.network.SerialsBeforeNext)
    (owned : candidate.1 = owner)
    (valid : initial.application.candidates.lookup candidate = .openable raw)
    (remaining : List Player) (complete : visits + remaining.count owner = slots)
    (network : runtime.NetworkPolicy leaks) (who : Player) (foreign : who ≠ owner)
    (response : (runtime.reactiveApplication leaks).Action)
    (waiting : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩) :
    let app := runtime.reactiveApplication leaks
    let family := fun selected => app.scheduledPolicy offset selected
      (fun _ _ => FinDist.pure (runtime.windowOpening leaks event candidate raw)) app.replayPolicy
    let posterior := (app.policyMixture choices family).posterior (current.recall owner)
    (∀ selected ∈ posterior.support,
      runtime.OpeningWindowFrame leaks owner event candidate raw offset selected visits
        initial current) →
    (runtime.runInteractionPlan leaks
      (runtime.openingWindowMixturePlayers leaks owner event candidate raw offset choices)
        network (remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
          (current.respond app who response)).map (fun final => final.application) =
      (runtime.runInteractionPlan leaks
        (runtime.openingWindowMixturePlayers leaks owner event candidate raw offset choices)
          network (remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
            current).map (fun final => final.application) := by
  intro app family posterior frames
  have recall := app.respond_recall_other current who owner foreign.symm response
  have afterFrames (selected : Option (Fin slots))
      (possible : selected ∈ ((app.policyMixture choices family).posterior
        ((current.respond app who response).recall owner)).support) :
      runtime.OpeningWindowFrame leaks owner event candidate raw offset selected visits
        initial (current.respond app who response) := by
    rw [recall] at possible
    have frame := (frames selected possible).waiting_response runtime leaks owner event candidate
      raw offset selected visits initial current who response waiting
        (by simp only [foreign, ↓reduceIte, Nat.add_zero])
    simpa only [foreign, ↓reduceIte, Nat.add_zero] using frame
  have after := runtime.openingWindowMixture_continuation_settlement leaks owner event candidate
    raw offset choices visits initial (current.respond app who response) serials owned valid
      remaining complete network afterFrames
  have before := runtime.openingWindowMixture_continuation_settlement leaks owner event candidate
    raw offset choices visits initial current serials owned valid remaining complete network frames
  change _ = ((app.policyMixture choices family).posterior
    ((current.respond app who response).recall owner)).map _ at after
  rw [recall] at after
  exact after.trans before.symm

end Vegas.EventGraphRuntime
