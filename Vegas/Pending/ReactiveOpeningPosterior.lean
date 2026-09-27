/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOpeningWindow
import GameTheoryExtensions.Math.Probability.ConditionalNoise

/-! # Source-result posterior through an actual opening window

The prior is an arbitrary correlated law of a starting execution and the
source's chosen disclosure result. The source choice can therefore depend on
hidden information. Conditional timing and actual sampling/replay traffic add
no further information within a coupled starting information fiber.

This is a one-phase posterior identity. It does not assume or prove a global
source-to-runtime equilibrium correspondence; successive phases still need
their coupled starting-information invariant and common perturbations.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Push forward the existing runtime's scheduled branches. `none` means no
fresh opening; `some raw` chooses a slot independently conditional on that
eventual source result. The fallback raw value is never transmitted. -/
def openingOutcomeTranscript (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (fallback : Raw L)
    (offset : Nat) {slots : Nat} (timing : FinDist (Fin slots))
    (network : runtime.NetworkPolicy leaks) (roster : List Player) (focal : Player)
    (start : (runtime.reactiveApplication leaks).Execution) (outcome : Option (Raw L)) :=
  let app := runtime.reactiveApplication leaks
  let readout := fun execution : app.Execution =>
    (app.messageView execution, execution.recall focal)
  match outcome with
  | none => (runtime.runInteractionPlan leaks
      (runtime.openingWindowPlayers leaks owner event candidate fallback offset
        (none : Option (Fin slots))) network (roster.map ServiceInstruction.player)
          start).map readout
  | some raw => timing.bind fun slot => (runtime.runInteractionPlan leaks
      (runtime.openingWindowPlayers leaks owner event candidate raw offset (some slot))
        network (roster.map ServiceInstruction.player) start).map readout

/-- Conditioning on the source result already accounts for any correlation
between the hidden starting state and the source's disclosure decision.
Observing the actual timing/sampling/replay transcript then changes nothing
about that posterior. The conclusion retains the entire hidden start. -/
theorem openingOutcome_posterior (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (fallback : Raw L)
    (offset : Nat) {slots : Nat} (timing : FinDist (Fin slots))
    (network : runtime.NetworkPolicy leaks) (roster : List Player) (focal : Player)
    (prior : FinDist ((runtime.reactiveApplication leaks).Execution × Option (Raw L)))
    (recalls : ∀ pair ∈ prior.support,
      pair.1.InputRecall (runtime.reactiveApplication leaks))
    (messages : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      (runtime.reactiveApplication leaks).messageView left.1 =
        (runtime.reactiveApplication leaks).messageView right.1)
    (recall : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      left.1.recall focal = right.1.recall focal)
    (publicView : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      left.1.application.publicView = right.1.application.publicView)
    (privateView : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      (runtime.reactiveApplication leaks).observePlayer left.1.application focal =
        (runtime.reactiveApplication leaks).observePlayer right.1.application focal)
    (owned : candidate.1 = owner)
    (meaning : ∀ pair ∈ prior.support, ∀ raw, pair.2 = some raw →
      pair.1.application.candidates.lookup candidate = .openable raw)
    (observed : Option (Raw L))
    (extra : (runtime.reactiveApplication leaks).MessageReadout ×
      List (runtime.reactiveApplication leaks).PlayerEntry)
    (present : ∃ pair ∈ prior.support, pair.2 = observed ∧ extra ∈
      (runtime.openingOutcomeTranscript leaks owner event candidate fallback offset timing
        network roster focal pair.1 pair.2).support) :
    let channel := fun pair => runtime.openingOutcomeTranscript leaks owner event candidate
      fallback offset timing network roster focal pair.1 pair.2
    let joint := prior.bind fun pair => (channel pair).map fun transcript => (pair, transcript)
    (joint.condOnFibre (fun output => (output.1.2, output.2)) (observed, extra)).map Prod.fst =
      prior.condOnFibre Prod.snd observed := by
  dsimp only
  apply FinDist.conditional_kernel_of_fiber prior Prod.snd _ _ observed extra present
  intro left leftSupported right rightSupported same
  obtain ⟨left, outcome⟩ := left
  obtain ⟨right, rightOutcome⟩ := right
  change outcome = rightOutcome at same
  subst rightOutcome
  cases outcome with
  | none =>
      exact runtime.openingWindow_coupling leaks owner event candidate fallback offset none
        network roster focal left right (recalls _ leftSupported) (recalls _ rightSupported)
        (messages _ leftSupported _ rightSupported) (recall _ leftSupported _ rightSupported)
        (publicView _ leftSupported _ rightSupported)
        (privateView _ leftSupported _ rightSupported) owned (by simp)
  | some raw =>
      change timing.bind _ = timing.bind _
      apply FinDist.bind_congr
      intro slot _
      exact runtime.openingWindow_coupling leaks owner event candidate raw offset (some slot)
        network roster focal left right (recalls _ leftSupported) (recalls _ rightSupported)
        (messages _ leftSupported _ rightSupported) (recall _ leftSupported _ rightSupported)
        (publicView _ leftSupported _ rightSupported)
        (privateView _ leftSupported _ rightSupported) owned (fun _ =>
          ⟨meaning _ leftSupported raw rfl, meaning _ rightSupported raw rfl⟩)

end Vegas.EventGraphRuntime
