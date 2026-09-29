/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOpeningWindow
import GameTheoryExtensions.Math.Probability.ConditionalNoise
import GameTheoryExtensions.Math.Probability.Conditioning

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
    (offset : Nat) {slots : Nat} (timing : PMF (Fin slots))
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
    (offset : Nat) {slots : Nat} (timing : PMF (Fin slots))
    (network : runtime.NetworkPolicy leaks) (roster : List Player) (focal : Player)
    (prior : PMF ((runtime.reactiveApplication leaks).Execution × Option (Raw L)))
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
    (fiberConditional joint (fun output => (output.1.2, output.2)) (observed, extra)).map Prod.fst =
      fiberConditional prior Prod.snd observed := by
  dsimp only
  apply PMF.conditional_kernel_of_fiber prior Prod.snd _ _ observed extra present
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
      apply bind_congr_on_support _
      intro slot _
      exact runtime.openingWindow_coupling leaks owner event candidate raw offset (some slot)
        network roster focal left right (recalls _ leftSupported) (recalls _ rightSupported)
        (messages _ leftSupported _ rightSupported) (recall _ leftSupported _ rightSupported)
        (publicView _ leftSupported _ rightSupported)
        (privateView _ leftSupported _ rightSupported) owned (fun _ =>
          ⟨meaning _ leftSupported raw rfl, meaning _ rightSupported raw rfl⟩)

/-- For the owner, its own opening value and source-choice law are fixed on
its information fiber. At any prefix of the phase, the actual behavioral
mixture's observed traffic therefore adds no information about hidden opponent
state, without conditioning on the future source result. The readout can be
any projection of the coupled transcript, including the owner's own recall. -/
theorem openingWindow_owner_posterior {Observation : Type}
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (choices : PMF (Option (Fin slots)))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (prior : PMF (runtime.reactiveApplication leaks).Execution)
    (reference : (runtime.reactiveApplication leaks).Execution)
    (before : (reference.recall owner).length ≤ offset)
    (referenceRecall : reference.InputRecall (runtime.reactiveApplication leaks))
    (recalls : ∀ start ∈ prior.support,
      start.InputRecall (runtime.reactiveApplication leaks))
    (messages : ∀ start ∈ prior.support,
      (runtime.reactiveApplication leaks).messageView start =
        (runtime.reactiveApplication leaks).messageView reference)
    (recall : ∀ start ∈ prior.support, start.recall owner = reference.recall owner)
    (publicView : ∀ start ∈ prior.support,
      start.application.publicView = reference.application.publicView)
    (privateView : ∀ start ∈ prior.support,
      (runtime.reactiveApplication leaks).observePlayer start.application owner =
        (runtime.reactiveApplication leaks).observePlayer reference.application owner)
    (owned : candidate.1 = owner)
    (referenceMeaning : reference.application.candidates.lookup candidate = .openable raw)
    (meaning : ∀ start ∈ prior.support,
      start.application.candidates.lookup candidate = .openable raw)
    (observe : (runtime.reactiveApplication leaks).MessageReadout ×
      List (runtime.reactiveApplication leaks).PlayerEntry → Observation)
    (observed : Observation) :
    let app := runtime.reactiveApplication leaks
    let players := runtime.openingWindowMixturePlayers leaks owner event candidate raw
      offset choices
    let readout := fun execution : app.Execution =>
      observe (app.messageView execution, execution.recall owner)
    let joint := prior.bind fun start =>
      ((runtime.runInteractionPlan leaks players network
        (roster.map ServiceInstruction.player) start).map readout).map
          (fun output => (output, start))
    (fiberConditional joint Prod.fst observed).map Prod.snd = prior := by
  dsimp only
  let app := runtime.reactiveApplication leaks
  let players := runtime.openingWindowMixturePlayers leaks owner event candidate raw offset choices
  let kernel := fun start : app.Execution =>
    (runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player) start).map
        (fun execution => observe (app.messageView execution, execution.recall owner))
  have same (start : app.Execution) (supported : start ∈ prior.support) :
      kernel start = kernel reference := by
    have atStart : (start.recall owner).length ≤ offset := by
      rw [recall start supported]
      exact before
    dsimp only [kernel, players]
    rw [runtime.openingWindowMixture_law leaks owner event candidate raw offset choices
      network _ start atStart,
      runtime.openingWindowMixture_law leaks owner event candidate raw offset choices
        network _ reference before, PMF.map_bind, PMF.map_bind]
    apply bind_congr_on_support _
    intro selected _
    have coupled := runtime.openingWindow_coupling leaks owner event candidate raw offset selected
      network roster owner start reference (recalls start supported) referenceRecall
      (messages start supported) (recall start supported) (publicView start supported)
      (privateView start supported) owned (fun _ => ⟨meaning start supported, referenceMeaning⟩)
    have projected := congrArg (PMF.map observe) coupled
    simpa only [PMF.map_comp, Function.comp_def] using projected
  have independent : (prior.bind fun start =>
      (kernel start).map fun output => (output, start)) =
        bindPairLaw (kernel reference) (fun _ => prior) := by
    calc
      _ = prior.bind (fun start =>
          (kernel reference).map fun output => (output, start)) := by
        apply bind_congr_on_support _
        intro start supported
        rw [same start supported]
      _ = _ := by
        simp only [FinDist.product, ← PMF.bind_pure_comp, Function.comp_def]
        rw [PMF.bind_comm]
  change ((fiberConditional (prior.bind fun start =>
    (kernel start).map fun output => (output, start)) Prod.fst observed).map
      Prod.snd) = prior
  rw [independent]
  exact conditional_snd_bindPairLaw_const (kernel reference) prior observed

end Vegas.EventGraphRuntime
