/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMessageReadout
import Interaction.ScheduledOpening
import Vegas.Pending.ReactiveService
import Vegas.Pending.ReactivePolicy
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Support

/-! # Coupling scheduled openings through a finite observation window

The window uses the existing player instructions and passive sampler. The
current owner may emit its canonical opening at one selected response count;
other responses are silent. Pending observations are retained. Equal auxiliary
starts can be coupled without assuming the sampler ignores message identity.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def windowOpening (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L) :
    (runtime.reactiveApplication leaks).Action :=
  ⟨some (disclosureSubmission (.opening event candidate raw))⟩

def openingWindowPlayers (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) :
    Player → (runtime.reactiveApplication leaks).Policy := fun who =>
  let app := runtime.reactiveApplication leaks
  if who = owner then app.scheduledPolicy offset selected
    (fun _ _ => PMF.pure (runtime.windowOpening leaks event candidate raw)) app.silentPolicy
  else app.silentPolicy

theorem windowOpening_packet (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (state : State graph) (known : List (Message Player (WitnessedPacket graph)))
    (owned : candidate.1 = owner) (valid : state.candidates.lookup candidate = .openable raw) :
    (runtime.reactiveApplication leaks).packet state owner known
      (disclosureSubmission (.opening event candidate raw)) =
        ⟨.opening event candidate raw, some ⟨candidate, raw⟩,
          state.publicView.tokenFor (.opening event candidate raw)⟩ := by
  have verified : state.candidates.verify candidate raw = true :=
    (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr valid
  simp only [reactiveApplication, disclosureSubmission, WitnessedSubmission.emit,
    owned, verified, and_self, ↓reduceIte]

end Vegas.EventGraphRuntime
