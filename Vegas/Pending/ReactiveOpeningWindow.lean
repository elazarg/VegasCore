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

/-- The behavioral realization of a conditional timing law. Its private
mixture is a proof construction; the actual runtime still receives one
ordinary response policy. -/
def openingWindowMixturePlayers (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (choices : PMF (Option (Fin slots))) :
    Player → (runtime.reactiveApplication leaks).Policy :=
  let app := runtime.reactiveApplication leaks
  Function.update (fun _ => app.silentPolicy) owner
    (app.policyMixture choices (fun selected => app.scheduledPolicy offset selected
      (fun _ _ => PMF.pure (runtime.windowOpening leaks event candidate raw))
        app.silentPolicy)).policy

/-- Every supported first opening makes this behavioral mixture permanently
respond silently for the rest of the phase. Thus fully mixed approximants
have the required off-path stop behavior before taking their common limit. -/
theorem openingWindowMixture_after_open (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (choices : PMF (Option (Fin slots))) (slot : Fin slots)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (atSlot : past.length = offset + slot.val)
    (opened : entry.action = runtime.windowOpening leaks event candidate raw)
    (supported : runtime.windowOpening leaks event candidate raw ∈
      (runtime.openingWindowMixturePlayers leaks owner event candidate raw offset choices
        owner past entry.beforeView).support)
    (suffix : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    runtime.openingWindowMixturePlayers leaks owner event candidate raw offset choices
      owner (past ++ [entry] ++ suffix) view =
        (runtime.reactiveApplication leaks).silentPolicy (past ++ [entry] ++ suffix) view := by
  let app := runtime.reactiveApplication leaks
  have distinct : runtime.windowOpening leaks event candidate raw ∉
      (app.silentPolicy past entry.beforeView).support := by
    intro member
    cases app.silentPolicy_cases past entry.beforeView _ member
  simp only [openingWindowMixturePlayers, Function.update_self] at supported ⊢
  exact app.scheduledMixture_after_open choices offset
    (runtime.windowOpening leaks event candidate raw) app.silentPolicy slot past entry
      atSlot opened distinct supported suffix view

theorem openingWindowPlayers_cases (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈
      (runtime.openingWindowPlayers leaks owner event candidate raw offset selected
        who past view).support) :
    action = ⟨none⟩ ∨
      (who = owner ∧ action = runtime.windowOpening leaks event candidate raw ∧
        selected.isSome) := by
  by_cases active : who = owner
  · simp only [openingWindowPlayers, active, ↓reduceIte,
      ReactiveApplication.scheduledPolicy] at supported
    split at supported
    · rename_i chosen
      refine Or.inr ⟨active, (PMF.mem_support_pure_iff _ _).mp supported, ?_⟩
      cases selected with
      | none => simp at chosen
      | some slot => rfl
    · exact Or.inl
        ((runtime.reactiveApplication leaks).silentPolicy_cases past view action supported)
  · simp only [openingWindowPlayers, active, ↓reduceIte] at supported
    exact Or.inl ((runtime.reactiveApplication leaks).silentPolicy_cases past view action supported)

theorem openingWindowPlayers_application (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (who : Player)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈
      (runtime.openingWindowPlayers leaks owner event candidate raw offset selected who
        (execution.recall who)
        (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    (execution.respond (runtime.reactiveApplication leaks) who action).application =
      execution.application := by
  rcases runtime.openingWindowPlayers_cases leaks owner event candidate raw offset selected
    who _ _ action supported with rfl | ⟨rfl, rfl, _⟩
  · rfl
  · rfl

theorem openingWindowPlayers_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (who : Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (counts : (left.recall who).length = (right.recall who).length) :
    runtime.openingWindowPlayers leaks owner event candidate raw offset selected who
      (left.recall who) (left.observe (runtime.reactiveApplication leaks) who) =
    runtime.openingWindowPlayers leaks owner event candidate raw offset selected who
      (right.recall who) (right.observe (runtime.reactiveApplication leaks) who) := by
  have silenced : (runtime.reactiveApplication leaks).silentPolicy
      (left.recall who) (left.observe (runtime.reactiveApplication leaks) who) =
    (runtime.reactiveApplication leaks).silentPolicy
      (right.recall who) (right.observe (runtime.reactiveApplication leaks) who) := rfl
  by_cases active : who = owner
  · subst who
    simp only [openingWindowPlayers, ↓reduceIte,
      ReactiveApplication.scheduledPolicy, counts, silenced]
  · simpa only [openingWindowPlayers, active, ↓reduceIte] using silenced

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

private theorem openingWindowPlayers_packet_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (who : Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈
      (runtime.openingWindowPlayers leaks owner event candidate raw offset selected who
        (left.recall who) (left.observe (runtime.reactiveApplication leaks) who)).support)
    (owned : candidate.1 = owner)
    (meaning : selected.isSome →
      left.application.candidates.lookup candidate = .openable raw ∧
        right.application.candidates.lookup candidate = .openable raw)
    (publicView : left.application.publicView = right.application.publicView) :
    ∀ submission, action.transmission = some submission →
      (runtime.reactiveApplication leaks).packet
        ((runtime.reactiveApplication leaks).submit left.application who submission) who
          (left.network.known who) submission =
      (runtime.reactiveApplication leaks).packet
        ((runtime.reactiveApplication leaks).submit right.application who submission) who
          (right.network.known who) submission := by
  intro submission transmitted
  rcases runtime.openingWindowPlayers_cases leaks owner event candidate raw offset selected
    who _ _ action supported with rfl | ⟨active, rfl, chosen⟩
  · cases transmitted
  · subst who
    simp only [windowOpening, Option.some.injEq] at transmitted
    subst submission
    change (runtime.reactiveApplication leaks).packet left.application owner
      (left.network.known owner) (disclosureSubmission (.opening event candidate raw)) =
        (runtime.reactiveApplication leaks).packet right.application owner
          (right.network.known owner) (disclosureSubmission (.opening event candidate raw))
    rw [windowOpening_packet runtime leaks owner event candidate raw _ _ owned (meaning chosen).1,
      windowOpening_packet runtime leaks owner event candidate raw _ _ owned (meaning chosen).2,
      publicView]

end Vegas.EventGraphRuntime
