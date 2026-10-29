/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveLedgerPolicy
import Vegas.Examples.OddsEvensRecoveryService
import Vegas.Pending.ExclusionProjection
import Vegas.Pending.ReactiveCanonicalDecision
import Mathlib.Probability.Distributions.Uniform

/-! # An explicit ledger-reading Odds–Evens client

Even uses a fair commitment. Odd uses a fair commitment unless an authentic
ledger certificate opens Even's accepted handle, in which case Odd chooses
the opposite bit. Both players request their ordinary successful openings.
Canonical service decisions handle packet allocation. Own submission recall
suppresses repeat packets for the same event.
Permanent exclusion stops the client. All pending observations are erased
before computing decisions, including observations in the player's recall.

The policy is explicit; its full sequential rationality is a separate result.
-/

noncomputable section

namespace Vegas.Examples.OddsEvensLedgerClient

open OddsEvens EventGraphRuntime Interaction GameTheory.Math.Probability

abbrev runtime := OddsEvensRecoveryService.runtime
abbrev app := OddsEvensRecoveryService.app

private abbrev eventId (n : Fin 4) : compiled.EventId := n

/-- Inspect only authenticated certificates for the accepted handle. The call
carrying a certificate can itself have been rejected. -/
def acceptedBit? (view : app.PlayerView) : Option Bool := do
  let accepted ← view.application.1.publicView.accepted (.inr ⟨0, by decide⟩)
  view.messages.ledger.findSome? fun message => do
    let fact ← message.payload.evidence
    if fact.handle = accepted then fact.raw.as? .bool else none

/-- The second player's source choice after reading the ledger. -/
def oddBitLaw (view : app.PlayerView) : PMF Bool :=
  match acceptedBit? view with
  | none => PMF.uniformOfFintype Bool
  | some bit => PMF.pure (!bit)

/-- Feed ordinary graph choices to the existing canonical packet client. -/
def ordinaryResponse (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) (event : compiled.EventId) (choice : compiled.Action event) :
    app.Action :=
  ⟨(runtime.canonicalServiceDecision OddsEvensRecoveryService.leaks who
    (past.map (RecoveryProjection.playerEntry runtime OddsEvensRecoveryService.leaks))
    (RecoveryProjection.playerView runtime OddsEvensRecoveryService.leaks view)
    event choice).transmission⟩

private def respond (who : Player) : app.Policy := fun past view =>
  if who ∈ view.application.2 then PMF.pure ⟨none⟩
  else match view.application.1.publicView.ownTurn? who with
    | none => PMF.pure ⟨none⟩
    | some event =>
        if runtime.eventRecorded OddsEvensRecoveryService.leaks
            (past.map (RecoveryProjection.playerEntry runtime OddsEvensRecoveryService.leaks))
            event then PMF.pure ⟨none⟩
        else match event with
        | ⟨0, _⟩ => (PMF.uniformOfFintype Bool).map fun bit =>
            ordinaryResponse who past view (eventId 0) (PublicationResult.success bit)
        | ⟨1, _⟩ => (oddBitLaw view).map fun bit =>
            ordinaryResponse who past view (eventId 1) (PublicationResult.success bit)
        | ⟨2, _⟩ => PMF.pure (ordinaryResponse who past view (eventId 2) true)
        | ⟨3, _⟩ => PMF.pure (ordinaryResponse who past view (eventId 3) true)

/-- A complete action law using ledger data and the player's own private state. -/
def policy (who : Player) : app.Policy := app.ledgerPolicy (respond who)

theorem policy_usesLedgerOnly (who : Player) :
    ReactiveApplication.Policy.UsesLedgerOnly app (policy who) :=
  app.ledgerPolicy_usesLedgerOnly (respond who)

theorem policy_of_excluded (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (excluded : who ∈ view.application.2) : policy who past view = PMF.pure ⟨none⟩ := by
  simp only [policy, ReactiveApplication.ledgerPolicy, respond,
    ReactiveApplication.PlayerView.ledgerOnly, excluded, ↓reduceIte]

theorem oddBitLaw_of_known (view : app.PlayerView) (bit : Bool)
    (known : acceptedBit? view = some bit) : oddBitLaw view = PMF.pure (!bit) := by
  simp only [oddBitLaw, known]

theorem oddBitLaw_of_unknown (view : app.PlayerView)
    (unknown : acceptedBit? view = none) : oddBitLaw view = PMF.uniformOfFintype Bool := by
  simp only [oddBitLaw, unknown]

theorem acceptedBit?_ledgerOnly (view : app.PlayerView) :
    acceptedBit? (view.ledgerOnly app) = acceptedBit? view := rfl

/-- At Odd's unsent commitment, an accepted ledger opening fixes the response. -/
theorem policy_at_informed_commitment (past : List app.PlayerEntry) (view : app.PlayerView)
    (included : odd ∉ view.application.2)
    (turn : view.application.1.publicView.ownTurn? odd = some (eventId 1))
    (unsent : runtime.eventRecorded OddsEvensRecoveryService.leaks
      ((past.map (ReactiveApplication.PlayerEntry.ledgerOnly app)).map
        (RecoveryProjection.playerEntry runtime OddsEvensRecoveryService.leaks)) (eventId 1) =
          false)
    (bit : Bool) (known : acceptedBit? view = some bit) :
    policy odd past view = PMF.pure (ordinaryResponse odd
      (past.map (ReactiveApplication.PlayerEntry.ledgerOnly app)) (view.ledgerOnly app)
      (eventId 1) (PublicationResult.success (!bit))) := by
  simp only [policy, ReactiveApplication.ledgerPolicy, respond,
    ReactiveApplication.PlayerView.ledgerOnly, included, ↓reduceIte, turn, unsent,
    Bool.false_eq_true]
  change (oddBitLaw view).map (fun selected : Bool => ordinaryResponse odd
    (past.map (ReactiveApplication.PlayerEntry.ledgerOnly app)) (view.ledgerOnly app)
    (eventId 1) (PublicationResult.success selected)) = _
  rw [oddBitLaw_of_known _ bit known, PMF.pure_map]
  rfl

private theorem recorded_ledgerOnly (past : List app.PlayerEntry) (event : compiled.EventId) :
    runtime.eventRecorded OddsEvensRecoveryService.leaks
      ((past.map (ReactiveApplication.PlayerEntry.ledgerOnly app)).map
        (RecoveryProjection.playerEntry runtime OddsEvensRecoveryService.leaks)) event =
    runtime.eventRecorded OddsEvensRecoveryService.leaks
      (past.map (RecoveryProjection.playerEntry runtime OddsEvensRecoveryService.leaks)) event := by
  simp only [eventRecorded, List.any_map, Function.comp_def,
    ReactiveApplication.PlayerEntry.ledgerOnly, RecoveryProjection.playerEntry,
    RecoveryProjection.action]

/-- Own submission recall suppresses another packet even before a receipt arrives. -/
theorem policy_of_recorded (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (event : compiled.EventId)
    (turn : view.application.1.publicView.ownTurn? who = some event)
    (recorded : runtime.eventRecorded OddsEvensRecoveryService.leaks
      (past.map (RecoveryProjection.playerEntry runtime OddsEvensRecoveryService.leaks)) event =
        true) : policy who past view = PMF.pure ⟨none⟩ := by
  simp only [policy, ReactiveApplication.ledgerPolicy, respond,
    ReactiveApplication.PlayerView.ledgerOnly]
  split
  · rfl
  · simp only [turn, recorded_ledgerOnly, recorded, ↓reduceIte]

end Vegas.Examples.OddsEvensLedgerClient
