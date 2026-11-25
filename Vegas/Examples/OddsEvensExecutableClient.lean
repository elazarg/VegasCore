module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensLedgerClient

@[expose] public section

/-! # Coin-driven decisions for the Odds–Evens ledger client -/

namespace Vegas.Examples.OddsEvensExecutableClient

open OddsEvens OddsEvensLedgerClient EventGraphRuntime Interaction
open GameTheory.Math.Probability

/-- The event still awaiting an own submission and the authenticated first bit,
when available from the ledger. -/
structure Observation where
  pendingTurn : Option (Fin 4)
  acceptedBit : Option Bool

/-- First-order decisions consumed by the canonical packet encoder. -/
inductive Decision where
  | silent
  | firstCommit (bit : Bool)
  | secondCommit (bit : Bool)
  | firstOpen
  | secondOpen
  deriving DecidableEq, Repr

/-- Use a fresh fair coin for an uninformed commitment. An authenticated first
bit makes the second commitment deterministic. -/
def decideResponse (observation : Observation) (coin : Bool) : Decision :=
  match observation.pendingTurn with
  | none => .silent
  | some ⟨0, _⟩ => .firstCommit coin
  | some ⟨1, _⟩ => .secondCommit (observation.acceptedBit.elim coin (!·))
  | some ⟨2, _⟩ => .firstOpen
  | some ⟨3, _⟩ => .secondOpen

/-- Decode the established callback view and own submission recall. -/
noncomputable def decodeObservation (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) : Observation where
  pendingTurn :=
    if who ∈ view.application.publicView.observation.defaulted then none
    else match view.application.publicView.ownTurn? who with
      | none => none
      | some event =>
        if eventRecorded OddsEvensLedgerClient.timeouts OddsEvensService.leaks past event then
          none
        else some event
  acceptedBit := acceptedBit? view

/-- Encode the first-order choice using the existing canonical packet builder. -/
noncomputable def encodeResponse (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) : Decision → app.Action
  | .silent => ⟨none⟩
  | .firstCommit bit =>
      ordinaryResponse who past view (eventId 0) (some (PublicationResult.success bit))
  | .secondCommit bit =>
      ordinaryResponse who past view (eventId 1) (some (PublicationResult.success bit))
  | .firstOpen => ordinaryResponse who past view (eventId 2) true
  | .secondOpen => ordinaryResponse who past view (eventId 3) true

private theorem encode_decideResponse_distribution (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) :
    (uniformLaw Bool).map (fun coin =>
      encodeResponse who past view (decideResponse (decodeObservation who past view) coin)) =
      respond who past view := by
  by_cases inactive : who ∈ view.application.publicView.observation.defaulted
  · simp only [decodeObservation, decideResponse, encodeResponse, respond, ite_eq_left inactive]
    exact PMF.map_const _ _
  · cases turn : view.application.publicView.ownTurn? who with
    | none =>
      simp only [decodeObservation, decideResponse, encodeResponse, respond, ite_eq_right inactive,
        turn]
      exact PMF.map_const _ _
    | some event =>
      cases recorded : eventRecorded OddsEvensLedgerClient.timeouts OddsEvensService.leaks past
          event with
      | true =>
        simp only [decodeObservation, decideResponse, encodeResponse, respond,
          ite_eq_right inactive, turn, recorded, ↓reduceIte]
        exact PMF.map_const _ _
      | false =>
        simp only [decodeObservation, respond, ite_eq_right inactive, turn, recorded,
          Bool.false_eq_true, ↓reduceIte]
        change Fin 4 at event
        fin_cases event
        · rfl
        · cases accepted : acceptedBit? view
          · simp only [decideResponse, accepted, oddBitDistribution]
            rfl
          · simp only [decideResponse, accepted, encodeResponse, oddBitDistribution, PMF.pure_map,
              Option.elim_some]
            exact PMF.map_const _ _
        · exact PMF.map_const _ _
        · exact PMF.map_const _ _

/-- The encoded executable decisions driven by a fair coin have exactly the
existing ledger client's packet law at every callback view and own recall. -/
theorem decideResponse_distribution (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) :
    let ledgerPast := past.map (ReactiveApplication.PlayerEntry.ledgerOnly app)
    let ledgerView := view.ledgerOnly app
    (uniformLaw Bool).map (fun coin =>
      encodeResponse who ledgerPast ledgerView
        (decideResponse (decodeObservation who ledgerPast ledgerView) coin)) =
      policy who past view :=
  encode_decideResponse_distribution who _ _

example : decideResponse ⟨some 0, none⟩ false = .firstCommit false := by decide
example : decideResponse ⟨some 0, none⟩ true = .firstCommit true := by decide
example : decideResponse ⟨some 1, none⟩ true = .secondCommit true := by decide
example : decideResponse ⟨some 1, some true⟩ true = .secondCommit false := by decide
example : decideResponse ⟨some 1, some false⟩ false = .secondCommit true := by decide
example : decideResponse ⟨some 2, none⟩ false = .firstOpen := by decide
example : decideResponse ⟨some 3, none⟩ true = .secondOpen := by decide
example : decideResponse ⟨none, some true⟩ true = .silent := by decide

end Vegas.Examples.OddsEvensExecutableClient
