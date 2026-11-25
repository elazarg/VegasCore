module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensExecutableClient

@[expose] public section

/-! # Executable observation decoding for Odds–Evens -/

namespace Vegas.Examples.OddsEvensExecutableClient

open OddsEvens OddsEvensLedgerClient EventGraphRuntime Interaction

def isDefaulted (view : app.PlayerView) (who : Bool) : Bool :=
  decide (who ∈ (view.application.publicView.observation.defaults.defaulted : Finset Bool))

def completed (view : app.PlayerView) : List (Fin 4) :=
  view.application.publicView.observation.completionOrder

def submittedEvent (response : app.Action) : Option (Fin 4) := do
  let material ← response.transmission
  match material.call.packet with
  | .commitment event _ | .opening event _ _ => some event
  | .malformed _ => none

def booleanValue (raw : Raw simpleExpr) : Option Bool :=
  match raw with
  | ⟨.bool, value⟩ => some value
  | _ => none

def readCertificate (view : app.PlayerView) : Option Bool := do
  let handle ← view.application.publicView.accepted (.inr (0 : Fin 4))
  view.messages.ledger.findSome? fun message => do
    let fact ← message.payload.evidence
    if (fact.handle : Bool × Slot 0) = handle then booleanValue fact.raw else none

def owns (event : Fin 4) : Bool := event == 1 || event == 3

def pendingEvent (who : Player) (events : List (Fin 4)) : Option (Fin 4) :=
  (List.finRange 4).find? fun event =>
    decide (event ∉ events ∧ (∀ earlier : Fin 4, earlier < event → earlier ∈ events) ∧
      owns event = who)

/-- Decode a callback using the player's raw view and recall. Only the public
completion order, defaults, own submissions and ledger certificates enter. -/
def readObservation (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) : Observation where
  pendingTurn := if isDefaulted view who then none else
    match pendingEvent who (completed view) with
    | none => none
    | some event =>
      if past.any (fun entry => decide (submittedEvent entry.action = some event)) then none
      else some event
  acceptedBit := readCertificate view

private theorem pendingEvent_eq (who : Player) (view : app.PlayerView) :
    pendingEvent who (completed view) = view.application.publicView.ownTurn? who := by
  unfold pendingEvent PublicView.ownTurn?
  congr 1
  funext event
  apply decide_eq_decide.mpr
  have predecessors : compiled.order.predecessors event =
      Finset.univ.filter (fun earlier : Fin 4 => earlier < event) := rfl
  have actor : compiled.actor? event = some (owns event) := by fin_cases event <;> rfl
  simp only [PublicView.EventReady, predecessors, Finset.mem_filter, Finset.mem_univ, true_and,
    actor, Option.some.injEq, completed, and_assoc]
  rfl

private theorem readCertificate_eq (view : app.PlayerView) :
    readCertificate view = acceptedBit? view := by
  unfold readCertificate acceptedBit?
  congr 1
  funext handle
  congr 1
  funext message
  congr 1
  funext fact
  by_cases same : fact.handle = handle
  · simp only [same, ↓reduceIte]
    rcases fact.raw with ⟨type, value⟩
    cases type <;> rfl
  · simp only [same, ↓reduceIte]

theorem readObservation_eq (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView) :
    readObservation who past view = decodeObservation who past view := by
  have recorded (event : Fin 4) :
      past.any (fun entry => decide (submittedEvent entry.action = some event)) =
        eventRecorded OddsEvensService.timeouts OddsEvensService.leaks past event := by
    unfold eventRecorded
    congr 1
    funext entry
    cases sent : entry.action.transmission with
    | none => simp [submittedEvent, submittedEvent?, sent]
    | some material =>
        cases call : material.call.packet <;> simp [submittedEvent, submittedEvent?, sent, call,
          Payload.event?]
  simp only [readObservation, decodeObservation, readCertificate_eq, pendingEvent_eq,
    isDefaulted, decide_eq_true_iff, EventPublicObservation.defaulted, recorded]
  rfl

/-- The executable decoder already ignores pending data, including in the
player's earlier observations. -/
theorem readObservation_ledgerOnly (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) :
    readObservation who (past.map (ReactiveApplication.PlayerEntry.ledgerOnly app))
      (view.ledgerOnly app) = readObservation who past view := by
  simp only [readObservation, List.any_map, Function.comp_def]
  rfl

/-- Feeding a fair coin to the raw callback decoder and decision rule gives
the prescribed packet distribution after canonical packet construction. -/
theorem readObservation_distribution (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) :
    (GameTheory.Math.Probability.uniformLaw Bool).map (fun coin =>
      encodeResponse who (past.map (ReactiveApplication.PlayerEntry.ledgerOnly app))
        (view.ledgerOnly app) (decideResponse (readObservation who past view) coin)) =
      policy who past view := by
  rw [← readObservation_ledgerOnly who past view, readObservation_eq]
  exact decideResponse_distribution who past view

end Vegas.Examples.OddsEvensExecutableClient
