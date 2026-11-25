module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensClientInput
public import Vegas.Examples.OddsEvensClientOpening
public import Vegas.Pending.BoundedCanonicalSlot

@[expose] public section

/-! # Executable packet encoding for Odds–Evens -/

namespace Vegas.Examples.OddsEvensExecutableClient

open OddsEvens OddsEvensLedgerClient EventGraphRuntime Interaction

def countCompletedBindings (view : app.PlayerView) (who : Bool) : Nat :=
  (completed view).countP fun event => (event == 0 || event == 1) && owns event == who

def bindingSlotFresh (view : app.PlayerView) (serial : Nat) : Bool :=
  match view.application.candidates (.prepared serial : Slot 0) with
  | .fresh => true
  | .unopenable | .openable _ => false

theorem bindingSlotFresh_eq (view : app.PlayerView) :
    bindingSlotFresh view = preparedSlotFresh view.application := by
  funext serial
  unfold bindingSlotFresh preparedSlotFresh
  cases view.application.candidates (.prepared serial : Slot 0) <;> rfl

def prepareBindingPacket (who : Bool) (past : List app.PlayerEntry)
    (view : app.PlayerView) (event : Fin 4) (bit : Bool) : app.Action :=
  ⟨(boundedCanonicalSlot (countCompletedBindings view who) past.length
      (bindingSlotFresh view)).map fun serial =>
    ⟨⟨.commitment event (who, .prepared serial), some ⟨.bool, bit⟩⟩, .none⟩⟩

theorem countCompletedBindings_eq (view : app.PlayerView) (who : Bool) :
    countCompletedBindings view who = view.application.publicView.bindingCount who := by
  unfold countCompletedBindings completed PublicView.bindingCount
  congr 1
  funext event
  change Fin 4 at event
  fin_cases event <;> cases who <;> rfl

private theorem commitPacket_eq (who : Bool) (past : List app.PlayerEntry)
    (view : app.PlayerView)
    (slot : boundedCanonicalSlot (countCompletedBindings view who) past.length
      (preparedSlotFresh view.application) = canonicalFreshSlot who view.application)
    (active : who ∉ view.application.publicView.observation.defaulted) (bit : Bool) :
    prepareBindingPacket who past view 0 bit =
        ordinaryResponse who past view (eventId 0) (some (PublicationResult.success bit)) ∧
      prepareBindingPacket who past view 1 bit =
        ordinaryResponse who past view (eventId 1) (some (PublicationResult.success bit)) := by
  simp only [prepareBindingPacket, bindingSlotFresh_eq, slot]
  have sourceFirst : (canonicalReactiveDecision OddsEvensLedgerClient.timeouts
      OddsEvensService.leaks who (eventId 0) (some (PublicationResult.success bit))
      view.application) = ⟨(canonicalFreshSlot who view.application).map fun serial =>
        ⟨⟨.commitment (eventId 0) (who, .prepared serial), some ⟨.bool, bit⟩⟩, .none⟩⟩ := by
    unfold canonicalReactiveDecision
    simp only [ite_eq_right active]
    rfl
  have sourceSecond : (canonicalReactiveDecision OddsEvensLedgerClient.timeouts
      OddsEvensService.leaks who (eventId 1) (some (PublicationResult.success bit))
      view.application) = ⟨(canonicalFreshSlot who view.application).map fun serial =>
        ⟨⟨.commitment (eventId 1) (who, .prepared serial), some ⟨.bool, bit⟩⟩, .none⟩⟩ := by
    unfold canonicalReactiveDecision
    simp only [ite_eq_right active]
    rfl
  simp only [ordinaryResponse, canonicalServiceDecision, sourceFirst, sourceSecond]
  cases chosen : canonicalFreshSlot who view.application with
  | none =>
      exact ⟨rfl, rfl⟩
  | some serial =>
      have fresh := canonicalFreshSlot_spec who view.application serial chosen
      have finish (event : Fin 4) :
          (WitnessedSubmission.mk
            ⟨.commitment event (who, .prepared serial), some ⟨.bool, bit⟩⟩ .none :
              WitnessedSubmission compiled).normalizeReactive who view.application
                  (ReactiveApplication.ResponseMenu.knownPackets past view) =
            ⟨⟨.commitment event (who, .prepared serial), some ⟨.bool, bit⟩⟩, .none⟩ := by
        simp [WitnessedSubmission.normalizeReactive, Submission.normalizeReactive,
          openingEffective, fresh]
      constructor <;>
        simp only [Option.map_some, ReactiveApplication.SubmissionNormalization.action,
          reactiveNormalization, finish]

/-- Compute the ordinary binding packet using concrete player and candidate types. -/
def writeBinding (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (second : Bool) (bit : Bool) : app.Action :=
  if isDefaulted view who then ⟨none⟩
  else prepareBindingPacket who past view (if second then 1 else 0) bit

private theorem writeBinding_eq (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) (second bit : Bool)
    (slot : boundedCanonicalSlot (countCompletedBindings view who) past.length
      (preparedSlotFresh view.application) = canonicalFreshSlot who view.application) :
    writeBinding who past view second bit =
      (if second then ordinaryResponse who past view (eventId 1)
        (some (PublicationResult.success bit))
      else ordinaryResponse who past view (eventId 0) (some (PublicationResult.success bit))) := by
  by_cases defaulted : who ∈ view.application.publicView.observation.defaulted
  · have stopped : isDefaulted view who = true := by
      simpa only [isDefaulted, decide_eq_true_iff, EventPublicObservation.defaulted] using defaulted
    cases second <;> simp only [writeBinding, stopped, ↓reduceIte, Bool.false_eq_true,
      ordinaryResponse, canonicalServiceDecision, canonicalReactiveDecision, defaulted,
      ReactiveApplication.SubmissionNormalization.action]
  · have running : isDefaulted view who = false := by
      simpa only [isDefaulted, decide_eq_false_iff_not, EventPublicObservation.defaulted]
        using defaulted
    have checked := commitPacket_eq who past view slot defaulted bit
    cases second
    · simpa only [writeBinding, running, Bool.false_eq_true, ↓reduceIte] using checked.1
    · simpa only [writeBinding, running, Bool.false_eq_true, ↓reduceIte] using checked.2

/-- At an initialized callback, the finite scan and service encoding agree on
bindings, including after arbitrary earlier submissions. -/
theorem writeBinding_history (inputs : PMF compiled.Inputs) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol (inputs.map State.initial) horizon scheduler).Trace (some control))
    (who : Player) (second bit : Bool) :
    let past := (control.execution.logs who).map (ReactiveApplication.PlayerEntry.ledgerOnly app)
    let view := (control.execution.observe app who).ledgerOnly app
    writeBinding who past view second bit =
      (if second then ordinaryResponse who past view (eventId 1)
        (some (PublicationResult.success bit))
      else ordinaryResponse who past view (eventId 0) (some (PublicationResult.success bit))) := by
  dsimp only
  apply writeBinding_eq
  rw [countCompletedBindings_eq, List.length_map]
  exact boundedCanonicalSlot_history OddsEvensLedgerClient.timeouts OddsEvensService.leaks
    inputs horizon scheduler control trace who

/-- Write the service packet for the concrete decision on a callback view. -/
def writeResponse (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView) :
    Decision → app.Action
  | .silent => ⟨none⟩
  | .firstCommit bit => writeBinding who past view false bit
  | .secondCommit bit => writeBinding who past view true bit
  | .firstOpen => writeOpening who past view false
  | .secondOpen => writeOpening who past view true

private theorem writeResponse_eq_of_slot (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) (decision : Decision)
    (slot : boundedCanonicalSlot (countCompletedBindings view who) past.length
      (bindingSlotFresh view) = canonicalFreshSlot who view.application) :
    writeResponse who past view decision = encodeResponse who past view decision := by
  rw [bindingSlotFresh_eq] at slot
  cases decision with
  | silent => rfl
  | firstCommit bit => exact writeBinding_eq who past view false bit slot
  | secondCommit bit => exact writeBinding_eq who past view true bit slot
  | firstOpen => exact writeOpening_first_eq who past view
  | secondOpen => exact writeOpening_second_eq who past view

/-- Remove leaked messages from the raw callback view. -/
def keepLedger (view : app.PlayerView) : app.PlayerView :=
  { view with messages := { view.messages with leaked := [] } }

/-- Remove the leaked messages remembered from an earlier callback. -/
def keepLedgerEntry (entry : app.PlayerEntry) : app.PlayerEntry :=
  { entry with beforeView := keepLedger entry.beforeView }

/-- Produce the raw network response from a callback and one fresh coin. -/
def respondWithCoin (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (coin : Bool) : app.Action :=
  let prior := past.map keepLedgerEntry
  let current := keepLedger view
  writeResponse who prior current (decideResponse (readObservation who prior current) coin)

/-- Whenever the finite search returns the canonical slot, the raw coin-driven
response has exactly the prescribed packet law at the callback. -/
theorem respondWithCoin_distribution_of_slot (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView)
    (slot : boundedCanonicalSlot (countCompletedBindings view who) past.length
      (bindingSlotFresh view) = canonicalFreshSlot who view.application) :
    (GameTheory.Math.Probability.uniformLaw Bool).map (respondWithCoin who past view) =
      policy who past view := by
  rw [← decideResponse_distribution]
  apply congrArg (fun f => (GameTheory.Math.Probability.uniformLaw Bool).map f)
  funext coin
  simp only [respondWithCoin, readObservation_eq]
  apply writeResponse_eq_of_slot
  simpa only [List.length_map, countCompletedBindings_eq, bindingSlotFresh_eq,
    keepLedger] using slot

/-- The concrete encoder sends exactly the canonical service response on
initialized callbacks with the ledger projection of the view and recall. -/
theorem writeResponse_history (inputs : PMF compiled.Inputs) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol (inputs.map State.initial) horizon scheduler).Trace (some control))
    (who : Player) (decision : Decision) :
    let past := (control.execution.logs who).map (ReactiveApplication.PlayerEntry.ledgerOnly app)
    let view := (control.execution.observe app who).ledgerOnly app
    writeResponse who past view decision = encodeResponse who past view decision := by
  dsimp only
  cases decision with
  | silent => rfl
  | firstCommit bit =>
      exact writeBinding_history inputs horizon scheduler control trace who false bit
  | secondCommit bit =>
      exact writeBinding_history inputs horizon scheduler control trace who true bit
  | firstOpen => exact writeOpening_first_eq who _ _
  | secondOpen => exact writeOpening_second_eq who _ _

/-- On every initialized trace the executable callback has the prescribed
distribution under a fair coin. -/
theorem respondWithCoin_distribution_history (inputs : PMF compiled.Inputs) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol (inputs.map State.initial) horizon scheduler).Trace (some control))
    (who : Player) :
    let past := control.execution.logs who
    let view := control.execution.observe app who
    (GameTheory.Math.Probability.uniformLaw Bool).map (respondWithCoin who past view) =
      policy who past view := by
  dsimp only
  apply respondWithCoin_distribution_of_slot
  rw [countCompletedBindings_eq, bindingSlotFresh_eq]
  exact boundedCanonicalSlot_history OddsEvensLedgerClient.timeouts OddsEvensService.leaks
    inputs horizon scheduler control trace who

end Vegas.Examples.OddsEvensExecutableClient
