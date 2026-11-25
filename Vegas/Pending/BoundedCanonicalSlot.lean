module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveCandidateBudget
public import Vegas.Pending.ReactiveCanonicalDecision

@[expose] public section

/-! # Computing the canonical prepared slot from finite recall -/

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Check the preferred public slot first. A player's own response count bounds
the subsequent search even if earlier packets mentioned arbitrarily large serials. -/
def boundedCanonicalSlot (preferred recallLength : Nat) (fresh : Nat → Bool) : Option Nat :=
  if fresh preferred then some preferred else (List.range (recallLength + 1)).find? fresh

/-- Inspecting the candidate tag does not require equality on private values. -/
def preparedSlotFresh (view : PlayerView graph) (serial : Nat) : Bool :=
  match view.candidates (.prepared serial) with
  | .fresh => true
  | .unopenable | .openable _ => false

omit [DecidableEq Player] in
private theorem preparedSlotFresh_spec (view : PlayerView graph) (serial : Nat) :
    preparedSlotFresh view serial = true ↔ view.candidates (.prepared serial) = .fresh := by
  unfold preparedSlotFresh
  cases view.candidates (.prepared serial) <;> simp

/-- At every initialized service history, finite slot selection implements the
canonical packet client's choice, including after arbitrary player deviations. -/
theorem boundedCanonicalSlot_history (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (control : ((reactiveApplication timeouts) leaks).Control)
    (trace : (((reactiveApplication timeouts) leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control)) (who : Player) :
    let view := (control.execution.observe ((reactiveApplication timeouts) leaks) who).application
    boundedCanonicalSlot (view.publicView.bindingCount who) (control.execution.logs who).length
      (preparedSlotFresh view) = canonicalFreshSlot who view := by
  classical
  dsimp only
  let view := (control.execution.observe ((reactiveApplication timeouts) leaks) who).application
  let count := view.publicView.bindingCount who
  change boundedCanonicalSlot count _ (preparedSlotFresh view) = canonicalFreshSlot who view
  by_cases preferred : view.candidates (.prepared count) = .fresh
  · rw [canonicalFreshSlot_canonical who view preferred]
    simp [boundedCanonicalSlot, (preparedSlotFresh_spec _ _).mpr preferred, count]
  have skipped : preparedSlotFresh view count = false := by
    exact Bool.eq_false_iff.mpr (fun found => preferred ((preparedSlotFresh_spec _ _).mp found))
  obtain ⟨serial, bound, selected⟩ := reactiveFreshSlot_le_recall timeouts leaks
    control.execution who (candidateRecall_history timeouts leaks inputs horizon scheduler trace)
  change reactiveFreshSlot view = some serial at selected
  have fresh := reactiveFreshSlot_spec view serial selected
  unfold canonicalFreshSlot
  change boundedCanonicalSlot count _ _ =
    if view.candidates (.prepared count) = .fresh then some count else reactiveFreshSlot view
  rw [ite_eq_right preferred, selected]
  simp only [boundedCanonicalSlot, skipped, Bool.false_eq_true, ↓reduceIte]
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨(preparedSlotFresh_spec _ _).mpr fresh, serial, by simpa using bound, by simp, ?_⟩
  intro j earlier
  simp only [List.getElem_range, Bool.not_eq_true']
  unfold reactiveFreshSlot at selected
  split at selected
  · rename_i existsFresh
    cases Option.some.inj selected
    exact Bool.eq_false_iff.mpr (fun found =>
      Nat.find_min existsFresh earlier ((preparedSlotFresh_spec _ _).mp found))
  · contradiction

end Vegas.EventGraphRuntime
