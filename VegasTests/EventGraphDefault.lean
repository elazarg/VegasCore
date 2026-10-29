/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.Semantics
import Vegas.Expr.Simple

/-! # Binding omission, unusable admission and public default records -/

namespace VegasTests

open Vegas Vegas.EventGraph GameTheory.Math.Probability

private def bindingLayout : Unit → EventField Unit simpleExpr := fun _ => .binding () .bool

private def bindingCode : EventCode bindingLayout (.binding () .bool) :=
  .bind (L := simpleExpr) () .bool

/-- Both choices store an unusable binding, but only omission is a public failure. -/
example : bindingCode.eval? none (fun _ => none) =
      bindingCode.eval? (some .failure) (fun _ => none) ∧
    bindingCode.defaultEvent none .failure = some () ∧
    bindingCode.defaultEvent (some .failure) .failure = none :=
  ⟨rfl, rfl, rfl⟩

private def twoBindings : Vegas.EventGraph Unit simpleExpr where
  inputCount := 0
  order := ⟨2, fun _ => ∅, fun {_ _} member => by simp at member⟩
  inputLayout := fun input => Fin.elim0 input
  outputLayout := fun _ => .binding () .bool
  nodes := fun _ => .bind (L := simpleExpr) () .bool
  reads_available := fun _ _ member => by simp [EventCode.readFields] at member
  payoffs := []

private def admitted : twoBindings.Completion :=
  Completion.fromDecision ⟨0, by decide⟩ (some (some .failure)) .failure

private def omitted : twoBindings.Completion :=
  Completion.fromDecision ⟨1, by decide⟩ (some none) .failure

private def automatic : twoBindings.Completion :=
  Completion.fromDecision ⟨1, by decide⟩ none .failure

/-- Original unusable admission and deliberate omission remain distinguishable. -/
example : admitted.defaultEvent = none ∧ omitted.defaultEvent = some () ∧
    admitted.decision = some (some .failure) ∧ omitted.decision = some none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A mechanical completion adds neither a choice nor a new public default. -/
example : automatic.decision = none ∧ automatic.defaultEvent = none := ⟨rfl, rfl⟩

/-- The chronological record determines both public timing and the current default set. -/
example : (Completion.defaults [admitted, omitted]).events = [some (), none] ∧
    (Completion.defaults [admitted, omitted]).defaulted = {()} := by
  exact ⟨rfl, by simp [Completion.defaults, DefaultHistory.defaulted, admitted, omitted,
    Completion.fromDecision, EventCode.defaultEvent, EventCode.causesDefault, EventCode.actor,
    twoBindings]⟩

end VegasTests

namespace VegasTests

open Vegas Vegas.EventGraph GameTheory.Math.Probability

private def bindingInitial : twoBindings.Config :=
  Config.initial (fun input => Fin.elim0 input)

private theorem firstBinding_ready : bindingInitial.cut.Ready ⟨0, by decide⟩ := by decide

private theorem secondBinding_ready : bindingInitial.cut.Ready ⟨1, by decide⟩ := by decide

private def afterOmission : twoBindings.Config :=
  bindingInitial.complete ⟨0, by decide⟩ firstBinding_ready none .failure

private def afterUnusable : twoBindings.Config :=
  bindingInitial.complete ⟨0, by decide⟩ firstBinding_ready (some .failure) .failure

private theorem secondBinding_ready_afterOmission : afterOmission.cut.Ready ⟨1, by decide⟩ :=
  secondBinding_ready.after_complete firstBinding_ready (by decide)

private theorem secondBinding_ready_afterUnusable : afterUnusable.cut.Ready ⟨1, by decide⟩ :=
  secondBinding_ready.after_complete firstBinding_ready (by decide)

/-- The first public omission is produced by the actual graph step. -/
example : bindingInitial.step ⟨0, by decide⟩ firstBinding_ready none =
    PMF.pure afterOmission := by
  unfold Config.step
  change (PMF.pure (PublicationResult.failure : PublicationResult Bool)).map _ = _
  rw [PMF.pure_map]
  rfl

/-- Admitting an unusable binding is also an actual, distinct graph decision. -/
example : bindingInitial.step ⟨0, by decide⟩ firstBinding_ready (some .failure) =
    PMF.pure afterUnusable := by
  unfold Config.step
  change (PMF.pure (PublicationResult.failure : PublicationResult Bool)).map _ = _
  rw [PMF.pure_map]
  rfl

private def bindingExecutionSummary (config : twoBindings.Config) :=
  (config.outputs ⟨0, by decide⟩, config.outputs ⟨1, by decide⟩,
    config.defaulted, config.defaults.events,
    config.history.map (fun completion =>
      (completion.decision : Option (Option (PublicationResult Bool)))))

/-- A requested successful binding after public omission is forced to fail;
the mechanical completion records no actual decision and no repeated default. -/
example : (afterOmission.step ⟨1, by decide⟩ secondBinding_ready_afterOmission
      (some (.success true))).map bindingExecutionSummary =
    PMF.pure (some PublicationResult.failure, some PublicationResult.failure,
      ({()} : Finset Unit), [none, some ()], [some none, none]) := by
  unfold Config.step
  change ((PMF.pure (PublicationResult.failure : PublicationResult Bool)).map _).map _ = _
  rw [PMF.pure_map, PMF.pure_map]
  rfl

/-- An unusable admitted binding leaves the next binding active and successful. -/
example : (afterUnusable.step ⟨1, by decide⟩ secondBinding_ready_afterUnusable
      (some (.success true))).map bindingExecutionSummary =
    PMF.pure (some PublicationResult.failure, some (PublicationResult.success true),
      (∅ : Finset Unit), [none, none],
      [some (some PublicationResult.failure), some (some (PublicationResult.success true))]) := by
  unfold Config.step
  change ((PMF.pure (PublicationResult.success true : PublicationResult Bool)).map _).map _ = _
  rw [PMF.pure_map, PMF.pure_map]
  rfl

/-- Public default timing remains visible, while automatic completion contributes
no action to the player's actual recall. -/
example : (afterOmission.step ⟨1, by decide⟩ secondBinding_ready_afterOmission
      (some (.success true))).map (fun final =>
        ((twoBindings.publicObserve final).defaults.events,
          (twoBindings.playerObserve () final).ownActions.map fun completion =>
            (completion.decision : Option (Option (PublicationResult Bool))))) =
    PMF.pure ([none, some ()], [some none]) := by
  unfold Config.step
  change ((PMF.pure (PublicationResult.failure : PublicationResult Bool)).map _).map _ = _
  rw [PMF.pure_map, PMF.pure_map]
  rfl

private def afterSecondBinding : twoBindings.Config :=
  bindingInitial.complete ⟨1, by decide⟩ secondBinding_ready (some (.success true)) (.success true)

private theorem firstBinding_ready_afterSecondBinding :
    afterSecondBinding.cut.Ready ⟨0, by decide⟩ :=
  firstBinding_ready.after_complete secondBinding_ready (by decide)

/-- The successful second binding is itself a supported execution from the initial cut. -/
example : bindingInitial.step ⟨1, by decide⟩ secondBinding_ready (some (.success true)) =
    PMF.pure afterSecondBinding := by
  unfold Config.step
  change (PMF.pure (PublicationResult.success true : PublicationResult Bool)).map _ = _
  rw [PMF.pure_map]
  rfl

/-- Two ready actions need not commute: omission suppresses a later same-owner action. -/
example :
    (afterOmission.step ⟨1, by decide⟩ secondBinding_ready_afterOmission
      (some (.success true))).map (fun final => final.outputs ⟨1, by decide⟩) ≠
    (afterSecondBinding.step ⟨0, by decide⟩ firstBinding_ready_afterSecondBinding none).map
      (fun final => final.outputs ⟨1, by decide⟩) := by
  unfold Config.step
  change ((PMF.pure (PublicationResult.failure : PublicationResult Bool)).map _).map _ ≠
    ((PMF.pure (PublicationResult.failure : PublicationResult Bool)).map _).map _
  rw [PMF.pure_map, PMF.pure_map, PMF.pure_map, PMF.pure_map]
  change PMF.pure (some (PublicationResult.failure : PublicationResult Bool)) ≠
    PMF.pure (some (PublicationResult.success true : PublicationResult Bool))
  intro same
  have contradiction := congrArg
    (fun law : PMF (Option (PublicationResult Bool)) => law (some .failure)) same
  simp at contradiction

end VegasTests
