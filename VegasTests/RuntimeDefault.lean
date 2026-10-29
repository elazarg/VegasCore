/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveRuntime
import Vegas.Expr.Simple

/-! # Public omission and opaque unusability in the ledger runtime -/

noncomputable section

namespace VegasTests

open Vegas Vegas.EventGraph Vegas.EventGraphRuntime GameTheory.Math.Probability Interaction

private def defaultGraph : Vegas.EventGraph Unit simpleExpr where
  inputCount := 0
  order := EventOrder.sequential 2
  inputLayout := fun input => Fin.elim0 input
  outputLayout := fun _ => .binding () .bool
  nodes := fun _ => .bind (L := simpleExpr) () .bool
  reads_available := fun _ _ member => by simp [EventCode.readFields] at member
  payoffs := []

private def defaultRuntime : EventGraphRuntime defaultGraph where
  deadline _ := 1

private def runtimeInitial : State defaultGraph :=
  State.initial (fun input => Fin.elim0 input)

private abbrev firstEvent : defaultGraph.EventId := ⟨0, by decide⟩

private abbrev unusableHandle : Handle defaultGraph := ((), .prepared 0)

private def unusableCall : Message Unit (Payload defaultGraph) :=
  ⟨((), 0), .commitment firstEvent unusableHandle⟩

private theorem runtimeFirst_ready : runtimeInitial.config.cut.Ready firstEvent := by decide

private def runtimeOmission : State defaultGraph :=
  { runtimeInitial with clock := 1 } |>.complete firstEvent runtimeFirst_ready none .failure

/-- Silence is recorded in private recall, and leaves the ledger configuration untouched. -/
example (leaks : MessageNetwork.ObservationRule Unit (WitnessedPacket defaultGraph))
    (execution : (defaultRuntime.reactiveApplication leaks).Execution) :
    (execution.respond (defaultRuntime.reactiveApplication leaks) () ⟨none⟩).application =
      execution.application := rfl

/-- Before its relative deadline, expiry does not resolve a binding omission. -/
example : environmentStep defaultRuntime runtimeInitial (.expire firstEvent) =
    PMF.pure runtimeInitial := by
  apply environmentStep_expire_of_not_due _ _ _ runtimeFirst_ready (entered := 0)
  · rfl
  · decide

/-- An accepted fresh handle is unusable but creates no public default. -/
example : (handle defaultRuntime runtimeInitial unusableCall).map
      (fun state => (state.config.defaulted, state.config.defaults.events)) =
    some (∅, [none]) := by
  have vacant : runtimeInitial.accepted (.inr firstEvent) = none := rfl
  have unused : runtimeInitial.HandleUnused unusableHandle := by
    intro field accepted
    obtain ⟨input, _, _, _, _, _⟩ :=
      State.initial_accepted_eq_some _ field unusableHandle accepted
    exact Fin.elim0 input
  have accepted := handle_commitment_eq defaultRuntime runtimeInitial ((), 0) firstEvent
    unusableHandle () .bool rfl rfl rfl runtimeFirst_ready (by change 0 < 1; decide) (by decide)
    rfl rfl vacant unused
  change (handle defaultRuntime runtimeInitial ⟨((), 0),
    .commitment firstEvent unusableHandle⟩).map _ = _
  rw [accepted]
  rfl

/-- Due expiry records the absent binding choice and the owner's public default. -/
private theorem runtimeExpiry :
    environmentStep defaultRuntime { runtimeInitial with clock := 1 }
      (.expire firstEvent) = PMF.pure runtimeOmission := by
  exact environmentStep_expire_bind_eq defaultRuntime { runtimeInitial with clock := 1 }
    firstEvent runtimeFirst_ready 0 rfl (by change 1 ≤ 1; decide)
    () .bool rfl rfl rfl

/-- The unified application services later defaulted instructions without player calls. -/
private theorem runtimeDrain_terminal : runtimeOmission.drain.config.cut.Terminal := by
  by_contra unfinished
  obtain ⟨event, ready⟩ :=
    runtimeOmission.drain.config.cut.exists_ready_of_not_terminal unfinished
  apply runtimeOmission.drain_quiescent event
  refine ⟨ready, ?_⟩
  change () ∈ runtimeOmission.drain.config.defaulted
  rw [runtimeOmission.drain_defaulted]
  decide

/-- Application expiry atomically completes later defaulted instructions. -/
example (leaks : MessageNetwork.ObservationRule Unit (WitnessedPacket defaultGraph)) :
    ((defaultRuntime.reactiveApplication leaks).environment
      { runtimeInitial with clock := 1 } (.expire firstEvent)).map
        (fun state => decide state.config.cut.Terminal) = PMF.pure true := by
  change (((environmentStep defaultRuntime { runtimeInitial with clock := 1 }
    (.expire firstEvent)).map State.drain).map _) = _
  rw [runtimeExpiry, PMF.pure_map, PMF.pure_map]
  simp only [runtimeDrain_terminal, decide_true]

/-- Public default rejects admission at an otherwise ready, timely binding. -/
example : runtimeOmission.config.cut.Ready ⟨1, by decide⟩ ∧
    runtimeOmission.WithinDeadline defaultRuntime ⟨1, by decide⟩ ∧
    handle defaultRuntime runtimeOmission
      ⟨((), 1), .commitment ⟨1, by decide⟩ unusableHandle⟩ = none := by
  refine ⟨by decide, ?_, ?_⟩
  · change 0 < 1
    decide
  · simp only [handle, Message.sender]
    split
    · rfl
    · rename_i active
      exact (active (by decide)).elim

end VegasTests
