/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastCountedFiber
import Interaction.ReactiveProvenance

/-! # Literal counted controls throughout a complete raw information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Literal silence throughout own recall leaves no own output. Authentic
network provenance rules out a spurious emitted envelope in a silent entry. -/
theorem silent_own_outputs_of_history (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current)) (owner : Player)
    (silent : ∀ entry ∈ current.execution.recall owner, entry.action.transmission = none) :
    app.outputs (current.execution.recall owner) = [] := by
  classical
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro message member
  have filtered : message ∈ current.execution.network.inputs.filter
      (fun input => input.sender = owner) := by
    rw [app.history_inputRecall initial horizon selected trace owner]
    exact member
  have input := (List.mem_filter.mp filtered).1
  have sender : message.sender = owner := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp filtered).2
  have actual := app.history_provenance initial horizon selected trace
  obtain ⟨entry, recorded, material, transmitted, _emitted, _packet⟩ := actual.inputs message input
  rw [sender] at recorded
  rw [silent entry recorded] at transmitted
  cases transmitted

/-- Each history sharing a counted decision's complete input has a counted
trace at its identical physical control, with the exact original own recall
and view. No reach or foreign-policy restriction is required. -/
theorem counted_information_raw_fiber_control
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (target : rawModel.InformationHistory owner (countedModel.infoOf owner source.trace)) :
    ∃ count next, target.1.state = some (⟨count, some owner, next⟩ : app.Control) ∧
      Nonempty (countedProtocol.Trace (some ⟨count, some owner, next⟩)) ∧
      next.recall owner = execution.recall owner ∧
      next.observe app owner = execution.observe app owner := by
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩) :=
    current ▸ source.trace
  have sourceInfo : countedModel.infoOf owner source.trace =
      some (execution.recall owner, execution.observe app owner) := by
    change (countedMenu.signals initial horizon scheduler).infoOf owner source.trace = _
    rw [countedMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  have info := ((rawMenu.info initial horizon scheduler owner target.1.trace).symm.trans
    target.2).trans sourceInfo
  cases state : target.1.state with
  | none => simp only [ReactiveApplication.observe, state] at info; cases info
  | some control =>
    rcases control with ⟨count, actor, next⟩
    by_cases active : actor = some owner
    · subst actor
      simp only [ReactiveApplication.observe, state, ite_true] at info
      have pair := Option.some.inj info
      have recalled : next.recall owner = execution.recall owner := congrArg Prod.fst pair
      have observed : next.observe app owner = execution.observe app owner := congrArg Prod.snd pair
      have rawTrace : rawProtocol.Trace (some ⟨count, some owner, next⟩) :=
        state ▸ target.1.trace
      have counted := counted_input_raw_fiber_trace scheduler scheduler
        ⟨remaining, some owner, execution⟩ ⟨count, some owner, next⟩ sourceTrace rawTrace
          owner rfl rfl recalled.symm observed.symm
      exact ⟨count, next, rfl, counted, recalled, observed⟩
    · simp only [ReactiveApplication.observe, state, active, ite_false] at info
      cases info

end Vegas.Examples.CommitSeedBroadcast
