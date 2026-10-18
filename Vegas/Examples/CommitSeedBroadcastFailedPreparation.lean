/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPayoffs
import Vegas.Examples.CommitSeedBroadcastBindingPersistence
import Vegas.Pending.PhaseRecordedBindingMaterial

/-! # Unusable original preparations and standing native binding failures -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The actual submitted preparation fixes its failed meaning permanently,
including arbitrary evidence requests and later raw continuations. -/
theorem recorded_unusable_binding_result (selected : app.Scheduler)
    (current : app.Control)
    (trace : (countedMenu.protocol initial horizon selected).Trace (some current))
    (owner : Player) (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall owner)
    (event : graph.EventId) (serial : Nat) (opening : Option (Raw simpleExpr))
    (evidence : EvidenceRequest graph)
    (declared : entry.action =
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (unusable : (opening.bind fun raw => raw.as? .bool) = none) :
    current.execution.application.current.native.bindingResult
      (owner, .prepared serial) .bool = .failure := by
  have result := phase_recorded_material_binding_result runtime leaks countedMenu initial horizon
    selected current trace owner event .bool serial opening evidence entry recorded declared fresh
  simpa only [unusable, Option.elim_none] using result

/-- A standing failed typed binding cannot produce a successful terminal
publication under any later policy. This is actual native reachability. -/
theorem failed_binding_publication (native : EventGraphRuntime.State graph)
    (valid : native.Invariant (encodeInputs (Env.empty (CellVal simpleExpr))))
    (complete : native.config.cut.Terminal) (owner : Player)
    (failed : native.config.outputs (bindingEvent owner) = some
      (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.failure : PublicationResult Bool))) :
    RecoveryState.publicationFailed native (revealEvent owner) = true := by
  classical
  fin_cases owner
  · have present : revealEvent alice ∈ native.config.cut.completed := by
      rw [complete]
      exact Finset.mem_univ _
    obtain ⟨result, output⟩ := Option.isSome_iff_exists.mp
      ((native.config.output_available (revealEvent alice)).mpr present)
    have failedOutput : native.config.outputs (revealEvent alice) = some .failure := by
      cases result with
      | failure => exact output
      | success value =>
          have binding := valid.reachable.publication_binding (revealEvent alice) alice .bool
            ⟨.inr (bindingEvent alice), bindingEvent_layout alice⟩ _ rfl rfl value output
          change native.config.outputs (bindingEvent alice) = some (.success value) at binding
          change native.config.outputs (bindingEvent alice) = some .failure at failed
          rw [failed] at binding
          cases binding
    change RecoveryState.publicationFailed native (revealEvent alice) = true
    cases node : nodeView graph (revealEvent alice) with
    | bind author payload kind code => cases kind.symm.trans (revealEvent_layout alice)
    | sample payload law kind code => cases kind.symm.trans (revealEvent_layout alice)
    | resolve author payload binding checks kind code =>
        have same := EventField.publication.inj (kind.symm.trans (revealEvent_layout alice))
        subst payload
        rw [RecoveryState.publicationFailed, node, failedOutput]
        rfl
  · have present : revealEvent bob ∈ native.config.cut.completed := by
      rw [complete]
      exact Finset.mem_univ _
    obtain ⟨result, output⟩ := Option.isSome_iff_exists.mp
      ((native.config.output_available (revealEvent bob)).mpr present)
    have failedOutput : native.config.outputs (revealEvent bob) = some .failure := by
      cases result with
      | failure => exact output
      | success value =>
          have binding := valid.reachable.publication_binding (revealEvent bob) bob .bool
            ⟨.inr (bindingEvent bob), bindingEvent_layout bob⟩ _ rfl rfl value output
          change native.config.outputs (bindingEvent bob) = some (.success value) at binding
          change native.config.outputs (bindingEvent bob) = some .failure at failed
          rw [failed] at binding
          cases binding
    change RecoveryState.publicationFailed native (revealEvent bob) = true
    cases node : nodeView graph (revealEvent bob) with
    | bind author payload kind code => cases kind.symm.trans (revealEvent_layout bob)
    | sample payload law kind code => cases kind.symm.trans (revealEvent_layout bob)
    | resolve author payload binding checks kind code =>
        have same := EventField.publication.inj (kind.symm.trans (revealEvent_layout bob))
        subst payload
        rw [RecoveryState.publicationFailed, node, failedOutput]
        rfl
  · have present : revealEvent carol ∈ native.config.cut.completed := by
      rw [complete]
      exact Finset.mem_univ _
    obtain ⟨result, output⟩ := Option.isSome_iff_exists.mp
      ((native.config.output_available (revealEvent carol)).mpr present)
    have failedOutput : native.config.outputs (revealEvent carol) = some .failure := by
      cases result with
      | failure => exact output
      | success value =>
          have binding := valid.reachable.publication_binding (revealEvent carol) carol .bool
            ⟨.inr (bindingEvent carol), bindingEvent_layout carol⟩ _ rfl rfl value output
          change native.config.outputs (bindingEvent carol) = some (.success value) at binding
          change native.config.outputs (bindingEvent carol) = some .failure at failed
          rw [failed] at binding
          cases binding
    change RecoveryState.publicationFailed native (revealEvent carol) = true
    cases node : nodeView graph (revealEvent carol) with
    | bind author payload kind code => cases kind.symm.trans (revealEvent_layout carol)
    | sample payload law kind code => cases kind.symm.trans (revealEvent_layout carol)
    | resolve author payload binding checks kind code =>
        have same := EventField.publication.inj (kind.symm.trans (revealEvent_layout carol))
        subst payload
        rw [RecoveryState.publicationFailed, node, failedOutput]
        rfl

/-- A failed standing binding has the exact exclusion payoff at every clean
completed native endpoint; future rationality is not needed. -/
theorem standing_failed_binding_terminal_payoff
    (history : rawProtocol.History) (current : app.Control)
    (state : history.state = some current)
    (complete : current.execution.application.current.native.config.cut.Terminal)
    (owner : Player) (clean : OwnPermitted owner current.execution)
    (failed : current.execution.application.current.native.config.outputs (bindingEvent owner) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.failure : PublicationResult Bool))) :
    rawPayoff owner history = -(3 / 2) := by
  have trace := rawMenu.toRawTrace initial horizon scheduler history.trace
  rw [state] at trace
  have valid := raw_native_valid scheduler current trace
  have compiled := trace
  rw [initial_eq_compiled] at compiled
  have coverage := phaseFailureCoverage_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon scheduler compiled
  have published := failed_binding_publication current.execution.application.current.native
    valid.active complete owner failed
  have excluded := coverage.active.covered (revealEvent owner) owner (reveal_actor owner)
    (Or.inr published)
  rw [rawPayoff_terminal_formula history current state complete owner clean,
    ite_eq_left excluded]

/-- After the commitment block closes, its failed binding cell survives every
subsequent raw response and environment operation. -/
theorem completed_binding_failure_persists (selected : app.Scheduler)
    (players : Player → app.Policy) (remaining count : Nat) (before after : app.Execution)
    (trace : (app.protocol initial horizon selected).Trace (some ⟨remaining, none, before⟩))
    (allDone : ∀ owner, bindingEvent owner ∈ before.application.current.native.config.cut.completed)
    (supported : after ∈ (app.runRounds selected players count before).support)
    (owner : Player)
    (failed : before.application.current.native.config.outputs (bindingEvent owner) = some
      (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.failure : PublicationResult Bool))) :
    after.application.current.native.config.outputs (bindingEvent owner) = some
      (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.failure : PublicationResult Bool)) := by
  have tail := completed_bindings_publication_tail selected _ trace allDone
  exact publication_tail_run_keepsStore selected players count before after tail supported
    (.inr (bindingEvent owner)) _ failed

end Vegas.Examples.CommitSeedBroadcast
