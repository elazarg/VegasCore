/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseSemanticProgress

/-! # Native store preservation when normalization creates no exclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Without a new exclusion, automatic phase completion preserves every
previously written typed cell. -/
theorem settle_keepsStore_of_no_new_exclusion (phases : List (RuntimePhase graph))
    (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (noNew : current.excluded ⊆ entry.excluded) :
    KeepsStore current.native (settle phases generation entry current retired).current.native := by
  induction phases generalizing generation entry current retired with
  | nil => exact fun _ _ stored => stored
  | cons phase remaining ih =>
    have noFailure : ¬ (phase.kind = .commitment ∧
        (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty) := by
      rw [phase.drain_excluded, Finset.sdiff_eq_empty_iff_subset.mpr noNew]
      simp only [Finset.empty_inter, Finset.not_nonempty_empty, and_false, not_false_eq_true]
    by_cases finished : phase.Finished (phase.drain current)
    · rw [settle_clean phase remaining generation entry current retired finished noFailure]
      have next := ih generation (phase.drain current) (phase.drain current) retired
        (Finset.Subset.refl _)
      exact fun field value stored => next field value
        (phase.drain_keepsStore current field value stored)
    · simpa only [settle, ite_eq_right finished] using phase.drain_keepsStore current

/-- Closing a noncommitment phase cannot restore its just-written cells.
Every later automatic phase starts from the state it has just saved. -/
theorem normalize_keepsStore_of_noncommitment (state : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : state.phases = phase :: remaining) (kind : phase.kind ≠ .commitment) :
    KeepsStore state.current.native state.normalize.current.native := by
  classical
  change KeepsStore state.current.native
    (settle state.phases state.generation state.entry state.current state.retired).current.native
  rw [installed]
  have noFailure : ¬ (phase.kind = .commitment ∧
      (((phase.drain state.current).excluded \ state.entry.excluded) ∩ phase.owners).Nonempty) :=
    fun failure => kind failure.1
  by_cases finished : phase.Finished (phase.drain state.current)
  · rw [settle_clean phase remaining state.generation state.entry state.current state.retired
      finished noFailure]
    have tail := settle_keepsStore_of_no_new_exclusion remaining state.generation
      (phase.drain state.current) (phase.drain state.current) state.retired (Finset.Subset.refl _)
    exact fun field value present => tail field value
      (phase.drain_keepsStore state.current field value present)
  · simpa only [settle, ite_eq_right finished] using phase.drain_keepsStore state.current

/-- An allowed public sample survives every subsequent automatic phase. -/
theorem normalize_sample_output (state : PhaseRuntimeState graph)
    (event : graph.EventId) (ready : state.current.native.config.cut.Ready event)
    (payload : L.Ty) (outputEq : graph.outputLayout event = .publicData payload)
    (allowed : state.commandAllowed (.executeSample event) = true)
    (value : (graph.outputLayout event).Value) :
    ({ state with current := (state.current.environmentResult (.executeSample event)
      (state.current.native.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) value)) } :
      PhaseRuntimeState graph).normalize.current.native.config.outputs event = some value := by
  obtain ⟨phase, remaining, installed⟩ :
      ∃ phase remaining, state.phases = phase :: remaining := by
    cases phases : state.phases with
    | nil => simp only [commandAllowed, phases, List.head?_nil, Option.any_none,
        Bool.false_eq_true] at allowed
    | cons phase remaining => exact ⟨phase, remaining, rfl⟩
  have inside : event ∈ phase.events := by
    simpa only [commandAllowed, installed, List.head?_cons, Option.any_some,
      decide_eq_true_eq] using allowed
  have notCommitment : phase.kind ≠ .commitment := by
    intro commitment
    have fields := phase.fields event ((phase.mem_events event).mp inside).1
      ((phase.mem_events event).mp inside).2
    rw [commitment] at fields
    obtain ⟨owner, ty, binding⟩ := fields
    rw [outputEq] at binding
    cases binding
  have kept := normalize_keepsStore_of_noncommitment
    ({ state with current := (state.current.environmentResult (.executeSample event)
      (state.current.native.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) value)) } :
      PhaseRuntimeState graph) phase remaining installed notCommitment
  exact kept (.inr event) value (Config.complete_output_same _ _ _ _ _)

/-- At one fixed physical state, the public result identifies every supported
application-command outcome. The only random command writes a public sample,
and that sample survives all subsequent automatic phase installation. -/
theorem environment_eq_of_publicView (runtime : EventGraphRuntime graph)
    (state first second : PhaseRuntimeState graph) (command : EnvironmentCommand graph)
    (left : first ∈ (state.environment runtime command).support)
    (right : second ∈ (state.environment runtime command).support)
    (same : first.publicView = second.publicView) : first = second := by
  classical
  unfold environment at left right
  split at left
  · rename_i allowed
    rw [ite_eq_left allowed] at right
    obtain ⟨firstNative, firstSupported, rfl⟩ := (PMF.mem_support_map_iff ..).mp left
    obtain ⟨secondNative, secondSupported, rfl⟩ := (PMF.mem_support_map_iff ..).mp right
    cases command with
    | advanceClock =>
        simp only [environmentStep, PMF.mem_support_pure_iff] at firstSupported secondSupported
        rw [firstSupported, secondSupported]
    | expire event =>
        simp only [environmentStep, PMF.mem_support_pure_iff] at firstSupported secondSupported
        rw [firstSupported, secondSupported]
    | executeSample event =>
        by_cases ready : state.current.native.config.cut.Ready event
        · cases node : nodeView graph event with
          | bind owner payload outputEq codeEq =>
              have law := environmentStep_executeSample_of_nonsample runtime state.current.native
                event ready (by intro ty law output code impossible; rw [node] at impossible
                                cases impossible)
              rw [law, PMF.mem_support_pure_iff] at firstSupported secondSupported
              rw [firstSupported, secondSupported]
          | resolve owner payload binding checks outputEq codeEq =>
              have law := environmentStep_executeSample_of_nonsample runtime state.current.native
                event ready (by intro ty law output code impossible; rw [node] at impossible
                                cases impossible)
              rw [law, PMF.mem_support_pure_iff] at firstSupported secondSupported
              rw [firstSupported, secondSupported]
          | sample payload law outputEq codeEq =>
              have applicationLaw := environmentStep_executeSample_eq runtime state.current.native
                event ready payload law outputEq codeEq node
              rw [applicationLaw] at firstSupported secondSupported
              obtain ⟨firstConfig, firstStep, rfl⟩ :=
                (PMF.mem_support_map_iff ..).mp firstSupported
              obtain ⟨secondConfig, secondStep, rfl⟩ :=
                (PMF.mem_support_map_iff ..).mp secondSupported
              rw [Config.step] at firstStep secondStep
              obtain ⟨firstValue, _firstDraw, rfl⟩ := (PMF.mem_support_map_iff ..).mp firstStep
              obtain ⟨secondValue, _secondDraw, rfl⟩ := (PMF.mem_support_map_iff ..).mp secondStep
              let next (value : (graph.outputLayout event).Value) : PhaseRuntimeState graph :=
                { state with current := (state.current.environmentResult (.executeSample event)
                  (state.current.native.complete event ready
                    (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) value)) }
              have output (value : (graph.outputLayout event).Value) :
                  (next value).normalize.current.native.config.outputs event = some value := by
                exact normalize_sample_output state event ready payload outputEq allowed value
              have observed := congrArg (fun view : PhasePublicView graph =>
                view.native.observation.store) same
              have visible : graph.fieldPublic (.inr event) := by
                change (graph.outputLayout event).IsPublic
                rw [outputEq]
                trivial
              have stored := congrFun observed (.inr event)
              change graph.publicStore (next firstValue).normalize.current.native.config.store
                  (.inr event) =
                graph.publicStore (next secondValue).normalize.current.native.config.store
                  (.inr event) at stored
              rw [publicStore_of_public _ _ _ visible, publicStore_of_public _ _ _ visible]
                at stored
              change (next firstValue).normalize.current.native.config.outputs event =
                (next secondValue).normalize.current.native.config.outputs event at stored
              rw [output firstValue, output secondValue] at stored
              cases Option.some.inj stored
              rfl
        · rw [environmentStep_executeSample_of_not_ready runtime state.current.native event ready,
            PMF.mem_support_pure_iff] at firstSupported secondSupported
          rw [firstSupported, secondSupported]
  · rename_i disallowed
    rw [ite_eq_right disallowed, PMF.mem_support_pure_iff] at right
    exact ((PMF.mem_support_pure_iff _ _).mp left).trans right.symm

end PhaseRuntimeState

end Vegas.EventGraphRuntime
