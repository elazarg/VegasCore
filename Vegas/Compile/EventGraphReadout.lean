/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphObservation
import Vegas.Compile.EventGraphState
import Vegas.EventGraph.Semantics

/-! # Typed source-state readout from event-graph stores

Unlike player observations, terminal readout reconstructs every source cell.
The decoder remains partial: it returns `none` whenever a referenced graph
field is unavailable, and never invents a binding or publication result.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Reconstruct a complete source prefix from its cell references. -/
def decodeState? {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L} :
    {Γ : SourceCtx Player L} → ContextRefs layout Γ →
      Vegas.EventGraph.Store layout → Option (State L Γ)
  | [], _, _ => some (Env.empty (CellVal L))
  | (name, .publicData payload) :: Γ, refs, store => do
      let head ← (refs.get (HasVar.here :
        HasVar ((name, .publicData payload) :: Γ) name (.publicData payload))).get? store
      let tail ← decodeState? refs.tail store
      pure (Env.cons head tail)
  | (name, .publication payload) :: Γ, refs, store => do
      let head ← (refs.get (HasVar.here :
        HasVar ((name, .publication payload) :: Γ) name (.publication payload))).get? store
      let tail ← decodeState? refs.tail store
      pure (Env.cons head tail)
  | (name, .privateData owner payload) :: Γ, refs, store => do
      let binding ← (refs.get (HasVar.here :
        HasVar ((name, .privateData owner payload) :: Γ) name
          (.privateData owner payload))).get? store
      let tail ← decodeState? refs.tail store
      pure (Env.cons binding tail)

omit [DecidableEq Player] R in
/-- Context-reference agreement makes full-state readout exact. -/
theorem decodeState?_eq_some {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (refsAgree : refs.Agrees state store) :
    decodeState? refs store = some state := by
  induction Γ with
  | nil =>
      apply congrArg some
      funext name cell source
      nomatch source
  | cons entry Γ ih =>
      obtain ⟨name, cell⟩ := entry
      have tail := ih refs.tail (fun _ _ source => state.get (.there source))
        fun source => refsAgree (.there source)
      have head := refsAgree (HasVar.here : HasVar ((name, cell) :: Γ) name cell)
      cases cell <;>
      · rw [decodeState?, head, tail]
        apply congrArg some
        funext readName readCell source
        cases source <;> rfl

omit [DecidableEq Player] R in
private theorem exists_decodeState_agrees {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L} :
    {Γ : SourceCtx Player L} → (refs : ContextRefs layout Γ) →
    (store : Vegas.EventGraph.Store layout) →
    (∀ field, (store field).isSome = true) →
    ∃ state, decodeState? refs store = some state ∧ refs.Agrees state store
  | [], _, _, _ => by
      refine ⟨Env.empty (CellVal L), rfl, ?_⟩
      intro name cell source
      nomatch source
  | (name, cell) :: Γ, refs, store, available => by
      have headSome := (refs.get (HasVar.here : HasVar ((name, cell) :: Γ) name cell)).get?_isSome
        store (available (refs.get HasVar.here).field)
      obtain ⟨tail, tailEq, tailAgree⟩ := exists_decodeState_agrees refs.tail store available
      cases cell <;>
      · cases headEq : (refs.get HasVar.here).get? store with
        | none => simp [headEq] at headSome
        | some head =>
            refine ⟨Env.cons head tail, by simp [decodeState?, headEq, tailEq], ?_⟩
            intro readName readCell source
            cases source with
            | here => simpa [cellValue] using headEq
            | there source => exact tailAgree source

omit [DecidableEq Player] R in
/-- If every graph field is present, full-state decoding succeeds without any
default value. -/
theorem decodeState?_isSome_of_available {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (store : Vegas.EventGraph.Store layout)
    (available : ∀ field, (store field).isSome = true) :
    (decodeState? refs store).isSome = true := by
  obtain ⟨state, decoded, _⟩ := exists_decodeState_agrees refs store available
  simp [decoded]

/-- Decode one terminal compiled configuration to its exact typed source
state. Totality follows from terminal store availability, not from a default. -/
def terminalState {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (result : {config : (toEventGraph program).Config //
      config.cut.Terminal}) : State L program.terminalCtx :=
  (decodeState? (terminalRefs program) result.1.store).get
    (decodeState?_isSome_of_available _ result.1.store
      (fun field => result.1.store_available_of_terminal result.2 field))

/-- Decoding completed plays depends only on their store law, not on their
completion order. The optional readout on the right succeeds on every play;
the left side exposes this without introducing a payload default. -/
theorem terminalOutcomes_map_decode
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (scheduler : (toEventGraph program).PublicScheduler)
    (profile : (toEventGraph program).BehavioralProfile)
    (inputs : (toEventGraph program).Inputs) :
    (((toEventGraph program).terminalOutcomes scheduler profile inputs).map
        (terminalState program)).map some =
      (((toEventGraph program).runPolicies scheduler profile inputs).map
        Vegas.EventGraph.Config.store).map
          (decodeState? (terminalRefs program)) := by
  have decodeTerminal : (some ∘ terminalState program) =
      (decodeState? (terminalRefs program) ∘
        Vegas.EventGraph.Config.store) ∘ Subtype.val := by
    funext result
    exact Option.some_get _
  rw [FinDist.map_comp, decodeTerminal, ← FinDist.map_comp,
    (toEventGraph program).terminalOutcomes_map_val,
    FinDist.map_comp]

/-- Agreement identifies the no-default terminal decoder with the simulated
source terminal state. -/
theorem terminalState_eq {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (result : {config : (toEventGraph program).Config //
      config.cut.Terminal})
    (state : State L program.terminalCtx)
    (refsAgree : (terminalRefs program).Agrees state result.1.store) :
    terminalState program result = state := by
  unfold terminalState
  have decoded := decodeState?_eq_some (terminalRefs program) state result.1.store refsAgree
  simp [decoded]

/-- Under terminal context-reference agreement, the compiled graph payoff
readout is exactly the source terminal expression evaluation. -/
theorem terminalPayoffs_eq_source {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (config : (toEventGraph program).Config)
    (terminal : config.cut.Terminal)
    (state : State L program.terminalCtx)
    (agree : (terminalRefs program).Agrees state config.store) :
    config.terminalPayoffs terminal =
      program.terminalPayoffs.map fun payoff =>
        (payoff.1, L.eval payoff.2 (sourcePublicEnv state)) := by
  unfold Vegas.EventGraph.Config.terminalPayoffs
  change (payoffs program).map _ = _
  rw [payoffs, List.map_map]
  apply List.map_congr_left
  intro payoff member
  obtain ⟨who, expression⟩ := payoff
  simp only [Function.comp_apply]
  have evaluated := compilePublicExpr_eval? (terminalRefs program) state config.store
    agree expression
  simp [evaluated]

/-- Integer payout readout of one completed compiled event execution. -/
def terminalPayouts {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (result : {config : (toEventGraph program).Config //
      config.cut.Terminal}) : List (Player × Int) :=
  (result.1.terminalPayoffs result.2).map fun payoff => (payoff.1, L.toInt payoff.2)

/-- Executable compiled payout readout agrees pointwise with evaluating the
source payout expressions on the decoded complete source state. -/
theorem terminalPayouts_eq_source {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (result : {config : (toEventGraph program).Config //
      config.cut.Terminal}) :
    terminalPayouts program result =
      program.evaluatePayoffs (terminalState program result) := by
  let available : ∀ field, (result.1.store field).isSome = true :=
    fun field => result.1.store_available_of_terminal result.2 field
  obtain ⟨state, decoded, agree⟩ := exists_decodeState_agrees
    (terminalRefs program) result.1.store available
  have stateEq : terminalState program result = state := by
    unfold terminalState
    simp [decoded]
  rw [stateEq, terminalPayouts,
    terminalPayoffs_eq_source program result.1 result.2 state agree]
  simp [SourceProgram.evaluatePayoffs, List.map_map]

end Vegas.SourceProgram.EventLowering
