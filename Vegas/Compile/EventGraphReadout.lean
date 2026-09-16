/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphObservation
import Vegas.Compile.EventGraphState

/-! # Typed source-state readout from event-graph stores

Unlike player observations, terminal readout reconstructs every source cell.
The decoder remains partial: it returns `none` whenever a referenced graph
field is unavailable, and never invents a binding or publication result.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Reconstruct a complete source prefix from its immutable cell references
and retained private-publication references. -/
def decodeState? {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L} :
    {Γ : SourceCtx Player L} → ContextRefs layout Γ → PublicationRefs layout Γ →
      Vegas.EventGraph.Store layout → Option (State L Γ)
  | [], _, _, _ => some (Env.empty (CellVal L))
  | (name, .publicData payload) :: Γ, refs, publications, store => do
      let head ← (refs.get (HasVar.here :
        HasVar ((name, .publicData payload) :: Γ) name (.publicData payload))).get? store
      let tail ← decodeState? refs.tail publications.tail store
      pure (Env.cons head tail)
  | (name, .publication payload) :: Γ, refs, publications, store => do
      let head ← (refs.get (HasVar.here :
        HasVar ((name, .publication payload) :: Γ) name (.publication payload))).get? store
      let tail ← decodeState? refs.tail publications.tail store
      pure (Env.cons head tail)
  | (name, .privateData owner payload) :: Γ, refs, publications, store => do
      let binding ← (refs.get (HasVar.here :
        HasVar ((name, .privateData owner payload) :: Γ) name
          (.privateData owner payload))).get? store
      let status ← publicationStatus? (publications
        (HasVar.here : HasVar ((name, .privateData owner payload) :: Γ) name
          (.privateData owner payload))) store
      let tail ← decodeState? refs.tail publications.tail store
      pure (Env.cons ((BoundValue.resultEquiv _).symm binding, status) tail)

omit [DecidableEq Player] R in
private theorem publicationStatus?_isSome_of_available {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L} {payload : L.Ty}
    (publication : PublicationRef layout payload)
    (store : Vegas.EventGraph.Store layout)
    (available : ∀ field, (store field).isSome = true) :
    (publicationStatus? publication store).isSome = true := by
  cases publication with
  | pending => rfl
  | publication ref =>
      have present := ref.get?_isSome store (available ref.field)
      change ((ref.get? store).map Vegas.EventGraph.publicationOfResult).isSome = true
      cases found : ref.get? store with
      | none => simp [found] at present
      | some result => rfl

omit [DecidableEq Player] R in
/-- If every graph field is present, full-state decoding succeeds without any
default value. -/
theorem decodeState?_isSome_of_available {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L} :
    {Γ : SourceCtx Player L} → (refs : ContextRefs layout Γ) →
    (publications : PublicationRefs layout Γ) →
    (store : Vegas.EventGraph.Store layout) →
    (∀ field, (store field).isSome = true) →
      (decodeState? refs publications store).isSome = true
  | [], _, _, _, _ => rfl
  | (name, .publicData payload) :: Γ, refs, publications, store, available => by
      have head := (refs.get (HasVar.here :
        HasVar ((name, .publicData payload) :: Γ) name
          (.publicData payload))).get?_isSome store
            (available (refs.get HasVar.here).field)
      have tail := decodeState?_isSome_of_available refs.tail publications.tail store available
      cases headFound : (refs.get (HasVar.here :
          HasVar ((name, .publicData payload) :: Γ) name
            (.publicData payload))).get? store with
      | none => simp [headFound] at head
      | some headValue =>
          cases tailFound : decodeState? refs.tail publications.tail store with
          | none => simp [tailFound] at tail
          | some tailState => simp [decodeState?, headFound, tailFound]
  | (name, .publication payload) :: Γ, refs, publications, store, available => by
      have head := (refs.get (HasVar.here :
        HasVar ((name, .publication payload) :: Γ) name
          (.publication payload))).get?_isSome store
            (available (refs.get HasVar.here).field)
      have tail := decodeState?_isSome_of_available refs.tail publications.tail store available
      cases headFound : (refs.get (HasVar.here :
          HasVar ((name, .publication payload) :: Γ) name
            (.publication payload))).get? store with
      | none => simp [headFound] at head
      | some headValue =>
          cases tailFound : decodeState? refs.tail publications.tail store with
          | none => simp [tailFound] at tail
          | some tailState => simp [decodeState?, headFound, tailFound]
  | (name, .privateData owner payload) :: Γ, refs, publications, store,
      available => by
      have binding := (refs.get (HasVar.here :
        HasVar ((name, .privateData owner payload) :: Γ) name
          (.privateData owner payload))).get?_isSome store
            (available (refs.get HasVar.here).field)
      have status := publicationStatus?_isSome_of_available
        (publications (HasVar.here :
          HasVar ((name, .privateData owner payload) :: Γ) name
            (.privateData owner payload))) store available
      have tail := decodeState?_isSome_of_available refs.tail publications.tail store available
      cases bindingFound : (refs.get (HasVar.here :
          HasVar ((name, .privateData owner payload) :: Γ) name
            (.privateData owner payload))).get? store with
      | none => simp [bindingFound] at binding
      | some bindingValue =>
          cases statusFound : publicationStatus? (publications (HasVar.here :
              HasVar ((name, .privateData owner payload) :: Γ) name
                (.privateData owner payload))) store with
          | none => simp [statusFound] at status
          | some publicationValue =>
              cases tailFound : decodeState? refs.tail publications.tail store with
              | none => simp [tailFound] at tail
              | some tailState =>
                  simp [decodeState?, bindingFound, statusFound, tailFound]

omit [DecidableEq Player] R in
/-- The two compiler agreement relations make full-state readout exact. -/
theorem decodeState?_eq_some {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (publications : PublicationRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (refsAgree : refs.Agrees state store)
    (publicationsAgree : publications.Agree state store) :
    decodeState? refs publications store = some state := by
  induction Γ with
  | nil =>
      apply congrArg some
      funext name cell source
      nomatch source
  | cons entry Γ ih =>
      obtain ⟨name, cell⟩ := entry
      have tailRefs : refs.tail.Agrees
          (fun _ _ source => state.get (.there source)) store := by
        intro readName readCell source
        exact refsAgree (.there source)
      have tailPublications : PublicationRefs.Agree
          (PublicationRefs.tail publications)
          (fun _ _ source => state.get (.there source)) store := by
        intro readOwner readPayload readName source
        exact publicationsAgree (.there source)
      cases cell with
      | publicData payload =>
          have head := refsAgree (HasVar.here :
            HasVar ((name, .publicData payload) :: Γ) name (.publicData payload))
          rw [decodeState?, head,
            ih refs.tail publications.tail
              (fun _ _ source => state.get (.there source)) tailRefs tailPublications]
          simp only [cellValue]
          apply congrArg some
          funext readName readCell source
          cases source with
          | here => rfl
          | there source => rfl
      | publication payload =>
          have head := refsAgree (HasVar.here :
            HasVar ((name, .publication payload) :: Γ) name (.publication payload))
          rw [decodeState?, head,
            ih refs.tail publications.tail
              (fun _ _ source => state.get (.there source)) tailRefs tailPublications]
          simp only [cellValue]
          apply congrArg some
          funext readName readCell source
          cases source with
          | here => rfl
          | there source => rfl
      | privateData owner payload =>
          have bindingStored := refsAgree (HasVar.here :
            HasVar ((name, .privateData owner payload) :: Γ) name
              (.privateData owner payload))
          have statusStored := publicationsAgree (HasVar.here :
            HasVar ((name, .privateData owner payload) :: Γ) name
              (.privateData owner payload))
          change publicationStatus? (publications HasVar.here) store =
            some (state.get HasVar.here).2 at statusStored
          rw [decodeState?, bindingStored, statusStored,
            ih refs.tail publications.tail
              (fun _ _ source => state.get (.there source)) tailRefs tailPublications]
          simp only [cellValue]
          apply congrArg some
          funext readName readCell source
          cases source with
          | here =>
              rw [Equiv.symm_apply_apply]
              generalize valueEq : state.get (HasVar.here :
                HasVar ((name, .privateData owner payload) :: Γ) name
                  (.privateData owner payload)) = value at *
              change BoundValue (L.Val payload) ×
                Interaction.Publication (L.Val payload) at value
              rcases value with ⟨binding, status⟩
              change (binding, status) = state.get (HasVar.here :
                HasVar ((name, .privateData owner payload) :: Γ) name
                  (.privateData owner payload))
              exact valueEq.symm
          | there source => rfl

/-- Carry retained private-publication references through the complete source
program, installing each reveal's concrete output reference. -/
def terminalPublicationsWith {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L} :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    (Γ.map Prod.fst).Nodup → PublicationRefs layout Γ →
    (∀ event, Vegas.EventGraph.FieldRef layout (outputLayout program event)) →
      PublicationRefs layout program.terminalCtx
  | _, _, .ret _, _, publications, _ => publications
  | _, _, .sample name fresh _ next, unique, publications, outputs =>
      terminalPublicationsWith next (by simp [fresh, unique])
        (weakenPublications publications)
        (fun tailEvent => outputs (Fin.succ tailEvent))
  | _, _, .commit name owner fresh _ next, unique, publications, outputs =>
      terminalPublicationsWith next (by simp [fresh, unique])
        (weakenPublications publications)
        (fun tailEvent => outputs (Fin.succ tailEvent))
  | Γ, _, .reveal published _ _ fresh selected _ next, unique, publications, outputs =>
      let headRef : Vegas.EventGraph.FieldRef layout (.publication _) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      terminalPublicationsWith next (by simp [fresh, unique])
        (resolvePublications publications unique selected headRef)
        (fun tailEvent => outputs (Fin.succ tailEvent))

/-- Terminal private-publication references in the whole compiled graph. -/
def terminalPublications {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup) :
    PublicationRefs (graphLayout program) program.terminalCtx :=
  terminalPublicationsWith program unique initialPublications (outputRef program)

/-- Decode one terminal compiled configuration to its exact typed source
state. Totality follows from terminal store availability, not from a default. -/
def terminalState {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup)
    (result : {config : (toEventGraph program unique).Config //
      config.cut.Terminal}) : State L program.terminalCtx :=
  (decodeState? (terminalRefs program) (terminalPublications program unique)
    result.1.store).get (decodeState?_isSome_of_available _ _ result.1.store
      (fun field => result.1.store_available_of_terminal result.2 field))

/-- Agreement identifies the no-default terminal decoder with the simulated
source terminal state. -/
theorem terminalState_eq {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup)
    (result : {config : (toEventGraph program unique).Config //
      config.cut.Terminal})
    (state : State L program.terminalCtx)
    (refsAgree : (terminalRefs program).Agrees state result.1.store)
    (publicationsAgree : PublicationRefs.Agree
      (terminalPublications program unique) state result.1.store) :
    terminalState program unique result = state := by
  unfold terminalState
  have decoded := decodeState?_eq_some (terminalRefs program)
    (terminalPublications program unique) state result.1.store refsAgree publicationsAgree
  simp [decoded]

/-- Under terminal context-reference agreement, the compiled graph payoff
readout is exactly the source terminal expression evaluation. -/
theorem terminalPayoffs_eq_source {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup)
    (config : (toEventGraph program unique).Config)
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

end Vegas.SourceProgram.EventLowering
