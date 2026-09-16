/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphAssembly
import Vegas.Compile.EventGraphEvaluation
import Vegas.EventGraph.Commutation

/-! # Source-state agreement across event-graph writes

The lowering carries two complementary typed views of a source prefix:
`ContextRefs` names immutable cell data, while `PublicationRefs` names the
evolving public status of private cells.  This module proves that completing
the current source-ranked event preserves both views of the earlier prefix,
then supplies the three constructor updates used by a source-order run proof.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

open Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

omit [DecidableEq Player] in
/-- A field preceding an event cannot be that event's output field. -/
theorem FieldBefore.ne_output {inputCount eventCount : Nat}
    {event : Fin eventCount}
    {field : Vegas.EventGraph.FieldId inputCount eventCount}
    (before : FieldBefore event field) : field ≠ .inr event := by
  cases field with
  | inl input => intro impossible; cases impossible
  | inr producer =>
      intro same
      have producerEq : producer = event := Sum.inr.inj same
      subst producer
      exact (Nat.lt_irrefl event.val) before

omit [DecidableEq Player] in
/-- Completing the current event leaves every earlier typed reference
unchanged. -/
theorem ContextRefs.Agrees.complete {graph : Vegas.EventGraph Player L}
    {config : graph.Config} {event : graph.EventId}
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value)
    {Γ : SourceCtx Player L} (refs : ContextRefs graph.layout Γ)
    (state : State L Γ) (agree : refs.Agrees state config.store)
    (before : ∀ {name cell} (source : HasVar Γ name cell),
      FieldBefore event (refs.get source).field) :
    refs.Agrees state (config.complete event ready action value).store := by
  intro name cell source
  rw [← agree source]
  apply (refs.get source).get?_congr
  rw [Vegas.EventGraph.store_complete]
  simp [Function.update, (before source).ne_output]

omit [DecidableEq Player] in
/-- Completing the current event likewise leaves every retained publication
reference to an earlier event unchanged. -/
theorem PublicationRefs.Agree.complete {graph : Vegas.EventGraph Player L}
    {config : graph.Config} {event : graph.EventId}
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value)
    {Γ : SourceCtx Player L} (publications : PublicationRefs graph.layout Γ)
    (state : State L Γ) (agree : publications.Agree state config.store)
    (before : PublicationsBefore publications event) :
    publications.Agree state (config.complete event ready action value).store := by
  intro owner payload name source
  cases found : publications source with
  | pending => simpa [found] using agree source
  | publication ref =>
      have refBefore : FieldBefore event ref.field :=
        before source ref.field (by simp [found, PublicationRef.field?])
      have unchanged : ref.get? (config.complete event ready action value).store =
          ref.get? config.store := by
        apply ref.get?_congr
        rw [Vegas.EventGraph.store_complete]
        simp [Function.update, refBefore.ne_output]
      simpa [found, unchanged] using agree source

namespace ContextRefs

omit [DecidableEq Player] R in
/-- Extending the reference environment preserves agreement when the new head
reference stores the new source cell's exact typed value. -/
theorem Agrees.cons {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : refs.Agrees state store)
    {name : VarId} {cell : CellTy Player L}
    (headRef : Vegas.EventGraph.FieldRef layout (cellField cell))
    (headValue : CellVal L cell)
    (headStored : headRef.get? store = some (cellValue headValue)) :
    (refs.cons (name := name) headRef).Agrees
      (Env.cons (x := name) headValue state) store := by
  intro readName readCell source
  cases source with
  | here => exact headStored
  | there source => exact agree source

end ContextRefs

namespace PublicationRefs

omit [DecidableEq Player] R in
/-- Adding ordinary public data does not change the retained private
publication map. -/
theorem Agree.weakenPublicData {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (publications : PublicationRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : publications.Agree state store)
    {name : VarId} {payload : L.Ty} (value : L.Val payload) :
    PublicationRefs.Agree
      (weakenPublications publications :
        PublicationRefs layout ((name, .publicData payload) :: Γ))
      (Env.cons (x := name) value state) store := by
  intro owner readPayload readName source
  cases source with
  | there source => exact agree source

omit [DecidableEq Player] R in
/-- Adding a public result cell does not change the retained private
publication map. -/
theorem Agree.weakenPublication {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (publications : PublicationRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : publications.Agree state store)
    {name : VarId} {payload : L.Ty}
    (value : PublicationResult (L.Val payload)) :
    PublicationRefs.Agree
      (weakenPublications publications :
        PublicationRefs layout ((name, .publication payload) :: Γ))
      (Env.cons (x := name) value state) store := by
  intro owner readPayload readName source
  cases source with
  | there source => exact agree source

omit [DecidableEq Player] R in
/-- A fresh private source cell begins with literal-pending publication status,
while all earlier statuses retain their references. -/
theorem Agree.weakenPrivate {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (publications : PublicationRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : publications.Agree state store)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (binding : BoundValue (L.Val payload)) :
    PublicationRefs.Agree
      (weakenPublications publications :
        PublicationRefs layout ((name, .privateData owner payload) :: Γ))
      (Env.cons (x := name) (binding, Interaction.Publication.pending) state) store := by
  intro readOwner readPayload readName source
  cases source with
  | here => rfl
  | there source => exact agree source

omit [DecidableEq Player] R in
/-- Resolving one private cell installs the new public-result reference for
that cell and retains every other private publication reference. -/
theorem Agree.resolve {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (publications : PublicationRefs layout Γ)
    (unique : (Γ.map Prod.fst).Nodup)
    {owner : Player} {payload : L.Ty} {name published : VarId}
    (selected : HasVar Γ name (.privateData owner payload))
    (resultRef : Vegas.EventGraph.FieldRef layout (.publication payload))
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : publications.Agree state store)
    (result : PublicationResult (L.Val payload))
    (resultStored : resultRef.get? store = some result) :
    PublicationRefs.Agree
      (resolvePublications publications unique selected resultRef)
      (Env.cons (x := published) (τ := .publication payload) result
        (updatePrivate state selected (resultPublication result))) store := by
  intro readOwner readPayload readName source
  cases source with
  | there source =>
      by_cases same : readName = name
      · subst readName
        have cellEq := HasVar.type_unique unique source selected
        have ownerEq := (CellTy.privateData.inj cellEq).1
        have payloadEq := (CellTy.privateData.inj cellEq).2
        subst readOwner
        subst readPayload
        have sourceEq := HasVar.eq_of_nodup unique source selected
        subst source
        simp [resolvePublications, resultStored, updatePrivate_get_source]
        cases result <;> rfl
      · have unchanged := congrArg Prod.snd
          (updatePrivate_get_of_name_ne state selected (resultPublication result)
            source same)
        change (match resolvePublications publications unique selected resultRef
              (HasVar.there source) with
            | .pending => some Interaction.Publication.pending
            | .publication ref =>
                (ref.get? store).map Vegas.EventGraph.publicationOfResult) =
          some ((updatePrivate state selected (resultPublication result)).get source).2
        rw [unchanged]
        have retained : resolvePublications (published := published)
            publications unique selected resultRef
            (HasVar.there (y := published) source) = publications source := by
          simp [resolvePublications, same]
        rw [retained]
        exact agree source

end PublicationRefs

omit [DecidableEq Player] R in
/-- State agreement update for a source `sample`: the sampled public value is
stored at the new head reference and private publication statuses are merely
weakened. -/
theorem sample_agrees {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (publications : PublicationRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (refsAgree : refs.Agrees state store)
    (publicationsAgree : publications.Agree state store)
    {name : VarId} {payload : L.Ty}
    (resultRef : Vegas.EventGraph.FieldRef layout (.publicData payload))
    (result : L.Val payload) (resultStored : resultRef.get? store = some result) :
    (refs.cons (name := name) (cell := .publicData payload) resultRef).Agrees
        (Env.cons (x := name) (τ := .publicData payload) result state) store ∧
      PublicationRefs.Agree
        (weakenPublications publications :
          PublicationRefs layout ((name, .publicData payload) :: Γ))
        (Env.cons (x := name) (τ := .publicData payload) result state) store := by
  exact ⟨ContextRefs.Agrees.cons refs state store refsAgree
      (name := name) (cell := .publicData payload) resultRef result resultStored,
    publicationsAgree.weakenPublicData publications state store result⟩

omit [DecidableEq Player] R in
/-- State agreement update for a source `commit`: the immutable binding result
is stored at the new head reference and its public status starts pending. -/
theorem commit_agrees {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (publications : PublicationRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (refsAgree : refs.Agrees state store)
    (publicationsAgree : publications.Agree state store)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (resultRef : Vegas.EventGraph.FieldRef layout (.binding owner payload))
    (binding : BoundValue (L.Val payload))
    (resultStored : resultRef.get? store =
      some (BoundValue.resultEquiv _ binding)) :
    (refs.cons (name := name) (cell := .privateData owner payload) resultRef).Agrees
        (Env.cons (x := name) (τ := .privateData owner payload)
          (binding, Interaction.Publication.pending) state) store ∧
      PublicationRefs.Agree
        (weakenPublications publications :
          PublicationRefs layout ((name, .privateData owner payload) :: Γ))
        (Env.cons (x := name) (τ := .privateData owner payload)
          (binding, Interaction.Publication.pending) state) store := by
  exact ⟨ContextRefs.Agrees.cons refs state store refsAgree
      (name := name) (cell := .privateData owner payload) resultRef
      (binding, Interaction.Publication.pending) resultStored,
    publicationsAgree.weakenPrivate publications state store binding⟩

omit [DecidableEq Player] R in
/-- State agreement update for a source `reveal`: the retained binding is
unchanged, the selected private status becomes the accepted result's public
form, and the same result is added as the new public source cell. -/
theorem reveal_agrees {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (publications : PublicationRefs layout Γ)
    (unique : (Γ.map Prod.fst).Nodup)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (refsAgree : refs.Agrees state store)
    (publicationsAgree : publications.Agree state store)
    {owner : Player} {payload : L.Ty} {name published : VarId}
    (selected : HasVar Γ name (.privateData owner payload))
    (resultRef : Vegas.EventGraph.FieldRef layout (.publication payload))
    (result : PublicationResult (L.Val payload))
    (resultStored : resultRef.get? store = some result) :
    let resolved := updatePrivate state selected (resultPublication result)
    (refs.cons (name := published) (cell := .publication payload) resultRef).Agrees
        (Env.cons (x := published) (τ := .publication payload) result resolved) store ∧
      PublicationRefs.Agree
        (resolvePublications publications unique selected resultRef)
        (Env.cons (x := published) (τ := .publication payload) result resolved) store := by
  dsimp only
  have resolvedRefs : refs.Agrees
      (updatePrivate state selected (resultPublication result)) store :=
    refsAgree.updatePrivate refs unique state store selected (resultPublication result)
  exact ⟨ContextRefs.Agrees.cons refs _ store resolvedRefs
      (name := published) (cell := .publication payload) resultRef result resultStored,
    publicationsAgree.resolve publications unique selected resultRef state store
      result resultStored⟩

/-- The canonical reference to a completed compiled event reads exactly the
value written by `Config.complete`. -/
theorem outputRef_get?_complete {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup)
    (config : (toEventGraph program unique).Config)
    (event : Fin (eventCount program))
    (ready : config.cut.Ready event)
    (action : (toEventGraph program unique).Action event)
    (value : (outputLayout program event).Value) :
    (outputRef program event).get?
        (config.complete event ready action value).store = some value := by
  change (config.complete event ready action value).outputs event = some value
  exact config.complete_output_same event ready action value

/-- An embedded suffix output reference reads back the uncast source value
written at its whole-graph event. -/
theorem OutputEmbedding.ref_get?_complete
    {Γ0 : SourceCtx Player L} {open0 : Finset VarId}
    (whole : SourceProgram Player L Γ0 open0)
    (wholeUnique : (Γ0.map Prod.fst).Nodup)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {program : SourceProgram Player L Γ openNames}
    (embedding : OutputEmbedding (inputLayout Γ0) (outputLayout whole) program)
    (config : (toEventGraph whole wholeUnique).Config)
    (index : Fin (eventCount program))
    (ready : config.cut.Ready (embedding.event index))
    (action : (toEventGraph whole wholeUnique).Action (embedding.event index))
    (outputEq : (toEventGraph whole wholeUnique).outputLayout (embedding.event index) =
      outputLayout program index)
    (value : (outputLayout program index).Value) :
    (embedding.ref index).get?
        (config.complete (embedding.event index) ready action
          (cast (congrArg Vegas.EventGraph.EventField.Value
            outputEq.symm) value)).store = some value := by
  change outputLayout whole (embedding.event index) = outputLayout program index at outputEq
  rw [Vegas.EventGraph.store_complete]
  simp only [OutputEmbedding.ref, Vegas.EventGraph.FieldRef.get?, Function.update_self]
  change cast (congrArg (fun kind => Option kind.Value) (embedding.layout_eq index))
      (some (cast (congrArg Vegas.EventGraph.EventField.Value
        outputEq.symm) value)) = some value
  have castSome {A B : Type} (same : A = B) (item : A) :
      cast (congrArg Option same) (some item) = some (cast same item) := by
    cases same
    rfl
  rw [castSome (congrArg Vegas.EventGraph.EventField.Value
    (embedding.layout_eq index))]
  have proofEq : congrArg Vegas.EventGraph.EventField.Value
      (embedding.layout_eq index) =
      congrArg Vegas.EventGraph.EventField.Value outputEq := Subsingleton.elim _ _
  rw [proofEq]
  have castInverse {A B : Type} (same : A = B) (item : B) :
      cast same (cast same.symm item) = item := by
    cases same
    rfl
  exact congrArg some
    (castInverse (congrArg Vegas.EventGraph.EventField.Value
      (embedding.layout_eq index)) value)

end Vegas.SourceProgram.EventLowering
