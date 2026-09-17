/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphAssembly
import Vegas.Compile.EventGraphObservation
import Vegas.EventGraph.Semantics

/-! # Source policies compiled to event-graph behavioral policies

Event identities retain the source operation that produced them, so dependent
graph actions can be decoded without consulting a possibly failed output.
Policy observation decoding remains partial and falls back only to the genuine
failure action at malformed, unreachable graph views.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- The source owner retained by an original strategic action. -/
def sourceActionOwner : OwnAction Player L → Player
  | .commit owner _ _ _ => owner
  | .reveal owner _ _ => owner

/-- Decode an original dependent graph action from its source-ranked event
identity. Chance events contribute no source own action. -/
def decodeEventAction : {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    (event : Fin (eventCount program)) →
    Vegas.EventGraph.EventField.Action (outputLayout program event) →
      Option (OwnAction Player L)
  | _, _, .ret _, event, _ => nomatch event
  | _, _, .sample _ _ _ next, event, action =>
      Fin.cases (fun _ => none) (decodeEventAction next) event action
  | _, _, .commit (payload := payload) name owner _ _ next, event, action =>
      Fin.cases
        (fun choice => some (.commit owner name payload choice))
        (decodeEventAction next) event action
  | _, _, .reveal _ owner name _ _ _ next, event, action =>
      Fin.cases (fun disclose => some (.reveal owner name disclose))
        (decodeEventAction next) event action

/-- Source owner of one source-ranked event, if it is strategic. -/
def eventOwner? : {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    Fin (eventCount program) → Option Player
  | _, _, .ret _, event => nomatch event
  | _, _, .sample _ _ _ next, event =>
      Fin.cases none (eventOwner? next) event
  | _, _, .commit _ owner _ _ next, event =>
      Fin.cases (some owner) (eventOwner? next) event
  | _, _, .reveal _ owner _ _ _ _ next, event =>
      Fin.cases (some owner) (eventOwner? next) event

/-- Actor extraction from the ranked compiler is independent of its typed
reference and causality witnesses. -/
private theorem compileRankedNodes_actor {inputCount totalCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin totalCount → Vegas.EventGraph.EventField Player L} :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    (unique : (Γ.map Prod.fst).Nodup) →
    (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ) →
    (revelations : Revelations Γ) →
    (registry : Registry Γ) →
    (embedding : OutputEmbedding inputs outputs program) →
    (refsBefore : ContextRefsBefore refs embedding) →
    (index : Fin (eventCount program)) →
    Vegas.EventGraph.EventCode.actor
        (compileRankedNodes program unique refs revelations registry embedding
          refsBefore index).code =
      eventOwner? program index := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro unique refs revelations registry embedding refsBefore index
      exact nomatch index
  | sample name fresh law next ih =>
      intro unique refs revelations registry embedding refsBefore index
      refine Fin.cases ?_ (fun tail => ?_) index
      · rfl
      · apply ih
  | commit name owner fresh guard next ih =>
      intro unique refs revelations registry embedding refsBefore index
      refine Fin.cases ?_ (fun tail => ?_) index
      · rfl
      · apply ih
  | reveal published owner name fresh selected unresolved next ih =>
      intro unique refs revelations registry embedding refsBefore index
      refine Fin.cases ?_ (fun tail => ?_) index
      · rfl
      · apply ih

/-- The source-ranked owner table is exactly the actor table of the assembled
event graph. -/
theorem eventOwner?_eq_actor {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup) (event : Fin (eventCount program)) :
    eventOwner? program event = (toEventGraph program unique).actor? event := by
  symm
  exact compileRankedNodes_actor program unique _ _ _ _ _ event

/-- Action decoding returns exactly one action at strategic events and none at
chance events, with the original source owner. -/
theorem decodeEventAction_owner : {Γ : SourceCtx Player L} →
    {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    (event : Fin (eventCount program)) →
    (action : Vegas.EventGraph.EventField.Action (outputLayout program event)) →
    (decodeEventAction program event action).map sourceActionOwner =
      eventOwner? program event
  | _, _, .ret _, event, _ => nomatch event
  | _, _, .sample name fresh law next, event, action => by
      refine Fin.cases (motive := fun event =>
        ∀ action : Vegas.EventGraph.EventField.Action
          (outputLayout (.sample name fresh law next) event),
          (decodeEventAction (.sample name fresh law next) event action).map
              sourceActionOwner =
            eventOwner? (.sample name fresh law next) event)
        (fun _ => rfl) (fun tail action => decodeEventAction_owner next tail action)
        event action
  | _, _, .commit name owner fresh guard next, event, action => by
      refine Fin.cases (motive := fun event =>
        ∀ action : Vegas.EventGraph.EventField.Action
          (outputLayout (.commit name owner fresh guard next) event),
          (decodeEventAction (.commit name owner fresh guard next) event action).map
              sourceActionOwner =
            eventOwner? (.commit name owner fresh guard next) event)
        (fun _ => rfl) (fun tail action => decodeEventAction_owner next tail action)
        event action
  | _, _, .reveal published owner name fresh selected unresolved next, event, action => by
      refine Fin.cases (motive := fun event =>
        ∀ action : Vegas.EventGraph.EventField.Action
          (outputLayout
            (.reveal published owner name fresh selected unresolved next) event),
          (decodeEventAction
              (.reveal published owner name fresh selected unresolved next) event action).map
              sourceActionOwner =
            eventOwner?
              (.reveal published owner name fresh selected unresolved next) event)
        (fun _ => rfl) (fun tail action => decodeEventAction_owner next tail action)
        event action

/-- Decode every strategic completion in chronological order. -/
def decodeCompletions {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup)
    (history : List (toEventGraph program unique).Completion) :
    List (OwnAction Player L) :=
  history.filterMap fun completion =>
    decodeEventAction program completion.event completion.action

@[simp] theorem decodeCompletions_nil {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup) :
    decodeCompletions program unique [] = [] := rfl

@[simp] theorem decodeCompletions_append {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup)
    (left right : List (toEventGraph program unique).Completion) :
    decodeCompletions program unique (left ++ right) =
      decodeCompletions program unique left ++ decodeCompletions program unique right := by
  simp [decodeCompletions, List.filterMap_append]

/-- Compile one source policy into a table indexed by every event in the
current source suffix. `history` is already decoded from the actor's retained
dependent graph actions. -/
def compilePolicyTable {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L} :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    (Γ.map Prod.fst).Nodup →
    (refs : ContextRefs layout Γ) →
    (outputs : ∀ event, Vegas.EventGraph.FieldRef layout
      (outputLayout program event)) →
    (who : Player) → BehavioralPolicy who program →
    (event : Fin (eventCount program)) → Vegas.EventGraph.Store layout →
    List (OwnAction Player L) →
      FinDist (Vegas.EventGraph.EventField.Action (outputLayout program event))
  | _, _, .ret _, _, _, _, _, _, event, _, _ => nomatch event
  | _, _, .sample name fresh law next, unique, refs, outputs,
      who, policy, event, store, history =>
      let headRef : Vegas.EventGraph.FieldRef layout (.publicData _) := by
        simpa [outputLayout, eventCount] using
          outputs ⟨0, by simp [eventCount]⟩
      Fin.cases (fun _ _ => FinDist.pure PUnit.unit)
        (compilePolicyTable next (by simp [fresh, unique]) (refs.cons headRef)
          (fun tail => outputs (Fin.succ tail)) who policy) event store history
  | _, _, .commit (payload := payload) name owner fresh guard next, unique, refs,
      outputs, who, policy, event, store, history =>
      let headRef : Vegas.EventGraph.FieldRef layout (.binding owner payload) := by
        simpa [outputLayout, eventCount] using
          outputs ⟨0, by simp [eventCount]⟩
      Fin.cases
        (fun store history =>
          if same : owner = who then
            match decodeObservation? who refs store with
            | some observation =>
                policy.1 same (observation, history)
            | none => FinDist.pure PublicationResult.failure
          else FinDist.pure PublicationResult.failure)
        (compilePolicyTable next (by simp [fresh, unique]) (refs.cons headRef)
          (fun tail => outputs (Fin.succ tail)) who policy.2) event store history
  | Γ, _, .reveal (payload := payload) published owner name fresh selected unresolved
      next, unique, refs, outputs, who, policy, event, store, history =>
      let headRef : Vegas.EventGraph.FieldRef layout (.publication payload) := by
        simpa [outputLayout, eventCount] using
          outputs ⟨0, by simp [eventCount]⟩
      Fin.cases
        (fun store history =>
          if same : owner = who then
            match decodeObservation? who refs store with
            | some observation => policy.1 same (observation, history)
            | none => FinDist.pure false
          else FinDist.pure false)
        (compilePolicyTable next (by simp [fresh, unique]) (refs.cons headRef)
          (fun tail => outputs (Fin.succ tail)) who policy.2) event store history

/-- At a well-formed commit observation, the compiled head kernel is exactly
the source kernel. -/
theorem compilePolicyTable_commit_of_decode {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner who : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .privateData owner payload) :: Γ)
      (insert name openNames)}
    (unique : (Γ.map Prod.fst).Nodup) (refs : ContextRefs layout Γ)
    (outputs : ∀ event, Vegas.EventGraph.FieldRef layout
      (outputLayout (.commit (payload := payload) name owner fresh guard next) event))
    (policy : BehavioralPolicy who
      (.commit (payload := payload) name owner fresh guard next))
    (same : owner = who) (store : Vegas.EventGraph.Store layout)
    (history : List (OwnAction Player L)) (observation : SourceObservation L who Γ)
    (decoded : decodeObservation? who refs store = some observation) :
    compilePolicyTable (.commit (payload := payload) name owner fresh guard next)
        unique refs outputs who policy
        ⟨0, Nat.zero_lt_succ (eventCount next)⟩ store history =
      policy.1 same (observation, history) := by
  change (if same' : owner = who then
      match decodeObservation? who refs store with
      | some observation =>
          policy.1 same' (observation, history)
      | none => FinDist.pure PublicationResult.failure
    else FinDist.pure PublicationResult.failure) = _
  simp [same, decoded]

/-- A malformed commit view chooses the genuine failure binding. -/
theorem compilePolicyTable_commit_of_decode_none {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner who : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .privateData owner payload) :: Γ)
      (insert name openNames)}
    (unique : (Γ.map Prod.fst).Nodup) (refs : ContextRefs layout Γ)
    (outputs : ∀ event, Vegas.EventGraph.FieldRef layout
      (outputLayout (.commit (payload := payload) name owner fresh guard next) event))
    (policy : BehavioralPolicy who
      (.commit (payload := payload) name owner fresh guard next))
    (same : owner = who) (store : Vegas.EventGraph.Store layout)
    (history : List (OwnAction Player L))
    (decoded : decodeObservation? who refs store = none) :
    compilePolicyTable (.commit (payload := payload) name owner fresh guard next)
        unique refs outputs who policy
        ⟨0, Nat.zero_lt_succ (eventCount next)⟩ store history =
      FinDist.pure PublicationResult.failure := by
  change (if same' : owner = who then
      match decodeObservation? who refs store with
      | some observation =>
          policy.1 same' (observation, history)
      | none => FinDist.pure PublicationResult.failure
    else FinDist.pure PublicationResult.failure) = _
  simp [same, decoded]

/-- At a well-formed reveal observation, the compiled head kernel is exactly
the source disclosure kernel. -/
theorem compilePolicyTable_reveal_of_decode {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner who : Player} {payload : L.Ty}
    {fresh : published ∉ Γ.map Prod.fst}
    {selected : HasVar Γ name (.privateData owner payload)} {unresolved : name ∈ openNames}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name)}
    (unique : (Γ.map Prod.fst).Nodup) (refs : ContextRefs layout Γ)
    (outputs : ∀ event, Vegas.EventGraph.FieldRef layout
      (outputLayout (.reveal (payload := payload) published owner name fresh selected
        unresolved next) event))
    (policy : BehavioralPolicy who
      (.reveal (payload := payload) published owner name fresh selected unresolved next))
    (same : owner = who) (store : Vegas.EventGraph.Store layout)
    (history : List (OwnAction Player L)) (observation : SourceObservation L who Γ)
    (decoded : decodeObservation? who refs store = some observation) :
    compilePolicyTable
        (.reveal (payload := payload) published owner name fresh selected unresolved next)
        unique refs outputs who policy
        ⟨0, Nat.zero_lt_succ (eventCount next)⟩ store history =
      policy.1 same (observation, history) := by
  change (if same' : owner = who then
      match decodeObservation? who refs store with
      | some observation => policy.1 same' (observation, history)
      | none => FinDist.pure false
    else FinDist.pure false) = _
  simp [same, decoded]

/-- A malformed reveal view refuses disclosure. -/
theorem compilePolicyTable_reveal_of_decode_none {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner who : Player} {payload : L.Ty}
    {fresh : published ∉ Γ.map Prod.fst}
    {selected : HasVar Γ name (.privateData owner payload)} {unresolved : name ∈ openNames}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name)}
    (unique : (Γ.map Prod.fst).Nodup) (refs : ContextRefs layout Γ)
    (outputs : ∀ event, Vegas.EventGraph.FieldRef layout
      (outputLayout (.reveal (payload := payload) published owner name fresh selected
        unresolved next) event))
    (policy : BehavioralPolicy who
      (.reveal (payload := payload) published owner name fresh selected unresolved next))
    (same : owner = who) (store : Vegas.EventGraph.Store layout)
    (history : List (OwnAction Player L))
    (decoded : decodeObservation? who refs store = none) :
    compilePolicyTable
        (.reveal (payload := payload) published owner name fresh selected unresolved next)
        unique refs outputs who policy
        ⟨0, Nat.zero_lt_succ (eventCount next)⟩ store history =
      FinDist.pure false := by
  change (if same' : owner = who then
      match decodeObservation? who refs store with
      | some observation => policy.1 same' (observation, history)
      | none => FinDist.pure false
    else FinDist.pure false) = _
  simp [same, decoded]

/-- Compile one source policy to the actual behavioral-policy interface of the
assembled ideal event graph. -/
def compileEventPolicy {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup) (who : Player)
    (policy : BehavioralPolicy who program) :
    (toEventGraph program unique).BehavioralPolicy who :=
  fun event _actor observation =>
    compilePolicyTable program unique
      (ContextRefs.initial Γ (outputLayout program))
      (outputRef program) who policy event observation.store
      (decodeCompletions program unique observation.ownActions)

/-- Compile a complete source behavioral profile playerwise. -/
def compileEventProfile {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup) (profile : BehavioralProfile program) :
    (toEventGraph program unique).BehavioralProfile :=
  fun who => compileEventPolicy program unique who (profile who)

end Vegas.SourceProgram.EventLowering
