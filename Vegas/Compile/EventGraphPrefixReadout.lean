module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphCheckpoint
public import Vegas.Compile.EventGraphReadout
public import Vegas.Compile.EventGraphParameterReadout
public import Vegas.Compile.EventGraphPolicy
public import Vegas.Source.SetupProtocolEvaluation
public import Vegas.Source.DefaultControl
public import Vegas.Source.ProtocolBehavioralPolicy

@[expose] public section

/-! # Reading full source protocol positions from native checkpoints

The static instruction prefix determines the typed field references, deferred
guard registry and publication references. Reading those existing fields and
the decoded completion history reconstructs the original source protocol
state. This decoder performs no source or runtime transition.
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Read an actual source position after a static number of instructions.
Samples, commitments and publications update only their typed references and
static bookkeeping; their values come from the existing native store. -/
def decodeSourcePrefix? {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) → ContextRefs layout Γ →
    Registry Γ → Revelations Γ →
    (∀ event, EventGraph.FieldRef layout (outputLayout program event)) →
    Nat → EventGraph.Store layout → History Player L → DefaultHistory Player →
      Option (ProtocolState program)
  | _, _, program, refs, registry, revelations, _, 0, store, history, defaults =>
      (decodeState? refs store).map fun state =>
        ProtocolState.entry program ⟨state, registry, revelations, history, defaults⟩
  | _, _, .ret _, _, _, _, _, _ + 1, _, _, _ => none
  | _, _, .sample (payload := payload) _ _ _ next,
      refs, registry, revelations, outputs, count + 1, store, history, defaults =>
      let headRef : EventGraph.FieldRef layout (.publicData payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      (decodeSourcePrefix? next (refs.cons headRef) registry.weaken revelations.weaken
        (fun tail => outputs tail.succ) count store history defaults).map Sum.inr
  | _, _, .commit (payload := payload) name owner _ guard next,
      refs, registry, revelations, outputs, count + 1, store, history, defaults =>
      let headRef : EventGraph.FieldRef layout (.binding owner payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      let nextRegistry :=
        { owner := owner, subject := name, payload := payload, source := HasVar.here,
          guard := guard.weaken } :: registry.weaken
      (decodeSourcePrefix? next (refs.cons headRef) nextRegistry revelations.weaken
        (fun tail => outputs tail.succ) count store history defaults).map Sum.inr
  | _, _, .reveal (payload := payload) _ _ _ _ selected _ next,
      refs, registry, revelations, outputs, count + 1, store, history, defaults =>
      let headRef : EventGraph.FieldRef layout (.publication payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      (decodeSourcePrefix? next (refs.cons headRef) registry.weaken
        (revelations.reveal selected) (fun tail => outputs tail.succ)
        count store history defaults).map
          Sum.inr

/-- Read the view of `who` at the source position after `count` events from a
store and `who`'s own decoded actions, walking the program exactly as
`Vegas.decodeSourcePrefix?` does. Only fields visible to `who` are read at the
position reached. -/
def decodeViewPrefix? {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} (who : Player) :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) → ContextRefs layout Γ →
    (∀ event, EventGraph.FieldRef layout (outputLayout program event)) →
    Nat → EventGraph.Store layout → List (OwnAction Player L) → DefaultHistory Player →
      Option (ProtocolView who program)
  | _, _, program, refs, _, 0, store, own, defaults =>
      (decodeObservation? who refs store).map fun observation =>
        ProtocolView.entry who program ⟨observation, defaults, own⟩
  | _, _, .ret _, _, _, _ + 1, _, _, _ => none
  | _, _, .sample (payload := payload) _ _ _ next, refs, outputs, count + 1, store, own,
      defaults =>
      let headRef : EventGraph.FieldRef layout (.publicData payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      (decodeViewPrefix? who next (refs.cons headRef) (fun tail => outputs tail.succ) count store
        own defaults).map Sum.inr
  | _, _, .commit (payload := payload) _ owner _ _ next, refs, outputs, count + 1, store, own,
      defaults =>
      let headRef : EventGraph.FieldRef layout (.binding owner payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      (decodeViewPrefix? who next (refs.cons headRef) (fun tail => outputs tail.succ) count store
        own defaults).map Sum.inr
  | _, _, .reveal (payload := payload) _ _ _ _ _ _ next, refs, outputs, count + 1, store, own,
      defaults =>
      let headRef : EventGraph.FieldRef layout (.publication payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      (decodeViewPrefix? who next (refs.cons headRef) (fun tail => outputs tail.succ) count store
        own defaults).map Sum.inr

/-- **The view decoder reads the decoded point's view.** Wherever the source
prefix decoder succeeds, the view decoder, given `who`'s part of the history,
returns `who`'s view of the decoded point. -/
theorem decodeViewPrefix?_eq_observe {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} (who : Player) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player)
      (point : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history defaults =
          some point →
        decodeViewPrefix? who program refs outputs count store (history who) defaults =
          some (ProtocolState.observe who program point)
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, defaults, point,
      decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨state, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      simp only [decodeViewPrefix?, decodeObservation?_eq_some refs who state store
        (decodeState?_agrees refs store state read), Option.map_some,
        ProtocolState.observe_entry]
      rfl
  | _ + 1, _, _, .ret _, _, _, _, _, _, _, _, _, decoded => by
      simp only [decodeSourcePrefix?, reduceCtorEq] at decoded
  | count + 1, _, _, .sample _ _ _ next, refs, registry, revelations, outputs, store, history,
      defaults, point, decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      simp only [decodeViewPrefix?, decodeViewPrefix?_eq_observe who count next _ _ _ _ store
        history defaults rest read, Option.map_some]
      rfl
  | count + 1, _, _, .commit _ _ _ _ next, refs, registry, revelations, outputs, store, history,
      defaults, point, decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      simp only [decodeViewPrefix?, decodeViewPrefix?_eq_observe who count next _ _ _ _ store
        history defaults rest read, Option.map_some]
      rfl
  | count + 1, _, _, .reveal _ _ _ _ _ _ next, refs, registry, revelations, outputs, store,
      history, defaults, point, decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      simp only [decodeViewPrefix?, decodeViewPrefix?_eq_observe who count next _ _ _ _ store
        history defaults rest read, Option.map_some]
      rfl

/-- The view decoder reads only fields visible to `who`, so it gives the same
result on `who`'s masked store. -/
theorem decodeViewPrefix?_playerStore {graph : EventGraph Player L} (who : Player) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (refs : ContextRefs graph.layout Γ)
      (outputs : ∀ event, EventGraph.FieldRef graph.layout (outputLayout program event))
      (store : EventGraph.Store graph.layout) (own : List (OwnAction Player L))
      (defaults : DefaultHistory Player),
      decodeViewPrefix? who program refs outputs count (graph.playerStore who store) own defaults =
        decodeViewPrefix? who program refs outputs count store own defaults
  | 0, _, _, program, refs, outputs, store, own, defaults => by
      simp only [decodeViewPrefix?, decodeObservation?_playerStore]
  | _ + 1, _, _, .ret _, _, _, _, _, _ => rfl
  | count + 1, _, _, .sample _ _ _ next, refs, outputs, store, own, defaults => by
      simp only [decodeViewPrefix?, decodeViewPrefix?_playerStore who count next]
  | count + 1, _, _, .commit _ _ _ _ next, refs, outputs, store, own, defaults => by
      simp only [decodeViewPrefix?, decodeViewPrefix?_playerStore who count next]
  | count + 1, _, _, .reveal _ _ _ _ _ _ next, refs, outputs, store, own, defaults => by
      simp only [decodeViewPrefix?, decodeViewPrefix?_playerStore who count next]

/-- The active policy table reproduces the source action law at the view
decoded at that event's rank. -/
theorem compilePolicyTable_map_decodeEventAction
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    (who : Player) {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) :
    ∀ (refs : ContextRefs layout Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (policy : BehavioralPolicy who program) (event : Fin (eventCount program))
      (store : EventGraph.Store layout) (defaults : DefaultHistory Player)
      (history : List (OwnAction Player L)) (view : ProtocolView who program),
      eventOwner? program event = some who → who ∉ defaults.defaulted →
      decodeViewPrefix? who program refs outputs event.val store history defaults = some view →
      (compilePolicyTable program refs outputs who policy event store defaults history).map
          (decodeEventAction program event) = policy.protocolAction program view := by
  induction program with
  | ret payoff =>
      intro refs outputs policy event
      exact nomatch event
  | sample name fresh law next ih =>
      intro refs outputs policy event
      refine Fin.cases ?_ (fun tail => ?_) event
      · intro store defaults history view owned
        cases owned
      · intro store defaults history view owned active decoded
        simp only [Fin.val_succ, decodeViewPrefix?, Option.map_eq_some_iff] at decoded
        obtain ⟨rest, read, rfl⟩ := decoded
        exact ih _ _ _ tail _ _ _ rest owned active read
  | commit name owner fresh guard next ih =>
      intro refs outputs policy event
      refine Fin.cases ?_ (fun tail => ?_) event
      · intro store defaults history view owned active decoded
        have same : owner = who := Option.some.inj owned
        simp only [Fin.val_zero, decodeViewPrefix?, Option.map_eq_some_iff] at decoded
        obtain ⟨observation, read, rfl⟩ := decoded
        have law := compilePolicyTable_commit_of_decode refs outputs policy same store defaults
          active history observation read
        refine (congrArg (PMF.map (decodeEventAction _ _)) law).trans ?_
        simp only [BehavioralPolicy.protocolAction,
          ProtocolView.entry, Sum.elim_inl, dite_eq_left same, DecisionView.defaulted,
          dite_eq_left active]
        rfl
      · intro store defaults history view owned active decoded
        simp only [Fin.val_succ, decodeViewPrefix?, Option.map_eq_some_iff] at decoded
        obtain ⟨rest, read, rfl⟩ := decoded
        exact ih _ _ _ tail _ _ _ rest owned active read
  | reveal published owner name fresh selected unresolved next ih =>
      intro refs outputs policy event
      refine Fin.cases ?_ (fun tail => ?_) event
      · intro store defaults history view owned active decoded
        have same : owner = who := Option.some.inj owned
        simp only [Fin.val_zero, decodeViewPrefix?, Option.map_eq_some_iff] at decoded
        obtain ⟨observation, read, rfl⟩ := decoded
        have law := compilePolicyTable_reveal_of_decode refs outputs policy same store defaults
          active history observation read
        refine (congrArg (PMF.map (decodeEventAction _ _)) law).trans ?_
        simp only [BehavioralPolicy.protocolAction,
          ProtocolView.entry, Sum.elim_inl, dite_eq_left same, DecisionView.defaulted,
          dite_eq_left active]
        rfl
      · intro store defaults history view owned active decoded
        simp only [Fin.val_succ, decodeViewPrefix?, Option.map_eq_some_iff] at decoded
        obtain ⟨rest, read, rfl⟩ := decoded
        exact ih _ _ _ tail _ _ _ rest owned active read

/-- The decoded actor is the instruction owner unless that owner has publicly defaulted. -/
theorem decodeSourcePrefix?_actor (who : Player) {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} : ∀ (count : Nat)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (refs : ContextRefs layout Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : History Player L)
    (defaults : DefaultHistory Player) (state : ProtocolState program),
    decodeSourcePrefix? program refs registry revelations outputs count store history defaults =
      some state →
    (inside : count < eventCount program) →
      ProtocolView.actor who program (ProtocolState.observe who program state) =
        (eventOwner? program ⟨count, inside⟩).filter
          (fun owner => decide (owner ∉ defaults.defaulted))
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, defaults, state,
      decoded, inside => by
      cases program with
      | ret _ => simp [eventCount] at inside
      | sample _ _ _ next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          rfl
      | commit name owner fresh guard next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          by_cases inactive : owner ∈ defaults.defaulted <;>
            simp [ProtocolView.actor, ProtocolState.observe, ProtocolState.entry, eventOwner?,
              Config.view, DecisionView.defaulted, Option.filter_some, inactive]
      | reveal published owner name fresh source unresolved next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          by_cases inactive : owner ∈ defaults.defaulted <;>
            simp [ProtocolView.actor, ProtocolState.observe, ProtocolState.entry, eventOwner?,
              Config.view, DecisionView.defaulted, Option.filter_some, inactive]
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, defaults,
      state, decoded, inside => by
      cases program with
      | ret _ => cases decoded
      | sample _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_actor who count next _ _ _ _ store history defaults rest
            restDecoded (by simpa [eventCount] using inside)
      | commit _ _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_actor who count next _ _ _ _ store history defaults rest
            restDecoded (by simpa [eventCount] using inside)
      | reveal _ _ _ _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_actor who count next _ _ _ _ store history defaults rest
            restDecoded (by simpa [eventCount] using inside)

/-- **A decoded action is available at its decoded point** under the forfeiture
interface, to every player. -/
theorem decodeSourcePrefix?_available (who : Player) {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} : ∀ (count : Nat)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (refs : ContextRefs layout Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : History Player L)
    (defaults : DefaultHistory Player) (state : ProtocolState program),
    decodeSourcePrefix? program refs registry revelations outputs count store history defaults =
      some state →
    (inside : count < eventCount program) →
    ∀ (graphAction : EventGraph.EventField.Action (outputLayout program ⟨count, inside⟩))
      (action : OwnAction Player L),
      decodeEventAction program ⟨count, inside⟩ graphAction = some action →
      action ∈ ProtocolView.available who program (CommitmentInterface.forfeiture program)
        (ProtocolState.observe who program state)
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, defaults,
      state, decoded, inside => by
      cases program with
      | ret _ => simp [eventCount] at inside
      | sample _ _ _ next =>
          intro _ _ decodedAction
          cases decodedAction
      | commit _ _ _ _ next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro graphAction action decodedAction
          cases decodedAction
          refine ⟨graphAction, ?_, rfl⟩
          cases graphAction with
          | none => trivial
          | some result => cases result <;> trivial
      | reveal _ _ _ _ _ _ next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro graphAction action decodedAction
          cases decodedAction
          exact ⟨graphAction, rfl⟩
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, defaults, state,
      decoded, inside => by
      cases program with
      | ret _ => cases decoded
      | sample _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_available who count next _ _ _ _ store history defaults rest
            restDecoded (by simpa [eventCount] using inside)
      | commit _ _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_available who count next _ _ _ _ store history defaults rest
            restDecoded (by simpa [eventCount] using inside)
      | reveal _ _ _ _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_available who count next _ _ _ _ store history defaults rest
            restDecoded (by simpa [eventCount] using inside)


/-- Current typed agreement reconstructs the whole source configuration,
including its nonempty deferred-guard registry and original own histories. -/
theorem decodeSourcePrefix?_zero_of_agrees
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (source : Config Player L Γ) (store : EventGraph.Store layout)
    (agrees : refs.Agrees source.state store) :
    decodeSourcePrefix? program refs source.registry source.revelations outputs 0
      store source.history source.defaults = some (ProtocolState.entry program source) := by
  rw [decodeSourcePrefix?, decodeState?_eq_some refs source.state store agrees]
  rfl

theorem decodeSourcePrefix?_sample
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) openNames)
    (refs : ContextRefs layout Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout
      (outputLayout (.sample name fresh law next) event))
    (count : Nat) (store : EventGraph.Store layout) (history : History Player L)
    (defaults : DefaultHistory Player) :
    decodeSourcePrefix? (.sample name fresh law next) refs registry revelations outputs
        (count + 1) store history defaults =
      (decodeSourcePrefix? next (refs.cons (outputs ⟨0, by simp [eventCount]⟩)) registry.weaken
        revelations.weaken (fun tail => outputs tail.succ) count store history defaults).map
        Sum.inr := rfl

theorem decodeSourcePrefix?_commit
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (refs : ContextRefs layout Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout
      (outputLayout (.commit name owner fresh guard next) event))
    (count : Nat) (store : EventGraph.Store layout) (history : History Player L)
    (defaults : DefaultHistory Player) :
    decodeSourcePrefix? (.commit name owner fresh guard next) refs registry revelations outputs
        (count + 1) store history defaults =
      (decodeSourcePrefix? next (refs.cons (outputs ⟨0, by simp [eventCount]⟩))
        ({ owner := owner, subject := name, payload := payload, source := HasVar.here,
           guard := guard.weaken } :: registry.weaken)
        revelations.weaken (fun tail => outputs tail.succ) count store history defaults).map
        Sum.inr := rfl

theorem decodeSourcePrefix?_reveal
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (refs : ContextRefs layout Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout
      (outputLayout (.reveal published owner name fresh selected unresolved next) event))
    (count : Nat) (store : EventGraph.Store layout) (history : History Player L)
    (defaults : DefaultHistory Player) :
    decodeSourcePrefix? (.reveal published owner name fresh selected unresolved next)
        refs registry revelations outputs (count + 1) store history defaults =
      (decodeSourcePrefix? next (refs.cons (outputs ⟨0, by simp [eventCount]⟩)) registry.weaken
        (revelations.reveal selected) (fun tail => outputs tail.succ)
        count store history defaults).map
          Sum.inr := rfl

/-- Decoding the full instruction count of a program yields a terminal
source protocol state. -/
theorem decodeSourcePrefix?_terminal
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (refs : ContextRefs layout Γ)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : History Player L)
    (defaults : DefaultHistory Player)
    (state : ProtocolState program)
    (decoded : decodeSourcePrefix? program refs registry revelations outputs (eventCount program)
      store history defaults = some state) : ProtocolState.terminal program state := by
  induction program with
  | ret _ => trivial
  | sample name fresh distribution next ih =>
      simp only [eventCount, decodeSourcePrefix?] at decoded
      obtain ⟨nextState, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact ih _ _ _ _ nextState read
  | commit name owner fresh guard next ih =>
      simp only [eventCount, decodeSourcePrefix?] at decoded
      obtain ⟨nextState, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact ih _ _ _ _ nextState read
  | reveal published owner name fresh binding unresolved next ih =>
      simp only [eventCount, decodeSourcePrefix?] at decoded
      obtain ⟨nextState, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact ih _ _ _ _ nextState read

/-- The prefix reader retains the full public default history. -/
theorem decodeSourcePrefix?_defaults {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    (count : Nat) → {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → (refs : ContextRefs layout Γ) →
    (registry : Registry Γ) → (revelations : Revelations Γ) →
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event)) →
    (store : EventGraph.Store layout) → (history : History Player L) →
    (defaults : DefaultHistory Player) → (point : ProtocolState program) →
    decodeSourcePrefix? program refs registry revelations outputs count store history defaults =
      some point → ProtocolState.defaults program point = defaults
  | 0, _, _, program, _, _, _, _, _, _, _, _, decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨state, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact ProtocolState.defaults_entry program _
  | count + 1, _, _, .ret _, _, _, _, _, _, _, _, _, decoded => by cases decoded
  | count + 1, _, _, .sample _ _ _ next, _, _, _, _, _, _, _, _, decoded => by
      rw [decodeSourcePrefix?_sample] at decoded
      obtain ⟨point, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact decodeSourcePrefix?_defaults count next _ _ _ _ _ _ _ point read
  | count + 1, _, _, .commit _ _ _ _ next, _, _, _, _, _, _, _, _, decoded => by
      rw [decodeSourcePrefix?_commit] at decoded
      obtain ⟨point, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact decodeSourcePrefix?_defaults count next _ _ _ _ _ _ _ point read
  | count + 1, _, _, .reveal _ _ _ _ _ _ next, _, _, _, _, _, _, _, _, decoded => by
      rw [decodeSourcePrefix?_reveal] at decoded
      obtain ⟨point, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact decodeSourcePrefix?_defaults count next _ _ _ _ _ _ _ point read

/-- The deterministic readout of a compiled graph configuration for any
dependency choice into the original initialized source protocol. Each owner's
completions keep source rank in every dependency choice, so the chronological completions
decode to the source history. -/
def serviceSourcePrefix? (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies) (rank : Nat)
    (config : (setup.dataflowGraph.withDependencies deps).Config) :
    setup.ProtocolState :=
  decodeSourcePrefix? setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) rank config.store
    (decodeHistory setup.program (config.history)) config.defaults

/-- The readout on the default sequential graph. -/
abbrev sourceServicePrefix? (setup : Setup (Player := Player) (L := L)) :
    Nat → setup.informationGraph.Config → setup.ProtocolState :=
  serviceSourcePrefix? setup setup.informationDependencies

/-- Continue the sole source evaluator from the actual decoded native prefix. -/
def sourceContinuation (setup : Setup (Player := Player) (L := L))
    {deps : setup.dataflowGraph.Dependencies} (profile : BehavioralProfile setup.program) (rank :
      Nat)
    (config : (setup.dataflowGraph.withDependencies deps).Config) :
    PMF (Option (Config Player L setup.program.terminalCtx)) :=
  (setup.continuationLaw profile (serviceSourcePrefix? setup deps rank config)).map some

theorem serviceSourcePrefix?_initial (setup : Setup (Player := Player) (L := L))
    {deps : setup.dataflowGraph.Dependencies} (initial : State L setup.context) :
      serviceSourcePrefix? setup
    deps 0
    (EventGraph.Config.initial (graph := setup.dataflowGraph.withDependencies deps)
        (setup.eventInputs initial)) =
      some (ProtocolState.entry setup.program (Config.initial initial)) := by
  unfold serviceSourcePrefix?
  rw [initial_history setup initial]
  exact decodeSourcePrefix?_zero_of_agrees setup.program _ _ (Config.initial initial) _
    (initial_agrees setup initial)

/-- A semantic runtime checkpoint supplies the readout identity directly;
there is no additional posterior or source-state equality premise. -/
theorem SourceCheckpoint.decode
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    {source : Config Player L Γ}
    {refs : ContextRefs (setup.dataflowGraph.withDependencies deps).layout Γ}
    {rank : Nat}
    {native : (setup.dataflowGraph.withDependencies deps).Config}
    (checkpoint : SourceCheckpoint setup source refs rank native)
    (outputs : ∀ event, EventGraph.FieldRef (setup.dataflowGraph.withDependencies deps).layout
        (outputLayout program event)) :
    decodeSourcePrefix? program refs source.registry source.revelations outputs 0 native.store
      (decodeHistory setup.program (native.history)) native.defaults =
      some (ProtocolState.entry program source) := by
  rw [checkpoint.history, checkpoint.defaults]
  exact decodeSourcePrefix?_zero_of_agrees program refs outputs source native.store
    checkpoint.agrees

/-- Locate the actual semantic checkpoint in the existing source protocol's
sum of positions. This carries the deferred registry through the static
prefix and imposes no strategy, posterior, or native-memory restriction. -/
def SourcePrefixCheckpoint (setup : Setup (Player := Player) (L := L))
    {deps : setup.dataflowGraph.Dependencies} : {Γ : SourceCtx Player L} → {openNames : Finset
      VarId} →
    (program : SourceProgram Player L Γ openNames) →
    ContextRefs (setup.dataflowGraph.withDependencies deps).layout Γ → Registry Γ → Revelations Γ →
    (∀ event, EventGraph.FieldRef (setup.dataflowGraph.withDependencies deps).layout
      (outputLayout program event)) →
    Nat → Nat → ProtocolState program → (setup.dataflowGraph.withDependencies deps).Config → Prop
  | _, _, program, refs, registry, revelations, _, offset, 0, state, native =>
      ∃ source, state = ProtocolState.entry program source ∧ source.registry = registry ∧
        @source.revelations = @revelations ∧ SourceCheckpoint setup source refs offset native
  | _, _, .ret _, _, _, _, _, _, _ + 1, _, _ => False
  | _, _, .sample (payload := payload) _ _ _ next,
      refs, registry, revelations, outputs, offset, count + 1, state, native =>
      let headRef : EventGraph.FieldRef (setup.dataflowGraph.withDependencies deps).layout
          (.publicData payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      match state with
      | .inl _ => False
      | .inr rest => SourcePrefixCheckpoint setup next (refs.cons headRef) registry.weaken
          revelations.weaken (fun tail => outputs tail.succ) (offset + 1) count rest native
  | _, _, .commit (payload := payload) name owner _ guard next,
      refs, registry, revelations, outputs, offset, count + 1, state, native =>
      let headRef : EventGraph.FieldRef (setup.dataflowGraph.withDependencies deps).layout
          (.binding owner payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      let nextRegistry :=
        { owner := owner, subject := name, payload := payload, source := HasVar.here,
          guard := guard.weaken } :: registry.weaken
      match state with
      | .inl _ => False
      | .inr rest => SourcePrefixCheckpoint setup next (refs.cons headRef) nextRegistry
          revelations.weaken (fun tail => outputs tail.succ) (offset + 1) count rest native
  | _, _, .reveal (payload := payload) _ _ _ _ selected _ next,
      refs, registry, revelations, outputs, offset, count + 1, state, native =>
      let headRef : EventGraph.FieldRef (setup.dataflowGraph.withDependencies deps).layout
          (.publication payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      match state with
      | .inl _ => False
      | .inr rest => SourcePrefixCheckpoint setup next (refs.cons headRef) registry.weaken
          (revelations.reveal selected) (fun tail => outputs tail.succ)
          (offset + 1) count rest native

/-- All related full-syntax prefixes decode to their actual original source
protocol state. Missing-field and excessive-prefix fallbacks are unreachable
on these concrete semantic checkpoints. -/
theorem SourcePrefixCheckpoint.decode {setup : Setup (Player := Player) (L := L)}
    {deps : setup.dataflowGraph.Dependencies} : ∀ {Γ : SourceCtx Player L} {openNames : Finset
      VarId}
    (program : SourceProgram Player L Γ openNames)
    (refs : ContextRefs (setup.dataflowGraph.withDependencies deps).layout Γ)
    (registry : Registry Γ)
    (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef (setup.dataflowGraph.withDependencies deps).layout
        (outputLayout program event)) (offset count : Nat) (state : ProtocolState program)
    (native : (setup.dataflowGraph.withDependencies deps).Config),
    SourcePrefixCheckpoint setup program refs registry
    revelations outputs offset count state native → decodeSourcePrefix? program refs registry
    revelations outputs count native.store (decodeHistory setup.program native.history)
      native.defaults = some state := by
  intro Γ openNames program refs registry revelations outputs offset count
  induction count generalizing Γ openNames program refs registry revelations outputs offset with
  | zero =>
      intro state native related
      cases program <;>
        obtain ⟨source, rfl, registryEq, revelationsEq, checkpoint⟩ := related <;>
        rw [← registryEq, ← revelationsEq] <;>
        exact checkpoint.decode _ outputs
  | succ count ih =>
      intro state native related
      cases program with
      | ret payoffs => exact related.elim
      | sample name fresh law next =>
          cases state with
          | inl source => exact related.elim
          | inr rest =>
              rw [decodeSourcePrefix?_sample, ih next _ _ _ _ (offset + 1) rest native related]
              rfl
      | commit name owner fresh guard next =>
          cases state with
          | inl source => exact related.elim
          | inr rest =>
              rw [decodeSourcePrefix?_commit, ih next _ _ _ _ (offset + 1) rest native related]
              rfl
      | reveal published owner name fresh selected unresolved next =>
          cases state with
          | inl source => exact related.elim
          | inr rest =>
              rw [decodeSourcePrefix?_reveal, ih next _ _ _ _ (offset + 1) rest native related]
              rfl

/-- Reading a complete instruction prefix returns the same full configuration
as terminal cell decoding, with the actual private and public histories retained. -/
theorem decodeSourcePrefix?_terminal_readout
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : SourceProgram.History Player L)
    (defaults : DefaultHistory Player) :
    (decodeSourcePrefix? program refs registry revelations outputs (eventCount program)
      store history defaults).bind (ProtocolState.readout program) =
        (decodeState? (terminalRefsWith program refs outputs) store).map fun state =>
          ⟨state, finalRegistry program registry, finalRevelations program revelations,
            history, defaults⟩ := by
  induction program with
  | ret payoffs =>
      simp only [eventCount, decodeSourcePrefix?, terminalRefsWith]
      cases decodeState? refs store <;> rfl
  | sample name fresh distribution next ih =>
      simp only [eventCount, decodeSourcePrefix?, terminalRefsWith, Option.bind_map]
      exact ih _ _ _ _
  | commit name owner fresh guard next ih =>
      simp only [eventCount, decodeSourcePrefix?, terminalRefsWith, Option.bind_map]
      exact ih _ _ _ _
  | reveal published owner name fresh binding unresolved next ih =>
      simp only [eventCount, decodeSourcePrefix?, terminalRefsWith, Option.bind_map]
      exact ih _ _ _ _

/-- A complete native prefix and terminal compilation use the same full source
configuration decoder in every dependency choice. -/
theorem serviceSourcePrefix?_terminal_readout
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (config : (setup.dataflowGraph.withDependencies deps).Config) :
    setup.protocolReadout (serviceSourcePrefix? setup deps (eventCount setup.program) config) =
      decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
        (config.history) := by
  rw [serviceSourcePrefix?, Setup.protocolReadout]
  rw [decodeSourcePrefix?_terminal_readout]
  simp only [decodeConfig?, EventGraph.Config.defaults, EventCompletion.defaults]
  rfl

/-- The sequential native prefix reader agrees with the full terminal compiler
readout, retaining all source configuration fields. -/
theorem sourceServicePrefix?_terminal_readout
    (setup : Setup (Player := Player) (L := L)) (config : setup.informationGraph.Config) :
    setup.protocolReadout (sourceServicePrefix? setup (eventCount setup.program) config) =
      decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
        (config.history) :=
  serviceSourcePrefix?_terminal_readout setup setup.informationDependencies config

/-- Every completed native cut decodes to a terminal source position. Field
availability suffices; no execution provenance or service premise is needed. -/
theorem serviceSourcePrefix?_terminal
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (config : (setup.dataflowGraph.withDependencies deps).Config) (terminal : config.cut.Terminal) :
    ∃ point, serviceSourcePrefix? setup deps (eventCount setup.program) config = some point ∧
      ProtocolState.terminal setup.program point := by
  obtain ⟨source, decoded, _⟩ := exists_decodeState_agrees (terminalRefs setup.program)
    config.store (config.store_available_of_terminal terminal)
  have readout := serviceSourcePrefix?_terminal_readout setup deps config
  change setup.protocolReadout (serviceSourcePrefix? setup deps (eventCount setup.program)
    config) = (decodeState? (terminalRefs setup.program) config.store).map _ at readout
  rw [decoded] at readout
  cases decodedPoint : serviceSourcePrefix? setup deps (eventCount setup.program) config with
  | none =>
      simp only [decodedPoint, Setup.protocolReadout, Option.bind_none, Option.map_some] at readout
      cases readout
  | some point =>
      exact ⟨point, rfl,
        decodeSourcePrefix?_terminal setup.program _ _ _ _ _ _ _ point decodedPoint⟩

/-- At a completed native cut, the source continuation is the pure full source
readout of that cut, including private decisions and the public default record. -/
theorem sourceContinuation_terminal
    (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
    (profile : BehavioralProfile setup.program)
    (config : (setup.dataflowGraph.withDependencies deps).Config)
    (terminal : config.cut.Terminal) :
    sourceContinuation setup profile (eventCount setup.program) config =
      PMF.pure (setup.protocolReadout
        (serviceSourcePrefix? setup deps (eventCount setup.program) config)) := by
  obtain ⟨point, decoded, stopped⟩ := serviceSourcePrefix?_terminal setup deps config terminal
  exact setup.continuationLaw_terminal profile _ (by rw [decoded]; exact stopped)

/-- The full terminal prefix is the return point of its retained configuration. -/
theorem decodeSourcePrefix?_terminal_state
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (refs : ContextRefs layout Γ)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : SourceProgram.History Player L)
    (defaults : DefaultHistory Player) :
    decodeSourcePrefix? program refs registry revelations outputs (eventCount program)
      store history defaults =
      ((decodeState? (terminalRefsWith program refs outputs) store).map fun state =>
        (⟨state, finalRegistry program registry, finalRevelations program revelations,
          history, defaults⟩ : SourceProgram.Config Player L program.terminalCtx)).map
          (ProtocolState.terminalState program) := by
  let decoded := decodeSourcePrefix? program refs registry revelations outputs (eventCount program)
    store history defaults
  calc
    _ = decoded.bind (fun point => (ProtocolState.readout program point).map
        (ProtocolState.terminalState program)) := by
      change decoded = _
      cases result : decoded with
      | none => rfl
      | some point =>
          exact (ProtocolState.terminalState_readout program point
            (decodeSourcePrefix?_terminal program refs registry revelations outputs store
              history defaults point result)).symm
    _ = (decoded.bind (ProtocolState.readout program)).map
        (ProtocolState.terminalState program) := by cases decoded <;> rfl
    _ = _ := by
      rw [decodeSourcePrefix?_terminal_readout]
end Vegas
