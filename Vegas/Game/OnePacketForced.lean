/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceDecodedDebt
import Vegas.Game.ServiceInformation
import Vegas.Compile.EventGraphParameterReadout
import Vegas.Source.FailedBindingDeviation
import Vegas.Source.Exclusion

/-! # The forced region and the projected source view

A native information state of the supplied runtime is *forced* for its owner
when some native history at it decodes, at its completed prefix, to a source
point at which no reveal of the owner has failed and every other player is
neither excluded nor owes a failed reveal (`Vegas.forcedAgent`). The owner's
own bad bindings are allowed: a guard-violating binding leaves it indebted, and
an unopenable or wrongly typed binding decodes to a failed binding of its own,
but neither is public before the reveal that completes it. A failed reveal is
public, so the owner's information after one is not forced. Forcing is a
property of the information state by construction, and depends on the response
menu, the initial law, the horizon and the scheduler only through the native
histories.

The source view of a native information state decodes the owner's masked
store at the length of its completion order and its own completions
(`Vegas.projectView`). At every native state whose configuration decodes at its
completed prefix, it is the owner's view of the decoded source point
(`Vegas.projectView_observe`); it reads no foreign private value. Every
configuration of every native history has a source residual at its completed
prefix (`Vegas.protocol_sourceResidual`), so a source property closed under
every step that holds at a decoded point is a decoded state property of that
history (`Vegas.decodedState_of_decode`).
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- A program point at which a publication written by one of `who`'s reveals
failed. Publications are public, so every player observes it. -/
def RevealFailed (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Prop
  | _, _, .ret _ => fun _ => False
  | _, _, .sample _ _ _ next => Sum.elim (fun _ => False) (RevealFailed who next)
  | _, _, .commit _ _ _ _ next => Sum.elim (fun _ => False) (RevealFailed who next)
  | _, _, .reveal _ owner _ _ _ _ next =>
      Sum.elim (fun _ => False)
        (fun rest => (owner = who ∧ (base next rest).get .here = .failure) ∨
          RevealFailed who next rest)

/-- A failed reveal is a debt: the player owes, and has paid, a failed reveal. -/
theorem RevealFailed.indebted {who : Player} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    RevealFailed who program state → Indebted who program state
  | _, _, .ret _, _, failed => failed.elim
  | _, _, .sample _ _ _ next, state, failed => by
      cases state with
      | inl _ => exact failed.elim
      | inr rest => exact RevealFailed.indebted next rest failed
  | _, _, .commit _ _ _ _ next, state, failed => by
      cases state with
      | inl _ => exact failed.elim
      | inr rest => exact RevealFailed.indebted next rest failed
  | _, _, .reveal _ _ _ _ _ _ next, state, failed => by
      cases state with
      | inl _ => exact failed.elim
      | inr rest =>
          rcases failed with own | later
          · exact Or.inl own
          · exact Or.inr (RevealFailed.indebted next rest later)

/-- A failed generated reveal excludes its owner when its publication has
the provenance retained by actual source histories. -/
theorem RevealFailed.excluded {who : Player} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    PublicationsDefaulted program state → RevealFailed who program state →
      Excluded who program state
  | _, _, .ret _, _, _, failed => failed.elim
  | _, _, .sample _ _ _ next, state, valid, failed => by
      cases state with
      | inl _ => exact failed.elim
      | inr rest => exact RevealFailed.excluded next rest valid failed
  | _, _, .commit _ _ _ _ next, state, valid, failed => by
      cases state with
      | inl _ => exact failed.elim
      | inr rest => exact RevealFailed.excluded next rest valid failed
  | _, _, .reveal _ _ _ _ _ _ next, state, valid, failed => by
      cases state with
      | inl _ => exact failed.elim
      | inr rest =>
          rcases failed with own | later
          · rcases own with ⟨rfl, failed⟩
            exact valid.1 failed
          · exact RevealFailed.excluded next rest valid.2 later

end ProtocolState

/-- The view of a program point's entry configuration, built from that
configuration's decision view. -/
def ProtocolView.entry (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → DecisionView who Γ → ProtocolView who program
  | _, _, .ret _, view => view
  | _, _, .sample _ _ _ _, view => Sum.inl view
  | _, _, .commit _ _ _ _ _, view => Sum.inl view
  | _, _, .reveal _ _ _ _ _ _ _, view => Sum.inl view

theorem ProtocolState.observe_entry (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    ProtocolState.observe who program (ProtocolState.entry program config) =
      ProtocolView.entry who program (config.view who) := by
  cases program <;> rfl

end Vegas.SourceProgram

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

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

omit [DecidableEq Player] in
/-- A configuration's chronological history has one completion per completed
event, so at a prefix its length is the prefix rank. -/
theorem history_length_of_isPrefix {graph : EventGraph Player L} (config : graph.Config)
    {rank : Nat} (ordered : config.cut.IsPrefix rank) : config.history.length = rank := by
  classical
  have completed : (config.history.map EventGraph.Completion.event).toFinset =
      config.cut.completed := by
    ext event
    rw [List.mem_toFinset]
    exact config.history_exact event
  have filtered : config.cut.completed =
      (Finset.univ : Finset graph.EventId).filter fun event => event.val < rank := by
    ext event
    rw [Finset.mem_filter]
    exact ⟨fun member => ⟨Finset.mem_univ _, (ordered.2 event).mp member⟩,
      fun below => (ordered.2 event).mpr below.2⟩
  rw [← List.length_map (f := EventGraph.Completion.event),
    ← List.toFinset_card_of_nodup config.history_nodup, completed, filtered]
  rw [show ((Finset.univ : Finset graph.EventId).filter fun event => event.val < rank) =
      Finset.univ.filter (fun event : Fin graph.order.eventCount => (event : Nat) < rank) from rfl,
    Fin.card_filter_val_lt]
  exact min_eq_right ordered.1

section Runtime

variable (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The source view a native player view of the supplied runtime shows `who`:
its masked store read at the length of its completion order, with its own
completions decoded to source actions. It is `none` at a view carrying another
player's identity and where decoding fails. -/
def sourceViewOf (who : Player) (view : (application setup runtime leaks).PlayerView) :
    setup.ProtocolView who :=
  if same : view.application.who = who then
    let observed : (graph setup).PlayerObservation who := same ▸ view.application.observation
    decodeViewPrefix? who setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputRef setup.program) observed.completionOrder.length observed.store
      (decodeCompletions setup.program
        (observed.ownActions.map (setup.eventGraph.fromModeCompletion .sequential)))
      observed.defaults
  else none

/-- **The projected source view.** The source view a native information state
of the supplied runtime shows its owner: at a decision input, the source view of
its current player view (`Vegas.sourceViewOf`); `none` at a non-decision
input. -/
def projectView (who : Player) : (application setup runtime leaks).Info → setup.ProtocolView who
  | none => none
  | some (_, view) => sourceViewOf setup runtime leaks who view

/-- **The projection is the decoded point's view.** At an execution whose
configuration decodes at its completed prefix to a source point, the projected
view of `who`'s observation, whatever its recall, is `who`'s view of that point. -/
theorem projectView_observe (who : Player) (execution : (application setup runtime leaks).Execution)
    (rank : Nat) (ordered : execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (past : List (application setup runtime leaks).PlayerEntry) :
    projectView setup runtime leaks who (some (past, execution.observe (application setup runtime
      leaks) who)) =
      setup.protocolObserve who (some point) := by
  change sourceViewOf setup runtime leaks who (execution.observe (application setup runtime leaks)
    who) = _
  unfold sourceViewOf
  rw [dite_eq_left
    (show (execution.observe (application setup runtime leaks) who).application.who = who from rfl)]
  change decodeViewPrefix? who setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
      ((graph setup).playerObserve who execution.application.config).completionOrder.length
      ((graph setup).playerStore who execution.application.config.store)
      (decodeCompletions setup.program
        (((graph setup).ownCompletions who execution.application.config.history).map
          (setup.eventGraph.fromModeCompletion .sequential)))
      execution.application.config.defaults = _
  rw [EventGraph.playerObserve_completionOrder, List.length_map,
    history_length_of_isPrefix execution.application.config ordered]
  refine (decodeViewPrefix?_playerStore (graph := graph setup) who rank setup.program _ _ _
    _ _).trans ?_
  refine (congrArg (fun own => decodeViewPrefix? who setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program) rank
    execution.application.config.store (decodeCompletions setup.program own)
    execution.application.config.defaults)
    (ownCompletions_fromModeCompletion setup (mode := .sequential) who
      execution.application.config.history)).trans ?_
  exact decodeViewPrefix?_eq_observe who rank setup.program _ [] _ _ _ _ _ point decoded

variable {setup runtime leaks}

/-- **Every native history decodes.** Every configuration of a history of any
response menu of the supplied runtime, under any scheduler, has a source
residual at some prefix, for every source profile. -/
theorem protocol_sourceResidual (profile : BehavioralProfile setup.program)
    (menu : (application setup runtime leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler) :
    ∀ {state} (_trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace state)
      (control : (application setup runtime leaks).Control), state = some control →
      ∃ rank,
        Nonempty (SourceResidual setup profile rank control.execution.application.config) := by
  intro state trace
  induction trace with
  | start => intro _ initialized; cases initialized
  | @extend before after prior joint _ realized ih =>
      intro control current
      subst current
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state =>
            some ⟨horizon, none, ReactiveApplication.Execution.initial
              (application setup runtime leaks) state⟩).support at realized
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨0, ⟨SourceResidual.initial setup profile initial⟩⟩
      | some previous =>
          obtain ⟨rank, ⟨residual⟩⟩ := ih previous rfl
          exact residual.path (reactive_protocol_graph_steps runtime leaks
            (initialLaw setup) horizon scheduler previous control joint realized)

/-- The source point decoded from an initialized native history retains
publication-default provenance, including through automatic completion. -/
theorem publicationsDefaulted_of_decode
    {menu : (application setup runtime leaks).ResponseMenu} {horizon : Nat}
    {scheduler : (application setup runtime leaks).Scheduler}
    (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (control : (application setup runtime leaks).Control) (current : history.state = some control)
    {rank : Nat} (ordered : control.execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank control.execution.application.config = some point) :
    ProtocolState.PublicationsDefaulted setup.program point := by
  obtain ⟨found, ⟨residual⟩, valid⟩ :=
    decodedState_history_of_stepClosed (profile := failureProfile setup.program)
      (property := ProtocolState.PublicationsDefaulted setup.program)
      (fun before joint after holds reached =>
        ProtocolState.publicationsDefaulted_step setup.program before after joint holds reached)
      (fun initial _ => ProtocolState.publicationsDefaulted_entry setup.program
        (Config.initial initial)) menu horizon scheduler history.trace control current
  have same := EventOrder.Cut.IsPrefix.unique ordered residual.checkpoint.ordered
  subst same
  exact valid point decoded

/-- A step-closed source property holding at the decoded point of a native
history's configuration, at its completed prefix, is a decoded state property
of that history, for every source profile. -/
theorem decodedState_of_decode (profile : BehavioralProfile setup.program)
    {property : ProtocolState setup.program → Prop}
    {menu : (application setup runtime leaks).ResponseMenu} {horizon : Nat}
    {scheduler : (application setup runtime leaks).Scheduler}
    (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (control : (application setup runtime leaks).Control) (current : history.state = some control)
    {rank : Nat} (ordered : control.execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank control.execution.application.config = some point)
    (holds : property point) :
    DecodedState setup runtime leaks profile property history.state := by
  obtain ⟨found, ⟨residual⟩⟩ :=
    protocol_sourceResidual (runtime := runtime) profile menu horizon scheduler history.trace
      control current
  rw [current]
  have same := EventOrder.Cut.IsPrefix.unique ordered residual.checkpoint.ordered
  subst same
  refine ⟨rank, ⟨residual⟩, fun other read => ?_⟩
  rw [decoded, Option.some.injEq] at read
  subst read
  exact holds

variable (setup runtime)

/-- **A forced source point for `who`.** No reveal of `who` has failed, and
every other player is neither excluded nor owes a failed reveal. `who` itself
may hold bad bindings: it may be indebted to a guard, or hold a failed binding. -/
def ForcedPoint (who : Player) (point : ProtocolState setup.program) : Prop :=
  ¬ ProtocolState.RevealFailed who setup.program point ∧
    ∀ other, other ≠ who →
      ¬ ProtocolState.Excluded other setup.program point ∧
        ¬ ProtocolState.OwesFailure other setup.program point

variable (leaks)

/-- An initialized native state whose configuration decodes at its completed
prefix to a forced source point for `who`. -/
def ForcedState (who : Player) : (application setup runtime leaks).ProtocolState → Prop
  | none => False
  | some control => ∃ rank point, control.execution.application.config.cut.IsPrefix rank ∧
      sourceServicePrefix? setup rank control.execution.application.config = some point ∧
      ForcedPoint setup who point

variable {setup runtime leaks}

/-- **The forced region.** An information state of `who` is forced when some
native history at it is in a forced state for `who`. This is a property of the
information state alone. -/
def forcedAgent (menu : (application setup runtime leaks).ResponseMenu)
    (initial : PMF (application setup runtime leaks).State) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler) (who : Player)
    (info : (menu.information initial horizon scheduler).InfoState who) : Prop :=
  ∃ history : (menu.protocol initial horizon scheduler).History,
    (menu.information initial horizon scheduler).infoOf who history.trace = info ∧
      ForcedState setup runtime leaks who history.state

/-- A history in a forced state makes its information state forced. -/
theorem forcedAgent_of_history {menu : (application setup runtime leaks).ResponseMenu}
    {initial : PMF (application setup runtime leaks).State} {horizon : Nat}
    {scheduler : (application setup runtime leaks).Scheduler} {who : Player}
    (history : (menu.protocol initial horizon scheduler).History)
    (forced : ForcedState setup runtime leaks who history.state) :
    forcedAgent (runtime := runtime) menu initial horizon scheduler who
      ((menu.information initial horizon scheduler).infoOf who history.trace) :=
  ⟨history, rfl, forced⟩

end Runtime

end Vegas
