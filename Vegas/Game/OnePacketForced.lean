module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceDecodedDebt
public import Vegas.Game.SourceServiceCompletion
public import Vegas.Game.ServiceInformation
public import Vegas.Compile.EventGraphParameterReadout
public import Vegas.Source.FailedBindingDeviation
public import Vegas.Source.Exclusion

@[expose] public section

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


end Vegas.SourceProgram

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section Runtime

variable (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts setup.informationGraph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))

/-- The source view a native player view of the supplied runtime shows `who`:
its masked store read at the length of its completion order, with its own
completions decoded to source actions. It is `none` at a view carrying another
player's identity and where decoding fails. -/
def sourceViewOf (who : Player) (view : (application setup timeouts leaks).PlayerView) :
    setup.ProtocolView who :=
  if same : view.application.who = who then
    let observed : setup.informationGraph.PlayerObservation who := same ▸
      view.application.observation
    decodeViewPrefix? who setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputRef setup.program) observed.completionOrder.length observed.store
      (decodeCompletions setup.program
        (observed.ownActions))
      observed.defaults
  else none

/-- **The projected source view.** The source view a native information state
of the supplied runtime shows its owner: at a decision input, the source view of
its current player view (`Vegas.sourceViewOf`); `none` at a non-decision
input. -/
def projectView (who : Player) : (application setup timeouts leaks).Info → setup.ProtocolView who
  | none => none
  | some (_, view) => sourceViewOf setup timeouts leaks who view

/-- **The projection is the decoded point's view.** At an execution whose
configuration decodes at its completed prefix to a source point, the projected
view of `who`'s observation, whatever its recall, is `who`'s view of that point. -/
theorem projectView_observe (who : Player) (execution : (application setup timeouts
  leaks).Execution)
    (rank : Nat) (ordered : execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (past : List (application setup timeouts leaks).PlayerEntry) :
    projectView setup timeouts leaks who (some (past, execution.observe (application setup timeouts
      leaks) who)) =
      setup.protocolObserve who (some point) := by
  change sourceViewOf setup timeouts leaks who (execution.observe (application setup timeouts leaks)
    who) = _
  unfold sourceViewOf
  rw [dite_eq_left
    (show (execution.observe (application setup timeouts leaks) who).application.who = who from
      rfl)]
  change decodeViewPrefix? who setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
      (setup.informationGraph.playerObserve who execution.application.config).completionOrder.length
      (setup.informationGraph.playerStore who execution.application.config.store)
      (decodeCompletions setup.program
        ((setup.informationGraph.ownCompletions who execution.application.config.history)))
      execution.application.config.defaults = _
  rw [EventGraph.playerObserve_completionOrder, List.length_map,
    EventGraph.Config.history_length_of_isPrefix execution.application.config ordered]
  refine (decodeViewPrefix?_playerStore (graph := setup.informationGraph) who rank setup.program _
    _ _
    _ _).trans ?_
  exact decodeViewPrefix?_eq_observe who rank setup.program _ [] _ _ _ _ _ point decoded

variable {setup timeouts leaks}

/-- **Every native history decodes.** Every configuration of a history of any
response menu of the supplied runtime, under any scheduler, has a source
residual at some prefix, for every source profile. -/
theorem protocol_sourceResidual (profile : BehavioralProfile setup.program)
    (menu : (application setup timeouts leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup timeouts leaks).Scheduler) :
    ∀ {state} (_trace : (menu.protocol (initialDistribution setup) horizon scheduler).Trace state)
      (control : (application setup timeouts leaks).Control), state = some control →
      ∃ rank,
        Nonempty (SourceResidual setup profile rank control.execution.application.config) := by
  intro state trace control current
  exact SourceResidual.of_rawTrace profile horizon scheduler
    (menu.toRawTrace (initialDistribution setup) horizon scheduler trace) control current

/-- The source point decoded from an initialized native history retains
publication-default provenance, including through automatic completion. -/
theorem publicationsDefaulted_of_decode
    {menu : (application setup timeouts leaks).ResponseMenu} {horizon : Nat}
    {scheduler : (application setup timeouts leaks).Scheduler}
    (history : (menu.protocol (initialDistribution setup) horizon scheduler).History)
    (control : (application setup timeouts leaks).Control) (current : history.state = some control)
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
    {menu : (application setup timeouts leaks).ResponseMenu} {horizon : Nat}
    {scheduler : (application setup timeouts leaks).Scheduler}
    (history : (menu.protocol (initialDistribution setup) horizon scheduler).History)
    (control : (application setup timeouts leaks).Control) (current : history.state = some control)
    {rank : Nat} (ordered : control.execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank control.execution.application.config = some point)
    (holds : property point) :
    DecodedState setup timeouts leaks profile property history.state := by
  obtain ⟨found, ⟨residual⟩⟩ :=
    protocol_sourceResidual (timeouts := timeouts) profile menu horizon scheduler history.trace
      control current
  rw [current]
  have same := EventOrder.Cut.IsPrefix.unique ordered residual.checkpoint.ordered
  subst same
  refine ⟨rank, ⟨residual⟩, fun other read => ?_⟩
  rw [decoded, Option.some.injEq] at read
  subst read
  exact holds

variable (setup timeouts)

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
def ForcedState (who : Player) : (application setup timeouts leaks).ProtocolState → Prop
  | none => False
  | some control => ∃ rank point, control.execution.application.config.cut.IsPrefix rank ∧
      sourceServicePrefix? setup rank control.execution.application.config = some point ∧
      ForcedPoint setup who point

variable {setup timeouts leaks}

/-- **The forced region.** An information state of `who` is forced when some
native history at it is in a forced state for `who`. This is a property of the
information state alone. -/
def forcedAgent (menu : (application setup timeouts leaks).ResponseMenu)
    (initial : PMF (application setup timeouts leaks).State) (horizon : Nat)
    (scheduler : (application setup timeouts leaks).Scheduler) (who : Player)
    (info : (menu.information initial horizon scheduler).InfoState who) : Prop :=
  ∃ history : (menu.protocol initial horizon scheduler).History,
    (menu.information initial horizon scheduler).infoOf who history.trace = info ∧
      ForcedState setup timeouts leaks who history.state

/-- A history in a forced state makes its information state forced. -/
theorem forcedAgent_of_history {menu : (application setup timeouts leaks).ResponseMenu}
    {initial : PMF (application setup timeouts leaks).State} {horizon : Nat}
    {scheduler : (application setup timeouts leaks).Scheduler} {who : Player}
    (history : (menu.protocol initial horizon scheduler).History)
    (forced : ForcedState setup timeouts leaks who history.state) :
    forcedAgent (timeouts := timeouts) menu initial horizon scheduler who
      ((menu.information initial horizon scheduler).infoOf who history.trace) :=
  ⟨history, rfl, forced⟩

end Runtime

end Vegas
