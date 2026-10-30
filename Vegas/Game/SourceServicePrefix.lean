/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceCheckpoint
import Vegas.Compile.EventGraphReadout
import Vegas.Source.SetupProtocolEvaluation

/-! # Reading full source protocol positions from native checkpoints

The static instruction prefix determines the typed field references, deferred
guard registry and publication references. Reading those existing fields and
the decoded completion history reconstructs the original source protocol
state. This decoder performs no source or runtime transition.
-/

noncomputable section

namespace Vegas

open SourceProgram

open EventGraphRuntime

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

/-- The deterministic readout of a configuration of the service graph of any
dependency mode into the original initialized source protocol. Each owner's
completions keep source rank in every mode, so the chronological completions
decode to the source history. -/
def serviceSourcePrefix? (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) (rank : Nat) (config : (serviceGraph setup mode).Config) :
    setup.ProtocolState :=
  decodeSourcePrefix? setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) rank config.store
    (decodeHistory setup.program (config.history.map
      (setup.eventGraph.fromModeCompletion mode))) config.defaults

/-- The readout on the default sequential graph. -/
abbrev sourceServicePrefix? (setup : Setup (Player := Player) (L := L)) :
    Nat → (graph setup).Config → setup.ProtocolState :=
  serviceSourcePrefix? setup .sequential

/-- Continue the sole source evaluator from the actual decoded native prefix. -/
def sourceContinuation (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} (profile : BehavioralProfile setup.program) (rank : Nat)
    (config : (serviceGraph setup mode).Config) :
    PMF (Option (Config Player L setup.program.terminalCtx)) :=
  (setup.continuationLaw profile (serviceSourcePrefix? setup mode rank config)).map some

theorem serviceSourcePrefix?_initial (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} (initial : State L setup.context) : serviceSourcePrefix? setup
    mode 0
    (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
        (setup.eventInputs initial)).config =
      some (ProtocolState.entry setup.program (Config.initial initial)) := by
  unfold serviceSourcePrefix?
  rw [initial_history setup initial]
  exact decodeSourcePrefix?_zero_of_agrees setup.program _ _ (Config.initial initial) _
    (initial_agrees setup initial)

/-- A semantic runtime checkpoint supplies the readout identity directly;
there is no additional posterior or source-state equality premise. -/
theorem SourceCheckpoint.decode
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    {source : Config Player L Γ} {refs : ContextRefs (serviceGraph setup mode).layout Γ}
    {rank : Nat}
    {native : (serviceGraph setup mode).Config}
    (checkpoint : SourceCheckpoint setup source refs rank native)
    (outputs : ∀ event, EventGraph.FieldRef (serviceGraph setup mode).layout
        (outputLayout program event)) :
    decodeSourcePrefix? program refs source.registry source.revelations outputs 0 native.store
      (decodeHistory setup.program (native.history.map
        (setup.eventGraph.fromModeCompletion mode))) native.defaults =
      some (ProtocolState.entry program source) := by
  rw [checkpoint.history, checkpoint.defaults]
  exact decodeSourcePrefix?_zero_of_agrees program refs outputs source native.store
    checkpoint.agrees

/-- Locate the actual semantic checkpoint in the existing source protocol's
sum of positions. This carries the deferred registry through the static
prefix and imposes no strategy, posterior, or native-memory restriction. -/
def SourcePrefixCheckpoint (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} : {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) → ContextRefs (serviceGraph setup mode).layout
    Γ → Registry Γ → Revelations Γ →
    (∀ event, EventGraph.FieldRef (serviceGraph setup mode).layout (outputLayout program event)) →
    Nat → Nat → ProtocolState program → (serviceGraph setup mode).Config → Prop
  | _, _, program, refs, registry, revelations, _, offset, 0, state, native =>
      ∃ source, state = ProtocolState.entry program source ∧ source.registry = registry ∧
        @source.revelations = @revelations ∧ SourceCheckpoint setup source refs offset native
  | _, _, .ret _, _, _, _, _, _, _ + 1, _, _ => False
  | _, _, .sample (payload := payload) _ _ _ next,
      refs, registry, revelations, outputs, offset, count + 1, state, native =>
      let headRef : EventGraph.FieldRef (serviceGraph setup mode).layout (.publicData payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      match state with
      | .inl _ => False
      | .inr rest => SourcePrefixCheckpoint setup next (refs.cons headRef) registry.weaken
          revelations.weaken (fun tail => outputs tail.succ) (offset + 1) count rest native
  | _, _, .commit (payload := payload) name owner _ guard next,
      refs, registry, revelations, outputs, offset, count + 1, state, native =>
      let headRef : EventGraph.FieldRef (serviceGraph setup mode).layout
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
      let headRef : EventGraph.FieldRef (serviceGraph setup mode).layout
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
    {mode : EventGraph.ExecutionMode} : ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (refs : ContextRefs (serviceGraph setup mode).layout Γ) (registry : Registry Γ)
    (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef (serviceGraph setup mode).layout
        (outputLayout program event)) (offset count : Nat) (state : ProtocolState program)
    (native : (serviceGraph setup mode).Config), SourcePrefixCheckpoint setup program refs registry
    revelations outputs offset count state native → decodeSourcePrefix? program refs registry
    revelations outputs count native.store (decodeHistory setup.program (native.history.map
          (setup.eventGraph.fromModeCompletion mode))) native.defaults = some state := by
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
configuration decoder in every dependency mode. -/
theorem serviceSourcePrefix?_terminal_readout
    (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    (config : (serviceGraph setup mode).Config) :
    setup.protocolReadout (serviceSourcePrefix? setup mode (eventCount setup.program) config) =
      decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
        (config.history.map (setup.eventGraph.fromModeCompletion mode)) := by
  rw [serviceSourcePrefix?, Setup.protocolReadout]
  rw [decodeSourcePrefix?_terminal_readout]
  simp only [decodeConfig?, EventGraph.Config.defaults, EventGraph.Completion.defaults,
    List.map_map]
  rfl

/-- The sequential native prefix reader agrees with the full terminal compiler
readout, retaining all source configuration fields. -/
theorem sourceServicePrefix?_terminal_readout
    (setup : Setup (Player := Player) (L := L)) (config : (graph setup).Config) :
    setup.protocolReadout (sourceServicePrefix? setup (eventCount setup.program) config) =
      decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
        (config.history.map (setup.eventGraph.fromModeCompletion .sequential)) :=
  serviceSourcePrefix?_terminal_readout setup .sequential config

/-- Every completed native cut decodes to a terminal source position. Field
availability suffices; no execution provenance or service premise is needed. -/
theorem serviceSourcePrefix?_terminal
    (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    (config : (serviceGraph setup mode).Config) (terminal : config.cut.Terminal) :
    ∃ point, serviceSourcePrefix? setup mode (eventCount setup.program) config = some point ∧
      ProtocolState.terminal setup.program point := by
  obtain ⟨source, decoded, _⟩ := exists_decodeState_agrees (terminalRefs setup.program)
    config.store (config.store_available_of_terminal terminal)
  have readout := serviceSourcePrefix?_terminal_readout setup mode config
  change setup.protocolReadout (serviceSourcePrefix? setup mode (eventCount setup.program)
    config) = (decodeState? (terminalRefs setup.program) config.store).map _ at readout
  rw [decoded] at readout
  cases decodedPoint : serviceSourcePrefix? setup mode (eventCount setup.program) config with
  | none =>
      simp only [decodedPoint, Setup.protocolReadout, Option.bind_none, Option.map_some] at readout
      cases readout
  | some point =>
      exact ⟨point, rfl,
        decodeSourcePrefix?_terminal setup.program _ _ _ _ _ _ _ point decodedPoint⟩

/-- At a completed native cut, the source continuation is the pure full source
readout of that cut, including private decisions and the public default record. -/
theorem sourceContinuation_terminal
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    (profile : BehavioralProfile setup.program) (config : (serviceGraph setup mode).Config)
    (terminal : config.cut.Terminal) :
    sourceContinuation setup profile (eventCount setup.program) config =
      PMF.pure (setup.protocolReadout
        (serviceSourcePrefix? setup mode (eventCount setup.program) config)) := by
  obtain ⟨point, decoded, stopped⟩ := serviceSourcePrefix?_terminal setup mode config terminal
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
