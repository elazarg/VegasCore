/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCheckpoint
import Vegas.Compile.EventGraphReadout

/-! # Reading full source protocol positions from native checkpoints

The static instruction prefix determines the typed field references, deferred
guard registry and publication references. Reading those existing fields and
the decoded completion history reconstructs the original source protocol
state. This decoder performs no source or runtime transition.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open EventGraphRuntime EventLowering

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
    Nat → EventGraph.Store layout → History Player L → Option (ProtocolState program)
  | _, _, program, refs, registry, revelations, _, 0, store, history =>
      (decodeState? refs store).map fun state =>
        ProtocolState.entry program ⟨state, registry, revelations, history⟩
  | _, _, .ret _, _, _, _, _, _ + 1, _, _ => none
  | _, _, .sample (payload := payload) _ _ _ next,
      refs, registry, revelations, outputs, count + 1, store, history =>
      let headRef : EventGraph.FieldRef layout (.publicData payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      (decodeSourcePrefix? next (refs.cons headRef) registry.weaken revelations.weaken
        (fun tail => outputs tail.succ) count store history).map Sum.inr
  | _, _, .commit (payload := payload) name owner _ guard next,
      refs, registry, revelations, outputs, count + 1, store, history =>
      let headRef : EventGraph.FieldRef layout (.binding owner payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      let nextRegistry :=
        { owner := owner, subject := name, payload := payload, source := HasVar.here,
          guard := guard.weaken } :: registry.weaken
      (decodeSourcePrefix? next (refs.cons headRef) nextRegistry revelations.weaken
        (fun tail => outputs tail.succ) count store history).map Sum.inr
  | _, _, .reveal (payload := payload) _ _ _ _ selected _ next,
      refs, registry, revelations, outputs, count + 1, store, history =>
      let headRef : EventGraph.FieldRef layout (.publication payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      (decodeSourcePrefix? next (refs.cons headRef) registry.weaken
        (revelations.reveal selected) (fun tail => outputs tail.succ) count store history).map
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
      store source.history = some (ProtocolState.entry program source) := by
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
    (count : Nat) (store : EventGraph.Store layout) (history : History Player L) :
    decodeSourcePrefix? (.sample name fresh law next) refs registry revelations outputs
        (count + 1) store history =
      (decodeSourcePrefix? next (refs.cons (outputs ⟨0, by simp [eventCount]⟩)) registry.weaken
        revelations.weaken (fun tail => outputs tail.succ) count store history).map Sum.inr := rfl

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
    (count : Nat) (store : EventGraph.Store layout) (history : History Player L) :
    decodeSourcePrefix? (.commit name owner fresh guard next) refs registry revelations outputs
        (count + 1) store history =
      (decodeSourcePrefix? next (refs.cons (outputs ⟨0, by simp [eventCount]⟩))
        ({ owner := owner, subject := name, payload := payload, source := HasVar.here,
           guard := guard.weaken } :: registry.weaken)
        revelations.weaken (fun tail => outputs tail.succ) count store history).map Sum.inr := rfl

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
    (count : Nat) (store : EventGraph.Store layout) (history : History Player L) :
    decodeSourcePrefix? (.reveal published owner name fresh selected unresolved next)
        refs registry revelations outputs (count + 1) store history =
      (decodeSourcePrefix? next (refs.cons (outputs ⟨0, by simp [eventCount]⟩)) registry.weaken
        (revelations.reveal selected) (fun tail => outputs tail.succ) count store history).map
          Sum.inr := rfl

/-- The deterministic readout into the original initialized source protocol. -/
def sourceServicePrefix? (setup : Setup (Player := Player) (L := L))
    (rank : Nat) (config : (graph setup).Config) : setup.ProtocolState :=
  decodeSourcePrefix? setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) rank config.store
    (decodeHistory setup.program (config.history.map
      (setup.eventGraph.fromModeCompletion .sequential)))

theorem sourceServicePrefix?_initial (setup : Setup (Player := Player) (L := L))
    (initial : State L setup.context) :
    sourceServicePrefix? setup 0
        (EventGraphRuntime.State.initial (graph := graph setup)
          (setup.eventInputs initial)).config =
      some (ProtocolState.entry setup.program (setup.initialConfig initial)) := by
  unfold sourceServicePrefix?
  rw [initial_history setup initial]
  exact decodeSourcePrefix?_zero_of_agrees setup.program _ _ (setup.initialConfig initial) _
    (initial_agrees setup initial)

/-- A semantic runtime checkpoint supplies the readout identity directly;
there is no additional posterior or source-state equality premise. -/
theorem SourceCheckpoint.decode
    {setup : Setup (Player := Player) (L := L)}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    {source : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {native : (graph setup).Config}
    (checkpoint : SourceCheckpoint setup source refs rank native)
    (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event)) :
    decodeSourcePrefix? program refs source.registry source.revelations outputs 0 native.store
      (decodeHistory setup.program (native.history.map
        (setup.eventGraph.fromModeCompletion .sequential))) =
      some (ProtocolState.entry program source) := by
  rw [checkpoint.history]
  exact decodeSourcePrefix?_zero_of_agrees program refs outputs source native.store
    checkpoint.agrees

/-- Locate the actual semantic checkpoint in the existing source protocol's
sum of positions. This carries the deferred registry through the static
prefix and imposes no strategy, posterior, or native-memory restriction. -/
def SourcePrefixCheckpoint (setup : Setup (Player := Player) (L := L)) :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) → ContextRefs (graph setup).layout Γ →
    Registry Γ → Revelations Γ →
    (∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event)) →
    Nat → Nat → ProtocolState program → (graph setup).Config → Prop
  | _, _, program, refs, registry, revelations, _, offset, 0, state, native =>
      ∃ source, state = ProtocolState.entry program source ∧ source.registry = registry ∧
        @source.revelations = @revelations ∧ SourceCheckpoint setup source refs offset native
  | _, _, .ret _, _, _, _, _, _, _ + 1, _, _ => False
  | _, _, .sample (payload := payload) _ _ _ next,
      refs, registry, revelations, outputs, offset, count + 1, state, native =>
      let headRef : EventGraph.FieldRef (graph setup).layout (.publicData payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      match state with
      | .inl _ => False
      | .inr rest => SourcePrefixCheckpoint setup next (refs.cons headRef) registry.weaken
          revelations.weaken (fun tail => outputs tail.succ) (offset + 1) count rest native
  | _, _, .commit (payload := payload) name owner _ guard next,
      refs, registry, revelations, outputs, offset, count + 1, state, native =>
      let headRef : EventGraph.FieldRef (graph setup).layout (.binding owner payload) := by
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
      let headRef : EventGraph.FieldRef (graph setup).layout (.publication payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      match state with
      | .inl _ => False
      | .inr rest => SourcePrefixCheckpoint setup next (refs.cons headRef) registry.weaken
          (revelations.reveal selected) (fun tail => outputs tail.succ)
          (offset + 1) count rest native

/-- All related full-syntax prefixes decode to their actual original source
protocol state. Missing-field and excessive-prefix fallbacks are unreachable
on these concrete semantic checkpoints. -/
theorem SourcePrefixCheckpoint.decode {setup : Setup (Player := Player) (L := L)} :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graph setup).layout Γ) (registry : Registry Γ)
      (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout
        (outputLayout program event))
      (offset count : Nat) (state : ProtocolState program) (native : (graph setup).Config),
      SourcePrefixCheckpoint setup program refs registry revelations outputs
        offset count state native →
      decodeSourcePrefix? program refs registry revelations outputs count native.store
        (decodeHistory setup.program (native.history.map
          (setup.eventGraph.fromModeCompletion .sequential))) = some state := by
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

/-- The same actual native checkpoint cannot decode to two source states.
This does not identify native histories with source histories. -/
theorem SourcePrefixCheckpoint.state_unique {setup : Setup (Player := Player) (L := L)}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (refs : ContextRefs (graph setup).layout Γ) (registry : Registry Γ)
    (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event))
    (offset count : Nat) (left right : ProtocolState program) (native : (graph setup).Config)
    (first : SourcePrefixCheckpoint setup program refs registry revelations outputs
      offset count left native)
    (second : SourcePrefixCheckpoint setup program refs registry revelations outputs
      offset count right native) : left = right := by
  have firstRead := SourcePrefixCheckpoint.decode program refs registry revelations outputs
    offset count left native first
  have secondRead := SourcePrefixCheckpoint.decode program refs registry revelations outputs
    offset count right native second
  exact Option.some.inj (firstRead.symm.trans secondRead)

end Vegas.SourceProgram.RevealService
