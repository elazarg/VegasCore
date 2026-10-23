/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceCheckpoint
import Vegas.Compile.EventGraphPolicyLaw
import Vegas.Pending.ReactiveInitialValues
import Vegas.Compile.EventGraphLaw

/-! # Reading actual source positions at service checkpoints

The decoder follows the static source prefix and reads the existing typed
store and source-action history. Its result is the existing source protocol
state, including private cells and each player's actions. It performs no source
or runtime transition and does not identify native response histories.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Read the source position after `count` reveals. The registry is empty in
this source class; publication bookkeeping is determined by the static prefix.
A missing typed field, a non-reveal instruction, or an excessive count fails. -/
def decodePrefix? {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) → ContextRefs layout Γ →
    Revelations Γ → (∀ event, EventGraph.FieldRef layout (outputLayout program event)) →
    Nat → EventGraph.Store layout → History Player L → Option (ProtocolState program)
  | _, _, program, refs, revelations, _, 0, store, history =>
      (decodeState? refs store).map fun state =>
        ProtocolState.entry program ⟨state, [], revelations, history⟩
  | _, _, .ret _, _, _, _, _ + 1, _, _ => none
  | _, _, .sample _ _ _ _, _, _, _, _ + 1, _, _ => none
  | _, _, .commit _ _ _ _ _, _, _, _, _ + 1, _, _ => none
  | _, _, .reveal (payload := payload) _ _ _ _ selected _ next,
      refs, revelations, outputs, count + 1, store, history =>
      let headRef : EventGraph.FieldRef layout (.publication payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      (decodePrefix? next (refs.cons headRef) (revelations.reveal selected)
        (fun tail => outputs tail.succ) count store history).map Sum.inr

/-- At the current source boundary, typed agreement and the decoded actual
action history recover the complete source configuration. -/
theorem decodePrefix?_zero_of_agrees {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (source : Config Player L Γ) (emptyRegistry : source.registry = [])
    (store : EventGraph.Store layout) (agrees : refs.Agrees source.state store) :
    decodePrefix? program refs source.revelations outputs 0 store source.history =
      some (ProtocolState.entry program source) := by
  rw [decodePrefix?, decodeState?_eq_some refs source.state store agrees]
  cases source
  cases emptyRegistry
  rfl

/-- One extra static reveal shifts the source position and its typed references.
No source action is inferred from private runtime memory. -/
theorem decodePrefix?_reveal
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (refs : ContextRefs layout Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout
      (outputLayout (.reveal published owner name fresh selected unresolved next) event))
    (count : Nat) (store : EventGraph.Store layout) (history : History Player L) :
    decodePrefix? (.reveal published owner name fresh selected unresolved next)
        refs revelations outputs (count + 1) store history =
      (decodePrefix? next (refs.cons (outputs ⟨0, by simp [eventCount]⟩))
        (revelations.reveal selected) (fun tail => outputs tail.succ) count store history).map
          Sum.inr := rfl

/-- Checkpoints along an existing source protocol position. The recursion only
locates the residual source configuration in `ProtocolState`; all operational
facts remain the fields of `Checkpoint`. It imposes no policy marginal. -/
def PrefixCheckpoint (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (initial : State L setup.context) :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    ContextRefs (graph setup).layout Γ → Revelations Γ →
    (∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event)) →
    Nat → Nat → ProtocolState program → (application setup leaks).Execution → Prop
  | _, _, program, refs, revelations, _, offset, 0, state, execution =>
      ∃ source, state = ProtocolState.entry program source ∧
        @source.revelations = @revelations ∧
        Checkpoint setup leaks initial source refs offset execution
  | _, _, .ret _, _, _, _, _, _ + 1, _, _ => False
  | _, _, .sample _ _ _ _, _, _, _, _, _ + 1, _, _ => False
  | _, _, .commit _ _ _ _ _, _, _, _, _, _ + 1, _, _ => False
  | _, _, .reveal (payload := payload) _ _ _ _ selected _ next,
      refs, revelations, outputs, offset, count + 1, state, execution =>
      let headRef : EventGraph.FieldRef (graph setup).layout (.publication payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      match state with
      | .inl _ => False
      | .inr rest => PrefixCheckpoint setup leaks initial next (refs.cons headRef)
          (revelations.reveal selected) (fun tail => outputs tail.succ) (offset + 1)
          count rest execution

/-- Every operationally related prefix decodes to its complete existing source
state. In particular the partial decoder never fails on these prefixes. -/
theorem PrefixCheckpoint.decode
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graph setup).layout Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout
        (outputLayout program event))
      (offset count : Nat) (state : ProtocolState program)
      (execution : (application setup leaks).Execution),
      PrefixCheckpoint setup leaks initial program refs revelations outputs
        offset count state execution →
      decodePrefix? program refs revelations outputs count execution.application.config.store
        (decodeHistory setup.program (execution.application.config.history.map
          (setup.eventGraph.fromModeCompletion .sequential))) = some state := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro refs revelations outputs offset count state execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [checkpoint.history, ← revelationsEq]
          exact decodePrefix?_zero_of_agrees _ refs outputs state checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count => exact related.elim
  | sample name fresh law next ih =>
      intro refs revelations outputs offset count state execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [checkpoint.history, ← revelationsEq]
          exact decodePrefix?_zero_of_agrees _ refs outputs source checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count => exact related.elim
  | commit name owner fresh guard next ih =>
      intro refs revelations outputs offset count state execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [checkpoint.history, ← revelationsEq]
          exact decodePrefix?_zero_of_agrees _ refs outputs source checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count => exact related.elim
  | reveal published owner name fresh selected unresolved next ih =>
      intro refs revelations outputs offset count state execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [checkpoint.history, ← revelationsEq]
          exact decodePrefix?_zero_of_agrees _ refs outputs source checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count =>
          cases state with
          | inl source => exact related.elim
          | inr rest =>
              rw [decodePrefix?_reveal]
              rw [ih _ _ _ (offset + 1) count rest execution related]
              rfl

def PublicPrefixCheckpoint (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (initial : State L setup.context) :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    ContextRefs (graph setup).layout Γ → Revelations Γ →
    (∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event)) →
    Nat → Nat → ProtocolState program → (application setup leaks).Execution → Prop
  | _, _, program, refs, revelations, _, offset, 0, state, execution =>
      ∃ source, state = ProtocolState.entry program source ∧
        @source.revelations = @revelations ∧
        PublicCheckpoint setup leaks initial source refs offset execution
  | _, _, .ret _, _, _, _, _, _ + 1, _, _ => False
  | _, _, .sample _ _ _ _, _, _, _, _, _ + 1, _, _ => False
  | _, _, .commit _ _ _ _ _, _, _, _, _, _ + 1, _, _ => False
  | _, _, .reveal (payload := payload) _ _ _ _ selected _ next,
      refs, revelations, outputs, offset, count + 1, state, execution =>
      let headRef : EventGraph.FieldRef (graph setup).layout (.publication payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      match state with
      | .inl _ => False
      | .inr rest => PublicPrefixCheckpoint setup leaks initial next (refs.cons headRef)
          (revelations.reveal selected) (fun tail => outputs tail.succ) (offset + 1)
          count rest execution

theorem PublicPrefixCheckpoint.checkpoint
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graph setup).layout Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event))
      (offset count : Nat) (state : ProtocolState program)
      (execution : (application setup leaks).Execution),
      PublicPrefixCheckpoint setup leaks initial program refs revelations outputs
        offset count state execution →
      ∃ context : SourceCtx Player L, ∃ source : Config Player L context,
        ∃ sourceRefs, PublicCheckpoint setup leaks initial source sourceRefs (offset + count)
          execution := by
  intro Γ openNames program refs revelations outputs offset count
  induction count generalizing Γ openNames program refs revelations outputs offset with
  | zero =>
      intro state execution related
      cases program <;> obtain ⟨source, _, _, checkpoint⟩ := related <;>
        exact ⟨Γ, source, refs, checkpoint⟩
  | succ count ih =>
      intro state execution related
      cases program with
      | ret => exact related.elim
      | sample => exact related.elim
      | commit => exact related.elim
      | reveal published owner name fresh selected unresolved next =>
          cases state with
          | inl source => exact related.elim
          | inr state =>
              simpa only [Nat.add_assoc, Nat.add_comm 1 count] using
                ih next _ _ _ (offset + 1) state execution related

/-- The event at a related prefix's rank is ready. -/
theorem PublicPrefixCheckpoint.ready
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {program : SourceProgram Player L Γ openNames} {refs : ContextRefs (graph setup).layout Γ}
    {revelations : Revelations Γ}
    {outputs : ∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event)}
    {offset count : Nat} {state : ProtocolState program}
    {execution : (application setup leaks).Execution}
    (related : PublicPrefixCheckpoint setup leaks initial program refs revelations outputs
      offset count state execution)
    (event : (graph setup).EventId) (rank : event.val = offset + count) :
    execution.application.config.cut.Ready event := by
  obtain ⟨_, _, _, checkpoint⟩ := PublicPrefixCheckpoint.checkpoint program refs revelations
    outputs offset count state execution related
  have active : offset + count < (graph setup).order.eventCount := rank ▸ event.isLt
  have chosen : (⟨offset + count, active⟩ : (graph setup).EventId) = event := Fin.ext rank.symm
  rw [← chosen]
  exact checkpoint.ordered.ready active

/-- Every operationally related prefix decodes to its complete existing source
state. In particular the partial decoder never fails on these prefixes. -/
theorem PublicPrefixCheckpoint.decode
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graph setup).layout Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout
        (outputLayout program event))
      (offset count : Nat) (state : ProtocolState program)
      (execution : (application setup leaks).Execution),
      PublicPrefixCheckpoint setup leaks initial program refs revelations outputs
        offset count state execution →
      decodePrefix? program refs revelations outputs count execution.application.config.store
        (decodeHistory setup.program (execution.application.config.history.map
          (setup.eventGraph.fromModeCompletion .sequential))) = some state := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro refs revelations outputs offset count state execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [checkpoint.history, ← revelationsEq]
          exact decodePrefix?_zero_of_agrees _ refs outputs state checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count => exact related.elim
  | sample name fresh law next ih =>
      intro refs revelations outputs offset count state execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [checkpoint.history, ← revelationsEq]
          exact decodePrefix?_zero_of_agrees _ refs outputs source checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count => exact related.elim
  | commit name owner fresh guard next ih =>
      intro refs revelations outputs offset count state execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [checkpoint.history, ← revelationsEq]
          exact decodePrefix?_zero_of_agrees _ refs outputs source checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count => exact related.elim
  | reveal published owner name fresh selected unresolved next ih =>
      intro refs revelations outputs offset count state execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [checkpoint.history, ← revelationsEq]
          exact decodePrefix?_zero_of_agrees _ refs outputs source checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count =>
          cases state with
          | inl source => exact related.elim
          | inr rest =>
              rw [decodePrefix?_reveal]
              rw [ih _ _ _ (offset + 1) count rest execution related]
              rfl

/-- Removing private recall restrictions preserves all public source-prefix facts. -/
theorem PrefixCheckpoint.toPublic
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graph setup).layout Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event))
      (offset count : Nat) (state : ProtocolState program)
      (execution : (application setup leaks).Execution),
      PrefixCheckpoint setup leaks initial program refs revelations outputs
        offset count state execution →
      PublicPrefixCheckpoint setup leaks initial program refs revelations outputs
        offset count state execution := by
  intro Γ openNames program refs revelations outputs offset count
  induction count generalizing Γ openNames program offset with
  | zero =>
      intro state execution related
      cases program <;>
        obtain ⟨source, same, revealed, checkpoint⟩ := related <;>
        exact ⟨source, same, revealed, checkpoint.toPublicCheckpoint⟩
  | succ count ih =>
      intro state execution related
      cases program with
      | ret payoffs => exact related.elim
      | sample name fresh law next => exact related.elim
      | commit name owner fresh guard next => exact related.elim
      | reveal published owner name fresh selected unresolved next =>
          cases state with
          | inl source => exact related.elim
          | inr rest => exact ih next _ _ _ (offset + 1) rest execution related

/-- A decoded prefix has exactly the source actor at the corresponding static
event rank. This fact is independent of private values and source policies. -/
theorem PublicPrefixCheckpoint.actor
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} (who : Player) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graph setup).layout Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout
        (outputLayout program event))
      (offset count : Nat) (state : ProtocolState program)
      (execution : (application setup leaks).Execution),
      PublicPrefixCheckpoint setup leaks initial program refs revelations outputs
        offset count state execution →
      (inside : count < eventCount program) →
      ProtocolView.actor who program (ProtocolState.observe who program state) =
        eventOwner? program ⟨count, inside⟩ := by
  intro Γ openNames program refs revelations outputs offset count
  induction count generalizing Γ openNames program refs revelations outputs offset with
  | zero =>
      intro state execution related inside
      cases program with
      | ret payoffs => simp only [eventCount] at inside; omega
      | sample name fresh law next =>
          obtain ⟨source, rfl, _, _⟩ := related
          rfl
      | commit name owner fresh guard next =>
          obtain ⟨source, rfl, _, _⟩ := related
          rfl
      | reveal published owner name fresh selected unresolved next =>
          obtain ⟨source, rfl, _, _⟩ := related
          rfl
  | succ count ih =>
      intro state execution related inside
      cases program with
      | ret payoffs => exact related.elim
      | sample name fresh law next => exact related.elim
      | commit name owner fresh guard next => exact related.elim
      | reveal published owner name fresh selected unresolved next =>
          cases state with
          | inl source => exact related.elim
          | inr rest =>
              have within : count < eventCount next := by simpa [eventCount] using inside
              exact ih next _ _ _ (offset + 1) rest execution related within

end Vegas
