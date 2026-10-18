/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphEvaluation
import Vegas.Pending.EventApplication
import Vegas.Source.ProposalRecoveryObservation
import Vegas.Source.ProtocolSuffix
import Vegas.Source.CommitRecoveryNoMissInformation

/-! # Native binding readback at source-ranked proposal steps -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def bindingProposalValue? {payload : L.Ty} :
    PublicationResult (L.Val payload) → Option (Sigma L.Val)
  | .failure => none
  | .success value => some ⟨payload, value⟩

/-- A publication's prestate proposal is read from its typed binding, not its
publication result. Guard rejection therefore does not erase the plaintext. -/
def nativeStoredProposal? {graph : Vegas.EventGraph Player L}
    (native : EventGraphRuntime.State graph) (rank : Nat) : Option (Sigma L.Val) :=
  if bounded : rank < graph.order.eventCount then
    match nodeView graph ⟨rank, bounded⟩ with
    | .resolve _ payload binding _ _ _ =>
        match binding.get? native.config.store with
        | some (.success value) => some ⟨payload, value⟩
        | _ => none
    | _ => none
  else none

omit [DecidableEq Player] in
theorem nativeStoredProposal?_resolve {graph : Vegas.EventGraph Player L}
    (native : EventGraphRuntime.State graph) (event : graph.EventId)
    {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks) (result : PublicationResult (L.Val payload))
    (stored : binding.get? native.config.store = some result) :
    nativeStoredProposal? native event.val =
      bindingProposalValue? result := by
  have viewed := nodeView_eq_resolve outputEq codeEq
  simp only [nativeStoredProposal?, event.isLt, dite_true, viewed, stored]
  cases result <;> rfl

/-- Source control selects the current absolute rank and disclosure bit;
the actual native store supplies the proposal value. -/
def nativeRecoveryProposal? {graph : Vegas.EventGraph Player L}
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (native : EventGraphRuntime.State graph) (offset : Nat)
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (joint : Player → Option (ProposalRecoveryMove Player L)) : Option (Sigma L.Val) :=
  if ProtocolState.atCommit program point then none else
    (ProtocolState.actor program point).bind fun owner =>
      if ((joint owner).map (·.discloses)).getD false then
        nativeStoredProposal? native
          (offset + (instructionCount program - ProtocolState.remaining program point))
      else none

/-- The complete proposal-value readback retained by a reconstructed source
prestate. It says nothing about physical receipt acceptance. -/
def NativeProposalReadback {graph : Vegas.EventGraph Player L}
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (native : EventGraphRuntime.State graph) (offset : Nat)
    (program : SourceProgram Player L Γ O) (point : ProtocolState program) : Prop :=
  ∀ joint, (ProtocolState.recoveryProposal program point joint).map Prod.snd =
    nativeRecoveryProposal? native offset program point joint

namespace SourceProgram.ProtocolSuffix

/-- Following a genuine syntax suffix only shifts the rank component of a
proposal; its typed prestate value remains literal. -/
theorem recoveryProposal_value_lift
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (point : ProtocolState program)
    (joint : Player → Option (ProposalRecoveryMove Player L)) :
    (ProtocolState.recoveryProposal whole (lift point) joint).map Prod.snd =
      (ProtocolState.recoveryProposal program point joint).map Prod.snd := by
  induction origin with
  | initial => rfl
  | sampleTail fresh law next previous ih =>
      simpa only [ProtocolState.recoveryProposal, Sum.elim_inr, Option.map_map,
        Function.comp_def] using
        ih (.inr point)
  | commitTail fresh guard next previous ih =>
      simpa only [ProtocolState.recoveryProposal, Sum.elim_inr, Option.map_map,
        Function.comp_def] using
        ih (.inr point)
  | revealTail fresh selected unresolved next previous ih =>
      simpa only [ProtocolState.recoveryProposal, Sum.elim_inr, Option.map_map,
        Function.comp_def] using
        ih (.inr point)

end SourceProgram.ProtocolSuffix

/-- Source suffix transport retains the same absolute native read. The
offset equation is the compiler's ordinary source-rank accounting. -/
theorem NativeProposalReadback.lift {graph : Vegas.EventGraph Player L}
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {embed : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program embed)
    (native : EventGraphRuntime.State graph) (outerOffset offset : Nat)
    (aligned : outerOffset + instructionCount whole = offset + instructionCount program)
    (point : ProtocolState program)
    (readback : NativeProposalReadback native offset program point) :
    NativeProposalReadback native outerOffset whole (embed point) := by
  have ranked : outerOffset + (instructionCount whole -
      ProtocolState.remaining whole (embed point)) =
        offset + (instructionCount program - ProtocolState.remaining program point) := by
    have same := origin.remaining_lift point
    have bounded := ProtocolState.remaining_le_instructionCount program point
    have wholeBounded := ProtocolState.remaining_le_instructionCount whole (embed point)
    omega
  intro joint
  rw [origin.recoveryProposal_value_lift, readback]
  simp only [nativeRecoveryProposal?, origin.atCommit_lift, origin.actor_lift, ranked]

/-- A compiler replay prestate agreeing with the native store retains exact
proposal values for all possible disclosure labels. -/
theorem nativeProposalReadback_reveal {graph : Vegas.EventGraph Player L}
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (source : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (native : EventGraphRuntime.State graph) (offset : Nat) (event : graph.EventId)
    (ranked : event.val = offset) (refs : ContextRefs graph.layout Γ)
    (config : Config Player L Γ) (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload (refs.get source) checks)
    (agree : refs.Agrees config.state native.config.store) :
    NativeProposalReadback native offset
      (.reveal published owner name fresh source unresolved next) (.inl config) := by
  intro joint
  have nativeRead := nativeStoredProposal?_resolve native event (refs.get source) checks outputEq
    codeEq (config.state.get source) (agree source)
  simp only [ProtocolState.recoveryProposal,
    nativeRecoveryProposal?, ProtocolState.atCommit, ProtocolState.actor,
    ProtocolState.remaining, instructionCount, Sum.elim_inl, Nat.sub_self, Nat.add_zero,
    Bool.false_eq_true, ite_false, Option.bind_some, ← ranked, nativeRead]
  split
  · cases config.state.get source <;>
      simp only [bindingProposalValue?, Option.map_none, Option.map_some]
  · rfl

end Vegas
