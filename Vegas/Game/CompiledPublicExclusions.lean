/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompiledRevealReadback
import Vegas.Source.CommitRecoveryPublicControl

/-! # Public source exclusion updates from original native publications

The source successor reads the same immutable public field as the native
failure footprint, at the actual structural suffix of the compiled program.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

open scoped Classical in
/-- Reading an actual native publication identifies the source successor's
exclusion update, including through its original whole-program suffix. -/
theorem compiled_reveal_public_exclusions
    {graph : Vegas.EventGraph Player L}
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (who : Player) (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    {lift : ProtocolState (.reveal published owner name fresh selected unresolved next) →
      ProtocolState whole}
    (origin : ProtocolSuffix whole
      (.reveal published owner name fresh selected unresolved next) lift)
    (native : EventGraphRuntime.State graph) (event : graph.EventId)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (before : SourceProgram.Config Player L Γ)
    (after : SourceProgram.Config Player L ((published, .publication payload) :: Γ))
    (refs : ContextRefs graph.layout Γ)
    (agree : (refs.cons (name := published) (cell := .publication payload)
      ⟨.inr event, outputEq⟩).Agrees after.state native.config.store)
    (excluded : Finset Player) :
    ProtocolView.publicSuccessorExclusions who whole
        (ProtocolView.publicOnly who whole
          (ProtocolState.observe who whole (lift (Sum.inl before))))
        (ProtocolView.publicOnly who whole (ProtocolState.observe who whole
          (lift (Sum.inr (ProtocolState.entry next after))))) excluded =
      if native.PublicFailure event then insert owner excluded else excluded := by
  classical
  rw [origin.publicSuccessorExclusions_lift,
    ProtocolView.publicSuccessorExclusions_reveal]
  have stored : (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
      native.config.store = some (after.state.get .here) := agree .here
  have failureRead := publication_failure_iff_read native event binding checks outputEq codeEq
    (after.state.get .here) stored
  by_cases failed : native.PublicFailure event
  · rw [ite_eq_left failed, failureRead.mp failed]
  · rw [ite_eq_right failed]
    cases result : after.state.get .here with
    | failure => exact (failed (failureRead.mpr result)).elim
    | success value => rfl

end Vegas
