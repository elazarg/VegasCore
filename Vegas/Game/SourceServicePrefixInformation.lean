/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefix
import Vegas.Game.RevealServiceInformation

/-! # Full-source views on actual native information fibers

The static prefix locates the existing source protocol observation. The native
player input already determines its masked typed source cells and decoded own
completion history. Equal native inputs therefore give equal source views at
related checkpoints, including samples, dynamic bindings and guarded reveals.
No equality of additional native observations is inferred in the other direction.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Actual native information refines the source observation at its recovered
position. Private aliases may still distinguish native inputs within that
source fiber; their conditional likelihood is a separate operational proof. -/
theorem SourcePrefixCheckpoint.source_view_eq_of_observe_eq
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (who : Player) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graph setup).layout Γ) (registry : Registry Γ)
      (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout
        (outputLayout program event))
      (offset count : Nat) (left right : ProtocolState program)
      (nativeLeft nativeRight : (application setup leaks).Execution),
      SourcePrefixCheckpoint setup program refs registry revelations outputs offset count left
        nativeLeft.application.config →
      SourcePrefixCheckpoint setup program refs registry revelations outputs offset count right
        nativeRight.application.config →
      nativeLeft.observe (application setup leaks) who =
        nativeRight.observe (application setup leaks) who →
      ProtocolState.observe who program left = ProtocolState.observe who program right := by
  intro Γ openNames program refs registry revelations outputs offset count
  induction count generalizing Γ openNames program refs registry revelations outputs offset with
  | zero =>
      intro left right nativeLeft nativeRight first second same
      cases program <;>
        obtain ⟨leftSource, rfl, _leftRegistry, _leftRevelations, leftCheckpoint⟩ := first <;>
        obtain ⟨rightSource, rfl, _rightRegistry, _rightRevelations, rightCheckpoint⟩ := second
      all_goals
        have equal := RevealService.source_view_eq_of_observe_eq setup leaks refs who _ _
          nativeLeft nativeRight leftCheckpoint.agrees rightCheckpoint.agrees
          leftCheckpoint.history rightCheckpoint.history same
        simpa only [ProtocolState.entry, ProtocolState.observe, Sum.elim_inl,
          Sum.inl.injEq] using equal
  | succ count ih =>
      intro left right nativeLeft nativeRight first second same
      cases program with
      | ret payoffs => exact first.elim
      | sample name fresh law next =>
          cases left with
          | inl source => exact first.elim
          | inr left =>
              cases right with
              | inl source => exact second.elim
              | inr right =>
                  exact congrArg Sum.inr
                    (ih next _ _ _ _ (offset + 1) left right nativeLeft nativeRight
                      first second same)
      | commit name owner fresh guard next =>
          cases left with
          | inl source => exact first.elim
          | inr left =>
              cases right with
              | inl source => exact second.elim
              | inr right =>
                  exact congrArg Sum.inr
                    (ih next _ _ _ _ (offset + 1) left right nativeLeft nativeRight
                      first second same)
      | reveal published owner name fresh selected unresolved next =>
          cases left with
          | inl source => exact first.elim
          | inr left =>
              cases right with
              | inl source => exact second.elim
              | inr right =>
                  exact congrArg Sum.inr
                    (ih next _ _ _ _ (offset + 1) left right nativeLeft nativeRight
                      first second same)

end Vegas.SourceProgram.RevealService
