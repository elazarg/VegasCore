/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryNonmissingPosition
import Vegas.Source.CommitPrefixInformationLaw
import Vegas.Source.SetupProtocolBehavioral

/-! # Typed source kernels of chronological nonmissing recovery choices -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Removing only the physical omission flag gives a legal original
forfeiture action at the same complete source view, including unrealized views. -/
def commitRecoveryUnderlyingChoice (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.ProtocolView who)
    (choice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryClearInformation wellFormed who view)) :
    (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Choice who view := by
  refine ⟨CommitRecoveryMove.underlying choice.1, ?_⟩
  have legal := choice.2
  cases view with
  | none =>
      cases raw : choice.1 with
      | none => rfl
      | some move =>
          rw [raw] at legal
          have active := legal.1
          unfold commitRecoveryActive at active
          rw [setup.commitRecoveryClearInformation_current] at active
          exact active.elim
  | some view =>
      cases raw : choice.1 with
      | none =>
          rw [raw] at legal
          change ProtocolView.actor who setup.program view ≠ some who
          intro actor
          apply legal
          unfold commitRecoveryActive
          rw [setup.commitRecoveryClearInformation_current,
            setup.commitRecoveryClearInformation_excluded]
          exact ⟨actor, Finset.notMem_empty _⟩
      | some move =>
          rw [raw] at legal
          refine ⟨?_, ?_⟩
          · have active := legal.1
            unfold commitRecoveryActive at active
            rw [setup.commitRecoveryClearInformation_current] at active
            exact active.1
          · have offered := legal.2
            rw [setup.commitRecoveryClearInformation_current] at offered
            exact offered.1

/-- The original typed source policy is obtained from the exact conditional
auxiliary move law. Accepted unusable results are retained as typed failures. -/
def commitRecoveryNonmissingSourcePolicy (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (who : Player) :
    (setup.informationModel (CommitmentInterface.forfeiture setup.program)).BehavioralPolicy who :=
  fun view => (setup.commitRecoveryNonmissingProfile profile who
    (setup.commitRecoveryClearInformation wellFormed who view)).map
      (setup.commitRecoveryUnderlyingChoice wellFormed who view)

/-- Use the owning protocol-to-structural policy equivalence, rather than
introducing another sampler for source-ranked hidden commitment cells. -/
def commitRecoveryNonmissingSourceProfile (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    BehavioralProfile setup.program := fun who =>
  ((setup.behavioralPolicyEquiv (CommitmentInterface.forfeiture setup.program) who).symm
    (setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who)).1

theorem commitRecovery_nonmissingSource_raw (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (who : Player)
    (view : SourceProgram.ProtocolView who setup.program) :
    (setup.commitRecoveryNonmissingSourceProfile wellFormed profile who).protocolAction
      setup.program view =
    (setup.commitRecoveryNonmissingProfile profile who
      (setup.commitRecoveryClearInformation wellFormed who (some view))).map
        (fun choice => CommitRecoveryMove.underlying choice.1) := by
  have bridge := BehavioralPolicy.protocolAction_fromProtocol setup.program
    (CommitmentInterface.forfeiture setup.program)
    (fun view => setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who (some view))
    view
  rw [commitRecoveryNonmissingSourcePolicy, PMF.map_comp] at bridge
  exact bridge

/-- The existing typed commitment-prefix law composes the conditional source
kernels at successive updated configurations, including repeated owners.
This is the complete typed continuation factorization of that same profile. -/
theorem commitRecovery_nonmissing_prefix_continuation (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    {Δ : SourceCtx Player L} {P : Finset VarId}
    (block : CommitPrefix setup.context setup.obligations Δ P)
    (suffix : SourceProgram Player L Δ P) (program : block.prepend suffix = setup.program)
    (entry : Config Player L setup.context) :
    let typed := cast (congrArg BehavioralProfile program.symm)
      (setup.commitRecoveryNonmissingSourceProfile wellFormed profile)
    (block.prefixLaw suffix typed entry).bind (fun final =>
      ProtocolState.continuationLaw (block.prepend suffix) typed
        (block.liftPoint suffix (ProtocolState.entry suffix final))) =
      runFrom (block.prepend suffix) typed entry := by
  exact block.prefixLaw_continuation suffix _ entry

end Vegas.SourceProgram.Setup
