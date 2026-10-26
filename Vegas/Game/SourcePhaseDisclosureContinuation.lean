/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourcePhaseDisclosure
import Vegas.Game.SourcePhaseSurvivingContinuation

/-! # Ineffective opening suppression preserves original source continuations

The compiled client suppresses a source intention whose publication would fail.
Both source successors exclude the actor, preserve every other player's full
information, and have the same semantic state. The entire subsequent common
observation law therefore agrees under every original source profile.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Suppressing an ineffective disclosure preserves the complete typed readout
and declared cash law of every subsequent source continuation. The original
intentions and excluded owner's private recall need not agree. -/
theorem sourcePhase_ineffective_disclosure_continuation
    (setup : Setup (Player := Player) (L := L))
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (suffix : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (lift : ProtocolState (.reveal published owner name fresh selected unresolved suffix) →
      ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program
      (.reveal published owner name fresh selected unresolved suffix) lift)
    (config : Config Player L Γ) (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (point : current.point = lift (.inl config)) (active : owner ∉ current.excluded)
    (disclose : Bool) (failed : disclosureResult published selected config disclose = .failure)
    (firstJoint secondJoint : Player → Option (CommitRecoveryMove Player L))
    (firstLegal : setup.commitRecoveryProtocol.Legal (some current) firstJoint)
    (secondLegal : setup.commitRecoveryProtocol.Legal (some current) secondJoint)
    (original : OwnAction.disclosure ((firstJoint owner).map (·.action)) = disclose)
    (effective : OwnAction.disclosure ((secondJoint owner).map (·.action)) =
      effectiveDisclosure published selected config disclose)
    (firstNext secondNext : CommitRecoveryState setup.program)
    (firstReached : some firstNext ∈ (setup.commitRecoveryProtocol.step (some current)
      ⟨firstJoint, firstLegal⟩).support)
    (secondReached : some secondNext ∈ (setup.commitRecoveryProtocol.step (some current)
      ⟨secondJoint, secondLegal⟩).support)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (fuel : Nat) :
    (setup.commitRecoveryModel.runBehavioralFrom profile fuel
        ⟨some firstNext, trace.extend firstJoint firstLegal firstReached⟩).map
          setup.sourcePhaseObservation =
      (setup.commitRecoveryModel.runBehavioralFrom profile fuel
        ⟨some secondNext, trace.extend secondJoint secondLegal secondReached⟩).map
          setup.sourcePhaseObservation := by
  obtain ⟨_excluded, information, semantic, excludedOwner⟩ :=
    sourcePhase_effective_disclosure_foreign_information setup fresh selected unresolved suffix
      lift origin config current trace point active disclose firstJoint secondJoint
      firstLegal secondLegal original effective (some firstNext) (some secondNext)
      firstReached secondReached
  apply setup.sourcePhaseObservation_surviving_continuation profile fuel firstNext secondNext
    _ _ (Option.some.inj semantic)
  intro who survives
  apply information who
  intro same
  subst who
  exact survives (excludedOwner failed)

end Vegas
