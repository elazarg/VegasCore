/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryLift
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Label agreement only at actual withheld reveal actions -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Labels have no effect at absent choices, bindings or truthful semantic
reveals. A legal joint already restricts its present actors to the live menu. -/
theorem proposalRecoveryLiftJoint_eq_of_withheld_labels
    (left right : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (event : setup.commitRecoveryProtocol.StepEvent)
    (same : ∀ who (move : CommitRecoveryMove Player L), event.joint who = some move →
      (∃ owner name, move.action = .reveal owner name false) →
        left event who = right event who) :
    setup.proposalRecoveryLiftJoint left event = setup.proposalRecoveryLiftJoint right event := by
  funext who
  cases selected : event.joint who with
  | none => simp only [proposalRecoveryLiftJoint, selected, Option.map_none]
  | some move =>
      simp only [proposalRecoveryLiftJoint, selected, Option.map_some]
      apply congrArg some
      rcases move with ⟨action, missing⟩
      cases action with
      | commit => rfl
      | reveal owner name disclose =>
          cases disclose with
          | true => rfl
          | false =>
              have flags := same who _ selected ⟨owner, name, rfl⟩
              rw [flags]

/-- Equality on the actual withheld-reveal events of this trace preserves
the entire labeled lift, even when labels differ on all other events. -/
theorem proposalRecoveryLiftTrace_eq_of_withheld_labels
    (left right : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state)
    (same : ∀ {before after : setup.commitRecoveryProtocol.State}
      (prior : setup.commitRecoveryProtocol.Trace before)
      (joint : Player → Option (CommitRecoveryMove Player L))
      (legal : setup.commitRecoveryProtocol.Legal before joint)
      (supported : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal supported) trace →
      ∀ who (move : CommitRecoveryMove Player L), joint who = some move →
        (∃ owner name, move.action = .reveal owner name false) →
          left ⟨before, joint, legal, after, supported⟩ who =
            right ⟨before, joint, legal, after, supported⟩ who) :
    setup.proposalRecoveryLiftTrace left trace = setup.proposalRecoveryLiftTrace right trace := by
  induction trace with
  | start => rfl
  | @extend before after prior joint legal supported ih =>
      have earlier := ih (fun earlierTrace selected allowed reached retained =>
        same earlierTrace selected allowed reached (retained.extend joint legal supported))
      have current := setup.proposalRecoveryLiftJoint_eq_of_withheld_labels left right
        ⟨before, joint, legal, after, supported⟩
        (same prior joint legal supported .refl)
      simp only [proposalRecoveryLiftTrace, earlier]
      congr 1

end Vegas.SourceProgram.Setup
