/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryClearBayes
import Vegas.Game.CommitRecoveryReferencePosition

/-! # Conditional source prefixes retain the next physical omission draw -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Record whether the sampled prefix is clear, together with the observer's
complete current source view. The false branch retains omitted and reset paths. -/
def commitRecoveryPrefixObservation (who : Player)
    (history : setup.commitRecoveryProtocol.History) : Bool × setup.ProtocolView who := by
  classical
  exact (decide (setup.CommitRecoveryClear history.state),
    setup.commitRecoveryPrivate who history.state)

/-- Reconstruct the original auxiliary source prefix distribution, including
all earlier omission flags, by sampling its observation and latent history.
Repeated owners are sampled by the actual sequential behavioral runner. -/
theorem commitRecovery_prefix_reconstruction
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (start : setup.commitRecoveryProtocol.History) (fuel : Nat) (who : Player) :
    ((setup.commitRecoveryModel.runBehavioralFrom profile fuel start).map
      (setup.commitRecoveryPrefixObservation who)).bind
        (fiberPosterior (setup.commitRecoveryModel.runBehavioralFrom profile fuel start)
          (setup.commitRecoveryPrefixObservation who)) =
      setup.commitRecoveryModel.runBehavioralFrom profile fuel start :=
  fiberPosterior_reconstruct _ _

/-- Completing a latent source prefix and then running the remaining source
instructions preserves the complete original history law. Earlier omissions,
later omissions, accepted failed bindings and retries are all retained. -/
theorem commitRecovery_prefix_continuation
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (start : setup.commitRecoveryProtocol.History) (fuel remaining : Nat) (who : Player) :
    (((setup.commitRecoveryModel.runBehavioralFrom profile fuel start).map
      (setup.commitRecoveryPrefixObservation who)).bind
        (fiberPosterior (setup.commitRecoveryModel.runBehavioralFrom profile fuel start)
          (setup.commitRecoveryPrefixObservation who))).bind
            (setup.commitRecoveryModel.runBehavioralFrom profile remaining) =
      setup.commitRecoveryModel.runBehavioralFrom profile (fuel + remaining) start := by
  rw [setup.commitRecovery_prefix_reconstruction,
    setup.commitRecoveryModel.runBehavioralFrom_add]

/-- Only the sampled prefix is conditioned to be clear. The next owned
action is drawn in its entirety, including its still-unsampled omission bit. -/
theorem commitRecovery_prefix_next_raw_joint (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (start : setup.commitRecoveryProtocol.History) (fuel : Nat) (who : Player)
    (view : setup.ProtocolView who)
    (present : (true, view) ∈
      ((setup.commitRecoveryModel.runBehavioralFrom profile fuel start).map
        (setup.commitRecoveryPrefixObservation who)).support) :
    let posterior := fiberPosterior
      (setup.commitRecoveryModel.runBehavioralFrom profile fuel start)
      (setup.commitRecoveryPrefixObservation who) (true, view)
    bindPairLaw posterior (fun history =>
      (profile who (setup.commitRecoveryModel.infoOf who history.trace)).map Subtype.val) =
      bindPairLaw posterior (fun _ =>
        (profile who (setup.commitRecoveryClearInformation wellFormed who view)).map
          Subtype.val) := by
  classical
  intro posterior
  unfold bindPairLaw
  apply bind_congr_on_support
  intro history supported
  have same := (mem_support_fiberPosterior present supported).1
  have clear : setup.CommitRecoveryClear history.state := by
    exact of_decide_eq_true (congrArg Prod.fst same)
  have current : setup.commitRecoveryPrivate who history.state = view :=
    congrArg Prod.snd same
  have sameInfo := (setup.commitRecoveryClearInformation_observed wellFormed who
    history.trace clear).trans
      (congrArg (setup.commitRecoveryClearInformation wellFormed who) current)
  have raw := congrArg (fun info : setup.commitRecoveryModel.InfoState who =>
    (profile who info).map (fun choice => choice.1)) sameInfo
  exact congrArg (fun law => law.map (fun action => (history, action))) raw

/-- A genuine initialized clear history has positive conditional prefix mass
under a fully mixed auxiliary assessment. No source-site witness or latent
choice admission is supplied externally. -/
theorem commitRecovery_prefix_next_raw_at_trace (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (clear : setup.CommitRecoveryClear state)
    (who : Player) :
    let view := setup.commitRecoveryPrivate who state
    let posterior := fiberPosterior
      (setup.commitRecoveryModel.runBehavioral assessment.strategy trace.length)
      (setup.commitRecoveryPrefixObservation who) (true, view)
    bindPairLaw posterior (fun history =>
      (assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace)).map
        Subtype.val) =
      bindPairLaw posterior (fun _ =>
        (assessment.strategy who
          (setup.commitRecoveryClearInformation wellFormed who view)).map Subtype.val) := by
  classical
  apply setup.commitRecovery_prefix_next_raw_joint wellFormed assessment.strategy
    setup.commitRecoveryProtocol.initHistory trace.length who _
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨⟨state, trace⟩, mixed.history_supported trace, ?_⟩
  simp only [commitRecoveryPrefixObservation, clear, decide_true]

/-- Marginalizing the latent prefix leaves the complete next auxiliary move
law unchanged. In particular a future omission is not conditioned to be false. -/
theorem commitRecovery_prefix_next_raw_law (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (clear : setup.CommitRecoveryClear state)
    (who : Player) :
    (fiberPosterior
      (setup.commitRecoveryModel.runBehavioral assessment.strategy trace.length)
      (setup.commitRecoveryPrefixObservation who)
      (true, setup.commitRecoveryPrivate who state)).bind (fun history =>
        (assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace)).map
          Subtype.val) =
      (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (setup.commitRecoveryPrivate who state))).map Subtype.val := by
  have joint := congrArg (fun law : PMF
    (setup.commitRecoveryProtocol.History × Option (CommitRecoveryMove Player L)) =>
      law.map Prod.snd)
    (setup.commitRecovery_prefix_next_raw_at_trace wellFormed assessment mixed trace clear who)
  simpa only [bindPairLaw_map_snd, PMF.bind_const] using joint

end Vegas.SourceProgram.Setup
