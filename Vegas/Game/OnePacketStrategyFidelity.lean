module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketSequentialPreservation
public import GameTheoryExtensions.Math.Probability.RetentionLimit

@[expose] public section

/-! # Strategy fidelity of the native one-packet assessment

At every clear forced first activation whose source projection is an intended
decision site, the common component limit uses exactly the canonical native
realization of the intended strategy. The result applies also when the intended
equilibrium assigns that site zero probability.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)

local notation "N" =>
  onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon scheduler

/-- Canonical native realization is continuous at every genuine projected
source decision site. -/
theorem honestChoice_convergesPointwise_of_projected_site
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {intended : setup.intendedModel.BehavioralAssessment}
    (sourceLimit : BehavioralAssessmentConvergesPointwise sequence intended)
    {who : Player} (info : (application setup timeouts leaks).Info)
    (sourceSite : setup.intendedModel.InformationSite who)
    (projected : sourceSite.1 = projectView setup timeouts leaks who info) :
    PMFConvergesPointwise
      (fun n => honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
        (sequence n) who info)
      (honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
        intended who info) := by
  have sourceConverges := sourceLimit.strategy who sourceSite
  rw [projected] at sourceConverges
  have asIfConverges := sourceConverges.map Subtype.val
  cases info with
  | none => exact pmfConvergesPointwise_const _
  | some input =>
    rcases input with ⟨past, view⟩
    cases turn : view.application.publicView.ownTurn? who with
    | none =>
      simp only [honestChoice, honestResponse, turn]
      exact pmfConvergesPointwise_const _
    | some event =>
      simp only [honestChoice, honestResponse, turn]
      apply PMFConvergesPointwise.map
      apply PMFConvergesPointwise.map
      exact asIfConverges

variable [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

/-- Away from late deliveries, every clear forced native site in a common
component limit has exactly the intended canonical native choice law. -/
theorem onePacketAssembled_limit_strategy_of_not_late
    (sourceSequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (vanishing : Tendsto scale atTop (nhds 0))
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sourceSequence
      scale scale_pos scale_le_one weights targetSequence)
    {intended : setup.intendedModel.BehavioralAssessment} {target : (N).BehavioralAssessment}
    (sourceLimit : BehavioralAssessmentConvergesPointwise sourceSequence intended)
    (targetLimit : BehavioralAssessmentConvergesPointwise targetSequence target)
    {who : Player} (site : (N).InformationSite who)
    (sourceSite : setup.intendedModel.InformationSite who)
    (projected : sourceSite.1 = projectView setup timeouts leaks who site.1)
    (notLate : ¬ LateDelivery setup timeouts leaks who site.1)
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks)
      (initialLaw setup) horizon scheduler who site.1)
    (clear : site.1.isSome → ClearInput timeouts leaks site.1) :
    target.strategy who site.1 =
      honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
        intended who site.1 := by
  have occurs : ∃ history : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).History, (N).infoOf who history.trace = site.1 := by
    obtain ⟨history, _, _⟩ := site.2
    exact ⟨history.1, history.2⟩
  apply pmf_limit_eq_of_retained_mass (targetLimit.strategy who site)
    (honestChoice_convergesPointwise_of_projected_site setup timeouts leaks bounds horizon scheduler
      sourceLimit site.1 sourceSite projected) (tendsto_slotRetention vanishing)
  intro n choice
  rw [assembled n]
  exact onePacketMixture_ge_honest_of_not_late setup timeouts leaks bounds horizon scheduler
    sourceSequence scale scale_pos scale_le_one n (weights n) notLate occurs forced clear choice

/-- The native strategy identity survives the common strictly increasing
subsequence used for assessment compactness. -/
theorem onePacketAssembled_subsequence_limit_strategy_of_not_late
    (sourceSequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (vanishing : Tendsto scale atTop (nhds 0))
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sourceSequence
      scale scale_pos scale_le_one weights targetSequence)
    (index : ℕ → ℕ) (increasing : StrictMono index)
    {intended : setup.intendedModel.BehavioralAssessment} {target : (N).BehavioralAssessment}
    (sourceLimit : BehavioralAssessmentConvergesPointwise sourceSequence intended)
    (targetLimit : BehavioralAssessmentConvergesPointwise
      (fun n => targetSequence (index n)) target)
    {who : Player} (site : (N).InformationSite who)
    (sourceSite : setup.intendedModel.InformationSite who)
    (projected : sourceSite.1 = projectView setup timeouts leaks who site.1)
    (notLate : ¬ LateDelivery setup timeouts leaks who site.1)
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks)
      (initialLaw setup) horizon scheduler who site.1)
    (clear : site.1.isSome → ClearInput timeouts leaks site.1) :
    target.strategy who site.1 =
      honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
        intended who site.1 := by
  have sourceSubsequence : BehavioralAssessmentConvergesPointwise
      (fun n => sourceSequence (index n)) intended := by
    constructor
    · intro player source choice
      exact (sourceLimit.strategy player source choice).comp increasing.tendsto_atTop
    · intro player source history
      exact (sourceLimit.belief player source history).comp increasing.tendsto_atTop
  exact onePacketAssembled_limit_strategy_of_not_late setup timeouts leaks bounds horizon scheduler
    (fun n => sourceSequence (index n)) (fun n => scale (index n)) (fun n => scale_pos (index n))
    (fun n => scale_le_one (index n)) (vanishing.comp increasing.tendsto_atTop)
    (fun n => weights (index n)) (fun n => targetSequence (index n))
    (fun n => assembled (index n)) sourceSubsequence targetLimit site sourceSite projected
    notLate forced clear

/-- At a clear forced first semantic activation, including an off-path one,
the common native limit realizes the intended source strategy exactly. -/
theorem onePacketAssembled_limit_strategy_of_firstActivation
    (sourceSequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (vanishing : Tendsto scale atTop (nhds 0))
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sourceSequence
      scale scale_pos scale_le_one weights targetSequence)
    (index : ℕ → ℕ) (increasing : StrictMono index)
    {intended : setup.intendedModel.BehavioralAssessment} {target : (N).BehavioralAssessment}
    (sourceLimit : BehavioralAssessmentConvergesPointwise sourceSequence intended)
    (targetLimit : BehavioralAssessmentConvergesPointwise
      (fun n => targetSequence (index n)) target)
    {who : Player} (site : (N).InformationSite who)
    (sourceSite : setup.intendedModel.InformationSite who)
    (projected : sourceSite.1 = projectView setup timeouts leaks who site.1)
    (first : FirstActivation setup timeouts leaks who site.1)
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks)
      (initialLaw setup) horizon scheduler who site.1)
    (clear : ClearInput timeouts leaks site.1) :
    target.strategy who site.1 =
      honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
        intended who site.1 := by
  exact onePacketAssembled_subsequence_limit_strategy_of_not_late setup timeouts leaks bounds
    horizon scheduler sourceSequence scale scale_pos scale_le_one vanishing weights targetSequence
    assembled index increasing sourceLimit targetLimit site sourceSite projected
    (not_lateDelivery_of_firstActivation (timeouts := timeouts) first) forced (fun _ => clear)

end Vegas
