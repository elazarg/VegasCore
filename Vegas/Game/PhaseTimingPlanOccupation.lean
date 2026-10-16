/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPoolPlan
import Interaction.ReactiveOccupationPosterior

/-! # Actual command-occupation posteriors for common timing plans -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  {Entry : Type} (entryLaw : PMF Entry)
  (entryState : Entry → (phaseApplication runtime leaks).State)
  (horizon : Nat) [NeZero horizon]
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (entryLaw.map entryState) horizon
    scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information (entryLaw.map entryState) horizon
      scheduler).InfoState who)]

local notation "initial" => entryLaw.map entryState
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds
  (entryLaw.map entryState) horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance : Fintype Pool := Fintype.ofFinite _

variable (fallback : (who : Player) →
    (ReactiveApplication.ResponseMenu.information (PhaseCount.onePacketMenu runtime leaks bounds)
      (entryLaw.map entryState) horizon scheduler).Policy who)
  (wellFormed : setup.WellFormed) (source : setup.commitRecoveryModel.BehavioralAssessment)
  (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)

omit [NeZero horizon] in
open Classical in
/-- Original finite timing plans remain jointly attached to the actual control
before a response. The original entry is not reconstructed from its encoding. -/
theorem phaseTimingAssessment_command_joint
    (weights : (p : Pool) → PMF (Parts p)) (assessment : (N).BehavioralAssessment)
    (assembled : assessment.strategy = (N).agentBehavior (N).playedInformation fallback
      (fun agent => (weights (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded agent)))
    (remaining count : Nat) (state : (app).State) :
    let members := fun owner plan => phaseTimingPlanPolicy setup mode runtime leaks bounds
      initial horizon scheduler bound fallback wellFormed source noise noiseNonnegative
        noiseBounded slotWeight slotNonnegative slotBounded plan owner
    let factors := fun control : (app).ProtocolState => fun owner =>
      ((app).policyMixture (independentProduct weights) (members owner)).posterior
        (control.elim [] (fun current => current.execution.recall owner))
    (independentProduct (fun _ : Player => independentProduct weights)).bind (fun plans =>
      ((app).commandControlLaw scheduler (fun owner => members owner (plans owner))
        (PMF.pure state) remaining count).map (fun control => (control, plans))) =
      ((app).commandControlLaw scheduler
        ((menu).decodeProfile initial horizon scheduler assessment.strategy)
          (PMF.pure state) remaining count).bind (fun control =>
            (independentProduct (factors control)).map (Prod.mk control)) := by
  intro members factors
  let start := ReactiveApplication.Execution.initial (app) state
  let continuation := fun pair : (app).Execution × (Player → (p : Pool) → Parts p) =>
    (scheduler pair.1.environmentRecall (pair.1.observeEnvironment (app))).bind fun command =>
      (pair.1.environmentStep (app) command).map fun active =>
        (some (⟨remaining, command.actor? (app), active⟩ : (app).Control), pair.2)
  have rounds := phaseTimingAssessment_runRounds_joint setup mode runtime leaks bounds initial
    horizon scheduler bound fallback wellFormed source noise noiseNonnegative noiseBounded
      slotWeight slotNonnegative slotBounded weights assessment assembled count start
  have moved := congrArg (fun distribution => distribution.bind continuation) rounds
  simp only [continuation, PMF.bind_bind, PMF.bind_map, Function.comp_def] at moved
  simp only [ReactiveApplication.commandControlLaw, PMF.pure_bind, PMF.map_bind,
    PMF.bind_bind, PMF.map_comp, Function.comp_def]
  change (independentProduct (fun _ : Player => independentProduct weights)).bind
    (fun plans => _) = _
  refine moved.trans ?_
  apply bind_congr_on_support
  intro before _
  rw [PMF.bind_comm]
  apply bind_congr_on_support
  intro command _
  have disintegrated := ReactiveApplication.environmentStep_disintegrate_profile
    (fun owner => (app).policyMixture (independentProduct weights) (members owner)) before
      command (fun active plans => PMF.pure
        (some (⟨remaining, command.actor? (app), active⟩ : (app).Control), plans))
  simpa only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, factors,
    Option.elim_some, members] using disintegrated

open Classical in
/-- Sampling the original command index and original entry retains their joint
law with all original private plans at the true before-response control. -/
theorem phaseTimingAssessment_occupation_joint
    (weights : (p : Pool) → PMF (Parts p)) (assessment : (N).BehavioralAssessment)
    (assembled : assessment.strategy = (N).agentBehavior (N).playedInformation fallback
      (fun agent => (weights (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded agent))) :
    let members := fun owner plan => phaseTimingPlanPolicy setup mode runtime leaks bounds
      initial horizon scheduler bound fallback wellFormed source noise noiseNonnegative
        noiseBounded slotWeight slotNonnegative slotBounded plan owner
    let factors := fun control : (app).ProtocolState => fun owner =>
      ((app).policyMixture (independentProduct weights) (members owner)).posterior
        (control.elim [] (fun current => current.execution.recall owner))
    let law := (PMF.uniformOfFintype (Fin horizon)).bind fun time => entryLaw.bind fun entry =>
      ((app).commandControlLaw scheduler
        ((menu).decodeProfile initial horizon scheduler assessment.strategy)
          (PMF.pure (entryState entry)) (horizon - time.val - 1) time.val).map
            (fun control => ((time, entry), control))
    (PMF.uniformOfFintype (Fin horizon)).bind (fun time => entryLaw.bind fun entry =>
      (independentProduct (fun _ : Player => independentProduct weights)).bind fun plans =>
        ((app).commandControlLaw scheduler (fun owner => members owner (plans owner))
          (PMF.pure (entryState entry)) (horizon - time.val - 1) time.val).map
            (fun control => (((time, entry), control), plans))) =
      law.bind (fun branch =>
        (independentProduct (factors branch.2)).map (Prod.mk branch)) := by
  intro members factors law
  simp only [law, PMF.bind_bind, PMF.bind_map]
  apply bind_congr_on_support
  intro time _
  apply bind_congr_on_support
  intro entry _
  have joint := phaseTimingAssessment_command_joint setup mode runtime leaks bounds entryLaw
    entryState horizon scheduler bound fallback wellFormed source noise noiseNonnegative
      noiseBounded slotWeight slotNonnegative slotBounded weights assessment assembled
        (horizon - time.val - 1) time.val (entryState entry)
  have tagged := congrArg (PMF.map (fun pair => (((time, entry), pair.1), pair.2))) joint
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using tagged

open Classical in
/-- The actual Bayes assessment fiber preserves the ORIGINAL current timing
weight independently of its full tagged physical control and remaining plans.
Original entries and command indices stay in the posterior remainder. -/
theorem phaseTimingAssessment_bayes_plan_posterior
    (weights : (p : Pool) → PMF (Parts p)) (assessment : (N).BehavioralAssessment)
    (assembled : assessment.strategy = (N).agentBehavior (N).playedInformation fallback
      (fun agent => (weights (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded agent)))
    (mixed : assessment.IsFullyMixed)
    (bayes : BehavioralAssessment.IsBayesConsistent (N) assessment
      ((menu).decisionInformationAntichain initial horizon scheduler))
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (decision : (N).IsDecisionInfo who (some (past, view))) :
    let site : (N).InformationSite who := ⟨some (past, view), decision⟩
    let current := (N).agentAt site
    let members := fun owner plan => phaseTimingPlanPolicy setup mode runtime leaks bounds
      initial horizon scheduler bound fallback wellFormed source noise noiseNonnegative
        noiseBounded slotWeight slotNonnegative slotBounded plan owner
    let original := (PMF.uniformOfFintype (Fin horizon)).bind fun time => entryLaw.bind fun entry =>
      (independentProduct (fun _ : Player => independentProduct weights)).bind fun plans =>
        ((app).commandControlLaw scheduler (fun owner => members owner (plans owner))
          (PMF.pure (entryState entry)) (horizon - time.val - 1) time.val).map
            (fun control => (((time, entry), control), plans))
    let observed := fiberPosterior original (fun pair => (app).observe who pair.1.2) site.1
    (∃ remainder : PMF (((p : {p // p ≠ pool current}) → Parts p.val) ×
        (((Fin horizon × Entry) × (app).ProtocolState) ×
          ((owner : {owner // owner ≠ who}) → (p : Pool) → Parts p))),
      observed.map (fun pair => (pair.2 who (pool current),
        ((fun p : {p // p ≠ pool current} => pair.2 who p.val),
          (pair.1, fun owner : {owner // owner ≠ who} => pair.2 owner.val)))) =
        (weights (pool current)).bind (fun part => remainder.map (Prod.mk part))) ∧
      observed.map (fun pair => pair.1.2) =
        (assessment.belief who site).map (fun history => history.1.state) := by
  intro site current members original observed
  let factors := fun control : (app).ProtocolState => fun owner =>
    ((app).policyMixture (independentProduct weights) (members owner)).posterior
      (control.elim [] (fun current => current.execution.recall owner))
  let law := (PMF.uniformOfFintype (Fin horizon)).bind fun time => entryLaw.bind fun entry =>
    ((app).commandControlLaw scheduler
      ((menu).decodeProfile initial horizon scheduler assessment.strategy)
        (PMF.pure (entryState entry)) (horizon - time.val - 1) time.val).map
          (fun control => ((time, entry), control))
  let observe := fun branch : (Fin horizon × Entry) × (app).ProtocolState =>
    (app).observe who branch.2
  have marginal : law.map Prod.snd = (app).occupationControlLaw scheduler
      ((menu).decodeProfile initial horizon scheduler assessment.strategy) initial horizon := by
    simp only [law, ReactiveApplication.occupationControlLaw,
      ReactiveApplication.commandControlLaw, PMF.map_bind, PMF.bind_map,
      PMF.pure_bind, PMF.map_comp, Function.comp_def]
  have positive := (N).informationMass_pos_of_fullSupport assessment.strategy mixed who site
  have present := (menu).occupation_observation_support initial horizon scheduler
    assessment.strategy who site positive
  rw [← marginal, PMF.map_comp] at present
  change site.1 ∈ (law.map observe).support at present
  have originalJoint := phaseTimingAssessment_occupation_joint setup mode runtime leaks bounds
    entryLaw entryState horizon scheduler bound fallback wellFormed source noise noiseNonnegative
      noiseBounded slotWeight slotNonnegative slotBounded weights assessment assembled
  change original = law.bind
    (fun branch => (independentProduct (factors branch.2)).map (Prod.mk branch)) at originalJoint
  let common := ((app).policyMixture (independentProduct weights) (members who)).posterior past
  have fixed : ∀ branch ∈ (fiberPosterior law observe site.1).support,
      factors branch.2 who = common := by
    intro branch supported
    have equal := (mem_support_fiberPosterior present supported).1
    change (app).observe who branch.2 = some (past, view) at equal
    cases stateEq : branch.2 with
    | none => simp only [stateEq, ReactiveApplication.observe] at equal; cases equal
    | some control =>
        simp only [stateEq, ReactiveApplication.observe] at equal
        split_ifs at equal with active
        have recallEq := congrArg Prod.fst (Option.some.inj equal)
        change control.execution.recall who = past at recallEq
        exact congrArg
          ((app).policyMixture (independentProduct weights) (members who)).posterior recallEq
  have ownerProduct := fiberPosterior_tagged_product_splitAt law
    (fun branch => independentProduct (factors branch.2)) observe site.1 present
      (fun branch => factors branch.2) (fun _ _ => rfl) who common fixed
  rw [← originalJoint] at ownerProduct
  have played : some (past, view) ∈ (N).playedInformation who :=
    (N).site_mem_playedInformation site
  obtain ⟨restLaw, currentProduct⟩ := phaseTimingPlanPolicy_posterior setup mode runtime leaks
    bounds initial horizon scheduler bound fallback wellFormed source noise noiseNonnegative
      noiseBounded slotWeight slotNonnegative slotBounded weights who past view played
  let others := (fiberPosterior law observe site.1).bind fun branch =>
    (independentProduct (fun owner : {owner // owner ≠ who} => factors branch.2 owner.val)).map
      (Prod.mk branch)
  change _ = common.bind (fun plan => others.map (Prod.mk plan)) at ownerProduct
  let read := fun pair : ((p : Pool) → Parts p) ×
      (((Fin horizon × Entry) × (app).ProtocolState) ×
        ((owner : {owner // owner ≠ who}) → (p : Pool) → Parts p)) =>
    (pair.1 (pool current), ((fun p : {p // p ≠ pool current} => pair.1 p.val), pair.2))
  have projected := congrArg (PMF.map read) ownerProduct
  simp only [PMF.map_comp, PMF.map_bind] at projected
  refine ⟨⟨restLaw.bind (fun rest => others.map (Prod.mk rest)), projected.trans ?_⟩, ?_⟩
  · have combined := congrArg (fun distribution => distribution.bind (fun pair =>
      others.map (fun other => (pair.1, (pair.2, other))))) currentProduct
    simpa only [PMF.bind_map, PMF.bind_bind, PMF.map_bind, PMF.map_comp, Function.comp_def,
      Equiv.piSplitAt_apply, read, common] using combined
  · have branchPosterior := fiberPosterior_bind_of_observation law
      (fun branch => (independentProduct (factors branch.2)).map (Prod.mk branch)) observe
      (fun pair => observe pair.1) (by
        intro branch _ pair member
        obtain ⟨plans, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        rfl) site.1 present
    rw [← originalJoint] at branchPosterior
    have controlReadout := map_fiberPosterior_readout law Prod.snd ((app).observe who)
      site.1 present
    have beliefEq := (BehavioralAssessment.isBayesConsistentAt_iff (N) assessment who site
      ((menu).decisionInformationAntichain initial horizon scheduler who site) positive).mp
        (bayes who site positive)
    have actualBayes := (menu).bayesBelief_state_eq_occupationPosterior initial horizon scheduler
      assessment.strategy who site
        ((menu).decisionInformationAntichain initial horizon scheduler who site) positive
    rw [beliefEq, actualBayes, ← marginal]
    change observed.map (fun pair => pair.1.2) = _
    rw [show observed = (fiberPosterior law observe site.1).bind
        (fun branch => (independentProduct (factors branch.2)).map (Prod.mk branch))
      from branchPosterior]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    change ((fiberPosterior law observe site.1).bind fun branch =>
      (independentProduct (factors branch.2)).map (Function.const _ branch.2)) = _
    simp only [PMF.map_const]
    exact controlReadout

end Vegas
