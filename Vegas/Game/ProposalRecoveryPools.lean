/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryPerturbation

/-! # Shared ordinary domains on genuine enriched recovery coordinates -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  [Fintype setup.proposalRecoveryProtocol.History]

open Classical in
def proposalRecoveryDomainSites (who : Player) : Finset (setup.ProposalRecoveryComponent who) :=
  (setup.proposalRecoveryModel.playedInformation who).image (setup.proposalRecoveryQuery who)

abbrev ProposalRecoveryValuePool :=
  (who : Player) × {key // key ∈ setup.proposalRecoveryDomainSites who}

abbrev ProposalRecoveryPoolPart (pool : setup.ProposalRecoveryValuePool) :=
  setup.CommitRecoveryValueChoice pool.1 pool.2.val.1

open Classical in
abbrev proposalRecoveryAgentPool
    (agent : setup.proposalRecoveryModel.InformationAgent
      setup.proposalRecoveryModel.playedInformation) : setup.ProposalRecoveryValuePool :=
  ⟨agent.1, ⟨setup.proposalRecoveryQuery agent.1 agent.2.val,
    Finset.mem_image.mpr ⟨agent.2.val, agent.2.property, rfl⟩⟩⟩

open Classical in
/-- All raw controls and prior proposals are in the shared key. The domain
floor and optional common pin are installed before the weights are optimized. -/
def proposalRecoveryPooledDomainLaw (finite : setup.program.FiniteBindingTypes)
    (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (pins : (pool : setup.ProposalRecoveryValuePool) →
      Option (PMF (setup.ProposalRecoveryPoolPart pool)))
    (weights : (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (who : Player) (key : setup.ProposalRecoveryComponent who) :
    PMF (setup.CommitRecoveryValueChoice who key.1) :=
  mix floor nonnegative bounded (setup.commitRecoveryValueReference finite who key.1)
    (if present : key ∈ setup.proposalRecoveryDomainSites who then
      (pins ⟨who, ⟨key, present⟩⟩).getD (weights ⟨who, ⟨key, present⟩⟩)
    else setup.commitRecoveryValueReference finite who key.1)

theorem proposalRecoveryPooledDomainLaw_fullSupport
    (finite : setup.program.FiniteBindingTypes)
    (floor : ℝ) (positive : 0 < floor) (bounded : floor ≤ 1)
    (pins : (pool : setup.ProposalRecoveryValuePool) →
      Option (PMF (setup.ProposalRecoveryPoolPart pool)))
    (weights : (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (who : Player) (key : setup.ProposalRecoveryComponent who) :
    FullSupport (setup.proposalRecoveryPooledDomainLaw finite floor positive.le bounded
      pins weights who key) := by
  intro value
  exact mem_support_mix_left _ _ _ positive
    (setup.commitRecoveryValueReference_fullSupport finite who key.1 value)

open Classical in
def proposalRecoveryPoolComponent (finite : setup.program.FiniteBindingTypes)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (pins : (pool : setup.ProposalRecoveryValuePool) →
      Option (PMF (setup.ProposalRecoveryPoolPart pool)))
    (agent : setup.proposalRecoveryModel.InformationAgent
      setup.proposalRecoveryModel.playedInformation)
    (part : setup.ProposalRecoveryPoolPart (setup.proposalRecoveryAgentPool agent)) :
    PMF (setup.proposalRecoveryModel.Choice agent.1 agent.2.val) :=
  (setup.proposalRecoveryComponentTrembledLaw agent.1
    (setup.proposalRecoveryAgentPool agent).2.val
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded
    (mix floor floorNonnegative floorBounded
      (setup.commitRecoveryValueReference finite agent.1
        (setup.proposalRecoveryAgentPool agent).2.val.1)
      ((pins (setup.proposalRecoveryAgentPool agent)).getD (PMF.pure part)))).map
        (setup.proposalRecoveryComponentChoice agent.1 agent.2.val).symm

open Classical in
theorem proposalRecoveryPoolComponent_fullSupport
    (finite : setup.program.FiniteBindingTypes)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (delivery : ℝ) (deliveryPositive : 0 < delivery) (deliverySmall : delivery < 1)
    (floor : ℝ) (floorPositive : 0 < floor) (floorSmall : floor < 1)
    (pins : (pool : setup.ProposalRecoveryValuePool) →
      Option (PMF (setup.ProposalRecoveryPoolPart pool)))
    (agent : setup.proposalRecoveryModel.InformationAgent
      setup.proposalRecoveryModel.playedInformation)
    (part : setup.ProposalRecoveryPoolPart (setup.proposalRecoveryAgentPool agent)) :
    FullSupport (setup.proposalRecoveryPoolComponent finite
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le
      delivery deliveryPositive.le deliverySmall.le
      floor floorPositive.le floorSmall.le pins agent part) := by
  have ordinary : FullSupport (mix floor floorPositive.le floorSmall.le
      (setup.commitRecoveryValueReference finite agent.1
        (setup.proposalRecoveryAgentPool agent).2.val.1)
      ((pins (setup.proposalRecoveryAgentPool agent)).getD (PMF.pure part))) := by
    intro value
    exact mem_support_mix_left _ _ _ floorPositive
      (setup.commitRecoveryValueReference_fullSupport finite agent.1 _ value)
  have full := setup.proposalRecoveryComponentTrembledLaw_fullSupport agent.1
    (setup.proposalRecoveryAgentPool agent).2.val
    omission omissionPositive omissionSmall bad badPositive badSmall
    delivery deliveryPositive deliverySmall _ ordinary
  intro choice
  refine (PMF.mem_support_map_iff _ _ _).mpr
    ⟨setup.proposalRecoveryComponentChoice agent.1 agent.2.val choice, full _, ?_⟩
  exact (setup.proposalRecoveryComponentChoice agent.1 agent.2.val).symm_apply_apply choice

open Classical in
theorem proposalRecoveryPoolComponent_bind
    (finite : setup.program.FiniteBindingTypes)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (pins : (pool : setup.ProposalRecoveryValuePool) →
      Option (PMF (setup.ProposalRecoveryPoolPart pool)))
    (weights : (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (agent : setup.proposalRecoveryModel.InformationAgent
      setup.proposalRecoveryModel.playedInformation) :
    (weights (setup.proposalRecoveryAgentPool agent)).bind
        (setup.proposalRecoveryPoolComponent finite omission omissionNonnegative omissionBounded
          bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded
          floor floorNonnegative floorBounded pins agent) =
      setup.proposalRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded
        (setup.proposalRecoveryPooledDomainLaw finite
          floor floorNonnegative floorBounded pins weights) agent.1 agent.2.val := by
  unfold proposalRecoveryNormalizedTrembledProfile proposalRecoveryPrescribedProfile
    proposalRecoveryPoolComponent
  rw [← PMF.map_bind, setup.proposalRecoveryComponentTrembledLaw_bind]
  apply congrArg (fun law => (setup.proposalRecoveryComponentTrembledLaw agent.1
    (setup.proposalRecoveryAgentPool agent).2.val omission omissionNonnegative omissionBounded
    bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded law).map
      (setup.proposalRecoveryComponentChoice agent.1 agent.2.val).symm)
  unfold proposalRecoveryPooledDomainLaw
  rw [dite_eq_left (setup.proposalRecoveryAgentPool agent).2.property]
  cases pinned : pins (setup.proposalRecoveryAgentPool agent) with
  | none =>
      simp only [Option.getD_none]
      exact bind_mix_pure _ _ _ _ _
  | some law => simp only [Option.getD_some, PMF.bind_const]

end Vegas.SourceProgram.Setup
