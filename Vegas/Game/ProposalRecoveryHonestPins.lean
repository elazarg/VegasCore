/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryInformationEmbedding
import Vegas.Game.ProposalRecoveryPools
import Vegas.Game.CommitRecoveryHonestPrescription

/-! # Selected intended laws on the actual archive-refined source pools -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The semantic component of an actual intended-image query is the old
normalized query. The complete extra archive remains a separate coordinate. -/
theorem proposalRecoveryQuery_intended_semantic (wellFormed : setup.WellFormed) (who : Player)
    (history : setup.intendedProtocol.History) :
    (setup.proposalRecoveryQuery who
        (setup.proposalRecoveryInformation wellFormed who
          (setup.intendedModel.infoOf who history.trace))).1 =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who
          (setup.commitRecoveryInformation wellFormed who
            (setup.intendedModel.infoOf who history.trace))) := by
  have erased := setup.proposalRecoveryEraseInfo_observed who
    (setup.proposalRecoveryIntendedLift wellFormed history).trace
  rw [setup.proposalRecoveryInformation_observed] at erased
  change setup.proposalRecoveryEraseInfo who _ =
    setup.commitRecoveryModel.infoOf who
      (setup.proposalRecoveryEraseTrace
        (setup.proposalRecoveryLiftTrace (fun _ _ => false)
          (setup.commitRecoveryLiftHistory wellFormed history).trace)) at erased
  rw [setup.proposalRecoveryEraseTrace_lift,
    setup.commitRecoveryInformation_observed] at erased
  exact congrArg (fun information => setup.commitRecoveryErasedInformation who
    (setup.commitRecoveryNoMissInformation who information)) erased

/-- Equal actual enriched pool keys of intended histories determine the SAME
full intended source information. The chosen source laws therefore agree. -/
theorem proposalRecovery_honest_information_eq_of_query_eq
    (wellFormed : setup.WellFormed) (who : Player)
    (first second : setup.intendedProtocol.History)
    (same : setup.proposalRecoveryQuery who
        (setup.proposalRecoveryInformation wellFormed who
          (setup.intendedModel.infoOf who first.trace)) =
      setup.proposalRecoveryQuery who
        (setup.proposalRecoveryInformation wellFormed who
          (setup.intendedModel.infoOf who second.trace))) :
    setup.intendedModel.infoOf who first.trace = setup.intendedModel.infoOf who second.trace := by
  apply setup.commitRecovery_honest_information_eq_of_query_eq wellFormed who first second
  have semantic := congrArg Prod.fst same
  rwa [setup.proposalRecoveryQuery_intended_semantic,
    setup.proposalRecoveryQuery_intended_semantic] at semantic

section Pools

variable [Fintype setup.proposalRecoveryProtocol.History]

/-- The pin recognizes the FULL enriched key, including its derived proposal
archive. Free pools do not inherit an honest law merely from erasure. -/
def proposalRecoveryHonestPoolPins (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (pool : setup.ProposalRecoveryValuePool) :
    Option (PMF (setup.ProposalRecoveryPoolPart pool)) := by
  classical
  exact if found : ∃ history : setup.intendedProtocol.History,
      setup.proposalRecoveryQuery pool.1
        (setup.proposalRecoveryInformation wellFormed pool.1
          (setup.intendedModel.infoOf pool.1 history.trace)) = pool.2.val then
    some ((source pool.1 (setup.intendedModel.infoOf pool.1 found.choose.trace)).map
      fun choice => Eq.mp (congrArg (setup.CommitRecoveryValueChoice pool.1)
        ((setup.proposalRecoveryQuery_intended_semantic wellFormed pool.1 found.choose).symm.trans
          (congrArg Prod.fst found.choose_spec)))
        (setup.commitRecoveryHonestDomainChoice wellFormed pool.1
          (setup.intendedModel.infoOf pool.1 found.choose.trace) choice))
  else none

omit [Fintype setup.proposalRecoveryProtocol.History] in
private theorem domain_cast_raw (who : Player)
    {first second : setup.commitRecoveryModel.InfoState who} (same : first = second)
    (choice : setup.CommitRecoveryValueChoice who first) :
    (Eq.mp (congrArg (setup.CommitRecoveryValueChoice who) same) choice).val.val =
      choice.val.val := by
  cases same
  rfl

/-- Every genuine intended witness reads the literal selected source law
from this pin. Its witness choice cannot select another private source view. -/
theorem proposalRecoveryHonestPoolPins_raw (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (pool : setup.ProposalRecoveryValuePool) (history : setup.intendedProtocol.History)
    (atQuery : setup.proposalRecoveryQuery pool.1
      (setup.proposalRecoveryInformation wellFormed pool.1
        (setup.intendedModel.infoOf pool.1 history.trace)) = pool.2.val) :
    (setup.proposalRecoveryHonestPoolPins wellFormed source pool).map
      (fun law => law.map (fun choice => choice.val.val)) =
      some ((source pool.1 (setup.intendedModel.infoOf pool.1 history.trace)).map
        (fun choice => CommitRecoveryMove.lift choice.val)) := by
  classical
  have present : ∃ other : setup.intendedProtocol.History,
      setup.proposalRecoveryQuery pool.1
        (setup.proposalRecoveryInformation wellFormed pool.1
          (setup.intendedModel.infoOf pool.1 other.trace)) = pool.2.val := ⟨history, atQuery⟩
  have sameInfo := setup.proposalRecovery_honest_information_eq_of_query_eq wellFormed pool.1
    present.choose history (present.choose_spec.trans atQuery.symm)
  unfold proposalRecoveryHonestPoolPins
  rw [dite_eq_left present]
  simp only [Option.map_some, PMF.map_comp, Function.comp_def]
  have rawMap : (source pool.1 (setup.intendedModel.infoOf pool.1 present.choose.trace)).map
      (fun choice =>
        (Eq.mp (congrArg (setup.CommitRecoveryValueChoice pool.1)
          ((setup.proposalRecoveryQuery_intended_semantic
            wellFormed pool.1 present.choose).symm.trans
              (congrArg Prod.fst present.choose_spec)))
          (setup.commitRecoveryHonestDomainChoice wellFormed pool.1
            (setup.intendedModel.infoOf pool.1 present.choose.trace) choice)).val.val) =
      (source pool.1 (setup.intendedModel.infoOf pool.1 present.choose.trace)).map
        (fun choice => CommitRecoveryMove.lift choice.val) := by
    apply congrArg (fun f =>
      (source pool.1 (setup.intendedModel.infoOf pool.1 present.choose.trace)).map f)
    funext choice
    exact (setup.domain_cast_raw pool.1
      ((setup.proposalRecoveryQuery_intended_semantic
        wellFormed pool.1 present.choose).symm.trans
          (congrArg Prod.fst present.choose_spec)) _).trans
      (setup.commitRecoveryHonestDomainChoice_raw wellFormed pool.1 _ choice)
  rw [rawMap, sameInfo]

theorem proposalRecoveryHonestPoolPins_absent_iff (wellFormed : setup.WellFormed)
    (first second : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (pool : setup.ProposalRecoveryValuePool) :
    setup.proposalRecoveryHonestPoolPins wellFormed first pool = none ↔
      setup.proposalRecoveryHonestPoolPins wellFormed second pool = none := by
  classical
  unfold proposalRecoveryHonestPoolPins
  split <;> simp only [Option.some_ne_none, iff_self]

theorem proposalRecoveryPooledDomainLaw_honest_raw
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (weights : (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (pool : setup.ProposalRecoveryValuePool) (history : setup.intendedProtocol.History)
    (atQuery : setup.proposalRecoveryQuery pool.1
      (setup.proposalRecoveryInformation wellFormed pool.1
        (setup.intendedModel.infoOf pool.1 history.trace)) = pool.2.val) :
    (setup.proposalRecoveryPooledDomainLaw finite floor nonnegative bounded
      (setup.proposalRecoveryHonestPoolPins wellFormed source) weights pool.1 pool.2.val).map
        (fun choice => choice.val.val) =
      mix floor nonnegative bounded
        ((setup.commitRecoveryValueReference finite pool.1 pool.2.val.1).map
          (fun choice => choice.val.val))
        ((source pool.1 (setup.intendedModel.infoOf pool.1 history.trace)).map
          (fun choice => CommitRecoveryMove.lift choice.val)) := by
  classical
  have pin := setup.proposalRecoveryHonestPoolPins_raw wellFormed source pool history atQuery
  unfold proposalRecoveryPooledDomainLaw
  rw [mix_map, dite_eq_left pool.2.property]
  congr 1
  change ((setup.proposalRecoveryHonestPoolPins wellFormed source pool).getD
    (weights pool)).map (fun choice => choice.val.val) = _
  cases selected : setup.proposalRecoveryHonestPoolPins wellFormed source pool with
  | none => rw [selected] at pin; cases pin
  | some law =>
      rw [selected] at pin
      exact Option.some.inj pin

end Pools
end Vegas.SourceProgram.Setup
