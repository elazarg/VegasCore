/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOrdinaryDomination
import Interaction.ReactiveFiniteAssessment

/-! # Finite ordinary response floors before preparation noise

The finite minimum ranges over positive atoms of one explicitly constructed
ordinary-only native policy. It does not range over bad-preparation atoms or
depend on optimized source pool weights. Inserting one handles games with no
decision sites without adding a player or event nonemptiness assumption.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "model" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- Represent the ordinary-only comparison in the actual counted model. -/
def phaseProposalOrdinaryStrategy
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) : (model).BehavioralPolicy who :=
  (menu).restrictPolicy initial horizon scheduler who
    (phaseProposalOrdinaryPolicy setup mode runtime leaks bounds plan values rates who)

/-- Finite actual histories give one positive bound on every supported
ordinary response atom. The policy has no preparation-noise or free-weight
argument when its table is instantiated with the fixed source value reference. -/
theorem exists_phaseProposalOrdinaryStrategy_floor
    [(app).FiniteNature initial scheduler]
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) :
    ∃ lower : ℝ, 0 < lower ∧ lower ≤ 1 ∧
      ∀ (who : Player) (site : (model).InformationSite who)
        (choice : (model).Choice who site.1),
        choice ∈ (phaseProposalOrdinaryStrategy setup mode runtime leaks bounds plan initial
          horizon scheduler values rates who site.1).support →
        lower ≤ (phaseProposalOrdinaryStrategy setup mode runtime leaks bounds plan initial
          horizon scheduler values rates who site.1 choice).toReal := by
  classical
  let Coordinate := (who : Player) × (site : (model).InformationSite who) ×
    (model).Choice who site.1
  let : Fintype Coordinate := Fintype.ofFinite Coordinate
  let mass : Coordinate → ℝ := fun coordinate =>
    (phaseProposalOrdinaryStrategy setup mode runtime leaks bounds plan initial horizon scheduler
      values rates coordinate.1 coordinate.2.1.val coordinate.2.2).toReal
  let positive : Finset Coordinate := Finset.univ.filter fun coordinate => 0 < mass coordinate
  let masses : Finset ℝ := insert 1 (positive.image mass)
  have nonempty : masses.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let lower := masses.min' nonempty
  have included : lower ∈ masses := Finset.min'_mem masses nonempty
  have strict : 0 < lower := by
    rcases Finset.mem_insert.mp included with same | present
    · rw [same]
      exact zero_lt_one
    · obtain ⟨coordinate, member, same⟩ := Finset.mem_image.mp present
      rw [← same]
      exact (Finset.mem_filter.mp member).2
  refine ⟨lower, strict, Finset.min'_le masses 1 (Finset.mem_insert_self _ _), ?_⟩
  intro who site choice supported
  have atomPositive : 0 < mass ⟨who, site, choice⟩ :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp supported) (PMF.apply_ne_top _ _)
  exact Finset.min'_le masses _ (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨⟨who, site, choice⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, atomPositive⟩, rfl⟩))

end Vegas
