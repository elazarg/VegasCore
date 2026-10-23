/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryFlags

/-! # Legal prescriptions on archive-refined source coordinates -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

abbrev ProposalRecoveryComponent (who : Player) :=
  setup.commitRecoveryModel.InfoState who × Finset (ProposalRecoveryProposal L)

/-- A component contains every original semantic choice and each valid
proposal label. Publicly failed disclosures remain genuine available actions. -/
def ProposalRecoveryComponentChoice (who : Player)
    (key : setup.ProposalRecoveryComponent who) :=
  {move : Option (ProposalRecoveryMove Player L) //
    setup.commitRecoveryModel.menu who key.1 (move.map (·.semantic)) ∧
      move.elim True ProposalRecoveryMove.Valid}

private theorem query_menu (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who) :
    setup.commitRecoveryModel.menu who (setup.proposalRecoveryQuery who information).1 =
      setup.commitRecoveryModel.menu who (setup.proposalRecoveryEraseInfo who information) := by
  dsimp only [proposalRecoveryQuery]
  rw [setup.commitRecoveryErasedInformation_menu, setup.commitRecoveryNoMissInformation_menu]

/-- Literal raw actions transport along equal legal menus, including every
usable alias and both proposal flags of a semantic withheld publication. -/
def proposalRecoveryComponentChoice (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who) :
    setup.proposalRecoveryModel.Choice who information ≃
      setup.ProposalRecoveryComponentChoice who (setup.proposalRecoveryQuery who information) where
  toFun choice := ⟨choice.1, by
    rw [setup.query_menu who information]
    exact (setup.proposalRecoveryMenu_semantic who information choice.1).mp choice.2⟩
  invFun choice := ⟨choice.1, by
    apply (setup.proposalRecoveryMenu_semantic who information choice.1).mpr
    change setup.commitRecoveryModel.menu who
      (setup.proposalRecoveryEraseInfo who information) (choice.1.map (·.semantic)) ∧ _
    rw [← setup.query_menu who information]
    exact choice.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev ProposalRecoveryPrescription (who : Player) :=
  (key : setup.ProposalRecoveryComponent who) → PMF (setup.ProposalRecoveryComponentChoice who key)

/-- The original perfect-recall game reads one common prescription at the
archive-refined coordinate. Its histories and chance laws are unchanged. -/
def proposalRecoveryPrescribedProfile
    (prescription : ∀ who, setup.ProposalRecoveryPrescription who) :
    ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who := fun who information =>
  (prescription who (setup.proposalRecoveryQuery who information)).map
    (setup.proposalRecoveryComponentChoice who information).symm

theorem proposalRecoveryPrescribedProfile_raw
    (prescription : ∀ who, setup.ProposalRecoveryPrescription who)
    (who : Player) (information : setup.proposalRecoveryModel.InfoState who) :
    (setup.proposalRecoveryPrescribedProfile prescription who information).map Subtype.val =
      (prescription who (setup.proposalRecoveryQuery who information)).map Subtype.val := by
  rw [proposalRecoveryPrescribedProfile, PMF.map_comp]
  rfl

theorem proposalRecoveryPrescribedProfile_normalized
    (prescription : ∀ who, setup.ProposalRecoveryPrescription who)
    (who : Player) (first second : setup.proposalRecoveryModel.InfoState who)
    (same : setup.proposalRecoveryQuery who first = setup.proposalRecoveryQuery who second) :
    (setup.proposalRecoveryPrescribedProfile prescription who first).map Subtype.val =
      (setup.proposalRecoveryPrescribedProfile prescription who second).map Subtype.val := by
  rw [setup.proposalRecoveryPrescribedProfile_raw,
    setup.proposalRecoveryPrescribedProfile_raw, same]

def proposalRecoveryPrescriptionSignature : GameSignature Player where
  Strategy := setup.ProposalRecoveryPrescription
  Outcome := setup.proposalRecoveryProtocol.History

/-- Replace one common component law without identifying any full histories. -/
def proposalRecoveryPrescriptionWithLaw (who : Player)
    (prescription : setup.ProposalRecoveryPrescription who)
    (key : setup.ProposalRecoveryComponent who)
    (law : PMF (setup.ProposalRecoveryComponentChoice who key)) :
    setup.ProposalRecoveryPrescription who := by
  classical
  exact (Equiv.piSplitAt key fun coordinate =>
    PMF (setup.ProposalRecoveryComponentChoice who coordinate)).symm
      (law, fun coordinate => prescription coordinate.1)

theorem proposalRecoveryPrescriptionWithLaw_self (who : Player)
    (prescription : setup.ProposalRecoveryPrescription who)
    (key : setup.ProposalRecoveryComponent who)
    (law : PMF (setup.ProposalRecoveryComponentChoice who key)) :
    setup.proposalRecoveryPrescriptionWithLaw who prescription key law key = law := by
  classical
  simp [proposalRecoveryPrescriptionWithLaw]

theorem proposalRecoveryPrescriptionWithLaw_of_ne (who : Player)
    (prescription : setup.ProposalRecoveryPrescription who)
    (key : setup.ProposalRecoveryComponent who)
    (law : PMF (setup.ProposalRecoveryComponentChoice who key))
    {other : setup.ProposalRecoveryComponent who} (different : other ≠ key) :
    setup.proposalRecoveryPrescriptionWithLaw who prescription key law other =
      prescription other := by
  classical
  simp [proposalRecoveryPrescriptionWithLaw, different]

theorem proposalRecoveryPrescriptionWithLaw_eq_self (who : Player)
    (prescription : setup.ProposalRecoveryPrescription who)
    (key : setup.ProposalRecoveryComponent who) :
    setup.proposalRecoveryPrescriptionWithLaw who prescription key (prescription key) =
      prescription := by
  classical
  funext other
  by_cases same : other = key
  · subst other
    exact setup.proposalRecoveryPrescriptionWithLaw_self who prescription key (prescription key)
  · exact setup.proposalRecoveryPrescriptionWithLaw_of_ne who prescription key
      (prescription key) same

end Vegas.SourceProgram.Setup
