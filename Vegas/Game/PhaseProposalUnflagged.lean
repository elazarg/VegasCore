/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalReference

/-! # Remove only future random response flags from the actual reference -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Zero BASE rates select canonical sending and syntax. This is deliberately
not an invocation of the full-support reference's totalization guard. -/
def PhaseProposalRates.zero : PhaseProposalRates :=
  let zero : Set.Icc (0 : ℝ) 1 := ⟨0, le_rfl, zero_le_one⟩
  ⟨zero, zero, zero, zero⟩

variable (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

/-- The same current ordinary source draw followed by the actual canonical
raw representative of its packet/preparation class. No past message, slot,
proposal, debt or response record is changed. Forced silence remains silence. -/
def phaseProposalUnflaggedResponses
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    PMF (PhaseProposal.Response runtime leaks bounds who past view) :=
  (phaseProposalBaseClasses setup mode runtime leaks bounds plan values PhaseProposalRates.zero who
    past view).map (PhaseProposal.canonicalResponse runtime leaks bounds who past view)

/-- The prospective comparison policy is evaluated on the unchanged actual
execution. It does not rehabilitate already unsafe pending packets, restart a
clock, repair known bad preparations, or suppress a forced WAIT. -/
def phaseProposalUnflaggedPolicy
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) : (app).Policy := fun past view =>
  (phaseProposalUnflaggedResponses setup mode runtime leaks bounds plan values who past view).map
    Subtype.val

/-- Removing prospective random flags remains inside the SAME counted menu. -/
theorem phaseProposalUnflaggedPolicy_covered
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (response : (app).Action)
    (supported : response ∈
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
        past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  obtain ⟨chosen, _positive, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact chosen.property

/-- Only raw syntax is canonicalized. The effective packet/preparation law
is exactly the unflagged BASE law, including a forced silent response. -/
theorem phaseProposalUnflaggedResponses_project
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (phaseProposalUnflaggedResponses setup mode runtime leaks bounds plan values who past view).map
        (PhaseProposal.projectResponse runtime leaks bounds who past view) =
      phaseProposalBaseClasses setup mode runtime leaks bounds plan values PhaseProposalRates.zero
        who past view := by
  rw [phaseProposalUnflaggedResponses, PMF.map_comp]
  simp only [Function.comp_def, PhaseProposal.project_canonicalResponse]
  exact PMF.map_id _

/-- At a menu with no valid transmission both policies, even at arbitrary
literal pasts, are forced to keep the entire next response silent. -/
theorem phaseProposalUnflaggedPolicy_forced_wait
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (onlyWait : ∀ response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view,
      response = ⟨none⟩) :
    phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who past view =
      PMF.pure ⟨none⟩ := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro response supported
  exact Set.mem_singleton_iff.mpr (onlyWait response
    (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan
      values who past view response supported))

end Vegas
