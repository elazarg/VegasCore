/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalReference
import Vegas.Game.PhaseCountServiceAliases

/-! # Actual initialized history laws after summing foreign private aliases

Only selected foreign owners' operationally inert syntax is normalized. The
existing history-projection theorem sums every original preimage under the
actual reference profile. The focal player's entire raw policy and full
information are retained, together with the original initialized state law.
No proportional-reach or source-belief identity is assumed here.
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
  (values : ∀ who (key : setup.ProposalRecoveryComponent who),
    PMF (setup.CommitRecoveryValueChoice who key.1)) (rates : PhaseProposalRates)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "reference" => phaseProposalReferencePolicy setup mode runtime leaks bounds plan
  values rates

/-- Literal reference laws agree after operational normalization of any
sender recall. The original table, rates, known evidence and catalogue remain. -/
theorem phaseProposalReferencePolicy_normal_recall (normal : (app).SubmissionNormalization)
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    reference who (normal.recall who past) view = reference who past view := by
  apply phaseProposalReferencePolicy_congr_input setup mode runtime leaks bounds plan values rates
    who (normal.recall who past) past view (normal.recall_outputs who past)
  exact phaseCountService_submissionCount_normal_recall setup mode runtime leaks normal who past

private theorem referenceWith_covered (focal : Player) (alternative : (app).Policy)
    (covered : ∀ past view response, response ∈ (alternative past view).support →
      response ∈ PhaseCount.onePacketActions runtime leaks bounds focal past view)
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (response : (app).Action)
    (supported : response ∈
      (Function.update reference focal alternative who past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  classical
  by_cases same : who = focal
  · subst who
    rw [Function.update_self] at supported
    exact covered past view response supported
  · rw [Function.update_of_ne same] at supported
    exact phaseProposalReferencePolicy_covered setup mode runtime leaks bounds plan values rates
      who past view response supported

private theorem referenceWith_normal_recall (owners : Finset Player) (focal : Player)
    (outside : focal ∉ owners) (alternative : (app).Policy) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    let normal := phaseCountServiceNormalization setup mode runtime leaks owners
    Function.update reference focal alternative who (normal.recall who past) view =
      Function.update reference focal alternative who past view := by
  classical
  intro normal
  by_cases same : who = focal
  · subst who
    rw [Function.update_self, phaseCountServiceNormalization_recall_fixed setup mode runtime
      leaks owners focal outside]
  · rw [Function.update_of_ne same]
    exact phaseProposalReferencePolicy_normal_recall setup mode runtime leaks bounds plan values
      rates normal who past view

/-- The full original counted history law projects to the actual normalized
raw response law. A focal alternative stays literal on both sides; every
foreign private preimage is integrated by the existing history runner. -/
theorem phaseProposalReference_alias_history
    (owners : Finset Player) (focal : Player) (outside : focal ∉ owners)
    (alternative : (app).Policy)
    (covered : ∀ past view response, response ∈ (alternative past view).support →
      response ∈ PhaseCount.onePacketActions runtime leaks bounds focal past view)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler) (fuel : Nat) :
    let normal := phaseCountServiceNormalization setup mode runtime leaks owners
    let stable := fun who past view =>
      phaseCountService_actions_normal_recall setup mode runtime leaks bounds
        normal who who past view
    let players := Function.update reference focal alternative
    let native := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let projected := fun who => (normal.menu menu).restrictPolicy initial horizon scheduler who
      (fun past view => (players who past view).map (normal.action who past view))
    (((menu).information initial horizon scheduler).runBehavioral native fuel).map
        (normal.history menu stable initial horizon scheduler) =
      ((normal.menu menu).information initial horizon scheduler).runBehavioral projected fuel := by
  classical
  intro normal stable players native projected
  have admitted := referenceWith_covered setup mode runtime leaks bounds plan values rates focal
    alternative covered
  have projectedCovered (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
      (response : (app).Action)
      (supported : response ∈ ((players who past view).map
        (normal.action who past view)).support) :
      response ∈ (normal.menu menu).actions who past view := by
    obtain ⟨raw, selected, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact (normal.menu_mem menu who past view _).mpr
      ⟨raw, admitted who past view raw selected, rfl⟩
  have projects (who : Player) (observed : (app).Info) :
      (native who observed).map (normal.choice menu stable initial horizon scheduler who observed) =
        projected who (normal.info who observed) := by
    apply pmf_map_injective Subtype.val_injective
    rw [PMF.map_comp]
    cases observed with
    | none => rfl
    | some pair =>
        rcases pair with ⟨past, view⟩
        change (((menu).restrictPolicy initial horizon scheduler who (players who)
          (some (past, view))).map (fun choice =>
            normal.optionChoice who (some (past, view)) choice.val)) =
          ((normal.menu menu).restrictPolicy initial horizon scheduler who
            (fun past view => (players who past view).map (normal.action who past view))
              (some (normal.recall who past, view))).map Subtype.val
        rw [show (fun choice => normal.optionChoice who (some (past, view)) choice.val) =
          (normal.optionChoice who (some (past, view))) ∘ Subtype.val from rfl,
            ← PMF.map_comp]
        rw [(menu).restrictPolicy_map_val initial horizon scheduler who (players who) past view
          (admitted who past view)]
        rw [(normal.menu menu).restrictPolicy_map_val initial horizon scheduler who _
          (normal.recall who past) view (projectedCovered who (normal.recall who past) view)]
        have unchanged : players who (normal.recall who past) view = players who past view :=
          referenceWith_normal_recall setup mode runtime leaks bounds plan values rates
            owners focal outside alternative who past view
        rw [unchanged]
        simp only [PMF.map_comp, Function.comp_def,
          ReactiveApplication.SubmissionNormalization.optionChoice,
          Option.map_some, normal.action_recall]
  exact normal.runBehavioral_projection menu stable initial horizon scheduler native projected
    projects fuel ((menu).protocol initial horizon scheduler).initHistory

/-- All foreign alias masses are summed while the focal player's FULL raw
input and complete application remain jointly unchanged. The initial PMF is
literal, so original correlated inputs and a hidden scheduler mixture can
be instantiated without replacing their priors or selecting a site per seed. -/
theorem phaseProposalReference_alias_focal_joint
    (owners : Finset Player) (focal : Player) (outside : focal ∉ owners)
    (alternative : (app).Policy)
    (covered : ∀ past view response, response ∈ (alternative past view).support →
      response ∈ PhaseCount.onePacketActions runtime leaks bounds focal past view)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler) (fuel : Nat) :
    let normal := phaseCountServiceNormalization setup mode runtime leaks owners
    let players := Function.update reference focal alternative
    let native := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let projected := fun who => (normal.menu menu).restrictPolicy initial horizon scheduler who
      (fun past view => (players who past view).map (normal.action who past view))
    (((menu).information initial horizon scheduler).runBehavioral native fuel).map
        (fun history => (((menu).information initial horizon scheduler).infoOf focal history.trace,
          history.state.map (fun control => control.execution.application))) =
      (((normal.menu menu).information initial horizon scheduler).runBehavioral projected fuel).map
        (fun history => (((normal.menu menu).information initial horizon scheduler).infoOf
          focal history.trace, history.state.map (fun control => control.execution.application))) :=
  by
  classical
  intro normal players native projected
  let stable := fun who past view =>
    phaseCountService_actions_normal_recall setup mode runtime leaks bounds normal who who past view
  have projection := phaseProposalReference_alias_history setup mode runtime leaks bounds plan
    values rates owners focal outside alternative covered initial horizon scheduler fuel
  rw [← projection, PMF.map_comp]
  congr 1
  funext history
  apply Prod.ext
  · change ((menu).information initial horizon scheduler).infoOf focal history.trace =
      ((normal.menu menu).information initial horizon scheduler).infoOf focal
        (normal.history menu stable initial horizon scheduler history).trace
    rw [normal.history_info menu stable initial horizon scheduler,
      phaseCountServiceNormalization_info_fixed setup mode runtime leaks owners focal outside]
  · change history.state.map (fun control => control.execution.application) =
      (normal.state history.state).map (fun control => control.execution.application)
    cases history.state <;> rfl

end Vegas
