/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ExclusionGame
import Vegas.Source.FailedBindingDeviation
import Vegas.Source.InitialState
import Vegas.Source.Forfeit
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Voluntary failure has the exclusion payoff at every source site

A legal failed binding creates an irrevocable failed-binding obligation, and
withholding creates an irrevocable publication failure. The obligation persists
through every source step. Thus choosing failure at any exclusion-game decision
site, including sites outside intended play, gives the player its fixed
exclusion payoff under every terminal continuation.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- Every legal failure action immediately creates a persistent failed-reveal
obligation. No intended-play or value-admission invariant is needed. -/
theorem owesFailure_of_failure_action (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (Γ.map Prod.fst).Nodup →
    (admission : CommitmentInterface program) → (state : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → (action : OwnAction Player L) →
    joint who = some action →
    ProtocolView.actor who program (observe who program state) = some who →
    action ∈ ProtocolView.available who program admission (observe who program state) →
    action.IsFailure →
    ∀ target ∈ (step program state joint).support, OwesFailure who program target
  | _, _, .ret _, _, _, _, _, _, _, acts, _, _, _, _ => by
      simp [ProtocolView.actor] at acts
  | _, _, .sample name fresh law next, unique, admission, state, joint, action, chosen, acts,
      available, failure, target, reached => by
      cases state with
      | inl config => simp [ProtocolView.actor, observe] at acts
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact owesFailure_of_failure_action who next (List.nodup_cons.mpr ⟨fresh, unique⟩)
            admission rest joint action chosen acts available failure after supported
  | _, _, .commit (payload := payload) name owner fresh guard next, unique, admission, state,
      joint, action, chosen, acts, available, failure, target, reached => by
      cases state with
      | inl config =>
          have same : owner = who := by simpa [ProtocolView.actor, observe] using acts
          subst same
          obtain ⟨choice, _, rfl⟩ := available
          have failed : choice = .failure := failure
          subst choice
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          rw [chosen, OwnAction.binding_commit]
          right
          exact failedBinding_entry next _ (Config.failedBinding_commit config unique fresh
            guard _)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact owesFailure_of_failure_action who next (List.nodup_cons.mpr ⟨fresh, unique⟩)
            (fun site => admission (some site)) rest joint action chosen acts available failure
            after supported
  | _, _, .reveal published owner name fresh source policy next, unique, admission, state,
      joint, action, chosen, acts, available, failure, target, reached => by
      cases state with
      | inl config =>
          have same : owner = who := by simpa [ProtocolView.actor, observe] using acts
          subst same
          obtain ⟨disclose, rfl⟩ := available
          have withheld : disclose = false := failure
          subst disclose
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          rw [chosen]
          left
          refine Or.inl ⟨rfl, ?_⟩
          rw [base_entry]
          simp [revealSuccessor, OwnAction.disclosure]
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases owesFailure_of_failure_action who next (List.nodup_cons.mpr ⟨fresh, unique⟩)
              admission rest joint action chosen acts available failure after supported with
            indebted | failed
          · exact Or.inl (Or.inr indebted)
          · exact Or.inr (Or.inr failed)

end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- The immediate successor of a voluntarily failed exclusion-game event owes
the acting player a failed reveal. -/
theorem exclusion_failure_step_owes (who : Player)
    (state : setup.ProtocolState) (joint : Player → Option (OwnAction Player L))
    (legal : setup.exclusionProtocol.Legal state joint)
    {action : OwnAction Player L} (chosen : joint who = some action)
    (failure : action.IsFailure) (target : setup.ProtocolState)
    (reached : target ∈ (setup.exclusionProtocol.step state ⟨joint, legal⟩).support) :
    target.elim False (ProtocolState.OwesFailure who setup.program) := by
  have permitted := (restrictAvailable.legal legal).2 who
  rw [chosen] at permitted
  cases state with
  | none => exact permitted.1.elim
  | some state =>
      change target ∈ ((ProtocolState.step setup.program state joint).map some).support at reached
      obtain ⟨after, supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact ProtocolState.owesFailure_of_failure_action who setup.program setup.namesNodup
        (CommitmentInterface.forfeiture setup.program) state joint action chosen permitted.1
        permitted.2 failure after supported

/-- At any decision site of the full source exclusion game, choosing a failure
action makes every terminal continuation record a failed reveal of its owner. -/
theorem exclusion_failure_failedReveals_pos [Fintype Player]
    (certificate : setup.exclusionProtocol.WellFoundedHistories)
    [∀ who, DecidableEq (setup.exclusionModel.InfoState who)]
    (profile : ∀ who, setup.exclusionModel.BehavioralPolicy who)
    (who : Player) (site : setup.exclusionModel.InformationSite who)
    (action : setup.exclusionModel.Choice who site.1)
    {chosenAction : OwnAction Player L} (selected : action.1 = some chosenAction)
    (failure : chosenAction.IsFailure)
    (history : setup.exclusionModel.InformationHistory who site.1) :
    ∀ final ∈ (setup.exclusionModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.exclusionModel.behavioralSignature) profile who
          ((profile who).commit site.1 action)) history.1).support,
      ∃ terminal, setup.protocolReadout final.state = some terminal ∧
        1 ≤ failedReveals setup.program who (publicOutcome setup.program terminal) := by
  intro final supported
  let model := setup.exclusionModel
  let deviating := Profile.update (sig := model.behavioralSignature) profile who
    ((profile who).commit site.1 action)
  have active := InformationModel.InformationSite.active (M := model) site history
  have running : ¬ setup.exclusionProtocol.terminal history.1.state := by
    intro stopped
    cases current : history.1.state with
    | none => rw [current] at active; exact active.elim
    | some state =>
        rw [current] at active stopped
        have inactive := ProtocolState.terminal_actor_none who setup.program state stopped
        cases inactive.symm.trans active
  change final ∈ (model.runBehavioralTerminalFrom certificate deviating history.1).support
    at supported
  rw [InformationModel.runBehavioralTerminalFrom_of_not_terminal _ _ _ running,
    PMF.support_bind] at supported
  obtain ⟨draw, drawn, continued⟩ := Set.mem_iUnion₂.mp supported
  rw [PMF.mem_support_bindOnSupport_iff] at continued
  obtain ⟨target, realized, child⟩ := continued
  have chosen : draw.1 who = some chosenAction := by
    have marginal : draw.1 ∈ ((model.behavioralJoint deviating history.1.trace running).map
        Subtype.val).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
    rw [model.behavioralJoint_map_val, independentProduct_support_iff] at marginal
    have own := marginal who
    rw [history.2] at own
    have same : draw.1 who = action.1 := by
      simpa [deviating, Profile.update_same, InformationModel.BehavioralPolicy.commit_self,
        PMF.pure_map] using own
    exact same.trans selected
  have owed := setup.exclusion_failure_step_owes who history.1.state draw.1 draw.2 chosen failure
    target realized
  let debt : setup.ProtocolState → Prop := fun state =>
    state.elim False (ProtocolState.OwesFailure who setup.program)
  have closed : ∀ state joint (legal : setup.exclusionProtocol.Legal state joint) target,
      debt state → target ∈ (setup.exclusionProtocol.step state ⟨joint, legal⟩).support →
        debt target := by
    intro state joint legal target holds reached
    cases state with
    | none => exact holds.elim
    | some state =>
        change target ∈ ((ProtocolState.step setup.program state joint).map some).support at reached
        obtain ⟨after, supported, rfl⟩ := PMF.support_map .. ▸ reached
        exact ProtocolState.owesFailure_step who setup.program state joint after holds supported
  have finalOwed := model.runBehavioralTerminalFrom_support_closed certificate deviating debt
    closed _ owed final child
  have stopped := model.runBehavioralTerminalFrom_support_terminal certificate deviating _ final
    child
  cases finalState : final.state with
  | none => rw [finalState] at finalOwed; exact finalOwed.elim
  | some state =>
      rw [finalState] at finalOwed stopped
      obtain ⟨terminal, read⟩ := ProtocolState.exists_readout_of_terminal setup.program state
        stopped
      exact ⟨terminal, read, ProtocolState.failedReveals_pos_of_owesFailure who setup.program state
        finalOwed read⟩

/-- Every terminal payoff after a locally chosen failure is the fixed exclusion
payoff, at arbitrary full exclusion-game sites and under arbitrary opponents. -/
theorem exclusion_failure_continuation_payoff [Fintype Player]
    (certificate : setup.exclusionProtocol.WellFoundedHistories)
    [∀ who, DecidableEq (setup.exclusionModel.InfoState who)]
    (profile : ∀ who, setup.exclusionModel.BehavioralPolicy who)
    (who : Player) (site : setup.exclusionModel.InformationSite who)
    (action : setup.exclusionModel.Choice who site.1)
    {chosenAction : OwnAction Player L} (selected : action.1 = some chosenAction)
    (failure : chosenAction.IsFailure)
    (history : setup.exclusionModel.InformationHistory who site.1)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    ∀ final ∈ (setup.exclusionModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.exclusionModel.behavioralSignature) profile who
          ((profile who).commit site.1 action)) history.1).support,
      ∃ terminal, setup.protocolReadout final.state = some terminal ∧
        exclusionUtility setup.program excludedPayoff utility
          (setup.parameterOutcome parameter terminal) who = excludedPayoff who := by
  intro final supported
  obtain ⟨terminal, read, failed⟩ := setup.exclusion_failure_failedReveals_pos certificate profile
    who site action selected failure history final supported
  exact ⟨terminal, read, exclusionUtility_of_failedReveals_pos _ _ _ failed⟩

/-- Committing locally to a failure action has exactly the exclusion value at
any source exclusion-game information site, under arbitrary assessment beliefs. -/
theorem exclusion_failure_context_value [Fintype Player]
    (certificate : setup.exclusionProtocol.WellFoundedHistories)
    [∀ who, DecidableEq (setup.exclusionModel.InfoState who)]
    (assessment : setup.exclusionModel.BehavioralAssessment)
    (who : Player) (site : setup.exclusionModel.InformationSite who)
    (action : setup.exclusionModel.Choice who site.1)
    {chosenAction : OwnAction Player L} (selected : action.1 = some chosenAction)
    (failure : chosenAction.IsFailure)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    (assessment.continuationContext certificate site (fun final =>
      (setup.protocolReadout final.state).elim 0 (fun terminal =>
        exclusionUtility setup.program excludedPayoff utility
          (setup.parameterOutcome parameter terminal) who))).value
      ((assessment.strategy who).commit site.1 action) = excludedPayoff who := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value]
  let continuation := (assessment.belief who site).bind fun history =>
    setup.exclusionModel.runBehavioralTerminalFrom certificate
      (Profile.update (sig := setup.exclusionModel.behavioralSignature) assessment.strategy who
        ((assessment.strategy who).commit site.1 action)) history.1
  change expect continuation _ = excludedPayoff who
  calc
    _ = expect continuation (fun _ => excludedPayoff who) := by
      apply expect_congr_on_support
      intro final supported
      change final ∈ ((assessment.belief who site).bind _).support at supported
      rw [PMF.support_bind] at supported
      obtain ⟨history, _, continued⟩ := Set.mem_iUnion₂.mp supported
      obtain ⟨terminal, read, payoff⟩ := setup.exclusion_failure_continuation_payoff certificate
        assessment.strategy who site action selected failure history parameter utility
        excludedPayoff final continued
      rw [read]
      exact payoff
    _ = _ := expect_constant _ _

end Setup

end Vegas.SourceProgram
