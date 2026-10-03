/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionContinuation
import Vegas.Game.SourceLocalContinuation
import GameTheoryExtensions.Protocol.ContinuationHorizon
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion
import GameTheoryExtensions.Math.Probability.Uniform
import Mathlib.Tactic.DeriveFintype

/-! # Source equilibrium of the late-resolution fixture

The original source has one actual strategic resolution, following two
non-strategic deterministic samples. Opening surely is optimal at its source
information site.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

def sourceAdmission : CommitmentInterface setup.program :=
  CommitmentInterface.forfeiture setup.program

abbrev sourceArena := setup.executionProtocol sourceAdmission
abbrev sourceModel := setup.informationModel sourceAdmission

def sourceStart := setup.initialConfig sourceInitial
def sourceSampled := sampleSuccessor 1 (payload := BaseTy.bool) sourceStart true
def sourceReady := sampleSuccessor 2 (payload := BaseTy.bool) sourceSampled true
def sourceDone (disclose : Bool) :=
  revealSuccessor 3 (.there (.there .here)) sourceReady disclose

inductive SourcePosition where
  | root
  | initialized
  | sampled
  | ready
  | done (disclose : Bool)
  deriving DecidableEq, Fintype

def SourcePosition.state : SourcePosition → setup.ProtocolState
  | .root => none
  | .initialized => some (.inl sourceStart)
  | .sampled => some (.inr (.inl sourceSampled))
  | .ready => some (.inr (.inr (.inl sourceReady)))
  | .done disclose => some (.inr (.inr (.inr (sourceDone disclose))))

theorem source_position_trace : ∀ {state} (_trace : sourceArena.Trace state),
    ∃ position : SourcePosition, state = position.state
  | _, .start => ⟨.root, rfl⟩
  | _, .extend earlier joint legal supported => by
      obtain ⟨position, stateEq⟩ := source_position_trace earlier
      cases stateEq
      cases position with
      | root =>
          change _ ∈ (setup.initialLaw.map _).support at supported
          rw [show setup.initialLaw = PMF.pure sourceInitial from rfl, PMF.pure_map] at supported
          exact ⟨.initialized, (PMF.mem_support_pure_iff _ _).mp supported⟩
      | initialized =>
          have step : sourceArena.step SourcePosition.initialized.state ⟨joint, legal⟩ =
              PMF.pure SourcePosition.sampled.state := by
            simp [sourceArena, Setup.executionProtocol, Setup.protocolStep, SourcePosition.state,
              setup, program, ProtocolState.step, ProtocolState.entry, sourceSampled,
              IExpr.evalDist, simpleExpr, evalLawDistExpr, RationalLaw.denote_pure, PMF.pure_map]
          rw [step] at supported
          exact ⟨.sampled, (PMF.mem_support_pure_iff _ _).mp supported⟩
      | sampled =>
          have step : sourceArena.step SourcePosition.sampled.state ⟨joint, legal⟩ =
              PMF.pure SourcePosition.ready.state := by
            simp [sourceArena, Setup.executionProtocol, Setup.protocolStep, SourcePosition.state,
              setup, program, ProtocolState.step, ProtocolState.entry, sourceReady,
              IExpr.evalDist, simpleExpr, evalLawDistExpr, RationalLaw.denote_pure, PMF.pure_map]
          rw [step] at supported
          exact ⟨.ready, (PMF.mem_support_pure_iff _ _).mp supported⟩
      | ready =>
          have step : sourceArena.step SourcePosition.ready.state ⟨joint, legal⟩ =
              PMF.pure (SourcePosition.done (OwnAction.disclosure (joint owner))).state := by
            simp [sourceArena, Setup.executionProtocol, Setup.protocolStep, SourcePosition.state,
              setup, program, ProtocolState.step, ProtocolState.entry, sourceDone, PMF.pure_map]
          rw [step] at supported
          exact ⟨.done (OwnAction.disclosure (joint owner)),
            (PMF.mem_support_pure_iff _ _).mp supported⟩
      | done disclose => exact (legal.1 trivial).elim

def sourcePolicy (law : PMF Bool) (who : Player) : BehavioralPolicy who setup.program :=
  (fun _ _ => law, PUnit.unit)

theorem sourcePolicy_admitted (law : PMF Bool) (who : Player) :
    (sourcePolicy law who).Admitted setup.program sourceAdmission := trivial

def sourceProfile (law : PMF Bool) : Profile sourceModel.behavioralSignature :=
  fun who => setup.toProtocolBehavioralPolicy sourceAdmission who (sourcePolicy law who)
    (sourcePolicy_admitted law who)

def uniformSourceProfile : Profile sourceModel.behavioralSignature :=
  sourceProfile (PMF.uniformOfFintype Bool)

theorem uniform_source_full (who : Player) (info : sourceModel.InfoState who) :
    FullSupport (uniformSourceProfile who info) := by
  intro choice
  suffices choice.val ∈ ((uniformSourceProfile who info).map Subtype.val).support by
    obtain ⟨other, supported, same⟩ := PMF.support_map .. ▸ this
    exact (Subtype.ext same) ▸ supported
  rw [uniformSourceProfile, sourceProfile, Setup.toProtocolBehavioralPolicy_map_val]
  rcases choice with ⟨action, legal⟩
  change setup.protocolMenu sourceAdmission who info action at legal
  cases info with
  | none => exact (PMF.mem_support_pure_iff _ _).mpr legal
  | some info =>
      rcases info with current | current | current | current
      all_goals fin_cases who; cases action
      all_goals
        have allowed := legal
        dsimp [Setup.protocolMenu, setup, program, ProtocolView.menu, ProtocolView.actor,
          ProtocolView.available] at allowed
        simp_all [setup, program, BehavioralPolicy.protocolAction, sourcePolicy,
          PMF.support_map, owner]

theorem uniform_source_fullyMixed :
    (InformationModel.BehavioralAssessment.ofStrategy uniformSourceProfile).IsFullyMixed :=
  fun who site => uniform_source_full who site.1

instance : setup.FiniteInitialLaw := ⟨by change (PMF.pure sourceInitial).support.Finite; simp⟩

instance : Finite sourceArena.History :=
  uniform_source_fullyMixed.finite_history (setup.protocol_bounded sourceAdmission)
    (fun who info =>
      have := setup.finite_choice (by trivial : setup.program.FiniteBindingTypes)
        sourceAdmission who info
      Set.toFinite _)
    (fun draw => setup.protocolStep_support_finite _ draw.1)

instance : Fintype sourceArena.History := Fintype.ofFinite _

/-- Every source information history at a strategic site has the same actual
source configuration; the deterministic samples introduce no hidden branch. -/
theorem source_active_state (who : Player) (site : sourceModel.InformationSite who)
    (history : sourceModel.InformationHistory who site.1) :
    history.1.state = SourcePosition.ready.state := by
  have active := InformationModel.InformationSite.active sourceModel site history
  obtain ⟨position, same⟩ := source_position_trace history.1.trace
  rw [same] at active
  cases position with
  | ready => exact same
  | root | initialized | sampled | done => cases active

def sourcePayoff (who : Player) (history : sourceArena.History) : ℝ :=
  (setup.protocolReadout history.state).elim 0 (fun source => sourceUtility source who)

theorem source_payoff_le_one (who : Player) (history : sourceArena.History) :
    sourcePayoff who history ≤ 1 := by
  unfold sourcePayoff
  cases setup.protocolReadout history.state with
  | none => norm_num
  | some source =>
      change (if (source.get .here).isSuccess then (1 : ℝ) else 0) ≤ 1
      split <;> norm_num

theorem source_done_payoff (who : Player) (disclose : Bool) :
    (setup.protocolReadout (SourcePosition.done disclose).state).elim 0
      (fun source => sourceUtility source who) = if disclose then 1 else 0 := by
  cases disclose <;> rfl

theorem source_site_depth (who : Player) (site : sourceModel.InformationSite who) :
    InformationModel.InformationSite.CommonDepth sourceModel site 3 := by
  intro history
  have count := setup.protocol_history_length sourceAdmission history.1.trace
  have remaining := congrArg setup.protocolRemaining (source_active_state who site history)
  change setup.protocolRemaining history.1.state = 1 at remaining
  rw [remaining] at count
  change history.1.trace.length + 1 = 4 at count
  omega

/-- Opening at the single source decision yields the declared terminal payoff one. -/
theorem source_opening_value (who : Player) (site : sourceModel.InformationSite who)
    (history : sourceModel.InformationHistory who site.1) :
    expect (sourceModel.runBehavioralFrom (sourceProfile (PMF.pure true)) 1 history.1)
      (sourcePayoff who) = 1 := by
  have same := source_active_state who site history
  have active := InformationModel.InformationSite.active sourceModel site history
  have running : ¬ sourceArena.terminal history.1.state := by
    rw [same]
    exact id
  have step := setup.run_one_choice_state sourceAdmission (sourceProfile (PMF.pure true))
    history.1 who running active
  have law : (sourceModel.runBehavioralFrom (sourceProfile (PMF.pure true)) 1 history.1).map
      History.state = PMF.pure (SourcePosition.done true).state := by
    rw [step]
    change _ = PMF.pure (SourcePosition.done true).state
    rw [show (sourceProfile (PMF.pure true) who (sourceModel.infoOf who history.1.trace)).bind
        (fun choice => setup.protocolStep history.1.state
          (fun player => if player = who then choice.1 else none)) =
        ((sourceProfile (PMF.pure true) who (sourceModel.infoOf who history.1.trace)).map
          Subtype.val).bind (fun choice => setup.protocolStep history.1.state
            (fun player => if player = who then choice else none)) from
        (PMF.bind_map
          (sourceProfile (PMF.pure true) who (sourceModel.infoOf who history.1.trace))
          Subtype.val (fun choice => setup.protocolStep history.1.state
            (fun player => if player = who then choice else none))).symm]
    rw [sourceProfile, Setup.toProtocolBehavioralPolicy_map_val]
    have observed : sourceModel.infoOf who history.1.trace =
        setup.protocolObserve who history.1.state :=
      setup.protocol_info sourceAdmission who history.1.trace
    rw [observed]
    rw [same]
    have own : who = owner := Subsingleton.elim _ _
    subst who
    simp [setup, program, SourcePosition.state, Setup.protocolObserve, ProtocolState.observe,
      BehavioralPolicy.protocolAction, sourcePolicy, Setup.protocolStep,
      ProtocolState.step, ProtocolState.entry, sourceDone, PMF.pure_map, OwnAction.disclosure]
  let readout (state : setup.ProtocolState) : ℝ :=
    (setup.protocolReadout state).elim 0 (fun source => sourceUtility source who)
  calc
    _ = expect ((sourceModel.runBehavioralFrom (sourceProfile (PMF.pure true))
        1 history.1).map History.state) readout :=
      (expect_map (fun last : sourceArena.History => last.state)
        (sourceModel.runBehavioralFrom (sourceProfile (PMF.pure true)) 1 history.1)
        readout).symm
    _ = readout (SourcePosition.done true).state := by rw [law, expect_pure]
    _ = 1 := source_done_payoff who true

theorem sourceCertificate : sourceArena.WellFoundedHistories :=
  sourceArena.wellFoundedHistories_of_fintype

theorem source_opening_rational (assessment : sourceModel.BehavioralAssessment)
    (strategy : assessment.strategy = sourceProfile (PMF.pure true)) :
    assessment.IsSequentiallyRationalFor (fun who site =>
      assessment.truncatedContinuationContext site (sourcePayoff who) 4) := by
  intro who site
  have context := assessment.truncatedContinuationContext_remaining sourceModel 4
    (setup.protocol_bounded sourceAdmission) who site 3 (source_site_depth who site)
    (sourcePayoff who)
  change assessment.truncatedContinuationContext site (sourcePayoff who) 1 = _ at context
  change (assessment.truncatedContinuationContext site (sourcePayoff who) 4).IsLocallyOptimal
    Set.univ (assessment.strategy who)
  rw [← context]
  refine (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    (fun _ _ => payoffIntegrable_of_finite _ _)).mpr fun alternative _ => ?_
  have baseline : (assessment.truncatedContinuationContext site (sourcePayoff who) 1).value
      (assessment.strategy who) = 1 := by
    rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
      Profile.update_eq_self, strategy, expect_bind_of_finite]
    calc
      _ = expect (assessment.belief who site) (fun _ => (1 : ℝ)) := by
        apply expect_congr_on_support
        intro history _
        exact source_opening_value who site history
      _ = 1 := expect_constant _ _
  rw [baseline]
  exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1
    (fun history _ => source_payoff_le_one who history)

/-- The concrete source admits a sequential equilibrium that surely opens its
single strategic resolution, for the declared source payoff. Consistency is
obtained from genuinely fully mixed source strategies. -/
theorem exists_source_opening_equilibrium :
    ∃ assessment : sourceModel.BehavioralAssessment,
      assessment.strategy = sourceProfile (PMF.pure true) ∧
      assessment.IsSequentialEquilibrium (setup.decision_antichain sourceAdmission)
        sourceCertificate sourcePayoff := by
  obtain ⟨assessment, strategy, consistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion
      (InformationModel.BehavioralAssessment.ofStrategy uniformSourceProfile)
      uniform_source_fullyMixed (setup.decision_antichain sourceAdmission)
      (sourceProfile (PMF.pure true))
  refine ⟨assessment, strategy, ?_⟩
  apply (assessment.isSequentialEquilibrium_iff_truncated_of_bounded sourceModel
    (setup.decision_antichain sourceAdmission) sourceCertificate
    (setup.protocol_bounded sourceAdmission) sourcePayoff).mpr
  exact ⟨source_opening_rational assessment strategy, consistent⟩

end Vegas.LateResolutionService
