/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSourceEquilibrium

/-! # Failed bindings in the concrete source game

The full forfeiture interface also permits Bob to bind failure. This additional
action forces his only publication to fail and yields payoff minus the forfeit.
Every value-only continuation is at least that valuable. Consequently each
value-only withholding equilibrium extends to this full source interface,
preserving its terminal-store and payoff law. This argument uses the particular
three-instruction program, rather than a theorem for arbitrary source programs.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSource

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

abbrev forfeitingProtocol :=
  setup.executionProtocol (CommitmentInterface.forfeiture setup.program)

abbrev forfeitingModel :=
  setup.informationModel (CommitmentInterface.forfeiture setup.program)

theorem forfeiting_bounded : forfeitingProtocol.BoundedHorizon 4 :=
  setup.protocol_bounded _

def forfeitingPayoff (reward forfeit : ℝ) (who : Player)
    (history : forfeitingProtocol.History) : ℝ :=
  (setup.protocolReadout history.state).elim 0 (fun terminal =>
    forfeitUtility setup.program forfeit (grossUtility reward)
      (setup.parameterOutcome parameter terminal) who)

def forfeitingTerminalLaw (reward forfeit : ℝ)
    (profile : ∀ who, forfeitingModel.BehavioralPolicy who) :=
  (forfeitingModel.runBehavioralTerminalFrom
      forfeiting_bounded.wellFoundedHistories profile forfeitingProtocol.initHistory).map
    (fun final => (setup.protocolReadout final.state,
      fun who => forfeitingPayoff reward forfeit who final))

private theorem values_available_subset (who : Player) (view : setup.ProtocolView who) :
    withholdingModel.menu who view ⊆ forfeitingModel.menu who view := by
  cases view with
  | none => exact fun _ allowed => allowed
  | some view =>
      cases view with
      | inl current => exact fun _ allowed => allowed
      | inr view =>
          cases view with
          | inl current =>
              intro choice allowed
              cases choice with
              | none => exact allowed
              | some action =>
                  obtain ⟨active, publication, admitted, rfl⟩ := allowed
                  refine ⟨active, publication, ?_, rfl⟩
                  cases publication with
                  | failure => cases admitted
                  | success value => trivial
          | inr view => exact fun _ allowed => allowed

private theorem values_state_available_subset (state : setup.ProtocolState) (who : Player) :
    withholdingProtocol.available state who ⊆ forfeitingProtocol.available state who := by
  cases state with
  | none => exact fun _ impossible => impossible.elim
  | some state =>
      cases state with
      | inl current => exact fun _ allowed => allowed
      | inr state =>
          cases state with
          | inl current =>
              rintro action ⟨publication, admitted, rfl⟩
              refine ⟨publication, ?_, rfl⟩
              cases publication with
              | failure => cases admitted
              | success value => trivial
          | inr state => exact fun _ allowed => allowed

private theorem values_progress (state : setup.ProtocolState)
    (running : ¬ forfeitingProtocol.terminal state) :
    ∃ joint, IsLegalJoint (forfeitingProtocol.active state)
      (withholdingProtocol.available state) joint :=
  withholdingProtocol.progress state running

private theorem values_menu_adequate (who : Player) {state : setup.ProtocolState}
    (trace : (forfeitingProtocol.restrictAvailable withholdingProtocol.available
      values_state_available_subset values_progress).Trace state)
    (choice : Option (OwnAction Player simpleExpr)) :
    choice ∈ withholdingModel.menu who
        (forfeitingModel.infoOf who (restrictAvailable.trace trace)) ↔
      LegalOption (forfeitingProtocol.restrictAvailable withholdingProtocol.available
        values_state_available_subset values_progress) state who choice := by
  have known : forfeitingModel.infoOf who (restrictAvailable.trace trace) =
      setup.protocolObserve who state := setup.protocol_info _ who _
  rw [known]
  change setup.protocolMenu (CommitmentInterface.values setup.program) who
    (setup.protocolObserve who state) choice ↔ LegalOption withholdingProtocol state who choice
  cases state <;> cases choice <;> simp [withholdingProtocol, Setup.protocolMenu,
    Setup.protocolObserve, SourceProgram.ProtocolView.menu, LegalOption, Setup.executionProtocol]

/-- Value-only bindings are an actual menu restriction of the full forfeiture
source interface. Both interfaces have the same source states and transitions. -/
def withholdingRestriction : withholdingModel.ActionRestriction forfeitingModel :=
  forfeitingModel.menuRestriction (available := withholdingProtocol.available)
    (included := values_state_available_subset) (progress := values_progress)
    withholdingModel.menu values_menu_adequate values_available_subset

private theorem extra_choice (who : Player) (site : withholdingModel.InformationSite who)
    (history : withholdingModel.InformationHistory who site.1)
    (action : forfeitingModel.Choice who (withholdingRestriction.site who site).1)
    (extra : action ∉ Set.range (withholdingRestriction.choice who site.1)) :
    ∃ config : Config Player simpleExpr ((2, .publication .bool) :: initialCtx),
      who = bob ∧ history.1.state = some (.inr (.inl config)) ∧
        action.1 = some (.commit bob 3 (.range 0 5) .failure) := by
  have missing : action.1 ∉ withholdingModel.menu who site.1 :=
    forfeitingModel.menuRestriction_extra_choice withholdingModel.menu values_menu_adequate
      values_available_subset who site.1 action extra
  have known : site.1 = setup.protocolObserve who history.1.state :=
    history.2.symm.trans (setup.protocol_info _ who history.1.trace)
  rw [known] at missing
  have allowed := action.2
  change action.1 ∈ forfeitingModel.menu who site.1 at allowed
  rw [known] at allowed
  cases positionEq : history.1.state with
  | none => rw [positionEq] at allowed missing; exact (missing allowed).elim
  | some position =>
      rw [positionEq] at allowed missing
      cases position with
      | inl current => exact (missing allowed).elim
      | inr position =>
          cases position with
          | inl config =>
              cases chosen : action.1 with
              | none => exact (missing (chosen ▸ allowed)).elim
              | some current =>
                  rw [chosen] at allowed missing
                  obtain ⟨active, publication, _, encoded⟩ := allowed
                  have same : bob = who := Option.some.inj active
                  subst who
                  cases publication with
                  | success value =>
                      exact (missing ⟨rfl, .success value, trivial, encoded⟩).elim
                  | failure =>
                      exact ⟨config, rfl, rfl, congrArg some encoded⟩
          | inr position => exact (missing allowed).elim

private theorem bob_failedReveals_le_one (outcome : PublicOutcome program) :
    failedReveals program bob outcome ≤ 1 := by
  simp only [failedReveals, revealCells, program]
  simp only [List.filter_cons, List.filter_nil, show alice ≠ bob by decide, decide_false,
    Bool.false_and, Bool.false_eq_true, ite_false, decide_true, Bool.true_and]
  split <;> simp

private theorem bob_payoff_lower (reward : ℝ) {forfeit : ℝ} (nonnegative : 0 ≤ forfeit)
    (history : withholdingProtocol.History) :
    -forfeit ≤ withholdingPayoff reward forfeit bob history := by
  unfold withholdingPayoff
  cases read : setup.protocolReadout history.state with
  | none => simpa using nonnegative
  | some terminal =>
      have gross := (bob_gross_bounds reward (setup.parameterOutcome parameter terminal)).1
      have count := bob_failedReveals_le_one (publicOutcome program terminal)
      have cast : (failedReveals program bob (publicOutcome program terminal) : ℝ) ≤ 1 := by
        exact_mod_cast count
      change -forfeit ≤ grossUtility reward (setup.parameterOutcome parameter terminal) bob -
        forfeit * failedReveals program bob (publicOutcome program terminal)
      have bounded := mul_le_mul_of_nonneg_left cast nonnegative
      linarith

private def BobFailed : setup.ProtocolState → Prop
  | none => False
  | some (.inl _) => False
  | some (.inr (.inl _)) => False
  | some (.inr (.inr (.inl config))) => config.state.get .here = .failure
  | some (.inr (.inr (.inr config))) => config.state.get .here = .failure

private theorem bob_failed_step (state : setup.ProtocolState)
    (joint : Player → Option (OwnAction Player simpleExpr))
    (legal : forfeitingProtocol.Legal state joint) (target : setup.ProtocolState)
    (failed : BobFailed state)
    (realized : target ∈ (forfeitingProtocol.step state ⟨joint, legal⟩).support) :
    BobFailed target := by
  cases state with
  | none => exact failed.elim
  | some state =>
      cases state with
      | inl current => exact failed.elim
      | inr state =>
          cases state with
          | inl current => exact failed.elim
          | inr state =>
              cases state with
              | inl config =>
                  have targetEq : target = some (.inr (.inr (.inr
                      (revealSuccessor 4 .here config (OwnAction.disclosure (joint bob)))))) := by
                    change target ∈ ((ProtocolState.step program
                      (.inr (.inr (.inl config))) joint).map some).support at realized
                    simpa [ProtocolState.step, program, ProtocolState.entry] using realized
                  subst target
                  change (revealSuccessor 4 .here config
                    (OwnAction.disclosure (joint bob))).state.get .here = .failure
                  change config.state.get .here = .failure at failed
                  simp [revealSuccessor, failed]
              | inr config => exact legal.1 trivial |>.elim

private theorem bob_failure_payoff (reward forfeit : ℝ)
    (terminal : State simpleExpr program.terminalCtx)
    (failed : terminal.get bobPublication = .failure) :
    forfeitUtility program forfeit (grossUtility reward)
      (setup.parameterOutcome parameter terminal) bob = -forfeit := by
  have published : bobResult (publicOutcome program terminal) = .failure := failed
  have count : failedReveals program bob (publicOutcome program terminal) = 1 := by
    simp only [failedReveals, revealCells, program, List.filter_cons, List.filter_nil]
    simp only [show alice ≠ bob by decide, decide_false, Bool.false_and,
      Bool.false_eq_true, ite_false]
    change (if !(terminal.get bobPublication).isSuccess then [RevealCell.mk bob _ _ _]
      else []).length = 1
    rw [failed]
    rfl
  change grossUtility reward (parameter (program.initialState terminal),
    publicOutcome program terminal) bob -
      forfeit * failedReveals program bob (publicOutcome program terminal) = -forfeit
  rw [count]
  simp [grossUtility, published]

open Classical in
private theorem extra_choice_payoff (reward forfeit : ℝ)
    (profile : ∀ who, forfeitingModel.BehavioralPolicy who)
    (who : Player) (site : withholdingModel.InformationSite who)
    (action : forfeitingModel.Choice who (withholdingRestriction.site who site).1)
    (extra : action ∉ Set.range (withholdingRestriction.choice who site.1))
    (history : withholdingModel.InformationHistory who site.1) :
    expect (forfeitingModel.runBehavioralTerminalFrom forfeiting_bounded.wellFoundedHistories
      (Profile.update (sig := forfeitingModel.behavioralSignature) profile who
        ((profile who).commit (withholdingRestriction.site who site).1 action))
      (withholdingRestriction.history history.1)) (forfeitingPayoff reward forfeit who) =
        -forfeit := by
  classical
  have : Finite forfeitingProtocol.History := setup.finite_history finiteBindingTypes _
  obtain ⟨config, rfl, state, encoded⟩ := extra_choice who site history action extra
  let deviating := Profile.update (sig := forfeitingModel.behavioralSignature) profile bob
    ((profile bob).commit (withholdingRestriction.site bob site).1 action)
  have active : forfeitingProtocol.active history.1.state bob :=
    InformationModel.InformationSite.active (M := withholdingModel) site history
  have running := setup.not_terminal_of_active _ active
  rw [← expect_constant (forfeitingModel.runBehavioralTerminalFrom
    forfeiting_bounded.wellFoundedHistories deviating
    (withholdingRestriction.history history.1)) (-forfeit)]
  apply expect_congr_on_support
  intro final supported
  change final ∈ (forfeitingModel.runBehavioralTerminalFrom
    forfeiting_bounded.wellFoundedHistories deviating
    (withholdingRestriction.history history.1)).support at supported
  rw [InformationModel.runBehavioralTerminalFrom_of_not_terminal _ _ _ running,
    PMF.support_bind] at supported
  obtain ⟨draw, drawn, continued⟩ := Set.mem_iUnion₂.mp supported
  rw [PMF.mem_support_bindOnSupport_iff] at continued
  obtain ⟨target, realized, child⟩ := continued
  have chosen : draw.1 bob = action.1 := by
    have marginal : draw.1 ∈ ((forfeitingModel.behavioralJoint deviating
        (withholdingRestriction.history history.1).trace running).map Subtype.val).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
    rw [forfeitingModel.behavioralJoint_map_val, independentProduct_support_iff] at marginal
    have own := marginal bob
    have info : forfeitingModel.infoOf bob (withholdingRestriction.history history.1).trace =
        (withholdingRestriction.site bob site).1 :=
      (withholdingRestriction.observed bob history.1).trans
        (congrArg (withholdingRestriction.information bob) history.2)
    rw [info] at own
    simpa [deviating, Profile.update_same, InformationModel.BehavioralPolicy.commit_self,
      PMF.pure_map] using own
  have failed : BobFailed target := by
    have decoded : OwnAction.binding (L := simpleExpr) bob 3 (.range 0 5) (draw.1 bob) =
        .failure := by
      rw [chosen, encoded]
      exact OwnAction.binding_commit _ _ _ _
    have targetEq : target = some (.inr (.inr (.inl
        (commitSuccessor 3 answerGuard config .failure)))) := by
      change target ∈ (setup.protocolStep history.1.state draw.1).support at realized
      rw [state] at realized
      simpa [Setup.protocolStep, setup, ProtocolState.step, program, decoded,
        ProtocolState.entry] using realized
    subst target
    rfl
  have finalFailed := forfeitingModel.runBehavioralTerminalFrom_support_closed
    forfeiting_bounded.wellFoundedHistories deviating BobFailed bob_failed_step
    _ failed final child
  have stopped := forfeitingModel.runBehavioralTerminalFrom_support_terminal
    forfeiting_bounded.wellFoundedHistories deviating _ final child
  cases finalState : final.state with
  | none => rw [finalState] at finalFailed; exact finalFailed.elim
  | some position =>
      rw [finalState] at finalFailed stopped
      cases position with
      | inl current => exact stopped.elim
      | inr position =>
          cases position with
          | inl current => exact stopped.elim
          | inr position =>
              cases position with
              | inl current => exact stopped.elim
              | inr terminal =>
                  unfold forfeitingPayoff
                  rw [finalState]
                  change forfeitUtility program forfeit (grossUtility reward)
                    (setup.parameterOutcome parameter terminal.state) bob = -forfeit
                  exact bob_failure_payoff reward forfeit terminal.state finalFailed

/-- Every value-only withholding equilibrium of this concrete program extends
to the interface admitting failed bindings, for any nonnegative forfeit. -/
theorem withholding_equilibrium_preserved_under_forfeiture (reward : ℝ) {forfeit : ℝ}
    (nonnegative : 0 ≤ forfeit) (source : withholdingModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium (setup.decision_antichain _)
      withholding_bounded.wellFoundedHistories (withholdingPayoff reward forfeit)) :
    ∃ target : forfeitingModel.BehavioralAssessment,
      target.IsSequentialEquilibrium (setup.decision_antichain _)
        forfeiting_bounded.wellFoundedHistories (forfeitingPayoff reward forfeit) ∧
      forfeitingTerminalLaw reward forfeit target.strategy =
        withholdingTerminalLaw reward forfeit source.strategy := by
  classical
  have : Finite forfeitingProtocol.History := setup.finite_history finiteBindingTypes _
  have : Finite withholdingProtocol.History := setup.finite_history finiteBindingTypes _
  let comparator (who : Player) (site : withholdingModel.InformationSite who)
      (_ : forfeitingModel.Choice who (withholdingRestriction.site who site).1) :
      PMF (withholdingModel.Choice who site.1) := PMF.pure (Classical.arbitrary _)
  obtain ⟨target, sequential, _, _, _, jointLaw⟩ :=
    withholdingRestriction.sequentialEquilibrium_extends_of_comparator_unclocked
      (setup.decision_antichain _) withholding_bounded.wellFoundedHistories
      forfeiting_bounded.wellFoundedHistories (setup.uniformReference finiteBindingTypes _)
      (setup.uniformReference_fullyMixed finiteBindingTypes _) (setup.protocol_decisionRecall _)
      (withholdingPayoff reward forfeit) (forfeitingPayoff reward forfeit)
      (fun _ _ => rfl) comparator (by
        intro sourceProfile targetProfile _ who site action extra history
        rw [extra_choice_payoff reward forfeit targetProfile who site action extra history]
        obtain ⟨_, rfl, _, _⟩ := extra_choice who site history action extra
        rw [← expect_constant (withholdingModel.runBehavioralTerminalFrom
          withholding_bounded.wellFoundedHistories
          (Profile.update (sig := withholdingModel.behavioralSignature) sourceProfile bob
            ((sourceProfile bob).withLaw site.1 (comparator bob site action))) history.1)
          (-forfeit)]
        exact expect_mono (fun final _ => bob_payoff_lower reward nonnegative final)
          (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)) source equilibrium
  refine ⟨target, sequential, ?_⟩
  have projected := congrArg (PMF.map fun pair => (setup.protocolReadout pair.1.state, pair.2))
    jointLaw
  have state (history : withholdingProtocol.History) :
      (withholdingRestriction.history history).state = history.state := rfl
  change forfeitingTerminalLaw reward forfeit target.strategy =
    withholdingTerminalLaw reward forfeit source.strategy
  simpa only [forfeitingTerminalLaw, withholdingTerminalLaw, PMF.map_comp, Function.comp_def,
    state]
    using projected.symm

/-- Every intended equilibrium of this initialized program has a full
forfeiture-source equilibrium with the same terminal store and payoffs. -/
theorem intended_equilibrium_preserved_under_forfeiture {reward forfeit : ℝ}
    (nonnegative : 0 ≤ reward) (coversAlice : reward ≤ forfeit) (coversBob : 1 ≤ forfeit)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium
      intended_decisionRecall.decisionInformationAntichain
      setup.intended_bounded.wellFoundedHistories (intendedPayoff reward)) :
    ∃ target : forfeitingModel.BehavioralAssessment,
      target.IsSequentialEquilibrium (setup.decision_antichain _)
        forfeiting_bounded.wellFoundedHistories (forfeitingPayoff reward forfeit) ∧
      forfeitingTerminalLaw reward forfeit target.strategy =
        intendedTerminalLaw reward intended.strategy := by
  obtain ⟨source, sourceEquilibrium, _, sourceLaw⟩ :=
    intended_equilibrium_preserved_under_withholding nonnegative coversAlice coversBob
      intended equilibrium
  obtain ⟨target, targetEquilibrium, sameLaw⟩ :=
    withholding_equilibrium_preserved_under_forfeiture reward (by linarith)
      source sourceEquilibrium
  exact ⟨target, targetEquilibrium, sameLaw.trans sourceLaw⟩

/-- The initialized Safe terminal-store and payoff law is a sequential
equilibrium outcome even when both bindings and publications can fail. -/
theorem exists_forfeiting_equilibrium_with_safe_law {reward forfeit : ℝ}
    (nonnegative : 0 ≤ reward) (coversAlice : reward ≤ forfeit) (coversBob : 1 ≤ forfeit) :
    ∃ assessment : forfeitingModel.BehavioralAssessment,
      assessment.IsSequentialEquilibrium (setup.decision_antichain _)
        forfeiting_bounded.wellFoundedHistories (forfeitingPayoff reward forfeit) ∧
      forfeitingTerminalLaw reward forfeit assessment.strategy = safeTerminalLaw reward := by
  obtain ⟨source, equilibrium, law⟩ :=
    exists_withholding_equilibrium_with_safe_law nonnegative coversAlice coversBob
  obtain ⟨target, sequential, sameLaw⟩ :=
    withholding_equilibrium_preserved_under_forfeiture reward (by linarith) source equilibrium
  exact ⟨target, sequential, sameLaw.trans law⟩

end Vegas.Examples.LateOpeningRuntimeSource
