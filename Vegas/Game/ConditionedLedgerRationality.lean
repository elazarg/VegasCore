module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ConditionedLedgerAssessment
public import Vegas.Game.SourceServiceFacts
public import Interaction.ReactiveResponseEvaluation
public import GameTheory.Protocol.BehavioralTerminal

@[expose] public section

/-! # Whole-policy rationality on observed ledger components -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr} [IExpr.ResultTypes L]
    {setup : Setup (Player := Player) (L := L)}
    {Signal : Type*} {signal : State L setup.context → Signal}
    {timeouts : EventTimeouts setup.informationGraph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
    {scheduler : (application setup timeouts leaks).Scheduler} {horizon : Nat}


variable (menu : (application setup timeouts leaks).ResponseMenu)

local notation "App" => application setup timeouts leaks
local notation "GlobalLaw" => Vegas.initialLaw setup
local notation "componentLaw" => fun key => Vegas.initialLaw (setup.conditionInitial signal key)

private theorem context_state_law {init : PMF (App).State}
    (A : (menu.information init horizon scheduler).BehavioralAssessment)
    (who : Player) (site : (menu.information init horizon scheduler).InformationSite who)
    (payoff : (App).ProtocolState → ℝ)
    (alternative : (menu.information init horizon scheduler).BehavioralPolicy who) :
    (((A.truncatedContinuationContext site
      (fun h : (menu.protocol init horizon scheduler).History => payoff h.state)
      (2 * horizon + 1)).outcome alternative).map History.state) =
      ((A.belief who site).map (fun h :
        (menu.information init horizon scheduler).InformationHistory who site.1 => h.1.state)).bind
        ((App).finish init horizon scheduler (Function.update
          (menu.decodeProfile init horizon scheduler A.strategy) who
          ((App).decodePolicy (menu.embedPolicy init horizon scheduler who alternative)))) := by
  change ((A.belief who site).bind (fun h =>
    menu.runFrom init horizon scheduler (GameTheory.Profile.update
      (sig := (menu.information init horizon scheduler).behavioralSignature)
      A.strategy who alternative) h.1)).map History.state = _
  rw [PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support
  intro h _
  exact (menu.runFrom_stateLaw init horizon scheduler _ h.1).trans
    (congrArg (fun p => (App).finish init horizon scheduler p h.1.state)
      (menu.decodeProfile_update init horizon scheduler A.strategy who alternative))

variable (read : Player → (application setup timeouts leaks).PlayerView → Signal)
    (observed : ∀ draw ∈ setup.initialLaw.support,
      ∀ execution : (application setup timeouts leaks).Execution,
      EventGraphRuntime.State.Invariant (graph := setup.informationGraph)
        (setup.eventInputs draw) execution.application → ∀ who,
        read who (execution.observe (application setup timeouts leaks) who) = signal draw)

omit [Finite Player] in
private theorem component_decision_invariant (key : Signal)
    (supported : key ∈ (setup.initialLaw.map signal).support)
    (who : Player)
    (site : (menu.information (componentLaw key) horizon scheduler).InformationSite who)
    (history : (menu.information (componentLaw key) horizon scheduler).InformationHistory
      who site.1) :
    ∃ (control : (App).Control) (draw : State L setup.context), history.1.state = some control ∧
      draw ∈ setup.initialLaw.support ∧
      signal draw = key ∧ EventGraphRuntime.State.Invariant (graph := setup.informationGraph)
        (setup.eventInputs draw) control.execution.application := by
  have active := InformationModel.InformationSite.active
    (M := menu.information (componentLaw key) horizon scheduler) site history
  cases eq : history.1.state with
  | none => rw [eq] at active; cases active
  | some control =>
    have trace := menu.toRawTrace (componentLaw key) horizon scheduler history.1.trace
    rw [eq] at trace
    change ((App).protocol (serviceInitialLaw (setup.conditionInitial signal key)
      setup.informationDependencies) horizon scheduler).Trace (some control) at trace
    rw [serviceInitialLaw_eq_inputs (setup.conditionInitial signal key)] at trace
    have valid := reactive_history_invariant timeouts leaks
      ((setup.conditionInitial signal key).initialLaw.map setup.eventInputs) horizon scheduler trace
    obtain ⟨inputs, member, valid⟩ := valid
    obtain ⟨draw, present, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have part := mem_support_fiberPosterior supported present
    exact ⟨control, draw, rfl, part.2, part.1, valid⟩

variable (components : ∀ k,
    (menu.information (Vegas.initialLaw (setup.conditionInitial signal k))
      horizon scheduler).BehavioralAssessment)
    (global : (menu.information (Vegas.initialLaw setup) horizon scheduler).BehavioralAssessment)

include observed in
/-- Matching decoded profiles and beliefs on controls give identical terminal state laws
for whole-policy changes at a supported component's decision site. -/
private theorem signal_context_stateLaw
    {key : Signal} (supported : key ∈ (setup.initialLaw.map signal).support)
    (who : Player) (site : (menu.information GlobalLaw horizon scheduler).InformationSite who)
    (localSite : (menu.information (componentLaw key) horizon scheduler).InformationSite who)
    (belief : ((global.belief who site).map (fun h => h.1.state)) =
      ((components key).belief who localSite).map (fun h => h.1.state))
    (payoff : (App).ProtocolState → ℝ)
    (a : (menu.information GlobalLaw horizon scheduler).BehavioralPolicy who)
    (b : ∀ k, (menu.information (componentLaw k) horizon scheduler).BehavioralPolicy who)
    (clients : Function.update (menu.decodeProfile GlobalLaw horizon scheduler global.strategy)
        who ((App).decodePolicy (menu.embedPolicy GlobalLaw horizon scheduler who a)) =
      signalClients read (fun k => Function.update
        (menu.decodeProfile (componentLaw k) horizon scheduler (components k).strategy) who
        ((App).decodePolicy (menu.embedPolicy (componentLaw k) horizon scheduler who (b k))))) :
    (((global.truncatedContinuationContext site (fun h => payoff h.state)
      (2 * horizon + 1)).outcome a).map History.state) =
    ((((components key).truncatedContinuationContext localSite (fun h => payoff h.state)
      (2 * horizon + 1)).outcome (b key)).map History.state) := by
  rw [context_state_law, context_state_law, belief, clients, PMF.bind_map, PMF.bind_map]
  apply bind_congr_on_support
  intro h _
  obtain ⟨control, draw, same, member, component, valid⟩ :=
    component_decision_invariant menu key supported who localSite h
  simp only [Function.comp_apply]
  rw [same]
  have law := finish_signalClients read observed
    (fun k => Function.update (menu.decodeProfile (componentLaw k) horizon scheduler
      (components k).strategy) who
      ((App).decodePolicy (menu.embedPolicy (componentLaw k) horizon scheduler who (b k))))
    draw member control valid horizon GlobalLaw (componentLaw key) (scheduler := scheduler)
  rwa [component] at law

include observed in
/-- Sequential rationality for every complete unilateral policy follows from local
rationality, a common decoded strategy and the component posterior at every site. -/
theorem signalAssessment_rational
    (clients : menu.decodeProfile GlobalLaw horizon scheduler global.strategy =
      signalClients (setup := setup) (timeouts := timeouts) (leaks := leaks) read (fun k =>
        menu.decodeProfile (componentLaw k) horizon scheduler (components k).strategy))
    (beliefs : ∀ who (site : (menu.information GlobalLaw horizon scheduler).InformationSite who),
      ∃ (key : Signal) (_supported : key ∈ (setup.initialLaw.map signal).support)
        (localSite : (menu.information (componentLaw key) horizon scheduler).InformationSite who),
        ((global.belief who site).map (fun h => h.1.state)) =
          ((components key).belief who localSite).map (fun h => h.1.state))
    (payoff : Player → (App).ProtocolState → ℝ)
    (rational : ∀ key, (components key).IsSequentiallyRational
      (menu.bounded (componentLaw key) horizon scheduler).wellFoundedHistories
      (fun who h => payoff who h.state)) :
    global.IsSequentiallyRational (menu.bounded GlobalLaw horizon scheduler).wellFoundedHistories
      (fun who h => payoff who h.state) := by
  apply (global.isSequentiallyRational_iff_truncated_of_bounded _
    (menu.bounded GlobalLaw horizon scheduler) _).mpr
  intro who site
  obtain ⟨key, supported, localSite, belief⟩ := beliefs who site
  let original := global.truncatedContinuationContext site (fun h => payoff who h.state)
    (2 * horizon + 1)
  let part := (components key).truncatedContinuationContext localSite (fun h => payoff who h.state)
    (2 * horizon + 1)
  have optimal := ((components key).isSequentiallyRational_iff_truncated_of_bounded _
    (menu.bounded (componentLaw key) horizon scheduler) _).mp (rational key) who localSite
  have baseline : ((original.outcome (global.strategy who)).map History.state) =
      (part.outcome ((components key).strategy who)).map History.state := by
    apply signal_context_stateLaw menu read observed components global supported who site localSite
      belief (payoff who) _ (fun k => (components k).strategy who)
    have unchanged (law : PMF (App).State)
        (strategy : ∀ p, (menu.information law horizon scheduler).BehavioralPolicy p) :
        Function.update (menu.decodeProfile law horizon scheduler strategy) who
          ((App).decodePolicy (menu.embedPolicy law horizon scheduler who (strategy who))) =
          menu.decodeProfile law horizon scheduler strategy :=
      Function.update_eq_self who (menu.decodeProfile law horizon scheduler strategy)
    simpa only [unchanged] using clients
  let transfer (k : Signal)
      (a : (menu.information GlobalLaw horizon scheduler).BehavioralPolicy who)
      := menu.restrictPolicy (componentLaw k) horizon scheduler who
          ((App).decodePolicy (menu.embedPolicy GlobalLaw horizon scheduler who a))
  have alternative (a) : ((original.outcome a).map History.state) =
      (part.outcome (transfer key a)).map History.state := by
    apply signal_context_stateLaw menu read observed components global supported who site localSite
      belief (payoff who) _ (fun k => transfer k a)
    rw [clients, ← signalClients_update]
    congr 1
    funext k
    exact congrArg (Function.update
      (menu.decodeProfile (componentLaw k) horizon scheduler (components k).strategy) who)
      (menu.decode_restrictPolicy_of_covered (componentLaw k) horizon scheduler who _
        (menu.decode_embedPolicy_covered GlobalLaw horizon scheduler who a)).symm
  refine ⟨(hasExpectation_observed_law_iff _ _ _ _ (payoff who) baseline).mpr optimal.1, ?_, ?_⟩
  · intro a _
    exact (hasExpectation_observed_law_iff _ _ _ _ (payoff who) (alternative a)).mpr
      (optimal.2.1 _ (Set.mem_univ _))
  · intro a _
    exact (extendedExpect_observed_law_eq _ _ _ _ (payoff who) (alternative a)).trans_le
      ((optimal.2.2 _ (Set.mem_univ _)).trans_eq
        (extendedExpect_observed_law_eq _ _ _ _ (payoff who) baseline).symm)

/-- A locally selected ledger assessment is rational at every global information site
when each component assessment is rational for the same state-dependent utilities. -/
theorem ledger_componentAssessment_rational
    (supported : ∀ key, key ∈ (setup.initialLaw.map signal).support)
    (infoRead : Player → (App).Info → Signal)
    (infoObserved : ∀ draw ∈ setup.initialLaw.support, ∀ execution : (App).Execution,
      State.Invariant (graph := setup.informationGraph) (setup.eventInputs draw)
        execution.application → ∀ who,
        infoRead who (some (execution.logs who, execution.observe (App) who)) = signal draw)
    (same : ∀ who past view, infoRead who (some (past, view)) = read who view)
    (payoff : Player → (App).ProtocolState → ℝ)
    (rational : ∀ key, (components key).IsSequentiallyRational
      (menu.bounded (componentLaw key) horizon scheduler).wellFoundedHistories
      (fun who h => payoff who h.state)) :
    (ledger_componentAssessment menu supported infoRead infoObserved
      components).IsSequentiallyRational
      (menu.bounded GlobalLaw horizon scheduler).wellFoundedHistories
      (fun who h => payoff who h.state) := by
  have actual draw member (execution : (App).Execution) valid who :
      read who (execution.observe (App) who) = signal draw :=
    (same who (execution.logs who) _).symm.trans (infoObserved draw member execution valid who)
  apply signalAssessment_rational menu read actual components _
    (decodeProfile_componentAssessment menu supported infoRead infoObserved read same components)
    _ payoff rational
  intro who site
  let key := infoRead who site.1
  refine ⟨key, supported key, ledger_componentSite menu supported infoRead infoObserved
    who site, ?_⟩
  exact PMF.map_comp _ _ _

end Vegas.SourceProgram.Setup
