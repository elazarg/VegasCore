module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveConditionedMenu
public import Vegas.Game.ConditionedLedgerClients

@[expose] public section

/-! # Decision-history fibers determined by an observed ledger component -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol EventGraphRuntime
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {Signal : Type*}
  {signal : State L setup.context → Signal}
  {timeouts : EventTimeouts setup.informationGraph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
  {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}

local notation "app" => application setup timeouts leaks

variable (menu : (application setup timeouts leaks).ResponseMenu)

/-- Every initialized global trace belongs to the component of its actual draw.
The invariant identifies that same draw at the last ledger control. -/
theorem ledgerTrace_component
    (allSupported : ∀ value, value ∈ (setup.initialLaw.map signal).support)
    {state} (trace : (menu.protocol (Vegas.initialLaw setup) horizon scheduler).Trace state) :
    ∀ (control : (app).Control) (_atControl : state = some control),
      ∃ draw ∈ setup.initialLaw.support,
        State.Invariant (graph := setup.informationGraph) (setup.eventInputs draw)
          control.execution.application ∧
        ∃ t : (menu.protocol (Vegas.initialLaw (setup.conditionInitial signal (signal draw)))
          horizon scheduler).Trace state,
          menu.traceOfInitialSupportSubset
            (setup.conditionInitial_ledgerSupport signal (signal draw) (allSupported _)) t =
                trace := by
  induction trace with
  | start => intro control atControl; cases atControl
  | @extend before after prior joint legal realized ih =>
    intro control atControl
    subst after
    cases before with
    | none =>
      obtain ⟨s, positive, atControl⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
      cases atControl
      obtain ⟨draw, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp positive
      have localDraw : draw ∈ (setup.conditionInitial signal (signal draw)).initialLaw.support := by
        change draw ∈ (fiberPosterior setup.initialLaw signal (signal draw)).support
        rw [fiberPosterior_support _ _ _ (allSupported _)]
        exact ⟨rfl, member⟩
      have localState : State.initial (graph := setup.informationGraph) (setup.eventInputs draw) ∈
          (Vegas.initialLaw (setup.conditionInitial signal (signal draw))).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, localDraw, rfl⟩
      have root := menu.trace_at_root prior
      subst prior
      refine ⟨draw, member, State.initial_invariant _, .extend .start joint legal ?_, ?_⟩
      · exact (PMF.mem_support_map_iff _ _ _).mpr ⟨_, localState, rfl⟩
      · simp only [ReactiveApplication.ResponseMenu.traceOfInitialSupportSubset]
    | some before =>
      obtain ⟨draw, member, valid, t, same⟩ := ih before rfl
      have preserved := (reactiveStateInvariant timeouts leaks (setup.eventInputs draw)).transition
        (PMF.pure (State.initial (setup.eventInputs draw))) horizon scheduler
        (by intro s member; cases (PMF.mem_support_pure_iff _ _).mp member
            exact State.initial_invariant _)
        (some before) (some control) joint valid realized
      refine ⟨draw, member, preserved, .extend t joint legal realized, ?_⟩
      simp only [ReactiveApplication.ResponseMenu.traceOfInitialSupportSubset, same]

variable (allSupported : ∀ value, value ∈ (setup.initialLaw.map signal).support)
  (read : Player → (application setup timeouts leaks).Info → Signal)
  (observed : ∀ draw ∈ setup.initialLaw.support,
    ∀ execution : (application setup timeouts leaks).Execution,
    State.Invariant (graph := setup.informationGraph) (setup.eventInputs draw)
      execution.application → ∀ who,
      read who (some (execution.logs who,
        execution.observe (application setup timeouts leaks) who)) =
        signal draw)

include observed

/-- Every history with the same genuine decision view belongs to the component
identified by that player's existing observation, for arbitrary legal responses. -/
theorem ledgerInfoHistory_component_surjective (who : Player)
    (site : (menu.information (Vegas.initialLaw setup) horizon scheduler).InformationSite who) :
    Function.Surjective
      (menu.infoHistoryOfInitialSupportSubset (scheduler := scheduler) (horizon := horizon)
        (setup.conditionInitial_ledgerSupport signal (read who site.1) (allSupported _))
        who site.1) := by
  intro history
  obtain ⟨⟨state, trace⟩, atSite⟩ := history
  have active := InformationModel.InformationSite.active
    (M := menu.information (Vegas.initialLaw setup) horizon scheduler) site
    ⟨⟨state, trace⟩, atSite⟩
  cases state with
  | none => cases active
  | some control =>
    obtain ⟨draw, member, valid, localTrace, same⟩ :=
      ledgerTrace_component menu allSupported trace control rfl
    have actor : control.actor = some who := active
    have view : site.1 = some (control.execution.logs who,
        control.execution.observe (application setup timeouts leaks) who) := by
      rw [← atSite]
      change (menu.signals _ _ _).infoOf who trace = _
      rw [menu.info]
      simp [ReactiveApplication.observe, actor]
    have key : signal draw = read who site.1 := by
      rw [view]
      exact (observed draw member control.execution valid who).symm
    obtain ⟨t, mapped⟩ : ∃ t :
        (menu.protocol (Vegas.initialLaw (setup.conditionInitial signal (read who site.1)))
        horizon scheduler).Trace (some control), menu.traceOfInitialSupportSubset
          (setup.conditionInitial_ledgerSupport signal (read who site.1) (allSupported _)) t =
            trace := by
      rw [← key]
      exact ⟨localTrace, same⟩
    refine ⟨⟨⟨some control, t⟩, ?_⟩, ?_⟩
    · change (menu.signals _ _ _).infoOf who t = _
      rw [menu.info, view]
      simp [ReactiveApplication.observe, actor]
    · apply Subtype.ext
      exact congrArg (History.mk _) mapped

local notation "law" k => Vegas.initialLaw (setup.conditionInitial signal k)

/-- A genuine global decision is the identical decision view in the player's component. -/
def ledger_componentSite (who : Player)
    (site : (menu.information (Vegas.initialLaw setup) horizon scheduler).InformationSite who) :
    (menu.information (law (read who site.1)) horizon scheduler).InformationSite who := by
  refine ⟨site.1, ?_⟩
  obtain ⟨h, running, action, allowed⟩ := site.2
  obtain ⟨t, mapped⟩ :=
    ledgerInfoHistory_component_surjective menu allSupported read observed who site h
  refine ⟨t, ?_, action, ?_⟩
  · have eq := congrArg (fun x => x.1.state) mapped
    exact eq.symm ▸ running
  · rw [menu.information_menu_initial_eq (initial := Vegas.initialLaw setup)]
    exact allowed

/-- One assessment implements the component assessments at every decision site,
transporting their actual history beliefs to the full raw menu. -/
def ledger_componentAssessment
    (assessments : ∀ value,
      (menu.information (law value) horizon scheduler).BehavioralAssessment) :
    (menu.information (Vegas.initialLaw setup) horizon scheduler).BehavioralAssessment where
  strategy := menu.signalStrategy read (fun value => (assessments value).strategy)
  belief who site := ((assessments (read who site.1)).belief who
    (ledger_componentSite menu allSupported read observed who site)).map
      (menu.infoHistoryOfInitialSupportSubset
        (setup.conditionInitial_ledgerSupport signal (read who site.1) (allSupported _)) who site.1)

end Vegas.SourceProgram.Setup
