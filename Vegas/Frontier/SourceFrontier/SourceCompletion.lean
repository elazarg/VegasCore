/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SourceFrontier.Strategic
import Vegas.Frontier.SourceFrontier.Query

/-!
# Source strategic completion horizon

The completed frontier games run to the graph completion bound and therefore
only expose `some` payoff outcomes.  The source-local strategic game needs the
matching source fact: after the remaining source instruction count, every
supported source trace is terminal.
-/

namespace Vegas

open GameTheory

namespace SourceStrategicHistory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A source continuation with zero instructions is terminal. -/
theorem terminal_of_instrCount_eq_zero
    {cfg : SourceConfig P L}
    (hcount : cfg.cont.instrCount = 0) :
    cfg.IsTerminal := by
  cases cfg with
  | mk Γ env cont =>
      cases cont with
      | ret payoffs =>
          exact ⟨payoffs, rfl⟩
      | sample x D tail =>
          simp [VegasCore.instrCount] at hcount
      | commit x who guard tail =>
          simp [VegasCore.instrCount] at hcount
      | reveal y who x hx tail =>
          simp [VegasCore.instrCount] at hcount

/-- Terminal source configurations have no remaining source instructions. -/
theorem instrCount_eq_zero_of_terminal
    {cfg : SourceConfig P L}
    (hterminal : cfg.IsTerminal) :
    cfg.cont.instrCount = 0 := by
  rcases hterminal with ⟨payoffs, hcont⟩
  rw [hcont]
  rfl

/-- A supported nonterminal source strategy step consumes exactly one source
instruction. -/
theorem instrCount_stepKernel_support_of_not_terminal
    {start : SourceConfig P L}
    (profile : SourceProfile (L := L) start)
    {state next : SourceStrategicHistory (L := L) start}
    (hnotTerminal : ¬ state.history.current.IsTerminal)
    (hsupport : next ∈ (stepKernel profile state).support) :
    state.history.current.cont.instrCount =
      next.history.current.cont.instrCount + 1 := by
  rcases state with ⟨history, hstart, hnorm⟩
  rcases history with ⟨startCfg, labels, current, run⟩
  rcases current with ⟨Γ, env, cont⟩
  cases cont with
  | ret payoffs =>
      exact False.elim (hnotTerminal ⟨payoffs, rfl⟩)
  | sample x D tail =>
      let dist := L.evalDist D env.eraseSampleEnv
      let hdist : FWeight.totalWeight dist = 1 := by
        have hdeps := hnorm.1
        rw [show dist = L.evalDist D env.eraseSampleEnv from rfl]
        rw [← L.evalDistDeps_eq_evalDist D env.eraseSampleEnv]
        exact hdeps (fun name ty hvar hmem => env.eraseSampleEnv name ty hvar)
      let pmf := dist.toPMF hdist
      rw [stepKernel] at hsupport
      change
        next ∈
          (PMF.map
            (fun value =>
              if hv : value ∈ dist.support then
                { history :=
                    SourceHistoryPoint.snoc
                      ⟨startCfg, labels,
                        ⟨Γ, env, VegasCore.sample x D tail⟩, run⟩
                      (LStep.sample D tail value hv)
                  start_eq := hstart
                  normalized := hnorm.2 }
              else
                { history :=
                    ⟨startCfg, labels,
                      ⟨Γ, env, VegasCore.sample x D tail⟩, run⟩
                  start_eq := hstart
                  normalized := hnorm })
            pmf).support at hsupport
      rcases (PMF.mem_support_map_iff _ _ _).mp hsupport with
        ⟨value, hvalueSupport, hnext⟩
      have hv : value ∈ dist.support := by
        simpa [pmf] using
          (FWeight.mem_support_toPMF dist hdist value).mp hvalueSupport
      rw [← hnext]
      rw [dif_pos hv]
      simp [SourceHistoryPoint.snoc, VegasCore.instrCount]
  | commit x who guard tail =>
      let sourceHistory : SourceHistoryPoint P L :=
        ⟨startCfg, labels,
          ⟨Γ, env, VegasCore.commit x who guard tail⟩, run⟩
      let view := sourceHistory.localHistoryView who
      let info : SourceReachableInfoState (L := L) start who :=
        SourceReachableInfoState.ofHistory sourceHistory (by
          simpa [sourceHistory] using hstart) who
      have hchoice :
          info.1.currentView.point.IsChoiceFor who := by
        simp [sourceHistory, SourceHistoryPoint.localHistoryView,
          SourceConfig.localView, SourceConfig.programPoint,
          SourceProgramPoint.IsChoiceFor, info,
          SourceReachableInfoState.ofHistory]
      rw [stepKernel] at hsupport
      change
        next ∈
          (PMF.map
            (fun choice => by
              have hguard :
                  evalGuard (Player := P) (L := L) guard choice.1
                    ((env.toView who).eraseEnv) = true := by
                simpa [SourceViewChoice, view, sourceHistory, info,
                  SourceReachableInfoState.ofHistory,
                  SourceHistoryPoint.localHistoryView, SourceConfig.localView,
                  SourceConfig.visibleEnv, SourceConfig.programPoint] using
                  choice.2
              exact
              { history :=
                  SourceHistoryPoint.snoc
                    sourceHistory
                    (LStep.commit guard tail choice.1 hguard)
                start_eq := hstart
                normalized := hnorm })
            (profile who info hchoice)).support at hsupport
      rcases (PMF.mem_support_map_iff _ _ _).mp hsupport with
        ⟨choice, _hchoiceSupport, hnext⟩
      rw [← hnext]
      simp [SourceHistoryPoint.snoc, VegasCore.instrCount, sourceHistory]
  | reveal y who x hx tail =>
      rw [stepKernel] at hsupport
      change
        next ∈
          (PMF.pure
            { history :=
                SourceHistoryPoint.snoc
                  ⟨startCfg, labels,
                    ⟨Γ, env, VegasCore.reveal y who x hx tail⟩, run⟩
                  (LStep.reveal hx tail)
              start_eq := hstart
              normalized := hnorm }).support at hsupport
      rw [PMF.support_pure, Set.mem_singleton_iff] at hsupport
      rw [hsupport]
      simp [SourceHistoryPoint.snoc, VegasCore.instrCount]

/-- A supported source trace is terminal once it has run for at least the
current continuation's remaining source instruction count. -/
theorem traceDistFrom_support_terminal_of_instrCount_le
    {start : SourceConfig P L}
    (profile : SourceProfile (L := L) start) :
    ∀ n (state dst : SourceStrategicHistory (L := L) start),
      dst ∈ (traceDistFrom profile n state).support →
        state.history.current.cont.instrCount ≤ n →
          dst.history.current.IsTerminal
  | 0, state, dst, hsupport, hbound => by
      have hdst : dst = state := by
        simpa [traceDistFrom, PMF.support_pure, Set.mem_singleton_iff]
          using hsupport
      subst dst
      have hcount : state.history.current.cont.instrCount = 0 := by
        omega
      exact terminal_of_instrCount_eq_zero hcount
  | n + 1, state, dst, hsupport, hbound => by
      by_cases hterminal : state.history.current.IsTerminal
      · rw [traceDistFrom] at hsupport
        have hstep :
            stepKernel profile state = PMF.pure state := by
          rcases state with ⟨history, hstart, hnorm⟩
          rcases history with ⟨startCfg, labels, current, run⟩
          rcases current with ⟨Γ, env, cont⟩
          cases cont with
          | ret payoffs =>
              rfl
          | sample x D tail =>
              rcases hterminal with ⟨payoffs, hcont⟩
              cases hcont
          | commit x who guard tail =>
              rcases hterminal with ⟨payoffs, hcont⟩
              cases hcont
          | reveal y who x hx tail =>
              rcases hterminal with ⟨payoffs, hcont⟩
              cases hcont
        rw [hstep, PMF.pure_bind] at hsupport
        exact
          traceDistFrom_support_terminal_of_instrCount_le
            profile n state dst hsupport (by
              have hzero :=
                instrCount_eq_zero_of_terminal
                  (L := L) (P := P) hterminal
              omega)
      · rw [traceDistFrom, PMF.mem_support_bind_iff] at hsupport
        rcases hsupport with ⟨mid, hmid, hdst⟩
        have hcountStep :
            state.history.current.cont.instrCount =
              mid.history.current.cont.instrCount + 1 :=
          instrCount_stepKernel_support_of_not_terminal
            profile hterminal hmid
        have hmidBound : mid.history.current.cont.instrCount ≤ n := by
          omega
        exact
          traceDistFrom_support_terminal_of_instrCount_le
            profile n mid dst hdst hmidBound

end SourceStrategicHistory

namespace SourceConfig

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Source guard legality is preserved by one labeled source step. -/
theorem legal_of_lstep
    {current next : SourceConfig P L} {label : Label P L}
    (hstep : LStep current label next)
    (hlegal : Legal current.cont) :
    Legal next.cont := by
  cases hstep with
  | sample D tail value hvalue =>
      simpa [Legal] using hlegal
  | commit guard tail value hguard =>
      simpa [Legal] using hlegal.2
  | reveal hx tail =>
      simpa [Legal] using hlegal

/-- Source guard legality is preserved along labeled source runs. -/
theorem legal_of_labeledStar
    {start current : SourceConfig P L} {labels : List (Label P L)}
    (hrun : LabeledStar start labels current)
    (hlegal : Legal start.cont) :
    Legal current.cont := by
  induction hrun with
  | refl cfg =>
      exact hlegal
  | cons hstep htail ih =>
      exact ih (legal_of_lstep hstep hlegal)

/-- Terminal source configurations report a concrete optional outcome. -/
theorem outcome?_support_some_of_terminal
    {cfg : SourceConfig P L}
    (hterminal : cfg.IsTerminal) :
    ∃ outcome, cfg.outcome? = some outcome := by
  rcases cfg with ⟨Γ, env, cont⟩
  rcases hterminal with ⟨payoffs, hcont⟩
  change cont = VegasCore.ret payoffs at hcont
  exact ⟨evalPayoffs payoffs env, by
    simp [SourceConfig.outcome?, hcont]⟩

end SourceConfig

namespace WFProgram

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- At the source program instruction-count horizon, the source strategic game
has only terminal histories in support. -/
theorem sourceStrategicGame_support_terminal_at_instrCount
    (program : WFProgram P L) (cutoff : Payoff P)
    (profile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    {state :
      SourceStrategicHistory (L := L)
        (ToEventGraph.sourceStart program.core)}
    (hsupport :
      state ∈
        ((program.sourceStrategicGame program.core.prog.instrCount cutoff).outcomeKernel
          profile).support) :
    state.history.current.IsTerminal := by
  simpa [sourceStrategicGame, ToEventGraph.sourceStart,
    SourceConfig.initial] using
    SourceStrategicHistory.traceDistFrom_support_terminal_of_instrCount_le
      profile program.core.prog.instrCount
      (SourceStrategicHistory.initial
        (ToEventGraph.sourceStart program.core) program.core.normalized)
      state hsupport (by rfl)

/-- Every source strategic history of a checked program carries a source suffix
whose guard menus remain legal. -/
theorem sourceStrategicHistory_current_legal
    (program : WFProgram P L)
    (state :
      SourceStrategicHistory (L := L)
        (ToEventGraph.sourceStart program.core)) :
    Legal state.history.current.cont := by
  have hstartLegal : Legal state.history.start.cont := by
    rw [state.start_eq]
    simpa [ToEventGraph.sourceStart, SourceConfig.initial] using
      program.legal
  exact
    SourceConfig.legal_of_labeledStar state.history.run hstartLegal

/-- At a legal source choice point, the acting player's source menu is
nonempty. -/
theorem sourceChoice_nonempty_of_legal
    {history : SourceHistoryPoint P L} {who : P}
    (hlegal : Legal history.current.cont)
    (hchoice : history.IsChoiceFor who) :
    Nonempty (SourceChoice (L := L) history who hchoice) := by
  rcases history with ⟨start, labels, current, run⟩
  rcases current with ⟨Γ, env, cont⟩
  cases cont with
  | ret payoffs =>
      simp [SourceHistoryPoint.IsChoiceFor, SourceConfig.IsChoiceFor,
        SourceConfig.activePlayer?, SourceConfig.programPoint,
        SourceProgramPoint.activePlayer?, SourceProgramPoint.kind] at hchoice
  | sample x dist tail =>
      simp [SourceHistoryPoint.IsChoiceFor, SourceConfig.IsChoiceFor,
        SourceConfig.activePlayer?, SourceConfig.programPoint,
        SourceProgramPoint.activePlayer?, SourceProgramPoint.kind] at hchoice
  | commit x owner guard tail =>
      have howner : owner = who := by
        simpa [SourceHistoryPoint.IsChoiceFor, SourceConfig.IsChoiceFor,
          SourceConfig.activePlayer?, SourceConfig.programPoint,
          SourceProgramPoint.activePlayer?, SourceProgramPoint.kind] using
          hchoice
      subst owner
      rcases hlegal.1 ((env.toView who).eraseEnv) with
        ⟨value, hguard⟩
      refine ⟨⟨value, ?_⟩⟩
      simpa [SourceChoice, SourceViewChoice,
        SourceHistoryPoint.localHistoryView, SourceConfig.localView,
        SourceConfig.visibleEnv, SourceConfig.programPoint] using hguard
  | reveal y owner x hx tail =>
      simp [SourceHistoryPoint.IsChoiceFor, SourceConfig.IsChoiceFor,
        SourceConfig.activePlayer?, SourceConfig.programPoint,
        SourceProgramPoint.activePlayer?, SourceProgramPoint.kind] at hchoice

/-- Source choice menus are nonempty at every checked-program strategic
history choice point. -/
theorem sourceStrategicHistory_choice_nonempty
    (program : WFProgram P L)
    (state :
      SourceStrategicHistory (L := L)
        (ToEventGraph.sourceStart program.core))
    {who : P}
    (hchoice : state.history.IsChoiceFor who) :
    Nonempty (SourceChoice (L := L) state.history who hchoice) :=
  sourceChoice_nonempty_of_legal
    (program.sourceStrategicHistory_current_legal state) hchoice

/-- Every reachable source information state of a checked program has a
nonempty menu when it is a choice point for the player. -/
theorem sourceReachableInfoState_choice_nonempty
    (program : WFProgram P L)
    {who : P}
    (info :
      SourceReachableInfoState (L := L)
        (ToEventGraph.sourceStart program.core) who)
    (hchoice : info.1.currentView.point.IsChoiceFor who) :
    Nonempty (SourceViewChoice (L := L) info.1 hchoice) := by
  rcases info with ⟨view, hreach⟩
  rcases hreach with ⟨history, hstart, hview⟩
  subst view
  have hstartLegal : Legal history.start.cont := by
    rw [hstart]
    simpa [ToEventGraph.sourceStart, SourceConfig.initial] using
      program.legal
  have hlegal : Legal history.current.cont :=
    SourceConfig.legal_of_labeledStar history.run hstartLegal
  have hchoiceHistory : history.IsChoiceFor who := by
    simpa [SourceHistoryPoint.IsChoiceFor,
      SourceHistoryPoint.localHistoryView, SourceConfig.localView,
      SourceConfig.programPoint] using hchoice
  simpa [SourceChoice] using
    sourceChoice_nonempty_of_legal
      (L := L) hlegal hchoiceHistory

/-- Canonical fallback source strategy for checked programs.

This is used only to make total strategy translations well-defined on
branches whose law is supplied elsewhere. -/
noncomputable def defaultSourceStrategy
    (program : WFProgram P L)
    (who : P) :
    SourceStrategy (L := L) (ToEventGraph.sourceStart program.core) who :=
  fun info hchoice =>
    PMF.pure
      (Classical.choice
        (program.sourceReachableInfoState_choice_nonempty info hchoice))

/-- Pointwise fallback source profile for checked programs. -/
noncomputable def defaultSourceProfile
    (program : WFProgram P L) :
    SourceProfile (L := L) (ToEventGraph.sourceStart program.core) :=
  fun who => program.defaultSourceStrategy who

/-- At the source instruction-count horizon, the optional source outcome law
only supports concrete outcomes. -/
theorem sourceStrategicOptionOutcomeView_law_support_some_at_instrCount
    (program : WFProgram P L) (cutoff : Payoff P)
    (profile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    {result : Option (Outcome P)}
    (hresult :
      result ∈
        ((program.sourceStrategicOptionOutcomeView
            program.core.prog.instrCount cutoff).law profile).support) :
    ∃ outcome, result = some outcome := by
  rw [GameForm.OutcomeView.law] at hresult
  rcases (PMF.mem_support_map_iff
      (program.sourceStrategicOptionOutcomeView
        program.core.prog.instrCount cutoff).observe
      ((program.sourceStrategicGame
        program.core.prog.instrCount cutoff).outcomeKernel profile)
      result).mp hresult with
    ⟨state, hstateSupport, hobserve⟩
  have hterminal :
      state.history.current.IsTerminal :=
    program.sourceStrategicGame_support_terminal_at_instrCount
      cutoff profile hstateSupport
  rw [← hobserve]
  rcases
      SourceConfig.outcome?_support_some_of_terminal hterminal with
    ⟨outcome, houtcome⟩
  exact ⟨outcome, by
    simpa [sourceStrategicOptionOutcomeView] using houtcome⟩

/-- The source optional outcome law has no `none` support at the source
instruction-count horizon. -/
theorem sourceStrategicOptionOutcomeView_law_none_not_support_at_instrCount
    (program : WFProgram P L) (cutoff : Payoff P)
    (profile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile) :
    none ∉
      ((program.sourceStrategicOptionOutcomeView
          program.core.prog.instrCount cutoff).law profile).support := by
  intro hnone
  rcases
      program.sourceStrategicOptionOutcomeView_law_support_some_at_instrCount
        cutoff profile hnone with
    ⟨outcome, hsome⟩
  cases hsome

end WFProgram

end Vegas
