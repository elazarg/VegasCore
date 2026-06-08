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
      have hstartView : view.startPoint = start.programPoint := by
        simpa [view, sourceHistory, SourceHistoryPoint.localHistoryView] using
          congrArg SourceConfig.programPoint hstart
      have hchoice :
          view.currentView.point.IsChoiceFor who := by
        simp [view, sourceHistory, SourceHistoryPoint.localHistoryView,
          SourceConfig.localView, SourceConfig.programPoint,
          SourceProgramPoint.IsChoiceFor]
      rw [stepKernel] at hsupport
      change
        next ∈
          (PMF.map
            (fun choice => by
              have hguard :
                  evalGuard (Player := P) (L := L) guard choice.1
                    ((env.toView who).eraseEnv) = true := by
                simpa [SourceViewChoice, view, sourceHistory,
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
            (profile who view hstartView hchoice)).support at hsupport
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

end WFProgram

end Vegas
