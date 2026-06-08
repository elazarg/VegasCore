/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Epistemic
import Vegas.Core.Obligations
import GameTheory.Core.KernelGame

/-!
# Source-native strategic semantics

This module puts a strategic `KernelGame` directly on the source small-step
semantics.  It is intentionally above the event graph: strategies are indexed by
source histories, nature samples from source `sample` distributions, and
terminal utility is read from `SourceConfig.outcome?`.
-/

namespace Vegas

open GameTheory
open Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The source action space available in a player-local history view.

At a commit point this is the subtype of guard-satisfying committed values for
the active owner.  At non-choice points it is empty; strategies are only queried
with a proof that the history is a choice point. -/
def SourceViewChoice {who : P}
    (view : SourceHistoryLocalView P L who)
    (hchoice : view.currentView.point.IsChoiceFor who) : Type :=
  match hview : view.currentView with
  | ⟨⟨Γ, .commit (b := b) x owner guard tail⟩, visibleEnv⟩ =>
      { value : L.Val b //
        evalGuard (Player := P) (L := L) guard value
          ((cast
            (congrArg (fun player => VEnv L (viewVCtx player Γ))
              (by
                have howner : owner = who := by
                  have hchoice' :
                      SourceProgramPoint.IsChoiceFor
                        ({ ctx := Γ,
                           cont := VegasCore.commit (Player := P) x owner guard
                             tail } :
                          SourceProgramPoint P L) who := by
                    simpa [hview] using hchoice
                  simpa [SourceProgramPoint.IsChoiceFor,
                    SourceProgramPoint.activePlayer?,
                    SourceProgramPoint.kind] using hchoice'
                exact howner.symm))
            visibleEnv).eraseEnv) = true }
  | _ => Empty

/-- The source action space at a realized history, read through the acting
player's local view. -/
abbrev SourceChoice (history : SourceHistoryPoint P L) (who : P)
    (hchoice : history.IsChoiceFor who) : Type :=
  SourceViewChoice (L := L) (history.localHistoryView who) (by
    simpa [SourceHistoryPoint.localHistoryView, SourceConfig.localView] using
      hchoice)

/-- A behavioral source strategy for one player.

The strategy is a function of the player's source-local history view, not of
the full instrumented history.  It is only queried at local views whose current
source program point is a choice point for that player. -/
abbrev SourceStrategy (start : SourceConfig P L) (who : P) : Type :=
  (view : SourceHistoryLocalView P L who) →
    view.startPoint = start.programPoint →
      (hchoice : view.currentView.point.IsChoiceFor who) →
        PMF (SourceViewChoice (L := L) view hchoice)

/-- A source behavioral profile. -/
abbrev SourceProfile (start : SourceConfig P L) : Type :=
  ∀ who : P, SourceStrategy (L := L) start who

/-- A source history together with the normalization proof needed to continue
sampling from its current continuation. -/
structure SourceStrategicHistory (start : SourceConfig P L) where
  history : SourceHistoryPoint P L
  start_eq : history.start = start
  normalized : NormalizedDists history.current.cont

namespace SourceStrategicHistory

/-- The initial normalized source strategic history. -/
def initial (start : SourceConfig P L)
    (normalized : NormalizedDists start.cont) :
    SourceStrategicHistory start where
  history := SourceHistoryPoint.refl start
  start_eq := rfl
  normalized := normalized

/-- Extend a source strategic history by one labeled step, supplying the
normalization proof for the successor continuation. -/
def snoc {start : SourceConfig P L}
    (state : SourceStrategicHistory (L := L) start)
    {next : SourceConfig P L} {label : Label P L}
    (step : LStep state.history.current label next)
    (normalizedNext : NormalizedDists next.cont) :
    SourceStrategicHistory start where
  history := state.history.snoc step
  start_eq := state.start_eq
  normalized := normalizedNext

@[simp] theorem initial_history
    (start : SourceConfig P L) (normalized : NormalizedDists start.cont) :
    (initial (L := L) start normalized).history =
      SourceHistoryPoint.refl start := rfl

@[simp] theorem snoc_history {start : SourceConfig P L}
    (state : SourceStrategicHistory (L := L) start)
    {next : SourceConfig P L} {label : Label P L}
    (step : LStep state.history.current label next)
    (normalizedNext : NormalizedDists next.cont) :
    (state.snoc step normalizedNext).history =
      state.history.snoc step := rfl

end SourceStrategicHistory

/-- Utility read directly from a source strategic history.

Finite-horizon games may stop before a terminal `ret`; `cutoff` supplies the
payoff used for such nonterminal truncations. -/
def sourceHistoryUtility {start : SourceConfig P L}
    (cutoff : Payoff P)
    (state : SourceStrategicHistory (L := L) start) : Payoff P :=
  match state.history.current.outcome? with
  | some outcome => fun who => (outcome who : ℝ)
  | none => cutoff

namespace SourceStrategicHistory

/-- Advance a source strategic history by one source step under a profile.

Terminals stutter.  Samples use the program's normalized source distribution.
Commits query the active player's source strategy.  Reveals are deterministic. -/
noncomputable def stepKernel {start : SourceConfig P L}
    (profile : SourceProfile (L := L) start)
    (state : SourceStrategicHistory (L := L) start) :
    PMF (SourceStrategicHistory start) := by
  rcases state with ⟨history, hstart, hnorm⟩
  rcases history with ⟨startCfg, labels, current, run⟩
  rcases current with ⟨Γ, env, cont⟩
  cases cont with
  | ret payoffs =>
      exact PMF.pure
        { history := ⟨startCfg, labels, ⟨Γ, env, .ret payoffs⟩, run⟩
          start_eq := hstart
          normalized := hnorm }
  | sample x D tail =>
      let dist := L.evalDist D env.eraseSampleEnv
      have hdist : FWeight.totalWeight dist = 1 := by
        have hdeps := hnorm.1
        rw [show dist = L.evalDist D env.eraseSampleEnv from rfl]
        rw [← L.evalDistDeps_eq_evalDist D env.eraseSampleEnv]
        exact hdeps (fun name ty hvar hmem => env.eraseSampleEnv name ty hvar)
      let pmf := dist.toPMF hdist
      exact PMF.map
        (fun value =>
          if hv : value ∈ dist.support then
            { history :=
                (SourceHistoryPoint.snoc
                  ⟨startCfg, labels,
                    ⟨Γ, env, VegasCore.sample x D tail⟩, run⟩
                  (LStep.sample D tail value hv))
              start_eq := hstart
              normalized := hnorm.2 }
          else
            { history :=
                ⟨startCfg, labels,
                  ⟨Γ, env, VegasCore.sample x D tail⟩, run⟩
              start_eq := hstart
              normalized := hnorm })
        pmf
  | commit x who guard tail =>
      let history :
          SourceHistoryPoint P L :=
        ⟨startCfg, labels,
          ⟨Γ, env, VegasCore.commit x who guard tail⟩, run⟩
      let view := history.localHistoryView who
      have hstartView : view.startPoint = start.programPoint := by
        simpa [view, history, SourceHistoryPoint.localHistoryView] using
          congrArg SourceConfig.programPoint hstart
      have hchoice :
          view.currentView.point.IsChoiceFor who := by
        simp [view, history, SourceHistoryPoint.localHistoryView,
          SourceConfig.localView, SourceConfig.programPoint,
          SourceProgramPoint.IsChoiceFor]
      exact PMF.map
        (fun choice => by
          have hguard :
              evalGuard (Player := P) (L := L) guard choice.1
                ((env.toView who).eraseEnv) = true := by
            simpa [SourceViewChoice, view, history,
              SourceHistoryPoint.localHistoryView, SourceConfig.localView,
              SourceConfig.visibleEnv, SourceConfig.programPoint] using
              choice.2
          exact
          { history :=
              (SourceHistoryPoint.snoc
                history
                (LStep.commit guard tail choice.1 hguard))
            start_eq := hstart
            normalized := hnorm })
        (profile who view hstartView hchoice)
  | reveal y who x hx tail =>
      exact PMF.pure
        { history :=
            (SourceHistoryPoint.snoc
              ⟨startCfg, labels,
                ⟨Γ, env, VegasCore.reveal y who x hx tail⟩, run⟩
              (LStep.reveal hx tail))
          start_eq := hstart
          normalized := hnorm }

/-- Run the source strategic kernel for a finite number of steps. -/
noncomputable def traceDistFrom {start : SourceConfig P L}
    (profile : SourceProfile (L := L) start) :
    Nat → SourceStrategicHistory (L := L) start →
      PMF (SourceStrategicHistory start)
  | 0, state => PMF.pure state
  | n + 1, state =>
      (stepKernel profile state).bind (traceDistFrom profile n)

/-- Source trace distribution from a normalized initial configuration. -/
noncomputable def traceDist
    (start : SourceConfig P L)
    (normalized : NormalizedDists start.cont)
    (profile : SourceProfile (L := L) start)
    (horizon : Nat) :
    PMF (SourceStrategicHistory start) :=
  traceDistFrom profile horizon (initial start normalized)

end SourceStrategicHistory

/-- The finite-horizon source-native strategic game induced by a normalized
source configuration. -/
noncomputable def sourceTraceKernelGame
    (start : SourceConfig P L)
    (normalized : NormalizedDists start.cont)
    (horizon : Nat)
    (cutoff : Payoff P) : KernelGame P where
  Strategy := SourceStrategy (L := L) start
  Outcome := SourceStrategicHistory (L := L) start
  utility := sourceHistoryUtility cutoff
  outcomeKernel := fun profile =>
    SourceStrategicHistory.traceDist start normalized profile horizon

end Vegas
