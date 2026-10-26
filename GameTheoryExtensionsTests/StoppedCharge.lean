/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedCharge
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Distinct conditional charge potentials at a merging state

Chance forks and then merges before the final transition. Its two actual
histories have the same endpoint state but different charges and automatic
expected remaining costs. Thus prefix-history charges need not factor through
state-only transition values.
-/

noncomputable section

namespace GameTheoryExtensionsTests.StoppedCharge

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability



inductive Stage where
  | initial
  | fork (bit : Bool)
  | merged
  | done
  deriving DecidableEq

def depth : Stage → Nat
  | .initial => 0
  | .fork _ => 1
  | .merged => 2
  | .done => 3

@[reducible] def arena : ExecutionProtocol Unit where
  State := Stage
  Action _ := Unit
  init := .initial
  active _ _ := False
  available _ _ := ∅
  terminal state := state = .done
  step state _ := match state with
    | .initial => (PMF.uniformOfFintype Bool).map Stage.fork
    | .fork _ => PMF.pure .merged
    | _ => PMF.pure .done
  progress _ _ := ⟨fun _ => none, fun _ => by simp⟩

def signals : InfoSignals arena where
  PublicSignal := Unit
  PrivateSignal _ := Unit
  initialPublic := ()
  initialPrivate _ := ()
  publicSignal _ := ()
  privateSignal _ _ := ()
  InfoState _ := Unit
  initInfo _ _ _ := ()
  pushInfo _ _ _ _ _ := ()

@[reducible] def model : InformationModel arena where
  toInfoSignals := signals
  menu _ _ := {none}
  menu_adequate := by
    intro who state trace choice
    cases choice <;> simp [LegalOption, arena]

def profile : ∀ who, model.BehavioralPolicy who := fun _ _ => PMF.pure ⟨none, rfl⟩

theorem step_depth (state target : Stage) (joint : {joint // arena.Legal state joint})
    (supported : target ∈ (arena.step state joint).support) : depth target = depth state + 1 := by
  cases state with
  | initial =>
      obtain ⟨bit, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | fork bit => cases (PMF.mem_support_pure_iff _ _).mp supported; rfl
  | merged => cases (PMF.mem_support_pure_iff _ _).mp supported; rfl
  | done => exact (joint.2.1 rfl).elim

theorem bounded : arena.BoundedHorizon 3 := by
  have accounted : ∀ {state} (trace : arena.Trace state), trace.length = depth state := by
    intro state trace
    induction trace with
    | start => rfl
    | extend prior joint legal realized ih =>
        change prior.length + 1 = _
        rw [ih]
        exact (step_depth _ _ ⟨joint, legal⟩ realized).symm
  intro state trace long
  rw [accounted trace] at long
  cases state <;> simp_all [arena, depth]

def forkHistory (bit : Bool) : arena.History :=
  arena.initHistory.extend (joint := fun _ => none)
    ⟨by decide, fun _ => by simp⟩ (by
      change Stage.fork bit ∈ ((PMF.uniformOfFintype Bool).map Stage.fork).support
      exact PMF.support_map .. ▸ ⟨bit, PMF.mem_support_uniformOfFintype bit, rfl⟩)

def mergedHistory (bit : Bool) : arena.History :=
  (forkHistory bit).extend (joint := fun _ => none)
    ⟨by change Stage.fork bit ≠ Stage.done; simp, fun _ => by simp⟩
    ((PMF.mem_support_pure_iff _ _).mpr rfl)

def charge (history : arena.History) : ℝ :=
  if history.state = .merged then
    if history.prior.state = .fork true then 3 / 4 else 1 / 4
  else 0

theorem charge_nonnegative (history : arena.History) : 0 ≤ charge history := by
  unfold charge
  split
  · split <;> norm_num
  · norm_num

theorem charge_bounded (history : arena.History) : charge history ≤ 1 := by
  unfold charge
  split
  · split <;> norm_num
  · norm_num

theorem expected_at_merge (bit : Bool) :
    expectedCharge model bounded.wellFoundedHistories profile (fun _ => False) charge
      (mergedHistory bit) = charge (mergedHistory bit) := by
  have drift := expectedCharge_drift model bounded bounded.wellFoundedHistories profile
    (fun _ => False) charge charge_nonnegative charge_bounded (mergedHistory bit)
    (by trivial) (by change Stage.merged ≠ Stage.done; simp)
  have nextZero : ∀ next ∈ (model.runBehavioralFrom profile 1 (mergedHistory bit)).support,
      expectedCharge model bounded.wellFoundedHistories profile (fun _ => False) charge next =
        0 := by
    intro next reached
    obtain ⟨⟨joint, legal, realized⟩, _⟩ :=
      model.mem_support_runBehavioralFrom_one profile
        (by change Stage.merged ≠ Stage.done; simp) reached
    have ended : arena.terminal next.state := by
      exact (PMF.mem_support_pure_iff _ _).mp realized
    rw [expectedCharge, model.runBehavioralUntil_of_terminal _ profile ended,
      expect_pure, sub_self]
  have average := (expect_congr_on_support nextZero).trans (expect_zero _)
  rw [average, add_zero] at drift
  exact drift.symm

/-- Merging endpoint states do not erase their actual paid history. The two
legal prefixes have identical current state but distinct future conditional costs. -/
theorem history_dependent_potential :
    (mergedHistory false).state = (mergedHistory true).state ∧
    expectedCharge model bounded.wellFoundedHistories profile (fun _ => False) charge
      (mergedHistory false) = 1 / 4 ∧
    expectedCharge model bounded.wellFoundedHistories profile (fun _ => False) charge
      (mergedHistory true) = 3 / 4 := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [expected_at_merge]
    norm_num [charge, mergedHistory, forkHistory, History.prior, History.extend, Stage.fork.injEq]
    decide
  · rw [expected_at_merge]
    norm_num [charge, mergedHistory, forkHistory, History.prior, History.extend, Stage.fork.injEq]


end GameTheoryExtensionsTests.StoppedCharge
