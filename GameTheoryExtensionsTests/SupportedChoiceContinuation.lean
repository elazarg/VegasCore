/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.SupportedChoiceContinuation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Active-player factors across chance and idle players

A genuine chance step draws a public bit, then Alice chooses a Boolean while
Bob remains idle, then execution stops. The active-count continuation bound
uses one player rather than the two-player carrier. The chance step itself
preserves the entire history law exactly under arbitrary profiles.
-/

noncomputable section

namespace GameTheoryExtensionsTests.SupportedChoiceContinuation

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

inductive State where
  | chance
  | choice (bit : Bool)
  | done (answer : Bool)
  deriving DecidableEq, Fintype

private def active : State → Bool → Prop
  | .choice _, who => who = false
  | _, _ => False

private def terminal : State → Prop
  | .done _ => True
  | _ => False

private def transition : State → (Bool → Option Bool) → PMF State
  | .chance, _ => (PMF.uniformOfFintype Bool).map State.choice
  | .choice _, joint => PMF.pure (.done ((joint false).getD false))
  | .done answer, _ => PMF.pure (.done answer)

@[reducible] def arena : ExecutionProtocol Bool where
  State := State
  Action _ := Bool
  init := .chance
  active := active
  available _ _ := Set.univ
  terminal := terminal
  step state joint := transition state joint.1
  progress state _ := by
    classical
    refine ⟨fun who => if active state who then some false else none, ?_⟩
    intro who
    by_cases acts : active state who <;> simp [acts]

private def signals : InfoSignals arena where
  PublicSignal := State
  PrivateSignal _ := State
  initialPublic := .chance
  initialPrivate _ := .chance
  publicSignal event := event.target
  privateSignal _ event := event.target
  InfoState _ := State
  initInfo _ state _ := state
  pushInfo _ _ _ state _ := state

@[simp] private theorem info_state (who : Bool) : ∀ {state : State}
    (trace : arena.Trace state), signals.infoOf who trace = state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

@[reducible] def model : InformationModel arena where
  toInfoSignals := signals
  menu who state := {choice | LegalOption arena state who choice}
  menu_adequate := by
    intro who state trace choice
    rw [info_state]
    rfl

private def policy (answer : Bool) : ∀ who, model.BehavioralPolicy who := fun who state => by
  classical
  exact if acts : active state who then
    PMF.pure ⟨some answer, acts, Set.mem_univ _⟩
  else PMF.pure ⟨none, acts⟩

private def noisy : ∀ who, model.BehavioralPolicy who := fun who info =>
  mix (1 / 2) (by norm_num) (by norm_num) (policy false who info) (policy true who info)

private theorem retained (who : Bool) (info : model.InfoState who)
    (choice : model.Choice who info) :
    (1 / 2 : ℝ) * ((policy false who info) choice).toReal ≤ ((noisy who info) choice).toReal := by
  rw [noisy, mix_apply_toReal]
  nlinarith [ENNReal.toReal_nonneg (a := (policy true who info) choice)]

open Classical in
private theorem active_count (state : State) :
    (Finset.univ.filter (arena.active state)).card ≤ 1 := by
  change (Finset.univ.filter (active state)).card ≤ 1
  cases state <;> simp [active, Fintype.univ_bool, Finset.filter_insert, Finset.filter_singleton]

/-- The active-player theorem applies to actual behavioral continuations with
no lower-bound premise on Bob's inactive coordinate. -/
theorem continuation_bound (start : arena.History) (fuel : ℕ) :
    PMF.WithinTV (1 - (1 / 2 : ℝ) ^ fuel)
      (model.runBehavioralFrom (policy false) fuel start)
      (model.runBehavioralFrom noisy fuel start) := by
  simpa only [one_mul] using model.runBehavioralFrom_withinTV_of_supported_active_choices
    (policy false) noisy (1 / 2) (by norm_num) (by norm_num) start 1
    (fun _ history _ => active_count history.state)
    (fun _ history _ who _ choice => retained who (model.infoOf who history.trace) choice) fuel

/-- Unlike a pure administrative move, this chance kernel has two distinct
supported successor states, even though neither player acts. -/
theorem chance_has_two_successors (legal : {joint // arena.Legal State.chance joint}) :
    State.choice false ∈ (arena.step State.chance legal).support ∧
      State.choice true ∈ (arena.step State.chance legal).support := by
  constructor <;> rw [show arena.step State.chance legal =
    (PMF.uniformOfFintype Bool).map State.choice from rfl, PMF.support_map]
  · exact ⟨false, PMF.mem_support_uniformOfFintype _, rfl⟩
  · exact ⟨true, PMF.mem_support_uniformOfFintype _, rfl⟩

private theorem chance_keeps_all (source target : ∀ who, model.BehavioralPolicy who)
    (next : arena.History) :
    ((model.runBehavioralFrom source 1 arena.initHistory) next).toReal ≤
      ((model.runBehavioralFrom target 1 arena.initHistory) next).toReal := by
  have bound := model.runBehavioralFrom_one_domination_of_active_choices source target
    (1 / 2) (by norm_num) arena.initHistory
    (by intro who acts; exact False.elim acts) next
  simpa [arena, active] using bound

/-- The exact one-step active exponent is zero at chance, so the runner's
entire history law agrees, not just its terminal or public projection. -/
theorem chance_runner_agrees (source target : ∀ who, model.BehavioralPolicy who) :
    model.runBehavioralFrom source 1 arena.initHistory =
      model.runBehavioralFrom target 1 arena.initHistory := by
  apply pmf_ext_toReal
  intro next
  exact le_antisymm (chance_keeps_all source target next) (chance_keeps_all target source next)

/-- Two steps use the one-active-player bound `3/4`, strictly below the
ambient two-player estimate `15/16`. -/
theorem sharper_numeric_bound :
    (1 - (1 / 2 : ℝ) ^ 2) = 3 / 4 ∧
      (1 - (1 / 2 : ℝ) ^ 2) < 1 - (1 / 2 : ℝ) ^ (2 * 2) := by norm_num

end GameTheoryExtensionsTests.SupportedChoiceContinuation
