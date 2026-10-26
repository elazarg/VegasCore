/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.PowerCertificate

/-! # Unequal local normalizers along actual histories

A rare direct path and a rare path with one extra decision reach the same
information site. The extra honest action contributes a distinct trembling
menu denominator. Their exact reach ratio is not the coefficient ratio, but
it converges to that ratio along the actual common power profile.
-/

noncomputable section

namespace GameTheoryExtensionsTests.PowerNormalizerPaths

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Filter

inductive State
  | root | extra | meet | done
  deriving DecidableEq, Fintype

def menu : State → Set (Option (Fin 3))
  | .done => {none}
  | _ => {move | ∃ action, move = some action}

def advance : State → Option (Fin 3) → State
  | .root, some action => if action = 1 then .extra else if action = 2 then .meet else .done
  | .extra, some action => if action = 0 then .meet else .done
  | _, _ => .done

@[reducible]
def arena : ExecutionProtocol Unit where
  State := State
  Action _ := Fin 3
  init := .root
  active state _ := state ≠ .done
  available _ _ := Set.univ
  terminal state := state = .done
  step state joint := PMF.pure (advance state (joint.1 ()))
  progress state running := by
    refine ⟨fun _ => some 0, ?_⟩
    intro who
    exact ⟨running, Set.mem_univ _⟩

@[reducible]
def signals : InfoSignals arena where
  PublicSignal := Unit
  PrivateSignal _ := State
  initialPublic := ()
  initialPrivate _ := .root
  publicSignal _ := ()
  privateSignal _ event := event.target
  InfoState _ := State
  initInfo _ signal _ := signal
  pushInfo _ _ _ signal _ := signal

theorem info_state : ∀ {state} (trace : arena.Trace state), signals.infoOf () trace = state
  | _, .start => rfl
  | _, .extend .. => rfl

@[reducible]
def model : InformationModel arena where
  toInfoSignals := signals
  menu _ := menu
  menu_adequate who state trace choice := by
    cases who
    rw [info_state]
    cases state <;> cases choice <;> simp [menu, LegalOption]

instance (who : Unit) (state : State) : Fintype (model.Choice who state) := Fintype.ofFinite _

def actionChoice (state : State) (running : state ≠ .done) (action : Fin 3) :
    model.Choice () state := ⟨some action, by cases state <;> simp_all [PowerNormalizerPaths.menu]⟩

def base (_ : Unit) (state : State) : PMF (model.Choice () state) :=
  match state with
  | .root => PMF.pure (actionChoice .root (by decide) 0)
  | .extra => PMF.pure (actionChoice .extra (by decide) 0)
  | .meet => PMF.pure (actionChoice .meet (by decide) 0)
  | .done => PMF.pure ⟨none, rfl⟩

def coefficient (_ : Unit) (state : State) (_ : model.Choice () state) : ℝ := 1

theorem coefficient_pos (who : Unit) (state : State) (choice : model.Choice who state) :
    0 < coefficient who state choice := zero_lt_one

def order (_ : Unit) (state : State) (choice : model.Choice () state) : Nat :=
  match choice.1 with
  | none => 0
  | some action => if action = 0 then 0 else if state = .extra ∧ action = 2 then 2 else 1

theorem constantTerm (who : Unit) (state : State) (choice : model.Choice who state) :
    (if order who state choice = 0 then coefficient who state choice else 0) =
      (base who state choice).toReal := by
  cases who
  by_cases terminal : state = .done
  · subst state
    have value : choice.1 = none := choice.property
    have same : choice = (⟨none, rfl⟩ : model.Choice () .done) := Subtype.ext value
    subst choice
    simp [order, coefficient, base, PMF.pure_apply]
  · have member : ∃ action, choice.1 = some action := by
      cases state with
      | root => exact choice.property
      | extra => exact choice.property
      | meet => exact choice.property
      | done => exact (terminal rfl).elim
    obtain ⟨action, same⟩ := member
    have chosen : choice = actionChoice state terminal action := Subtype.ext same
    subst choice
    cases state
    all_goals first
      | exact (terminal rfl).elim
      | fin_cases action <;>
          simp [order, coefficient, base, PMF.pure_apply, actionChoice, Subtype.ext_iff]

def joint (action : Fin 3) : Unit → Option (Fin 3) := fun _ => some action

theorem joint_legal (state : State) (running : state ≠ .done) (action : Fin 3) :
    arena.Legal state (joint action) := ⟨running, fun _ => ⟨running, Set.mem_univ _⟩⟩

def shortTrace : arena.Trace .meet :=
  .extend .start (joint 2) (joint_legal .root (by decide) 2) (by simp [arena, advance, joint])

def extraTrace : arena.Trace .extra :=
  .extend .start (joint 1) (joint_legal .root (by decide) 1) (by simp [arena, advance, joint])

def longTrace : arena.Trace .meet :=
  .extend extraTrace (joint 0) (joint_legal .extra (by decide) 0)
    (by simp [arena, advance, joint])

def site : model.InformationSite () :=
  ⟨.meet, ⟨⟨⟨.meet, shortTrace⟩, rfl⟩, by decide, 0, ⟨0, rfl⟩⟩⟩

def shortMember : model.InformationHistory () site.1 := ⟨⟨.meet, shortTrace⟩, rfl⟩
def longMember : model.InformationHistory () site.1 := ⟨⟨.meet, longTrace⟩, rfl⟩

def actionEquiv (state : State) (running : state ≠ .done) : Fin 3 ≃ model.Choice () state :=
  Equiv.ofBijective (actionChoice state running) ⟨fun _ _ same =>
    Option.some.inj (congrArg Subtype.val same), fun choice => by
    have member : ∃ action, choice.1 = some action := by
      cases state with
      | root => exact choice.property
      | extra => exact choice.property
      | meet => exact choice.property
      | done => exact (running rfl).elim
    obtain ⟨action, same⟩ := member
    exact ⟨action, Subtype.ext same.symm⟩⟩

theorem rootNormalizer (t : ℝ) :
    powerNormalizer (coefficient () .root) (order () .root) t = 1 + 2 * t := by
  rw [powerNormalizer, ← Equiv.sum_comp (actionEquiv .root (by decide))]
  rw [Fin.sum_univ_three]
  norm_num [coefficient, order, actionEquiv, actionChoice,
    show (2 : Fin 3) ≠ 0 by decide]
  ring

theorem extraNormalizer (t : ℝ) :
    powerNormalizer (coefficient () .extra) (order () .extra) t = 1 + t + t ^ 2 := by
  rw [powerNormalizer, ← Equiv.sum_comp (actionEquiv .extra (by decide))]
  rw [Fin.sum_univ_three]
  norm_num [coefficient, order, actionEquiv, actionChoice,
    show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide]

theorem short_order : model.powerHistoryOrder order shortTrace = 1 := by
  simp [shortTrace, powerHistoryOrder, order, choicesOfLegal, joint]

theorem long_order : model.powerHistoryOrder order longTrace = 1 := by
  simp [longTrace, extraTrace, powerHistoryOrder, order, choicesOfLegal, joint]

theorem short_coefficient : model.powerHistoryCoefficient coefficient shortTrace = 1 := by
  simp [shortTrace, powerHistoryCoefficient, coefficient, arena, advance, joint]

theorem long_coefficient : model.powerHistoryCoefficient coefficient longTrace = 1 := by
  simp [longTrace, extraTrace, powerHistoryCoefficient, coefficient, arena, advance, joint]

theorem short_normalizer (t : ℝ) :
    model.powerHistoryNormalizer coefficient order t shortTrace = 1 + 2 * t := by
  change (1 * ∏ who : Unit,
    powerNormalizer (coefficient who .root) (order who .root) t) = _
  simpa only [Fintype.prod_unique, one_mul] using rootNormalizer t

theorem long_normalizer (t : ℝ) :
    model.powerHistoryNormalizer coefficient order t longTrace =
      (1 + 2 * t) * (1 + t + t ^ 2) := by
  change ((1 * ∏ who : Unit,
      powerNormalizer (coefficient who .root) (order who .root) t) *
    ∏ who : Unit, powerNormalizer (coefficient who .extra) (order who .extra) t) = _
  simp only [Fintype.prod_unique, one_mul]
  rw [rootNormalizer, extraNormalizer]

theorem short_reach (t : ℝ) (positive : 0 < t) :
    (model.historyReachWeight (model.powerProfile base coefficient coefficient_pos order t positive)
      shortMember.1).toReal = t / (1 + 2 * t) := by
  rw [model.powerProfile_historyReachWeight]
  change model.powerHistoryCoefficient coefficient shortTrace *
    t ^ model.powerHistoryOrder order shortTrace /
      model.powerHistoryNormalizer coefficient order t shortTrace = _
  rw [short_order, short_coefficient, short_normalizer, pow_one, one_mul]

theorem long_reach (t : ℝ) (positive : 0 < t) :
    (model.historyReachWeight (model.powerProfile base coefficient coefficient_pos order t positive)
      longMember.1).toReal = t / ((1 + 2 * t) * (1 + t + t ^ 2)) := by
  rw [model.powerProfile_historyReachWeight]
  change model.powerHistoryCoefficient coefficient longTrace *
    t ^ model.powerHistoryOrder order longTrace /
      model.powerHistoryNormalizer coefficient order t longTrace = _
  rw [long_order, long_coefficient, long_normalizer, pow_one, one_mul]

/-- Two actual histories in the same information fiber have unequal local
normalizer products, and their exact ratio retains the additional denominator. -/
theorem actual_reach_ratio (t : ℝ) (positive : 0 < t) :
    (model.historyReachWeight (model.powerProfile base coefficient coefficient_pos order t positive)
      longMember.1).toReal /
      (model.historyReachWeight
        (model.powerProfile base coefficient coefficient_pos order t positive)
        shortMember.1).toReal = 1 / (1 + t + t ^ 2) := by
  rw [short_reach, long_reach]
  field_simp

/-- The actual evaluator ratio converges to the computed leading coefficient
ratio despite the unequal, noncancelling local normalizers. -/
theorem actual_reach_ratio_tendsto {parameter : Nat → ℝ}
    (positive : ∀ n, 0 < parameter n) (vanishes : Tendsto parameter atTop (nhds 0)) :
    Tendsto (fun n =>
      (model.historyReachWeight (model.powerProfile base coefficient coefficient_pos order
        (parameter n) (positive n)) longMember.1).toReal /
        (model.historyReachWeight (model.powerProfile base coefficient coefficient_pos order
          (parameter n) (positive n)) shortMember.1).toReal) atTop (nhds 1) := by
  change Tendsto (fun n =>
    (model.historyReachWeight (model.powerProfile base coefficient coefficient_pos order
      (parameter n) (positive n)) ⟨.meet, longTrace⟩).toReal /
      (model.historyReachWeight (model.powerProfile base coefficient coefficient_pos order
        (parameter n) (positive n)) ⟨.meet, shortTrace⟩).toReal) atTop (nhds 1)
  have short := model.powerProfile_history_scaled_tendsto base coefficient coefficient_pos order
    constantTerm positive vanishes shortTrace
  have long := model.powerProfile_history_scaled_tendsto base coefficient coefficient_pos order
    constantTerm positive vanishes longTrace
  rw [short_coefficient, short_order] at short
  rw [long_coefficient, long_order] at long
  have limit := long.div short (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [div_self (by norm_num : (1 : ℝ) ≠ 0), Pi.div_def, pow_one,
    div_div_div_cancel_right₀ (ne_of_gt (positive _))] using limit

/-- The discrepancy is present at every positive parameter, so the limit
cannot be justified by claiming exact cancellation of the two paths. -/
theorem actual_reach_ratio_ne_one (t : ℝ) (positive : 0 < t) :
    (model.historyReachWeight (model.powerProfile base coefficient coefficient_pos order t positive)
      longMember.1).toReal /
      (model.historyReachWeight
        (model.powerProfile base coefficient coefficient_pos order t positive)
        shortMember.1).toReal ≠ 1 := by
  rw [actual_reach_ratio]
  have greater : 1 < 1 + t + t ^ 2 := by nlinarith [sq_nonneg t]
  exact ne_of_lt ((div_lt_one (by positivity)).mpr greater)

end GameTheoryExtensionsTests.PowerNormalizerPaths
