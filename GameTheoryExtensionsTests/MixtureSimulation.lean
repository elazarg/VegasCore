/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.MixtureSimulationComposition
import GameTheoryExtensions.Math.Probability.Support

/-! # Regression tests for mixture simulation and composition -/

noncomputable section

namespace GameTheory.GameForm.MixtureSimulationOn.Tests

open GameTheory.Math.Probability

def coin : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure true)

inductive SourceOutcome where | observed (value : Bool)
inductive MiddleOutcome where | visible (value : Bool)
inductive TargetOutcome where | published (value : Bool)

abbrev sourceSignature : GameSignature Unit where
  Strategy _ := Bool
  Outcome := SourceOutcome

abbrev middleSignature : GameSignature Unit where
  Strategy _ := Fin 3
  Outcome := MiddleOutcome

abbrev targetSignature : GameSignature Unit where
  Strategy _ := Fin 3
  Outcome := TargetOutcome

abbrev source : GameForm Unit where
  sig := sourceSignature
  play profile := PMF.pure (.observed (profile ()))

abbrev middle : GameForm Unit where
  sig := middleSignature
  play profile :=
    if profile () = 0 then PMF.pure (.visible false)
    else if profile () = 1 then PMF.pure (.visible true)
    else coin.map .visible

abbrev target : GameForm Unit where
  sig := targetSignature
  play profile :=
    if profile () = 0 then PMF.pure (.published false)
    else if profile () = 1 then PMF.pure (.published true)
    else coin.map .published

def sourceObserve : SourceOutcome → Bool := fun | .observed value => value
def middleObserve : MiddleOutcome → Bool := fun | .visible value => value
def targetObserve : TargetOutcome → Bool := fun | .published value => value

def first : MixtureSimulationOn source middle sourceObserve middleObserve (fun _ _ => True) where
  compileStrategy _ strategy := if strategy then 1 else 0
  honest_law profile := by cases h : profile () <;> simp [source, middle, sourceObserve,
    middleObserve, h]
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    cases who
    fin_cases replacement
    · exact ⟨PMF.pure false, by simp [source, middle, sourceObserve, middleObserve]⟩
    · exact ⟨PMF.pure true, by simp [source, middle, sourceObserve, middleObserve]⟩
    · exact ⟨coin, by
        simp only [Fin.reduceFinMk, Profile.update_same, Fin.isValue, Fin.reduceEq,
          ↓reduceIte, PMF.map_comp, PMF.pure_map]
        change coin.map id = coin.bind PMF.pure
        rw [PMF.map_id, PMF.bind_pure]⟩

def second : MixtureSimulationOn middle target middleObserve targetObserve (fun _ _ => True) where
  compileStrategy _ strategy := strategy
  honest_law profile := by
    simp only [middle, target]
    split_ifs <;> simp only [PMF.pure_map, PMF.map_comp, Function.comp_def,
      middleObserve, targetObserve]
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    cases who
    refine ⟨PMF.pure replacement, ?_⟩
    simp only [middle, target, PMF.pure_bind, Profile.update_same]
    split_ifs <;> simp only [PMF.pure_map, PMF.map_comp, Function.comp_def,
      middleObserve, targetObserve]

def composed : MixtureSimulationOn source target sourceObserve targetObserve (fun _ _ => True) :=
  first.trans second (fun _ _ => trivial)

/-- The extra target strategy has a genuinely mixed observation law, so it
cannot be represented by selecting either pure source strategy. -/
theorem mixed_target_not_single_source :
    (target.play (fun _ => (2 : Fin 3))).map targetObserve ≠
        (source.play (fun _ => false)).map sourceObserve ∧
      (target.play (fun _ => (2 : Fin 3))).map targetObserve ≠
        (source.play (fun _ => true)).map sourceObserve := by
  have htarget : (target.play (fun _ => (2 : Fin 3))).map targetObserve = coin := by
    change (coin.map TargetOutcome.published).map targetObserve = coin
    rw [PMF.map_comp]
    change coin.map id = coin
    exact PMF.map_id coin
  constructor <;> intro h
  · rw [htarget] at h
    simp only [PMF.pure_map, sourceObserve] at h
    have := congrArg (fun law => (law true).toReal) h
    norm_num [coin, mix_apply_toReal, toReal_pure_apply] at this
  · rw [htarget] at h
    simp only [PMF.pure_map, sourceObserve] at h
    have := congrArg (fun law => (law false).toReal) h
    norm_num [coin, mix_apply_toReal, toReal_pure_apply] at this

/-- Composition expands the third game's mixed deviation into the source
mixture rather than strengthening it to one source strategy. -/
example : ∃ alternatives : PMF (source.sig.Strategy ()),
    (target.play (Profile.update (composed.compileProfile (fun _ => false)) () (2 : Fin 3))).map
        targetObserve =
      alternatives.bind fun alternative =>
        (source.play (Profile.update (fun _ => false) () alternative)).map sourceObserve :=
  composed.deviation_mixture (fun _ => false) () 2 trivial

end GameTheory.GameForm.MixtureSimulationOn.Tests
