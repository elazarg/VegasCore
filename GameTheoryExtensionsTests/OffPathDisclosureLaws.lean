/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.OffPathDisclosureIncentives

/-! # Initialized law preservation does not imply SPE preservation

Erasing Bob's extra information gives a playerwise, utility-independent
compiler preserving the complete terminal state law for every source profile.
Around the prescribed stop profile, every target unilateral deviation also
has a source match. Nevertheless the information experiment has no uniform
SPE-preserving translation, as proved in the imported module.
-/

noncomputable section

namespace GameTheoryExtensionsTests.OffPathDisclosure

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

def forgetInfo (who : Bool) (info : Option Bool) : Option Bool :=
  if who then info.map (fun _ => false) else info

def compile (who : Bool) (policy : (model false).BehavioralPolicy who) :
    (model true).BehavioralPolicy who := fun info =>
  (policy (forgetInfo who info)).map fun choice => ⟨choice.val, by
    have legal := choice.property
    cases who <;> cases info <;> exact legal⟩

theorem compiled_choice (profile : Profile (model false).behavioralSignature)
    (who : Bool) (info : Option Bool) :
    choiceLaw (Profile.map (target := (model true).behavioralSignature) compile profile) who info =
      choiceLaw profile who (forgetInfo who info) := by
  simp only [choiceLaw, Profile.map, compile, FinDist.map_comp, Function.comp_def]

theorem compiled_prescribed :
    Profile.map (target := (model true).behavioralSignature) compile (prescribed false) =
      prescribed true := by
  funext who info
  cases who <;> cases info <;>
    simp [Profile.map, compile, prescribed, choose, forgetInfo]

/-- The state retains both the original private bit and public result. -/
theorem compiled_initial_law (profile : Profile (model false).behavioralSignature) :
    ((model true).runSingleMoverBehavioralFrom single
      (Profile.map (target := (model true).behavioralSignature) compile profile)
      3 arena.initHistory).map History.state =
    ((model false).runSingleMoverBehavioralFrom single profile 3 arena.initHistory).map
      History.state := by
  rw [run_initial, run_initial]
  simp only [resultLaw, compiled_choice, forgetInfo, Bool.false_eq_true, ↓reduceIte,
    Option.map_some]

/-- At the prescribed profile, even all target unilateral deviations preserve
the joint type/result law. The opponent of the deviator has not deviated. -/
theorem initial_deviation_law (who : Bool) (alternative : (model true).BehavioralPolicy who) :
    ((model true).runSingleMoverBehavioralFrom single
      (Profile.update (prescribed true) who alternative) 3 arena.initHistory).map History.state =
    ((model false).runSingleMoverBehavioralFrom single
      (Profile.update (prescribed false) who alternative) 3 arena.initHistory).map
      History.state := by
  rw [run_initial, run_initial]
  cases who <;> simp [resultLaw, choiceLaw, Profile.update, prescribed, choose]

end GameTheoryExtensionsTests.OffPathDisclosure
