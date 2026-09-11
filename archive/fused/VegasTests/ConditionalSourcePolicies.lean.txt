/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.ConditionalApplicationImage
import Vegas.Core.Strategy

/-! # Source strategies for the chance-free conditional fragment -/

noncomputable section

namespace VegasTests.ConditionalSourcePolicies

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  GameTheory GameTheory.Math.Probability
open VegasTests.ConditionalApplicationImage

abbrev PublicEnv := Env simpleExpr.Val [(2, .option .bool)]

def publicEnv (value : Option Bool) : PublicEnv :=
  Env.cons value (Env.empty simpleExpr.Val)

theorem publicEnv_get (env : PublicEnv) : publicEnv (env.get .here) = env := by
  funext name ty member
  cases member with
  | here => rfl
  | there member => cases member

/-- A pure source policy chooses its binding and later reads that own binding
when publishing. It is legal at every source-visible environment. -/
def sourceStrategy (outcome : Option Bool) : SourceBehavioralPolicy core (0 : Fin 2) := by
  intro context name ty guard site visible
  cases site with
  | here => exact FinDist.pure ⟨outcome.getD false, rfl⟩
  | commit site =>
      cases site with
      | here =>
          exact if outcome.isSome then
            FinDist.pure ⟨some (visible.get .here), by
              change decide (some (visible.get .here) = some (visible.get .here)) = true
              simp⟩
          else FinDist.pure ⟨none, rfl⟩
      | commit site =>
          cases site with
          | reveal site => cases site

/-- The other player's source policy is retained verbatim. -/
theorem sourceStrategy_law (profile : SourceBehavioralProfile core)
    (outcome : Option Bool) :
    (denoteSource core
      (Profile.update (sig := sourceGameSignature core) profile 0 (sourceStrategy outcome))
      source.env).map (fun terminal => (true, some terminal.erasePubEnv)) =
      FinDist.pure (true, some (publicEnv outcome)) := by
  cases outcome with
  | none =>
      simp [core, tail, denoteSource, sourceStrategy, Profile.update,
        SourceBehavioralProfile.afterCommit,
        publicEnv, source, VEnv.erasePubEnv]
  | some value =>
      simp [core, tail, denoteSource, sourceStrategy, Profile.update,
        SourceBehavioralProfile.afterCommit,
        publicEnv, source, VEnv.erasePubEnv]
      rfl

end VegasTests.ConditionalSourcePolicies

/-- info: 'VegasTests.ConditionalSourcePolicies.sourceStrategy_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalSourcePolicies.sourceStrategy_law
