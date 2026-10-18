/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialCallbackSeed
import Vegas.Examples.CommitSeedBroadcastNativeTimingWaitLaw

/-! # Exact quiet continuations from each initial native decision -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Later initial WAIT responses give the same physical fifth-command frame
from any current quiet initial decision. Earlier policy values are irrelevant. -/
theorem quiet_initial_remaining_prefix (seed : Seeds) (owner : Player)
    (players : Player → app.Policy)
    (waited : ∀ who, owner.val < who.val →
      players who ((initialCallback who).recall who)
        ((initialCallback who).observe app who) = PMF.pure ⟨none⟩) :
    app.runRounds (family seed) players (4 - owner.val)
      ((initialCallback owner).respond app owner ⟨none⟩) = PMF.pure quietStart := by
  have bobRound (waitedBob : players bob ((initialCallback bob).recall bob)
      ((initialCallback bob).observe app bob) = PMF.pure ⟨none⟩) :
      app.round (family seed) players (quietResponse initialExecution alice) =
        PMF.pure (quietResponse (quietResponse initialExecution alice) bob) := by
    rw [show quietResponse initialExecution alice =
      initialAliceCallback.respond app alice ⟨none⟩ from rfl, initial_bob_round]
    change (players bob ((initialCallback bob).recall bob)
      ((initialCallback bob).observe app bob)).map _ = _
    rw [waitedBob, PMF.pure_map]
    rfl
  have carolRound (waitedCarol : players carol ((initialCallback carol).recall carol)
      ((initialCallback carol).observe app carol) = PMF.pure ⟨none⟩) :
      app.round (family seed) players
        (quietResponse (quietResponse initialExecution alice) bob) =
          PMF.pure quietAfterCallbacks := by
    rw [show quietResponse (quietResponse initialExecution alice) bob =
      (initialBobCallback ⟨none⟩).respond app bob ⟨none⟩ from rfl, initial_carol_round]
    change (players carol ((initialCallback carol).recall carol)
      ((initialCallback carol).observe app carol)).map _ = _
    rw [waitedCarol, PMF.pure_map]
    rfl
  fin_cases owner
  · change app.runRounds (family seed) players 4 (quietResponse initialExecution alice) = _
    rw [ReactiveApplication.runRounds, bobRound (waited bob (by decide)), PMF.pure_bind,
      ReactiveApplication.runRounds, carolRound (waited carol (by decide)), PMF.pure_bind,
      quiet_initial_advances]
  · change app.runRounds (family seed) players 3
      (quietResponse (quietResponse initialExecution alice) bob) = _
    rw [ReactiveApplication.runRounds, carolRound (waited carol (by decide)), PMF.pure_bind,
      quiet_initial_advances]
  · exact quiet_initial_advances seed players

/-- The complete remaining native law factors through the literal quiet
fifth-command frame once the current and later initial responses wait. -/
theorem quiet_initial_fixed_finish (seed : Seeds) (owner : Player)
    (players : Player → app.Policy)
    (waited : ∀ who, owner.val ≤ who.val →
      players who ((initialCallback who).recall who)
        ((initialCallback who).observe app who) = PMF.pure ⟨none⟩) :
    app.finish initial horizon (family seed) players
      (some ⟨horizon - owner.val - 1, some owner, initialCallback owner⟩) =
        (app.runRounds (family seed) players (horizon - 5) quietStart).map app.finished := by
  have split : horizon - owner.val - 1 = (4 - owner.val) + (horizon - 5) := by
    have := owner.isLt
    norm_num
    omega
  rw [ReactiveApplication.finish, ReactiveApplication.resume, ReactiveApplication.invoke,
    waited owner le_rfl, PMF.pure_map, PMF.pure_bind, split, app.runRounds_add,
    quiet_initial_remaining_prefix seed owner players
      (fun who later => waited who (Nat.le_of_lt later)), PMF.pure_bind]

/-- The native mixed continuation retains the initialized original law at
this exact input, so the same factorization holds with its actual scheduler. -/
theorem quiet_initial_native_finish (owner : Player) (players : Player → app.Policy)
    (waited : ∀ who, owner.val ≤ who.val →
      players who ((initialCallback who).recall who)
        ((initialCallback who).observe app who) = PMF.pure ⟨none⟩) :
    app.finish initial horizon scheduler players
      (some ⟨horizon - owner.val - 1, some owner, initialCallback owner⟩) =
        (nativeSeedLaw.bind fun seed =>
          app.runRounds (family seed) players (horizon - 5) quietStart).map app.finished := by
  rw [native_finish_original_seed_law, quiet_initial_original_seed_posterior]
  simp_rw [quiet_initial_fixed_finish _ owner players waited]
  exact (PMF.map_bind ..).symm

end Vegas.Examples.CommitSeedBroadcast
