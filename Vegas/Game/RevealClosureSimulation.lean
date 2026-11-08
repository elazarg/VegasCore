/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealClosureSolitary

/-! # Simulating a deviation through the closure

Every deviation of one player from honest effective-opening clients is
simulated phase by phase, from every phase boundary, by the last-served
erased-key laws of normalized graph deviations of the base, read at the
closure key: a solitary commitment or chance event is one phase, and a run of
concurrent reveals is a sequence of steps, one to each reveal of the deviator
in the run and a last one to the run's end. No condition on the runs of reveals
is needed.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- **A solitary phase through the closure.** At a phase boundary whose event
is not a reveal, the phase completing that event supplies its joint law and
averaged target for the closure key. -/
theorem solitary_phaseJoint {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (base : (serviceGraph setup mode).BehavioralProfile)
    (referenceIndependent : ReadyIndependent ((serviceGraph setup mode).normalizeProfile base))
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (independent : ∀ policy, LastIndependent
      ((serviceGraph setup mode).lastDeviationProfile base who policy) who)
    (relaxed : RelaxedOrder (serviceGraph setup mode))
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (event : (serviceGraph setup mode).EventId)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication) :
    PhaseJoint (fun execution : (serviceApplication setup mode deadline leaks).Execution =>
        runKey (EventGraph.closure ((serviceGraph setup mode).normalizeProfile base) who
          execution.application.config))
      ((serviceRuntime setup mode deadline).bindingTraffic leaks who) (keyView who)
      (fun policy => keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy)
        who)
      (PhaseBoundary scheduler (Function.update (serviceReferenceTurnPolicy setup mode deadline
        leaks bound turns (firstTurnTiming setup turns mode)
        ((serviceGraph setup mode).normalizeProfile base)) who deviation) horizon event.val)
      (fun execution => (serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
        (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
          who deviation)
        (fun current => event ∈ current.application.config.cut.completed) horizon execution) := by
  classical
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  let app := serviceApplication setup mode deadline leaks
  let players := Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
    turns (firstTurnTiming setup turns mode) R) who deviation
  have alone := alone_of_not_publication concurrent notPublication
  have endpoint := solitaryPhase_endpoint contract players concurrent event notPublication
  have stays : ∀ execution, PhaseBoundary scheduler players horizon event.val execution →
      event ∈ execution.application.config.cut.completed →
      app.runUntilHorizon scheduler players
        (fun current => event ∈ current.application.config.cut.completed) horizon execution =
        PMF.pure execution :=
    fun execution _ done => app.runUntil_of_stop scheduler players _ _ execution done
  have completesOf {Seed : Type} (prior : PMF Seed) (execution : Seed → app.Execution)
      (goods : ∀ seed ∈ prior.support,
        PhaseBoundary scheduler players horizon event.val (execution seed) ∧
          event ∉ (execution seed).application.config.cut.completed) :
      ∀ seed ∈ prior.support, ∀ final ∈ (app.runUntilHorizon scheduler players
        (fun current => event ∈ current.application.config.cut.completed) horizon
        (execution seed)).support, event ∈ final.application.config.cut.completed :=
    fun seed member => runUntilHorizon_stop contract players
      (fun current => event ∈ current.application.config.cut.completed)
      (fun current terminal => by rw [terminal]; exact Finset.mem_univ _)
      (execution seed) (goods seed member).1.supported (goods seed member).1.bounded
  have pendingPrefixOf {Seed : Type} (prior : PMF Seed) (execution : Seed → app.Execution)
      (goods : ∀ seed ∈ prior.support,
        PhaseBoundary scheduler players horizon event.val (execution seed) ∧
          event ∉ (execution seed).application.config.cut.completed) :
      ∀ seed ∈ prior.support, event ∉ (execution seed).application.config.cut.completed →
        (execution seed).application.config.cut.IsPrefix event.val :=
    fun seed member pending => (goods seed member).1.prefix_of_pending relaxed notPublication
      pending
  cases view : nodeView G event with
  | resolve owner payload binding checks outputEq codeEq =>
      exfalso
      apply notPublication
      rw [outputEq]
      trivial
  | bind owner payload outputEq codeEq =>
      have owned : G.actor? event = some owner := nodeView_bind_actor outputEq codeEq
      apply PhaseJoint.of_skipping
        (fun execution : app.Execution => event ∈ execution.application.config.cut.completed)
        (DefaultedBefore who event owner)
        (fun execution boundary => completed_iff_defaultedBefore R who owned boundary .refl)
        (fun execution boundary final reached => completed_iff_defaultedBefore R who owned
          boundary (runUntil_config_path scheduler players _ _ execution final reached))
        stays
      apply pending_closure_joint base who independent referenceIndependent relaxed event
        notPublication endpoint
      intro Seed prior execution goods noise factor
      by_cases isWho : owner = who
      · subst isWho
        exact lastOwned_phase_patched scheduler horizon bound turns
          (firstTurnTiming setup turns mode) R base owner deviation independent event owned alone
          prior execution (fun seed member => (goods seed member).1.quiescent)
          (pendingPrefixOf prior execution goods)
          (fun seed member done => ((goods seed member).2 done).elim)
          (completesOf prior execution goods) noise factor
      · obtain ⟨nextNoise, joint, averaged⟩ := lastForeign_phase scheduler horizon delay bound
          turns contract timely base referenceIndependent who deviation independent event owner
          owned isWho outputEq codeEq view alone prior execution
          (fun seed member => (goods seed member).1.supported)
          (fun seed member => (goods seed member).1.bounded) (pendingPrefixOf prior execution goods)
          (fun seed member _ => (goods seed member).1.seen.untouched (by omega))
          (fun seed member done => ((goods seed member).2 done).elim)
          noise factor
        exact ⟨id, nextNoise, joint, averaged, fun _ _ _ _ => rfl⟩
  | sample payload law outputEq codeEq =>
      have ownerless : G.actor? event = none := nodeView_sample_actor outputEq codeEq
      have visible : G.fieldVisibleTo who (.inr event) := by
        unfold EventGraph.fieldVisibleTo
        change (G.outputLayout event).VisibleTo who
        rw [outputEq]
        trivial
      have neverDone : ∀ execution, PhaseBoundary scheduler players horizon event.val execution →
          event ∉ execution.application.config.cut.completed := by
        intro execution boundary done
        obtain ⟨_, _, owner, ownedOwner, _⟩ := boundary.later event le_rfl done
        rw [ownerless] at ownedOwner
        cases ownedOwner
      apply PhaseJoint.of_skipping
        (fun execution : app.Execution => event ∈ execution.application.config.cut.completed)
        (fun _ => False)
        (fun execution boundary => iff_false_intro (neverDone execution boundary))
        (fun execution boundary _ _ => iff_false_intro (neverDone execution boundary))
        stays
      apply pending_closure_joint base who independent referenceIndependent relaxed event
        notPublication endpoint
      intro Seed prior execution goods noise factor
      obtain ⟨nextNoise, joint, averaged⟩ := lastChance_phase scheduler horizon bound turns
        (firstTurnTiming setup turns mode) R base who deviation independent event ownerless
        visible alone prior execution (fun seed member => (goods seed member).1.quiescent)
        (fun seed member => pendingPrefixOf prior execution goods seed member
          (goods seed member).2)
        (completesOf prior execution goods) noise factor
      exact ⟨id, nextNoise, joint, averaged, fun _ _ _ _ => rfl⟩

end Vegas
