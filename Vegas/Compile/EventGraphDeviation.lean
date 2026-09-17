/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphScheduling
import Vegas.Compile.EventGraphPolicyAlignment
import Vegas.EventGraph.SchedulerMixture

/-! # Setup-wide deviation laws for compiled event graphs -/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Every canonical graph deviation is implemented by its single source
backtranslation, uniformly over the concrete initial source state. -/
theorem canonical_deviation_terminalState_law
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup) (profile : BehavioralProfile program)
    (who : Player) (replacement : (toEventGraph program unique).BehavioralPolicy who)
    (state : State L Γ) :
    ((toEventGraph program unique).terminalOutcomes
      (toEventGraph program unique).canonicalScheduler
      (Profile.update (sig := (toEventGraph program unique).gameSignature)
        (compileEventProfile program unique profile) who replacement)
      (encodeInputs state)).map (terminalState program unique) =
        SourceProgram.run program
          (Profile.update (sig := SourceProgram.gameSignature program) profile who
            (backtranslateEventPolicy program unique who replacement)) state := by
  let graph := toEventGraph program unique
  let translated := Profile.update (sig := SourceProgram.gameSignature program) profile who
    (backtranslateEventPolicy program unique who replacement)
  have kernelLaw :
      graph.runPolicies graph.canonicalScheduler (compileEventProfile program unique translated)
          (encodeInputs state) =
        graph.runPolicies graph.canonicalScheduler
          (Profile.update (sig := graph.gameSignature)
            (compileEventProfile program unique profile) who
            (graph.normalizePolicy who replacement)) (encodeInputs state) := by
    apply Vegas.EventGraph.runPolicies_canonical_eq_of_reachable
    intro config reachable offset ordered event ready rank owner actor
    rw [show compileEventProfile program unique translated =
        Profile.update (sig := graph.gameSignature) (compileEventProfile program unique profile)
          who (compileEventPolicy program unique who
            (backtranslateEventPolicy program unique who replacement)) from
      compileEventProfile_update program unique profile who _]
    by_cases same : owner = who
    · subst owner
      simp only [Profile.update_same]
      exact compileEventPolicy_backtranslate_at_prefix program unique who replacement
        (encodeInputs state) config reachable offset ordered event ready rank actor
    · simp only [Profile.update_of_ne _ _ same]
  have normalized := graph.runPolicies_canonical_normalize_eq
    (Profile.update (sig := graph.gameSignature)
      (compileEventProfile program unique profile) who replacement) (encodeInputs state)
  rw [Vegas.EventGraph.normalizeProfile_update, normalizeProfile_compileEventProfile,
    ← kernelLaw] at normalized
  rw [← canonical_terminalState_law program unique translated state]
  apply FinDist.map_injective (f := some) (Option.some_injective _)
  rw [terminalOutcomes_map_decode, terminalOutcomes_map_decode, normalized]

/-- Decode a canonical graph replacement through its source backtranslation.
The same replacement is used throughout the private initial-state law. -/
theorem canonical_setup_deviation_decode
    (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (who : Player)
    (replacement : setup.eventGraph.BehavioralPolicy who) :
    (setup.initialLaw.bind fun initial =>
      ((setup.eventGraph.runPolicies setup.eventGraph.canonicalScheduler
        (setup.eventGraph.normalizeProfile
          (Profile.update (sig := setup.eventGraph.gameSignature)
            (compileEventProfile setup.program setup.namesNodup profile) who replacement))
        (setup.eventInputs initial)).map (fun config => config.store)).map
          (decodeState? (terminalRefs setup.program))) =
      (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program) profile who
        (backtranslateEventPolicy setup.program setup.namesNodup who replacement))).map some := by
  rw [Setup.run, FinDist.map_bind]
  apply FinDist.bind_congr
  intro initial _
  rw [← setup.eventGraph.runPolicies_canonical_normalize_eq]
  have law := congrArg (fun measure => measure.map some)
    (canonical_deviation_terminalState_law setup.program setup.namesNodup profile who replacement
      initial)
  rw [terminalOutcomes_map_decode] at law
  exact law

/-- A canonical graph replacement has exactly the distributed source law of
one backtranslated policy. The policy is fixed before the private initial
state is sampled, and every opponent policy remains unchanged. -/
theorem canonical_setup_deviation_law
    (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (who : Player)
    (replacement : setup.eventGraph.BehavioralPolicy who) :
    ((setup.eventGraph.canonicalGame
        (setup.initialLaw.map fun initial => setup.eventInputs initial)).play
      (Profile.update (sig := setup.eventGraph.gameSignature)
        (compileEventProfile setup.program setup.namesNodup profile) who replacement)).map
          (terminalState setup.program setup.namesNodup) =
      setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
        profile who
          (backtranslateEventPolicy setup.program setup.namesNodup who replacement)) := by
  unfold Vegas.EventGraph.canonicalGame Vegas.EventGraph.gameForm Setup.run
  simp only [FinDist.map_bind, FinDist.bind_map]
  apply FinDist.bind_congr
  intro initial _
  exact canonical_deviation_terminalState_law setup.program setup.namesNodup profile who
    replacement initial

/-- Read the graph-local scheduler mixture through the compiler's total
terminal-state decoder, retaining a single mixture across private setup. -/
private theorem scheduled_canonical_deviation_mixture
    (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (profile : BehavioralProfile setup.program) (who : Player)
    (replacement : setup.eventGraph.BehavioralPolicy who) :
    ∃ mixture : FinDist (setup.eventGraph.BehavioralPolicy who),
      (setup.initialLaw.bind fun initial =>
        (setup.eventGraph.terminalOutcomes scheduler
          (Profile.update (sig := setup.eventGraph.gameSignature)
            (compileEventProfile setup.program setup.namesNodup profile) who replacement)
          (setup.eventInputs initial)).map
            (terminalState setup.program setup.namesNodup)) =
        mixture.bind fun alternative =>
          setup.initialLaw.bind fun initial =>
            (setup.eventGraph.terminalOutcomes setup.eventGraph.canonicalScheduler
              (Profile.update (sig := setup.eventGraph.gameSignature)
                (compileEventProfile setup.program setup.namesNodup profile) who alternative)
              (setup.eventInputs initial)).map
                (terminalState setup.program setup.namesNodup) := by
  dsimp only [Setup.eventGraph] at *
  let ordered := toEventGraph_barrierOrdered setup.program setup.namesNodup
  obtain ⟨mixture, law⟩ := ordered.exists_deviation_mixture
      (setup.initialLaw.map fun initial => setup.eventInputs initial) scheduler
      (compileEventProfile setup.program setup.namesNodup profile) who replacement
  rw [normalizeProfile_compileEventProfile] at law
  refine ⟨mixture, ?_⟩
  apply FinDist.map_injective (f := some) (Option.some_injective _)
  simp only [FinDist.map_bind]
  simp_rw [terminalOutcomes_map_decode]
  have decoded := congrArg
    (fun distribution => distribution.map
      (decodeState? (terminalRefs setup.program))) law
  simpa only [FinDist.map_bind, FinDist.bind_map] using decoded

/-- Every unilateral asynchronous graph deviation has the law of a finite
mixture of source deviations, against unchanged source opponents. The mixture
is chosen before the private initial state is sampled. -/
theorem scheduled_setup_deviation_law
    (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (profile : BehavioralProfile setup.program) (who : Player)
    (replacement : setup.eventGraph.BehavioralPolicy who) :
    ∃ mixture : FinDist (BehavioralPolicy who setup.program),
      (setup.initialLaw.bind fun initial =>
        (setup.eventGraph.terminalOutcomes scheduler
          (Profile.update (sig := setup.eventGraph.gameSignature)
            (compileEventProfile setup.program setup.namesNodup profile) who replacement)
          (setup.eventInputs initial)).map
            (terminalState setup.program setup.namesNodup)) =
        mixture.bind fun alternative =>
          setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
            profile who alternative) := by
  obtain ⟨mixture, law⟩ := scheduled_canonical_deviation_mixture setup scheduler
    profile who replacement
  refine ⟨mixture.map (backtranslateEventPolicy setup.program setup.namesNodup who), ?_⟩
  rw [law, FinDist.bind_map]
  apply FinDist.bind_congr
  intro alternative _
  unfold Setup.run
  apply FinDist.bind_congr
  intro initial _
  exact canonical_deviation_terminalState_law setup.program setup.namesNodup profile
    who alternative initial

end Vegas.SourceProgram.EventLowering
