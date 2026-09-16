/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.Policies

/-! # Commands emitted by the prescribed policy compiler

The runtime admits arbitrary traffic. These restrictions concern only the
actual compiled policy: it never prepares or submits for a future phase,
replays a packet, or emits a malformed payload. They are the local input to
candidate-freshness and reserved-inclusion proofs for unchanged players.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- The publicly addressable shape of a prescribed command. This predicate
does not impose restrictions on arbitrary native deviators. -/
def Command.AtPhase (runtime : GraphRuntime Player L Δ) (who : Player) (phase : Nat) :
    Command runtime → Prop
  | .wait | .privateCommand (.rememberDisclosure _) => True
  | .privateCommand (.prepare slot _) => slot = phase
  | .submit (.commitment site handle) => site = phase ∧ handle = (who, .prepared phase)
  | .submit (.opening site _ _) | .submit (.withhold site) => site = phase
  | .submit (.malformed _) | .replay _ => False

theorem compileAt_command_atPhase (runtime : GraphRuntime Player L Δ)
    (who : Player) (whole : Graph Player L Γ₀ Δ) (graph : Graph Player L Γ Δ)
    (policy : BehavioralPolicy who graph) (site : Nat)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (command : Command runtime)
    (supported : command ∈ (compileAt runtime who whole graph policy site history view).support) :
    Command.AtPhase runtime who view.application.publicState.pc command := by
  induction graph generalizing site with
  | ret =>
      simp only [compileAt, FinDist.mem_support_pure] at supported
      subst command
      trivial
  | sample name fresh law tail ih =>
      simp only [compileAt] at supported
      split at supported
      · simp only [FinDist.mem_support_pure] at supported
        subst command
        trivial
      · exact ih runtime whole policy (site + 1) history view command supported
  | bind name owner fresh tail ih =>
      simp only [compileAt] at supported
      split at supported
      · rename_i phase
        split at supported
        · split at supported
          · simp only [FinDist.mem_support_pure] at supported
            subst command
            trivial
          · split at supported
            · simp only [FinDist.mem_support_pure] at supported
              subst command
              exact ⟨phase.symm, by rw [phase]⟩
            · split at supported
              · split at supported
                · simp only [FinDist.support_map, Set.mem_image] at supported
                  obtain ⟨choice, _, rfl⟩ := supported
                  exact phase.symm
                · simp only [FinDist.mem_support_pure] at supported
                  subst command
                  trivial
              · simp only [FinDist.mem_support_pure] at supported
                subst command
                trivial
        · simp only [FinDist.mem_support_pure] at supported
          subst command
          trivial
      · exact ih runtime whole policy.2 (site + 1) history view command supported
  | resolve output owner binding fresh source checks tail ih =>
      simp only [compileAt] at supported
      split at supported
      · rename_i phase
        split at supported
        · split at supported
          · simp only [FinDist.mem_support_pure] at supported
            subst command
            trivial
          · split at supported
            · split at supported
              · split at supported
                · simp only [FinDist.support_map, Set.mem_image] at supported
                  obtain ⟨disclose, _, rfl⟩ := supported
                  trivial
                · simp only [FinDist.mem_support_pure] at supported
                  subst command
                  trivial
              · simp only [FinDist.mem_support_pure] at supported
                subst command
                trivial
            · split at supported
              · split at supported
                · split at supported
                  · simp only [disclosureCommand] at supported
                    split at supported
                    · simp only [FinDist.mem_support_pure] at supported
                      subst command
                      exact phase.symm
                    · split at supported <;>
                        simp only [FinDist.mem_support_pure] at supported <;>
                        subst command
                      · exact phase.symm
                      · trivial
                  · simp only [FinDist.mem_support_pure] at supported
                    subst command
                    exact phase.symm
                · simp only [FinDist.mem_support_pure] at supported
                  subst command
                  trivial
              · simp only [FinDist.mem_support_pure] at supported
                subst command
                trivial
        · simp only [FinDist.mem_support_pure] at supported
          subst command
          trivial
      · exact ih runtime whole policy.2 (site + 1) history view command supported

theorem compilePlayerPolicy_command_atPhase (runtime : GraphRuntime Player L Δ)
    (graph : Graph Player L Γ Δ) (who : Player) (policy : BehavioralPolicy who graph)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (command : Command runtime)
    (supported : command ∈ (runtime.compilePlayerPolicy graph who policy history view).support) :
    Command.AtPhase runtime who view.application.publicState.pc command :=
  compileAt_command_atPhase runtime who graph graph policy 0 history view command supported

/-- Once the current phase has been submitted, the prescribed player cannot
allocate a newer message while that phase remains active. This is why reserved
newest-message inclusion cannot strand its required packet. -/
theorem compileAt_wait_of_submitted (runtime : GraphRuntime Player L Δ)
    (who : Player) (whole : Graph Player L Γ₀ Δ) (graph : Graph Player L Γ Δ)
    (policy : BehavioralPolicy who graph) (site : Nat)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (submitted : submittedAt history view.application.publicState.pc = true) :
    compileAt runtime who whole graph policy site history view = FinDist.pure .wait := by
  induction graph generalizing site with
  | ret => rfl
  | sample name fresh law tail ih =>
      simp only [compileAt]
      split
      · rfl
      · exact ih runtime whole policy (site + 1) history view submitted
  | bind name owner fresh tail ih =>
      simp only [compileAt]
      split
      · rename_i phase
        have hsubmitted : submittedAt history site = true := phase ▸ submitted
        simp only [hsubmitted, ↓reduceIte]
        split <;> rfl
      · exact ih runtime whole policy.2 (site + 1) history view submitted
  | resolve output owner binding fresh source checks tail ih =>
      simp only [compileAt]
      split
      · rename_i phase
        have hsubmitted : submittedAt history site = true := phase ▸ submitted
        simp only [hsubmitted, ↓reduceIte]
        split <;> rfl
      · exact ih runtime whole policy.2 (site + 1) history view submitted

end Vegas.GraphRuntime
