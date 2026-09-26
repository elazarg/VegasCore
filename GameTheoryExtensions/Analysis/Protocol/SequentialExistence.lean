/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.AgentCompletionLimit
import GameTheoryExtensions.Analysis.Protocol.SequentialOneShot

/-! # Sequential equilibrium existence for finite clocked protocols

All information agents are free in the constrained completion construction.
One common assessment limit is consistent and locally optimal, and the
posterior one-shot principle supplies whole-policy sequential rationality.
The theorem uses the original evaluator and standard assessment predicate.
Its contexts evaluate the stated remaining horizon. Interpreting their payoffs
as completed-run terminal utilities additionally requires a sufficient horizon.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} (M : InformationModel E) [Finite E.History]
  [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]

/-- Finite perfect-recall protocols with finite decision menus admit a
sequential equilibrium in these remaining-horizon contexts for arbitrary real
payoffs. The fully mixed reference supplies finite supported menus and need
not satisfy any incentive condition. Adequacy for terminal payoffs is separate. -/
theorem exists_sequential_equilibrium
    (reference : M.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (perfectRecall : M.PerfectRecall) (horizon : Nat)
    (payoff : Player → E.History → ℝ)
    (depth : ∀ who, M.InformationSite who → Nat)
    (clock : ∀ who site, InformationSite.CommonDepth M site (depth who site))
    (within : ∀ who site, depth who site ≤ horizon) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.IsSequentialEquilibriumFor
        (M.decisionInformationAntichain_of_perfectRecall perfectRecall)
        (fun who site =>
          assessment.continuationContext site (payoff who) (horizon - depth who site)) := by
  classical
  let _ := Fintype.ofFinite E.History
  let sites (who : Player) : Finset (M.InfoState who) :=
    Finset.univ.image fun history : {history : E.History // ¬ E.terminal history.state} =>
      M.infoOf who history.1.trace
  have covered : M.CoversInformationSites sites horizon := by
    intro history _ nonterminal who
    exact Finset.mem_image.mpr ⟨⟨history, nonterminal⟩, Finset.mem_univ _, rfl⟩
  have decisionCovered (who : Player) (site : M.InformationSite who) : site.1 ∈ sites who := by
    obtain ⟨history, running, _⟩ := site.2
    exact Finset.mem_image.mpr ⟨⟨history.1, running⟩, Finset.mem_univ _, history.2⟩
  let fallback (who : Player) : M.Policy who := fun info =>
    ((reference.strategy who info).support_nonempty).choose
  let laws (agent : M.InformationAgent sites) := reference.strategy agent.1 agent.2.1
  have full (agent : M.InformationAgent sites) : (laws agent).FullSupport := by
    obtain ⟨history, _, observed⟩ := Finset.mem_image.mp agent.2.2
    dsimp only [laws]
    rw [← observed]
    by_cases active : E.active history.1.state agent.1
    · obtain ⟨site, same⟩ := M.exists_informationSite_of_active
        agent.1 history.1 history.2 active
      rw [← same]
      exact referenceMixed agent.1 site
    · let _ := M.subsingleton_choice_of_not_active history.1.trace active
      intro choice
      obtain ⟨witness, supported⟩ :=
        (reference.strategy agent.1 (M.infoOf agent.1 history.1.trace)).support_nonempty
      simpa only [Subsingleton.elim witness choice] using supported
  let epsilon (n : ℕ) : ℝ := (1 / 2) * (1 / ((n : ℝ) + 1))
  have positive (n : ℕ) : 0 < epsilon n := by dsimp only [epsilon]; positivity
  have small (n : ℕ) : epsilon n < 1 := by
    have bound : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    dsimp only [epsilon]
    linarith
  have vanishes : Tendsto epsilon atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
  obtain ⟨_, _, assessment, _, _, _, _, _, _, consistent, localOptimal⟩ :=
    exists_consistent_free_agent_completion sites fallback horizon perfectRecall covered
      decisionCovered (fun history who => payoff who history) Finset.univ
      (fun _ => laws) laws (fun _ agent _ => full agent) full
      epsilon positive small vanishes
  refine ⟨assessment, ?_, consistent⟩
  apply consistent.sequentiallyRational_of_localOptimal perfectRecall horizon payoff
    depth clock within
  intro who site before law
  exact localOptimal who site (decisionCovered who site) (Finset.mem_univ _)
    (depth who site) (horizon - depth who site) (clock who site)
    (by have := within who site; omega) law

end GameTheory.Protocol.InformationModel
