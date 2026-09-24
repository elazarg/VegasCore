/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAliasSelector
import Interaction.ReactiveAliasConsistency
import GameTheoryExtensions.Analysis.Protocol.HistoryBayesProjection
import GameTheoryExtensions.Analysis.Protocol.CounterfactualBeliefs

/-! # Exact Bayes beliefs under private response aliases

Fixing one player's legal alias recall selects every compatible normalized
history. Other players retain their independently split responses. Own reach
is constant at a decision site, so changing only that player's alias selector
does not change its Bayes belief. The resulting law projects to the source
belief at every site, including sites outside the limiting strategy's support.
-/

noncomputable section

namespace Interaction.ReactiveApplication.SubmissionNormalization

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.InformationModel

variable {Principal : Type} [Fintype Principal] [DecidableEq Principal]
  {app : ReactiveApplication Principal}
  (normal : app.SubmissionNormalization) (raw : app.ResponseMenu)
  (stable : ∀ who past view,
    raw.actions who (normal.recall who past) view = raw.actions who past view)
  (closed : ∀ who past view response, response ∈ raw.actions who past view →
    normal.action who past view response ∈ raw.actions who past view)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

theorem splitBayes_projection
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (mixed : source.IsFullyMixed)
    (bayes : BehavioralAssessment.IsBayesConsistent
      ((normal.menu raw).information initial horizon scheduler) source
      ((normal.menu raw).decisionInformationAntichain initial horizon scheduler))
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1)
    (who : Principal) (original : (raw.information initial horizon scheduler).InformationSite who) :
    ((normal.splitBayes raw stable closed initial horizon scheduler source mixed weight positive
        atMostOne).belief who original).map
      (normal.informationHistory raw stable initial horizon scheduler who original.1) =
        source.belief who (normal.site raw stable initial horizon scheduler who original) := by
  classical
  let M := raw.information initial horizon scheduler
  let N := (normal.menu raw).information initial horizon scheduler
  let native := (normal.splitBayes raw stable closed initial horizon scheduler
    source mixed weight positive atMostOne).strategy
  let target := normal.site raw stable initial horizon scheduler who original
  have nativeMixed := normal.splitBayes_fullyMixed raw stable closed initial horizon scheduler
    source mixed weight positive atMostOne
  have nativePositive : 0 < M.informationMass native who original :=
    nativeMixed.informationMass_pos who original
  have sourcePositive : 0 < N.informationMass source.strategy who target :=
    mixed.informationMass_pos who target
  obtain ⟨reference, _running, response, member⟩ := original.2
  have hasData : ∃ past view, original.1 = some (past, view) := by
    cases infoEq : original.1 with
    | none =>
        rw [infoEq] at member
        change some response = none at member
        contradiction
    | some data => exact ⟨data.1, data.2, rfl⟩
  obtain ⟨past, view, infoEq⟩ := hasData
  let selected := Profile.update (sig := M.behavioralSignature) native who
    (normal.selectorPolicy raw stable closed initial horizon scheduler who past
      (source.strategy who))
  have selectedOwn : selected who =
      normal.selectorPolicy raw stable closed initial horizon scheduler who past
        (source.strategy who) := Profile.update_same ..
  have projects : ∀ player observed,
      (selected player observed).map
        (normal.choice raw stable initial horizon scheduler player observed) =
          source.strategy player (normal.info player observed) := by
    intro player observed
    by_cases same : player = who
    · subst player
      rw [selectedOwn]
      exact normal.selectorPolicy_project raw stable closed initial horizon scheduler
        who past (source.strategy who) observed
    · rw [show selected player = native player from Profile.update_of_ne _ _ same]
      exact normal.splitPolicy_project raw stable closed initial horizon scheduler player
        (source.strategy player) weight positive.le atMostOne observed
  let project := normal.history raw stable initial horizon scheduler
  have lengths : ∀ history, (project history).trace.length = history.trace.length :=
    fun history => normal.trace_length raw stable initial horizon scheduler history.trace
  have laws : ∀ fuel, (M.runBehavioral selected fuel).map project =
      N.runBehavioral source.strategy fuel := by
    intro fuel
    exact normal.runBehavioral_projection raw stable initial horizon scheduler selected
      source.strategy projects fuel (raw.protocol initial horizon scheduler).initHistory
  have maps : ∀ history, M.infoOf who history.trace = original.1 →
      N.infoOf who (project history).trace = target.1 := by
    intro history belongs
    exact (normal.history_info raw stable initial horizon scheduler who history).trans
      (congrArg (normal.info who) belongs)
  have reflects : ∀ history, 0 < M.historyReachProbability selected history →
      N.infoOf who (project history).trace = target.1 →
        M.infoOf who history.trace = original.1 := by
    intro history reached belongs
    rw [normal.history_info] at belongs
    change normal.info who (M.infoOf who history.trace) = normal.info who original.1 at belongs
    rw [infoEq] at belongs
    rw [infoEq]
    exact normal.selector_information_fiber raw stable closed initial horizon scheduler who
      reference.1 past view (reference.2.trans infoEq) (source.strategy who) selected
      selectedOwn history reached belongs
  have masses := M.informationMass_projection N selected source.strategy project lengths laws
    who original target maps reflects
  have selectedPositive : 0 < M.informationMass selected who original :=
    masses.symm ▸ sourcePositive
  have sameBeliefs := M.bayesBelief_eq_of_eq_off native selected who original
    (raw.decisionInformationAntichain initial horizon scheduler who original)
    (fun player different =>
      (Profile.update_of_ne (sig := M.behavioralSignature) native _ different).symm)
    (raw.commonPlayerReachAt initial horizon scheduler native who original)
    (raw.commonPlayerReachAt initial horizon scheduler selected who original)
    nativePositive selectedPositive
  have projected := M.bayesBelief_projection N selected source.strategy project lengths laws
    who original target maps reflects
    (raw.decisionInformationAntichain initial horizon scheduler who original)
    ((normal.menu raw).decisionInformationAntichain initial horizon scheduler who target)
    selectedPositive sourcePositive
  change (M.bayesBelief native who original
    (raw.decisionInformationAntichain initial horizon scheduler who original)
    nativePositive).map
      (normal.informationHistory raw stable initial horizon scheduler who original.1) = _
  rw [sameBeliefs]
  change (M.bayesBelief selected who original
    (raw.decisionInformationAntichain initial horizon scheduler who original)
    selectedPositive).map
      (fun history => (⟨project history.1, maps history.1 history.2⟩ :
        N.InformationHistory who target.1)) = _
  rw [projected]
  apply FinDist.ext_of_prob
  intro history
  rw [N.bayesBelief_prob]
  exact (bayes who target sourcePositive history).symm

/-- Every consistent normalized assessment has consistent raw beliefs for the
canonical response policy, with exactly the prescribed belief projection at
every decision site. Sequential rationality is a separate obligation. -/
theorem exists_canonical_consistent
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (consistent : source.IsSequentiallyConsistent
      ((normal.menu raw).decisionInformationAntichain initial horizon scheduler)) :
    ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
      target.strategy = (fun who => normal.canonicalPolicy raw stable closed
        initial horizon scheduler who (source.strategy who)) ∧
      target.IsSequentiallyConsistent (raw.decisionInformationAntichain initial horizon scheduler) ∧
      ∀ who (original : (raw.information initial horizon scheduler).InformationSite who),
        (target.belief who original).map
          (normal.informationHistory raw stable initial horizon scheduler who original.1) =
        source.belief who (normal.site raw stable initial horizon scheduler who original) := by
  obtain ⟨sequence, admissible, converges⟩ := consistent
  let weight (n : Nat) : ℝ := 1 / ((n : ℝ) + 1)
  have positive (n : Nat) : 0 < weight n := by dsimp [weight]; positivity
  have atMostOne (n : Nat) : weight n ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have vanishes : Filter.Tendsto weight Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply normal.consistent_of_splitBayes_projection raw stable closed initial horizon scheduler
    sequence source (fun n => (admissible n).1) converges weight positive atMostOne vanishes
  intro n who original
  exact normal.splitBayes_projection raw stable closed initial horizon scheduler
    (sequence n) (admissible n).1 (admissible n).2
      (weight n) (positive n) (atMostOne n) who original

end Interaction.ReactiveApplication.SubmissionNormalization
