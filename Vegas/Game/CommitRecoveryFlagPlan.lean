/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryDomainPlan

/-! # Original occurrence flags independent of reduced domain tables

Source logical time is public and strictly advances at each instruction.
Counterfactual private queries at the same occurrence share their failure
flags. Domain values remain independent coordinates of the original table.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Public logical times that occur at genuine reduced source queries. -/
def commitRecoveryFlagSites (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (who : Player) : Finset Nat := by
  classical
  exact (setup.commitRecoveryDomainSites finite who).image (fun info => info.1.2.length)

/-- One owner has one pair of failure flags at each public occurrence. -/
def CommitRecoveryFlagDraw (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (who : Player) :=
  setup.commitRecoveryFlagSites finite who → Bool × Bool

/-- Omission and accepted source failure are independent, fixed-rate draws. -/
def commitRecoveryFlagLaw
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1) : PMF (Bool × Bool) :=
  (mix omission omissionNonnegative omissionBounded (PMF.pure true) (PMF.pure false)).bind
    fun omitted =>
      (mix bad badNonnegative badBounded (PMF.pure true) (PMF.pure false)).map (Prod.mk omitted)

omit [Fintype Player] in
/-- At a single query the independent occurrence flags and ordinary domain
draw give exactly the original legal three-class source perturbation. -/
theorem commitRecoveryFlagLaw_choice (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who info)) :
    (commitRecoveryFlagLaw omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded).bind
        (fun flags => values.map (setup.commitRecoveryValueFlags who info flags.1 flags.2)) =
      setup.commitRecoveryValueTremble who info omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded values := by
  rw [commitRecoveryFlagLaw, PMF.bind_bind]
  simp only [PMF.bind_map]
  exact setup.commitRecoveryValueFlags_law who info omission omissionNonnegative omissionBounded
    bad badNonnegative badBounded values

/-- Sample one complete public-occurrence flag array and one independent
domain table at initialization. Neither is refreshed at a saved entry. -/
def commitRecoveryFlagPlan (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (who : Player)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info)) :
    PMF (setup.CommitRecoveryFlagDraw finite who × setup.CommitRecoveryDomainDraw finite who) :=
  (independentProduct (fun _ : setup.commitRecoveryFlagSites finite who =>
    commitRecoveryFlagLaw omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded)).bind fun flags =>
        (setup.commitRecoveryDomainPlan finite who values).map (Prod.mk flags)

/-- The same occurrence flags are used at all counterfactual private queries
of that source time. Ordinary values use their original reduced coordinate. -/
def commitRecoveryFlagPolicy (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (who : Player)
    (memory : setup.CommitRecoveryFlagDraw finite who × setup.CommitRecoveryDomainDraw finite who) :
    setup.commitRecoveryErasedModel.Policy who := by
  classical
  intro info
  let flags := FiniteAssignment.resolve (fun _ : Nat => (false, false))
    (setup.commitRecoveryFlagSites finite who) memory.1 info.1.2.length
  let value := FiniteAssignment.resolve (setup.commitRecoveryDomainFallback who)
    (setup.commitRecoveryDomainSites finite who) memory.2 info
  exact setup.commitRecoveryValueFlags who info flags.1 flags.2 value

omit [Fintype Player] in
/-- Genuine chronological own actions have distinct public source times,
including actions in retired attempts and passive source transitions. -/
theorem commitRecoveryErasedModel_record_clock_nodup (who : Player) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state),
      ((setup.commitRecoveryErasedModel.ownPlay who trace).map
        (fun record => record.1.1.2.length)).Nodup
  | _, .start => by
      change ([] : List Nat).Nodup
      exact List.nodup_nil
  | _, .extend prior joint legal supported => by
      rw [InfoSignals.ownPlay_extend]
      cases chosen : joint who with
      | none =>
          exact commitRecoveryErasedModel_record_clock_nodup who prior
      | some action =>
          simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, commitRecoveryErasedModel_record_clock_nodup who prior⟩
          intro member
          obtain ⟨record, recorded, same⟩ := List.mem_map.mp member
          have acted : record.1 ∈ setup.commitRecoveryErasedModel.actedAt who prior := by
            rw [setup.commitRecoveryErasedModel.actedAt_eq_map_ownPlay]
            exact List.mem_map.mpr ⟨record, recorded, rfl⟩
          have earlier := setup.commitRecoveryErasedModel_record_word_length_lt who
            prior record.1 acted
          rw [same, setup.commitRecoveryErasedModel_word_length who prior] at earlier
          exact Nat.lt_irrefl _ earlier

/-- Any chronologically distinct genuine queries read independent source
answers from the ONE initialized occurrence-flag/domain-table joint law.
The assertion concerns the decoded answers, not equality of private plan joints. -/
theorem commitRecoveryFlagPlan_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (queries : List (setup.commitRecoveryErasedModel.InfoState who))
    (distinct : (queries.map (fun info => info.1.2.length)).Nodup)
    (played : ∀ info ∈ queries, info ∈ setup.commitRecoveryDomainSites finite who) :
    (setup.commitRecoveryFlagPlan finite who omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded values).map
        (fun memory (index : Fin queries.length) =>
          setup.commitRecoveryFlagPolicy finite who memory queries[index.val]) =
      independentProduct (fun index : Fin queries.length =>
        setup.commitRecoveryValueTremble who queries[index.val]
          omission omissionNonnegative omissionBounded bad badNonnegative badBounded
          (values queries[index.val])) := by
  classical
  let clock : Fin queries.length ↪ setup.commitRecoveryFlagSites finite who :=
    ⟨fun index => ⟨queries[index.val].1.2.length, Finset.mem_image.mpr
        ⟨queries[index.val], played _ (List.getElem_mem index.isLt), rfl⟩⟩, by
      intro first second same
      apply Fin.ext
      apply (List.Nodup.getElem_inj_iff distinct
        (i := first.val) (hi := by simpa only [List.length_map] using first.isLt)
        (j := second.val) (hj := by simpa only [List.length_map] using second.isLt)).mp
      simp only [List.getElem_map]
      exact congrArg Subtype.val same⟩
  let coordinate : Fin queries.length ↪ setup.commitRecoveryDomainSites finite who :=
    ⟨fun index => ⟨queries[index.val], played _ (List.getElem_mem index.isLt)⟩, by
      intro first second same
      apply clock.injective
      apply Subtype.ext
      exact congrArg (fun info : setup.commitRecoveryErasedModel.InfoState who =>
        info.1.2.length) (congrArg Subtype.val same)⟩
  let flagLaw := commitRecoveryFlagLaw omission omissionNonnegative omissionBounded
    bad badNonnegative badBounded
  let flags : PMF (setup.CommitRecoveryFlagDraw finite who) :=
    independentProduct (fun _ => flagLaw)
  let domains := setup.commitRecoveryDomainPlan finite who values
  let flagRead := fun draw : setup.CommitRecoveryFlagDraw finite who =>
    fun index : Fin queries.length => draw (clock index)
  let domainRead := fun draw : setup.CommitRecoveryDomainDraw finite who =>
    fun index : Fin queries.length => draw (coordinate index)
  have flagReadout : flags.map flagRead =
      independentProduct (fun _ : Fin queries.length => flagLaw) :=
    independentProduct_map_embedding clock (fun _ => flagLaw)
  have domainReadout : domains.map domainRead =
      independentProduct (fun index : Fin queries.length => values queries[index.val]) :=
    independentProduct_map_embedding coordinate (fun site => values site.val)
  calc
    _ = (flags.map flagRead).bind (fun localFlags =>
        (domains.map domainRead).map fun localValues =>
          fun index : Fin queries.length => setup.commitRecoveryValueFlags who queries[index.val]
            (localFlags index).1 (localFlags index).2 (localValues index)) := by
      simp only [commitRecoveryFlagPlan, PMF.map_bind, PMF.map_comp, PMF.bind_map,
        Function.comp_def]
      apply congrArg (PMF.bind flags)
      funext flagTable
      apply congrArg (PMF.map · domains)
      funext domainTable index
      change setup.commitRecoveryValueFlags who queries[index.val]
          (FiniteAssignment.resolve (fun _ : Nat => (false, false))
            (setup.commitRecoveryFlagSites finite who) flagTable queries[index.val].1.2.length).1
          (FiniteAssignment.resolve (fun _ : Nat => (false, false))
            (setup.commitRecoveryFlagSites finite who) flagTable queries[index.val].1.2.length).2
          (FiniteAssignment.resolve (setup.commitRecoveryDomainFallback who)
            (setup.commitRecoveryDomainSites finite who) domainTable queries[index.val]) = _
      have clockPlayed : queries[index.val].1.2.length ∈
          setup.commitRecoveryFlagSites finite who := (clock index).property
      have queryPlayed : queries[index.val] ∈
          setup.commitRecoveryDomainSites finite who := (coordinate index).property
      rw [FiniteAssignment.resolve_of_mem _ _ _ clockPlayed,
        FiniteAssignment.resolve_of_mem _ _ _ queryPlayed]
      rfl
    _ = _ := by
      rw [flagReadout, domainReadout]
      let kernel (index : Fin queries.length) (pair : Bool × Bool) :=
        (values queries[index.val]).map
          (setup.commitRecoveryValueFlags who queries[index.val] pair.1 pair.2)
      calc
        _ = (independentProduct (fun _ : Fin queries.length => flagLaw)).bind
            (fun localFlags =>
              independentProduct (fun index => kernel index (localFlags index))) := by
          apply congrArg (PMF.bind (independentProduct (fun _ : Fin queries.length => flagLaw)))
          funext localFlags
          exact independentProduct_map
            (fun index : Fin queries.length => values queries[index.val])
            (fun index value => setup.commitRecoveryValueFlags who queries[index.val]
              (localFlags index).1 (localFlags index).2 value)
        _ = independentProduct (fun index => flagLaw.bind (kernel index)) :=
          independentProduct_bind (fun _ : Fin queries.length => flagLaw) kernel
        _ = _ := by
          apply congrArg independentProduct
          funext index
          exact setup.commitRecoveryFlagLaw_choice who queries[index.val]
            omission omissionNonnegative omissionBounded bad badNonnegative badBounded _

/-- The decoded chronological action vector has its exact source likelihood,
with omissions and accepted failures retained at every retired occurrence. -/
theorem commitRecoveryFlagPlan_record_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (history : setup.commitRecoveryProtocol.History) :
    let queries := (setup.commitRecoveryErasedModel.ownPlay who history.trace).map Prod.fst
    (setup.commitRecoveryFlagPlan finite who omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded values).map
        (fun memory (index : Fin queries.length) =>
          setup.commitRecoveryFlagPolicy finite who memory queries[index.val]) =
      independentProduct (fun index : Fin queries.length =>
        setup.commitRecoveryValueTremble who queries[index.val]
          omission omissionNonnegative omissionBounded bad badNonnegative badBounded
          (values queries[index.val])) := by
  classical
  intro queries
  apply setup.commitRecoveryFlagPlan_readout
  · simpa only [queries, List.map_map, Function.comp_def] using
      setup.commitRecoveryErasedModel_record_clock_nodup who history.trace
  · intro info present
    obtain ⟨record, recorded, rfl⟩ := List.mem_map.mp present
    obtain ⟨site, observed, _legal⟩ :=
      setup.commitRecoveryErasedModel.exists_informationSite_of_mem_ownPlay history.trace recorded
    obtain ⟨prior, running, _⟩ := site.2
    have played := setup.commitRecoveryDomainSites_current finite who prior.1 running
    rw [prior.2, observed] at played
    exact played

/-- The present query and every remembered action use distinct occurrence
flags in the initialized plan. This is the joint law needed for conditioning. -/
theorem commitRecoveryFlagPlan_current_record_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) :
    let queries := setup.commitRecoveryErasedModel.infoOf who history.trace ::
      (setup.commitRecoveryErasedModel.ownPlay who history.trace).map Prod.fst
    (setup.commitRecoveryFlagPlan finite who omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded values).map
        (fun memory (index : Fin queries.length) =>
          setup.commitRecoveryFlagPolicy finite who memory queries[index.val]) =
      independentProduct (fun index : Fin queries.length =>
        setup.commitRecoveryValueTremble who queries[index.val]
          omission omissionNonnegative omissionBounded bad badNonnegative badBounded
          (values queries[index.val])) := by
  classical
  intro queries
  apply setup.commitRecoveryFlagPlan_readout
  · simp only [queries, List.map_cons, List.map_map, Function.comp_def]
    refine List.nodup_cons.mpr ⟨?_,
      setup.commitRecoveryErasedModel_record_clock_nodup who history.trace⟩
    intro member
    obtain ⟨record, recorded, equal⟩ := List.mem_map.mp member
    have acted : record.1 ∈ setup.commitRecoveryErasedModel.actedAt who history.trace := by
      rw [setup.commitRecoveryErasedModel.actedAt_eq_map_ownPlay]
      exact List.mem_map.mpr ⟨record, recorded, rfl⟩
    have earlier := setup.commitRecoveryErasedModel_record_word_length_lt who
      history.trace record.1 acted
    rw [equal, setup.commitRecoveryErasedModel_word_length who history.trace] at earlier
    exact Nat.lt_irrefl _ earlier
  · intro info present
    rcases List.mem_cons.mp present with rfl | past
    · exact setup.commitRecoveryDomainSites_current finite who history running
    · obtain ⟨record, recorded, rfl⟩ := List.mem_map.mp past
      obtain ⟨site, observed, _legal⟩ :=
        setup.commitRecoveryErasedModel.exists_informationSite_of_mem_ownPlay history.trace recorded
      obtain ⟨prior, priorRunning, _⟩ := site.2
      have played := setup.commitRecoveryDomainSites_current finite who prior.1 priorRunning
      rw [prior.2, observed] at played
      exact played

end Vegas.SourceProgram.Setup
