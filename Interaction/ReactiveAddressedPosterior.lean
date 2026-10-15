/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAddressedScheduler
import Interaction.ReactiveSchedulerTranscript

/-! # Conditional products for an actually addressed scheduler

Fixing the retained original remainder seed fixes every addressed request in an
actual command transcript. Command consistency then restricts each local seed
separately. The resulting posterior product is derived from the planner and
original independent product, rather than supplied as a scheduler premise.
-/

noncomputable section

namespace Interaction.ReactiveApplication.AddressedScheduler

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal Address LocalSeed RestSeed Query : Type}
  {app : ReactiveApplication Principal}
  (controller : AddressedScheduler app Address LocalSeed RestSeed Query)

def remainderConsistentFrom (rest : RestSeed) (earlier : List app.EnvironmentEntry) :
    List app.EnvironmentEntry → Prop
  | [] => True
  | entry :: later =>
      (controller.request rest earlier entry.beforeView = none →
        controller.fallback rest earlier entry.beforeView = entry.command) ∧
      remainderConsistentFrom rest (earlier ++ [entry]) later

def coordinateConsistentFrom (rest : RestSeed) (address : Address) (seed : LocalSeed)
    (earlier : List app.EnvironmentEntry) : List app.EnvironmentEntry → Prop
  | [] => True
  | entry :: later =>
      (∀ query, controller.request rest earlier entry.beforeView = some (address, query) →
        controller.reply address seed query = entry.command) ∧
      coordinateConsistentFrom rest address seed (earlier ++ [entry]) later

/-- For a fixed original remainder, concrete command consistency is a rectangle
in all local seed coordinates. -/
theorem command_rectangle (rest : RestSeed) (values : Address → LocalSeed)
    (earlier past : List app.EnvironmentEntry) :
    app.commandConsistentFrom controller.choose (rest, values) earlier past ↔
      controller.remainderConsistentFrom rest earlier past ∧
        ∀ address, controller.coordinateConsistentFrom rest address (values address)
          earlier past := by
  induction past generalizing earlier with
  | nil => simp only [commandConsistentFrom, remainderConsistentFrom,
      coordinateConsistentFrom, implies_true, and_self]
  | cons entry later ih =>
      constructor
      · rintro ⟨first, future⟩
        obtain ⟨remainder, coordinates⟩ := (ih _).mp future
        refine ⟨⟨?_, remainder⟩, fun address => ⟨?_, coordinates address⟩⟩
        · intro absent
          simpa only [choose, absent] using first
        · intro query requested
          simpa only [choose, requested] using first
      · rintro ⟨⟨remainder, restLater⟩, coordinates⟩
        refine ⟨?_, (ih _).mpr ⟨restLater, fun address => (coordinates address).2⟩⟩
        cases requested : controller.request rest earlier entry.beforeView with
        | none => simpa only [choose, requested] using remainder requested
        | some pair =>
            simpa only [choose, requested] using (coordinates pair.1).1 pair.2 requested

/-- An extra coordinate retains the original remainder seed. -/
def CoordinateSeed : Option Address → Type
  | none => RestSeed
  | some _ => LocalSeed

local notation "AllSeed" =>
  CoordinateSeed (LocalSeed := LocalSeed) (RestSeed := RestSeed)

def coordinateLaws (laws : Address → PMF LocalSeed) (restLaw : PMF RestSeed) :
    (index : Option Address) → PMF (AllSeed index)
  | none => restLaw
  | some address => laws address

def unpack (values : (index : Option Address) →
    AllSeed index) :
    RestSeed × (Address → LocalSeed) := (values none, fun address => values (some address))

variable [Fintype Address]

/-- The coordinate representation is the same original all-event seed law. -/
theorem unpack_prior (laws : Address → PMF LocalSeed) (restLaw : PMF RestSeed) :
    (independentProduct (coordinateLaws laws restLaw)).map unpack = prior laws restLaw := by
  classical
  let embed : Address ↪ {index : Option Address // index ≠ none} :=
    ⟨fun address => ⟨some address, by simp⟩, by
      intro first second same
      exact Option.some.inj (congrArg Subtype.val same)⟩
  have marginal := independentProduct_map_embedding
    (A := fun index : {index : Option Address // index ≠ none} => AllSeed index.1) embed
    (fun index : {index : Option Address // index ≠ none} =>
      coordinateLaws laws restLaw index.1)
  rw [independentProduct_splitAt (coordinateLaws laws restLaw) none, PMF.map_bind]
  change (restLaw.bind _) = _
  apply congrArg restLaw.bind
  funext rest
  have mapped := congrArg (fun law => law.map (Prod.mk rest)) marginal
  simpa [unpack, embed, coordinateLaws, PMF.map_comp, Function.comp_def] using mapped

def coordinateImplementation (laws : Address → PMF LocalSeed) (restLaw : PMF RestSeed) :
    app.SchedulerImplementation ((index : Option Address) →
      AllSeed index) :=
  app.schedulerMixture (independentProduct (coordinateLaws laws restLaw))
    (fun values => controller.family (unpack values))

def coordinateRestriction (rest : RestSeed) (past : List app.EnvironmentEntry) :
    (index : Option Address) → Set (AllSeed index)
  | none => {seed | seed = rest}
  | some address => {seed | controller.coordinateConsistentFrom rest address seed [] past}

/-- The complete actual scheduler posterior, additionally conditioned on its
original remainder seed, filters all local seed coordinates separately. -/
theorem posterior_given_remainder (laws : Address → PMF LocalSeed) (restLaw : PMF RestSeed)
    (past : List app.EnvironmentEntry) (rest : RestSeed)
    (positive : ∃ values ∈ {values |
      app.commandConsistentFrom (fun values => controller.choose (unpack values)) values [] past ∧
        values none = rest}, values ∈ (independentProduct (coordinateLaws laws restLaw)).support) :
    ∃ positiveCoordinates : ∀ index : Option Address,
      ∃ seed ∈ controller.coordinateRestriction rest past index,
        seed ∈ (coordinateLaws laws restLaw index).support,
      fiberPosterior ((controller.coordinateImplementation laws restLaw).posterior past)
        (fun values => values none) rest =
          independentProduct (fun index => (coordinateLaws laws restLaw index).filter
            (controller.coordinateRestriction rest past index) (positiveCoordinates index)) := by
  let restriction := controller.coordinateRestriction rest past
  have originalPositive := positive
  obtain ⟨witness, compatible, supported⟩ := positive
  have witnessCompatible : app.commandConsistentFrom controller.choose
      (rest, fun address => witness (some address)) [] past := by
    simpa only [app.commandConsistentFrom_comp, unpack, compatible.2] using compatible.1
  have remainder := ((controller.command_rectangle rest _ [] past).mp witnessCompatible).1
  have rectangle : {values |
      app.commandConsistentFrom (fun values => controller.choose (unpack values)) values [] past ∧
        values none = rest} = Set.pi Set.univ restriction := by
    ext values
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · rintro ⟨commands, same⟩ index
      have localCommands : app.commandConsistentFrom controller.choose
          (rest, fun address => values (some address)) [] past := by
        simpa only [app.commandConsistentFrom_comp, unpack, same] using commands
      cases index with
      | none => exact same
      | some address =>
          exact ((controller.command_rectangle rest _ [] past).mp localCommands).2 address
    · intro members
      have same : values none = rest := members none
      have localCommands := (controller.command_rectangle rest
        (fun address => values (some address)) [] past).mpr
          ⟨remainder, fun address => members (some address)⟩
      exact ⟨by simpa only [app.commandConsistentFrom_comp, unpack, same] using localCommands, same⟩
  have listed : witness ∈ Set.pi Set.univ restriction := by rw [← rectangle]; exact compatible
  have coordinates (index : Option Address) :
      ∃ seed ∈ restriction index, seed ∈ (coordinateLaws laws restLaw index).support :=
    ⟨witness index, listed index (Set.mem_univ _),
      (independentProduct_support_iff _ witness).mp supported index⟩
  refine ⟨coordinates, ?_⟩
  rw [show (controller.coordinateImplementation laws restLaw).posterior past =
    (app.schedulerMixture (independentProduct (coordinateLaws laws restLaw))
      (fun values before view => PMF.pure
        (controller.choose (unpack values) before view))).posterior past from rfl]
  rw [app.schedulerMixture_posterior_fiber_eq_filter _ _ past _ rest originalPositive]
  simpa only [rectangle] using
    filter_independentProduct (coordinateLaws laws restLaw) restriction coordinates

variable [DecidableEq Principal]

/-- The coordinate posterior belongs to a genuine scheduler with exactly the
same complete execution law as the original addressed implementation. -/
theorem coordinate_realize (laws : Address → PMF LocalSeed) (restLaw : PMF RestSeed)
    (players : Principal → app.Policy) (count : Nat) (state : app.State) :
    app.runRounds (controller.coordinateImplementation laws restLaw).scheduler players count
      (Execution.initial app state) =
      app.runRounds (controller.implementation laws restLaw).scheduler players count
        (Execution.initial app state) := by
  unfold coordinateImplementation
  rw [← app.schedulerMixture_realize, ← controller.realize]
  rw [← unpack_prior laws restLaw, PMF.bind_map]
  rfl

end Interaction.ReactiveApplication.AddressedScheduler
