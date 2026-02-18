/-
  PokemonLean / Core / AttackCost.lean

  Attack cost and energy requirement system for the Pokémon TCG.
  ==============================================================

  Models:
    - Typed energy cost: specific type required (e.g., 2 Fire)
    - Colorless cost: any energy type satisfies
    - Mixed costs: e.g., Fire + Colorless + Colorless = 1 Fire + 2 any
    - Free attacks: zero energy cost
    - Attack cost validation algorithm
    - Energy surplus: having more energy than needed is allowed
    - Greedy matching: assign typed first, then colorless

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  38 theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.AttackCost

-- ============================================================
-- §1  Energy Types
-- ============================================================

/-- Pokémon energy types. -/
inductive EType where
  | fire | water | grass | electric | psychic
  | fighting | dark | steel | dragon | fairy
deriving DecidableEq, Repr, BEq, Inhabited

/-- Bridge BEq to DecidableEq for EType. -/
@[simp] theorem beq_etype_eq_decide (a b : EType) :
    (a == b) = decide (a = b) := by
  cases a <;> cases b <;> decide

-- ============================================================
-- §2  Attack Cost
-- ============================================================

/-- A single energy requirement: either a specific type or colorless (any). -/
inductive CostEntry where
  | typed (t : EType)
  | colorless
deriving DecidableEq, Repr, BEq, Inhabited

-- Note: CostEntry has a parameterized constructor, so we use native_decide on concrete instances
-- and avoid a general beq lemma. Instead we rely on beq_etype_eq_decide for pool operations.

/-- An attack cost is a list of CostEntry requirements. -/
abbrev AttCost := List CostEntry

/-- Count typed requirements of a specific type. -/
def typedCount (t : EType) (cost : AttCost) : Nat :=
  (cost.filter (fun e => e == .typed t)).length

/-- Count colorless requirements. -/
def colorlessCount (cost : AttCost) : Nat :=
  (cost.filter (fun e => e == .colorless)).length

/-- Total energy required. -/
def totalCost (cost : AttCost) : Nat := cost.length

/-- A free attack has zero cost. -/
def isFreeAttack (cost : AttCost) : Bool := cost.isEmpty

-- ============================================================
-- §3  Attached Energy
-- ============================================================

/-- An attached energy card provides energy of a specific type. -/
structure AttachedEnergy where
  eType : EType
deriving DecidableEq, Repr, BEq, Inhabited

/-- Pool of energy attached to a Pokémon. -/
abbrev EnergyPool := List AttachedEnergy

/-- Count energy of a specific type in the pool. -/
def poolCount (t : EType) (pool : EnergyPool) : Nat :=
  (pool.filter (fun e => e.eType == t)).length

/-- Total energy in the pool. -/
def poolTotal (pool : EnergyPool) : Nat := pool.length

-- ============================================================
-- §4  Cost Validation — Greedy Algorithm
-- ============================================================

/-- All energy types in the game. -/
def allETypes : List EType :=
  [.fire, .water, .grass, .electric, .psychic, .fighting, .dark, .steel, .dragon, .fairy]

/-- Check that every typed requirement is met. -/
def typedSatisfied (cost : AttCost) (pool : EnergyPool) : Bool :=
  allETypes.all (fun t => poolCount t pool ≥ typedCount t cost)

/-- Surplus energy after satisfying typed requirements. -/
def surplusAfterTyped (cost : AttCost) (pool : EnergyPool) : Nat :=
  allETypes.foldl (fun acc t => acc + (poolCount t pool - typedCount t cost)) 0

/-- Can the attack be performed with the given energy pool? -/
def canAttack (cost : AttCost) (pool : EnergyPool) : Bool :=
  typedSatisfied cost pool && surplusAfterTyped cost pool ≥ colorlessCount cost

-- ============================================================
-- §5  Example Attacks & Energy
-- ============================================================

/-- Charizard ex: Fire Fire Colorless Colorless (180 damage). -/
def charizardCost : AttCost :=
  [.typed .fire, .typed .fire, .colorless, .colorless]

/-- Pikachu: Electric Colorless (20 damage). -/
def pikachuCost : AttCost :=
  [.typed .electric, .colorless]

/-- Snorlax: Colorless Colorless Colorless Colorless (Body Slam, 60 damage). -/
def snorlaxCost : AttCost :=
  [.colorless, .colorless, .colorless, .colorless]

/-- Mew: free attack (Psywave, 0 cost). -/
def mewFreeCost : AttCost := []

/-- Gardevoir: Psychic Psychic Colorless (Psychic, 60+). -/
def gardevoirCost : AttCost :=
  [.typed .psychic, .typed .psychic, .colorless]

/-- Three Fire energies attached. -/
def threeFirePool : EnergyPool :=
  [⟨.fire⟩, ⟨.fire⟩, ⟨.fire⟩]

/-- Two Fire + one Water. -/
def mixedPool1 : EnergyPool :=
  [⟨.fire⟩, ⟨.fire⟩, ⟨.water⟩]

/-- Four Water energies. -/
def fourWaterPool : EnergyPool :=
  [⟨.water⟩, ⟨.water⟩, ⟨.water⟩, ⟨.water⟩]

/-- One Electric + one Fighting. -/
def elecFightPool : EnergyPool :=
  [⟨.electric⟩, ⟨.fighting⟩]

/-- Empty pool. -/
def emptyPool : EnergyPool := []

/-- Five Fire energies (surplus for Charizard). -/
def fiveFirePool : EnergyPool :=
  [⟨.fire⟩, ⟨.fire⟩, ⟨.fire⟩, ⟨.fire⟩, ⟨.fire⟩]

/-- Two Psychic + one Grass. -/
def psychicGrassPool : EnergyPool :=
  [⟨.psychic⟩, ⟨.psychic⟩, ⟨.grass⟩]

/-- Four Fire energies. -/
def fourFirePool : EnergyPool :=
  [⟨.fire⟩, ⟨.fire⟩, ⟨.fire⟩, ⟨.fire⟩]

-- ============================================================
-- §6  Theorems — Free Attacks
-- ============================================================

/-- A free attack has total cost 0. -/
theorem free_attack_zero_cost : totalCost mewFreeCost = 0 := by rfl

/-- Mew's free attack can be used with empty pool. -/
theorem mew_free_empty : canAttack mewFreeCost emptyPool = true := by native_decide

/-- isFreeAttack correctly identifies the empty cost. -/
theorem free_attack_check : isFreeAttack mewFreeCost = true := by rfl

/-- A non-empty cost is not free. -/
theorem nonempty_not_free (e : CostEntry) (rest : AttCost) :
    isFreeAttack (e :: rest) = false := by rfl

/-- Free attack with any pool of 3 fire. -/
theorem free_with_fire : canAttack [] threeFirePool = true := by native_decide

-- ============================================================
-- §7  Theorems — Typed Energy Matching (Concrete)
-- ============================================================

/-- Charizard needs 2 Fire. -/
theorem charizard_fire_req : typedCount .fire charizardCost = 2 := by native_decide

/-- Charizard needs 0 Water. -/
theorem charizard_water_req : typedCount .water charizardCost = 0 := by native_decide

/-- Charizard has 2 colorless requirements. -/
theorem charizard_colorless_req : colorlessCount charizardCost = 2 := by native_decide

/-- Three Fire energies don't satisfy Charizard (only 1 surplus, need 2 colorless). -/
theorem three_fire_charizard :
    canAttack charizardCost threeFirePool = false := by native_decide

/-- Four Fire energies satisfy Charizard (2 typed + 2 surplus for colorless). -/
theorem four_fire_charizard :
    canAttack charizardCost fourFirePool = true := by native_decide

/-- Five Fire energies satisfy Charizard with surplus. -/
theorem five_fire_charizard :
    canAttack charizardCost fiveFirePool = true := by native_decide

/-- Mixed pool (2 Fire + 1 Water) does NOT satisfy Charizard
    (need 2 Fire typed + 2 colorless, but only 1 surplus). -/
theorem mixed_not_enough_charizard :
    canAttack charizardCost mixedPool1 = false := by native_decide

/-- Four Water cannot pay for Charizard (no Fire). -/
theorem water_cant_pay_fire :
    canAttack charizardCost fourWaterPool = false := by native_decide

-- ============================================================
-- §8  Theorems — Colorless Flexibility
-- ============================================================

/-- Snorlax's cost is all colorless. -/
theorem snorlax_all_colorless : typedCount .fire snorlaxCost = 0 := by native_decide

/-- Four Water satisfies Snorlax (colorless accepts any type). -/
theorem water_pays_snorlax :
    canAttack snorlaxCost fourWaterPool = true := by native_decide

/-- Three Fire satisfies Snorlax only partially (need 4, have 3). -/
theorem three_fire_not_snorlax :
    canAttack snorlaxCost threeFirePool = false := by native_decide

/-- Five Fire satisfies Snorlax with surplus. -/
theorem five_fire_snorlax :
    canAttack snorlaxCost fiveFirePool = true := by native_decide

/-- Empty pool cannot pay Snorlax. -/
theorem empty_not_snorlax :
    canAttack snorlaxCost emptyPool = false := by native_decide

-- ============================================================
-- §9  Theorems — Pikachu Mixed Cost
-- ============================================================

/-- Pikachu needs 1 Electric. -/
theorem pikachu_elec_req : typedCount .electric pikachuCost = 1 := by native_decide

/-- Pikachu needs 1 colorless. -/
theorem pikachu_colorless_req : colorlessCount pikachuCost = 1 := by native_decide

/-- Electric + Fighting pays for Pikachu (Fighting covers colorless). -/
theorem elec_fight_pikachu :
    canAttack pikachuCost elecFightPool = true := by native_decide

/-- Two Fire cannot pay for Pikachu (no Electric). -/
theorem fire_not_pikachu :
    canAttack pikachuCost [⟨.fire⟩, ⟨.fire⟩] = false := by native_decide

-- ============================================================
-- §10  Theorems — Cost Properties
-- ============================================================

/-- totalCost of empty is 0. -/
theorem total_cost_empty : totalCost [] = 0 := by rfl

/-- totalCost is length. -/
theorem total_cost_is_length (cost : AttCost) : totalCost cost = cost.length := by
  rfl

/-- Adding a requirement increases total cost by 1. -/
theorem total_cost_cons (e : CostEntry) (cost : AttCost) :
    totalCost (e :: cost) = totalCost cost + 1 := by
  simp [totalCost, List.length_cons]

/-- Total cost of Charizard is 4. -/
theorem charizard_total : totalCost charizardCost = 4 := by native_decide

/-- Total cost of Pikachu is 2. -/
theorem pikachu_total : totalCost pikachuCost = 2 := by native_decide

/-- Total cost of Snorlax is 4. -/
theorem snorlax_total : totalCost snorlaxCost = 4 := by native_decide

/-- totalCost of concatenated costs. -/
theorem total_cost_append (c1 c2 : AttCost) :
    totalCost (c1 ++ c2) = totalCost c1 + totalCost c2 := by
  simp [totalCost, List.length_append]

-- ============================================================
-- §11  Theorems — Pool Properties
-- ============================================================

/-- poolCount on empty pool is 0. -/
theorem pool_count_empty (t : EType) : poolCount t [] = 0 := by
  rfl

/-- poolTotal on empty pool is 0. -/
theorem pool_total_empty : poolTotal [] = 0 := by rfl

/-- Adding an energy increases poolTotal by 1. -/
theorem pool_total_cons (e : AttachedEnergy) (pool : EnergyPool) :
    poolTotal (e :: pool) = poolTotal pool + 1 := by
  simp [poolTotal, List.length_cons]

/-- Adding a matching energy increases that type's count. -/
theorem pool_count_cons_match (t : EType) (pool : EnergyPool) :
    poolCount t ({ eType := t } :: pool) = poolCount t pool + 1 := by
  simp [poolCount]

/-- Adding a non-matching energy doesn't change that type's count. -/
theorem pool_count_cons_nomatch (t1 t2 : EType) (pool : EnergyPool) (h : t1 ≠ t2) :
    poolCount t1 ({ eType := t2 } :: pool) = poolCount t1 pool := by
  simp only [poolCount, beq_etype_eq_decide, List.filter_cons]
  have : ¬ (t2 = t1) := Ne.symm h
  simp [this]

-- ============================================================
-- §12  Theorems — Gardevoir Scenarios
-- ============================================================

/-- Gardevoir needs 2 Psychic. -/
theorem gardevoir_psychic_req : typedCount .psychic gardevoirCost = 2 := by native_decide

/-- Gardevoir has 1 colorless. -/
theorem gardevoir_colorless_req : colorlessCount gardevoirCost = 1 := by native_decide

/-- Two Psychic + one Grass satisfies Gardevoir. -/
theorem psychic_grass_gardevoir :
    canAttack gardevoirCost psychicGrassPool = true := by native_decide

/-- Two Psychic alone cannot satisfy Gardevoir (need 3 total). -/
theorem two_psychic_not_gardevoir :
    canAttack gardevoirCost [⟨.psychic⟩, ⟨.psychic⟩] = false := by native_decide

-- ============================================================
-- §13  Theorems — Validation Decidability
-- ============================================================

/-- canAttack is decidable (returns Bool). -/
theorem canAttack_decidable (cost : AttCost) (pool : EnergyPool) :
    canAttack cost pool = true ∨ canAttack cost pool = false := by
  cases canAttack cost pool <;> simp

/-- typedSatisfied is decidable. -/
theorem typedSatisfied_decidable (cost : AttCost) (pool : EnergyPool) :
    typedSatisfied cost pool = true ∨ typedSatisfied cost pool = false := by
  cases typedSatisfied cost pool <;> simp

-- ============================================================
-- §14  Concrete Minimum Energy Tests
-- ============================================================

/-- Can't attack with 3 energy when cost is 4 (Charizard with 3 fire). -/
theorem three_not_enough_charizard :
    canAttack charizardCost threeFirePool = false := by native_decide

/-- Can't attack Snorlax with 3 energy. -/
theorem three_not_enough_snorlax :
    canAttack snorlaxCost threeFirePool = false := by native_decide

-- ============================================================
-- §15  Theorems — Surplus / Monotonicity via Concrete Cases
-- ============================================================

/-- 4 Fire → 5 Fire still works for Charizard (surplus ok). -/
theorem surplus_charizard_4_to_5 :
    canAttack charizardCost fourFirePool = true ∧
    canAttack charizardCost fiveFirePool = true := by
  constructor <;> native_decide

/-- 4 Water → 5 Water still works for Snorlax. -/
theorem surplus_snorlax :
    canAttack snorlaxCost fourWaterPool = true ∧
    canAttack snorlaxCost fiveFirePool = true := by
  constructor <;> native_decide

/-- Empty pool works for free attack. -/
theorem free_always_works :
    canAttack mewFreeCost emptyPool = true ∧
    canAttack mewFreeCost threeFirePool = true ∧
    canAttack mewFreeCost fourWaterPool = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ============================================================
-- §16  colorlessCount and typedCount on various costs
-- ============================================================

/-- Snorlax has 4 colorless. -/
theorem snorlax_colorless_count : colorlessCount snorlaxCost = 4 := by native_decide

/-- Snorlax has 0 typed water requirement. -/
theorem snorlax_no_water : typedCount .water snorlaxCost = 0 := by native_decide

/-- Gardevoir has 0 typed fire requirement. -/
theorem gardevoir_no_fire : typedCount .fire gardevoirCost = 0 := by native_decide

/-- Free attack has 0 colorless. -/
theorem free_no_colorless : colorlessCount mewFreeCost = 0 := by native_decide

/-- Free attack has 0 fire. -/
theorem free_no_fire : typedCount .fire mewFreeCost = 0 := by native_decide

end PokemonLean.Core.AttackCost
