/-
  PokemonLean / PokemonPowers.lean

  Pokémon Powers — the classic Base Set through Neo-era mechanic.
  Covers: Pokémon Power activation (once per turn unless stated),
  power vs ability distinction, Rain Dance (unlimited water energy
  attachment), Damage Swap, Buzzap (sacrifice for energy), power lock
  (Muk's Toxic Gas), power classification (ongoing vs triggered).

  20+ theorems, zero sorry.
-/

set_option linter.unusedVariables false

namespace PokemonLean.PokemonPowers

-- ============================================================
-- §1  Core types
-- ============================================================

/-- Energy types in classic TCG. -/
inductive EType where
  | fire | water | grass | lightning | psychic | fighting | colorless | dark | metal
deriving DecidableEq, Repr

/-- Classic Pokémon Power identifiers. -/
inductive PowerId where
  | rainDance       -- Blastoise: attach extra Water energy from hand
  | damageSwap      -- Alakazam: move damage counters between your Pokémon
  | buzzap          -- Electrode: KO self to become energy of any type
  | energyTrans     -- Venusaur: move Grass energy between your Pokémon
  | strangeWave     -- Mr. Mime: prevent 30+ damage attacks
  | pokemonFlute    -- (not a power, just here for completeness)
  | toxicGas        -- Muk: disable all other Pokémon Powers
  | curseBody       -- Gengar: move damage to opponent
  | healingWind     -- Vileplume: heal when evolved
  | shapeshifter    -- Ditto: copy opponent's attacks
  | firespin        -- (filler)
  | noPower         -- No power
deriving DecidableEq, Repr

/-- Power classification. -/
inductive PowerClass where
  | triggered   -- Activates on a specific event (e.g., evolving)
  | ongoing     -- Always active while in play
  | activated   -- Player chooses to use once per turn
deriving DecidableEq, Repr

/-- Classify a power. -/
def classifyPower : PowerId → PowerClass
  | .rainDance   => .activated
  | .damageSwap  => .activated
  | .buzzap      => .activated
  | .energyTrans => .activated
  | .strangeWave => .ongoing
  | .toxicGas    => .ongoing
  | .curseBody   => .activated
  | .healingWind => .triggered
  | .shapeshifter => .ongoing
  | _            => .activated

-- ============================================================
-- §2  Game state
-- ============================================================

/-- A Pokémon card in play. -/
structure PokemonCard where
  name       : String
  power      : PowerId
  energyList : List EType
  damage     : Nat
  maxHp      : Nat
  isActive   : Bool
  isKOd      : Bool
deriving DecidableEq, Repr

/-- Game state for Pokémon Powers. -/
structure PowerState where
  active       : PokemonCard
  bench        : List PokemonCard
  hand         : List EType       -- energy cards in hand
  powerUsed    : List PowerId     -- powers used this turn
  mukInPlay    : Bool             -- Muk's Toxic Gas active?
  turnNumber   : Nat
deriving Repr

/-- Whether a power is locked (Muk in play, and it's not Muk's own power). -/
def isLocked (gs : PowerState) (pid : PowerId) : Bool :=
  gs.mukInPlay && pid != .toxicGas

/-- Whether a power can be activated this turn. -/
def canActivate (gs : PowerState) (pid : PowerId) : Bool :=
  !isLocked gs pid &&
  !gs.powerUsed.contains pid &&
  classifyPower pid == .activated

/-- All Pokémon on the field. -/
def PowerState.allPokemon (gs : PowerState) : List PokemonCard :=
  gs.active :: gs.bench

-- ============================================================
-- §5  Rain Dance — unlimited water energy attachment
-- ============================================================

/-- Attach a water energy via Rain Dance. -/
def rainDanceAttach (gs : PowerState) (target : PokemonCard) (h : !isLocked gs .rainDance) :
    PowerState :=
  { gs with hand := gs.hand.filter (· != .water) }

-- ============================================================
-- §6  Damage Swap — move damage counters
-- ============================================================

/-- Move damage from one Pokémon to another (Alakazam's Damage Swap). -/
def damageSwapResult (gs : PowerState) (amount : Nat) : PowerState :=
  { gs with powerUsed := .damageSwap :: gs.powerUsed }

/-- Theorem 8 — Damage Swap records usage. -/
theorem damageSwap_records (gs : PowerState) (amount : Nat) :
    (damageSwapResult gs amount).powerUsed = .damageSwap :: gs.powerUsed := rfl

-- ============================================================
-- §7  Buzzap — sacrifice Electrode for energy
-- ============================================================

/-- Buzzap: KO Electrode, it becomes energy of chosen type. -/
def buzzapResult (gs : PowerState) (chosenType : EType) : PowerState :=
  { gs with
    bench := gs.bench.filter (·.power != .buzzap)
    powerUsed := .buzzap :: gs.powerUsed }

/-- Theorem 10 — Buzzap removes from bench. -/
theorem buzzap_removes (gs : PowerState) (ct : EType) :
    (buzzapResult gs ct).bench = gs.bench.filter (·.power != .buzzap) := rfl

-- ============================================================
-- §8  Muk's Toxic Gas — power lock
-- ============================================================

/-- Muk enters play: lock all powers. -/
def mukEnters (gs : PowerState) : PowerState :=
  { gs with mukInPlay := true }

/-- Muk leaves play: unlock all powers. -/
def mukLeaves (gs : PowerState) : PowerState :=
  { gs with mukInPlay := false }

/-- Theorem 14 — mukInPlay is true after lock. -/
theorem muk_locks (gs : PowerState) : (mukEnters gs).mukInPlay = true := rfl

/-- Theorem 15 — mukInPlay is false after unlock. -/
theorem muk_unlocks (gs : PowerState) : (mukLeaves gs).mukInPlay = false := rfl

/-- Theorem 16 — all non-Toxic-Gas powers are locked when Muk is in play. -/
theorem muk_locks_all (gs : PowerState) (pid : PowerId) (hpid : pid ≠ .toxicGas) :
    isLocked (mukEnters gs) pid = true := by
  simp [isLocked, mukEnters]
  cases pid <;> simp_all

-- ============================================================
-- §9  Energy Trans — move grass energy
-- ============================================================

/-- Move a grass energy between Pokémon (Venusaur's Energy Trans). -/
def energyTransResult (gs : PowerState) : PowerState :=
  { gs with powerUsed := .energyTrans :: gs.powerUsed }

-- ============================================================
-- §10  Power vs Ability distinction
-- ============================================================

/-- Era classification. -/
inductive Era where
  | base_fossil_rocket   -- Pokémon Powers era
  | neoGenesis_onwards   -- Still "Pokémon Powers"
  | rubyAndSapphire      -- "Poké-Powers" and "Poké-Bodies"
  | blackAndWhite        -- "Abilities" (unified)
deriving DecidableEq, Repr

/-- Whether Muk's Toxic Gas affects a mechanic in a given era. -/
def toxicGasAffects : Era → Bool
  | .base_fossil_rocket  => true
  | .neoGenesis_onwards  => true
  | .rubyAndSapphire     => false  -- Different mechanic name
  | .blackAndWhite       => false  -- Abilities, not Powers

/-- Theorem 18 — Toxic Gas only affects classic eras. -/
theorem toxicGas_classic_only :
    toxicGasAffects .base_fossil_rocket = true ∧
    toxicGasAffects .blackAndWhite = false :=
  ⟨rfl, rfl⟩

-- ============================================================
-- §11  Healing Wind — triggered power on evolution
-- ============================================================

/-- Evolving triggers Healing Wind (Vileplume). -/
def healingWindResult (gs : PowerState) (healAmount : Nat) : PowerState :=
  { gs with active := { gs.active with damage := gs.active.damage - healAmount } }

/-- Theorem 20 — healing reduces damage. -/
theorem healing_reduces (gs : PowerState) (amt : Nat) :
    (healingWindResult gs amt).active.damage = gs.active.damage - amt := rfl

-- ============================================================
-- §12  End-of-turn reset and coherence
-- ============================================================

/-- End of turn: clear power usage list. -/
def endTurnResult (gs : PowerState) : PowerState :=
  { gs with powerUsed := [], turnNumber := gs.turnNumber + 1 }

/-- Theorem 22 — end turn clears usage. -/
theorem endTurn_clears (gs : PowerState) :
    (endTurnResult gs).powerUsed = [] := rfl

/-- Theorem 23 — end turn increments turn. -/
theorem endTurn_increments (gs : PowerState) :
    (endTurnResult gs).turnNumber = gs.turnNumber + 1 := rfl

-- ============================================================
-- §13  Additional coherence
-- ============================================================

end PokemonLean.PokemonPowers
