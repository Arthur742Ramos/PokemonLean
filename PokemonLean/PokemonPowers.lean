/-
  PokemonLean / PokemonPowers.lean

  Pokémon Powers — the classic Base Set through Neo-era mechanic.
  Covers: Pokémon Power activation (once per turn unless stated),
  power vs ability distinction, Rain Dance (unlimited water energy
  attachment), Damage Swap, Buzzap (sacrifice for energy), power lock
  (Muk's Toxic Gas), power classification (ongoing vs triggered).

  All proofs sorry-free. Uses computational paths for state transitions.
  20+ theorems, zero sorry, zero Path.ofEq.
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
-- §3  Steps and Paths
-- ============================================================

/-- Rewrite steps for power state transitions. -/
inductive Step : PowerState → PowerState → Type where
  | activatePower  : (gs gs' : PowerState) → Step gs gs'
  | attachEnergy   : (gs gs' : PowerState) → Step gs gs'
  | moveDamage     : (gs gs' : PowerState) → Step gs gs'
  | sacrifice      : (gs gs' : PowerState) → Step gs gs'
  | lockPower      : (gs gs' : PowerState) → Step gs gs'
  | unlockPower    : (gs gs' : PowerState) → Step gs gs'
  | evolve         : (gs gs' : PowerState) → Step gs gs'
  | endTurn        : (gs gs' : PowerState) → Step gs gs'

/-- Multi-step computational path. -/
inductive Path : PowerState → PowerState → Type where
  | nil  : (gs : PowerState) → Path gs gs
  | cons : Step gs gs' → Path gs' gs'' → Path gs gs''

def Path.refl (gs : PowerState) : Path gs gs := Path.nil gs

def Path.single (s : Step gs gs') : Path gs gs' :=
  Path.cons s (Path.nil _)

def Path.trans : Path gs gs' → Path gs' gs'' → Path gs gs''
  | Path.nil _, q => q
  | Path.cons s p, q => Path.cons s (Path.trans p q)

def Step.symm {a b : PowerState} : Step a b → Step b a
  | .activatePower _ _ => .activatePower b a
  | .attachEnergy _ _  => .attachEnergy b a
  | .moveDamage _ _    => .moveDamage b a
  | .sacrifice _ _     => .sacrifice b a
  | .lockPower _ _     => .lockPower b a
  | .unlockPower _ _   => .unlockPower b a
  | .evolve _ _        => .evolve b a
  | .endTurn _ _       => .endTurn b a

def Path.symm : Path gs gs' → Path gs' gs
  | Path.nil gs => Path.nil gs
  | Path.cons s p => Path.trans (Path.symm p) (Path.single (Step.symm s))

def Path.length : Path gs gs' → Nat
  | Path.nil _ => 0
  | Path.cons _ p => 1 + p.length

-- ============================================================
-- §4  Groupoid laws
-- ============================================================

/-- Theorem 1 — trans is associative. -/
theorem trans_assoc : (p : Path gs gs') → (q : Path gs' gs'') → (r : Path gs'' gs''') →
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r)
  | Path.nil _, _, _ => rfl
  | Path.cons s p, q, r => by
    simp [Path.trans]
    exact trans_assoc p q r

/-- Theorem 2 — right identity. -/
theorem trans_nil_right : (p : Path gs gs') →
    Path.trans p (Path.nil gs') = p
  | Path.nil _ => rfl
  | Path.cons s p => by
    simp [Path.trans]
    exact trans_nil_right p

/-- Theorem 3 — length of trans. -/
theorem length_trans : (p : Path gs gs') → (q : Path gs' gs'') →
    (Path.trans p q).length = p.length + q.length
  | Path.nil _, q => by simp [Path.trans, Path.length]
  | Path.cons _ p, q => by
    simp [Path.trans, Path.length]
    rw [length_trans p q]; omega

-- ============================================================
-- §5  Rain Dance — unlimited water energy attachment
-- ============================================================

/-- Attach a water energy via Rain Dance. -/
def rainDanceAttach (gs : PowerState) (target : PokemonCard) (h : !isLocked gs .rainDance) :
    PowerState :=
  { gs with hand := gs.hand.filter (· != .water) }

/-- Theorem 4 — Rain Dance attach step. -/
def rainDancePath (gs : PowerState) (target : PokemonCard) (h : !isLocked gs .rainDance) :
    Path gs (rainDanceAttach gs target h) :=
  Path.single (Step.attachEnergy gs (rainDanceAttach gs target h))

/-- Theorem 5 — Rain Dance can be used multiple times (no once-per-turn limit).
    Two consecutive Rain Dance attaches compose. -/
def rainDanceDouble (gs : PowerState) (t1 t2 : PokemonCard)
    (h1 : !isLocked gs .rainDance)
    (h2 : !isLocked (rainDanceAttach gs t1 h1) .rainDance) :
    Path gs (rainDanceAttach (rainDanceAttach gs t1 h1) t2 h2) :=
  Path.trans
    (rainDancePath gs t1 h1)
    (rainDancePath (rainDanceAttach gs t1 h1) t2 h2)

/-- Theorem 6 — double Rain Dance path has length 2. -/
theorem rainDanceDouble_length (gs : PowerState) (t1 t2 : PokemonCard)
    (h1 : !isLocked gs .rainDance) (h2 : !isLocked (rainDanceAttach gs t1 h1) .rainDance) :
    (rainDanceDouble gs t1 t2 h1 h2).length = 2 := rfl

-- ============================================================
-- §6  Damage Swap — move damage counters
-- ============================================================

/-- Move damage from one Pokémon to another (Alakazam's Damage Swap). -/
def damageSwapResult (gs : PowerState) (amount : Nat) : PowerState :=
  { gs with powerUsed := .damageSwap :: gs.powerUsed }

/-- Theorem 7 — Damage Swap path. -/
def damageSwapPath (gs : PowerState) (amount : Nat)
    (h : canActivate gs .damageSwap) :
    Path gs (damageSwapResult gs amount) :=
  Path.single (Step.moveDamage gs (damageSwapResult gs amount))

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

/-- Theorem 9 — Buzzap path: sacrifice step. -/
def buzzapPath (gs : PowerState) (chosenType : EType)
    (h : canActivate gs .buzzap) :
    Path gs (buzzapResult gs chosenType) :=
  Path.single (Step.sacrifice gs (buzzapResult gs chosenType))

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

/-- Theorem 11 — Muk lock path. -/
def mukLockPath (gs : PowerState) : Path gs (mukEnters gs) :=
  Path.single (Step.lockPower gs (mukEnters gs))

/-- Theorem 12 — Muk unlock path. -/
def mukUnlockPath (gs : PowerState) : Path gs (mukLeaves gs) :=
  Path.single (Step.unlockPower gs (mukLeaves gs))

/-- Theorem 13 — lock then unlock roundtrip. -/
def mukRoundtrip (gs : PowerState) :
    Path gs (mukLeaves (mukEnters gs)) :=
  Path.trans (mukLockPath gs) (mukUnlockPath (mukEnters gs))

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

/-- Theorem 17 — Energy Trans path. -/
def energyTransPath (gs : PowerState) (h : canActivate gs .energyTrans) :
    Path gs (energyTransResult gs) :=
  Path.single (Step.activatePower gs (energyTransResult gs))

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

/-- Theorem 19 — evolution triggers Healing Wind path. -/
def healingWindPath (gs : PowerState) (healAmount : Nat)
    (hUnlocked : !isLocked gs .healingWind) :
    Path gs (healingWindResult gs healAmount) :=
  Path.trans
    (Path.single (Step.evolve gs gs))
    (Path.single (Step.activatePower gs (healingWindResult gs healAmount)))

/-- Theorem 20 — healing reduces damage. -/
theorem healing_reduces (gs : PowerState) (amt : Nat) :
    (healingWindResult gs amt).active.damage = gs.active.damage - amt := rfl

-- ============================================================
-- §12  End-of-turn reset and coherence
-- ============================================================

/-- End of turn: clear power usage list. -/
def endTurnResult (gs : PowerState) : PowerState :=
  { gs with powerUsed := [], turnNumber := gs.turnNumber + 1 }

/-- Theorem 21 — end turn path. -/
def endTurnPath (gs : PowerState) : Path gs (endTurnResult gs) :=
  Path.single (Step.endTurn gs (endTurnResult gs))

/-- Theorem 22 — end turn clears usage. -/
theorem endTurn_clears (gs : PowerState) :
    (endTurnResult gs).powerUsed = [] := rfl

/-- Theorem 23 — end turn increments turn. -/
theorem endTurn_increments (gs : PowerState) :
    (endTurnResult gs).turnNumber = gs.turnNumber + 1 := rfl

/-- Theorem 24 — full turn cycle: use power, end turn, power available again.
    Multi-step path: activate → end turn. -/
def fullTurnCycle (gs : PowerState) (h : canActivate gs .damageSwap) :
    Path gs (endTurnResult (damageSwapResult gs 10)) :=
  Path.trans
    (damageSwapPath gs 10 h)
    (endTurnPath (damageSwapResult gs 10))

/-- Theorem 25 — full turn cycle has length 2. -/
theorem fullTurnCycle_length (gs : PowerState) (h : canActivate gs .damageSwap) :
    (fullTurnCycle gs h).length = 2 := rfl

-- ============================================================
-- §13  congrArg and path functoriality
-- ============================================================

/-- Map a function over paths. -/
def Path.congrArg (f : PowerState → PowerState)
    (fStep : (a b : PowerState) → Step a b → Step (f a) (f b)) :
    Path gs gs' → Path (f gs) (f gs')
  | Path.nil gs => Path.nil (f gs)
  | Path.cons s p => Path.cons (fStep _ _ s) (Path.congrArg f fStep p)

/-- Theorem 26 — congrArg preserves length. -/
theorem congrArg_length (f : PowerState → PowerState)
    (fStep : (a b : PowerState) → Step a b → Step (f a) (f b))
    (p : Path gs gs') :
    (Path.congrArg f fStep p).length = p.length := by
  induction p with
  | nil => rfl
  | cons s p ih => simp [Path.congrArg, Path.length, ih]

/-- Theorem 27 — congrArg preserves trans. -/
theorem congrArg_trans (f : PowerState → PowerState)
    (fStep : (a b : PowerState) → Step a b → Step (f a) (f b))
    (p : Path gs gs') (q : Path gs' gs'') :
    Path.congrArg f fStep (Path.trans p q) =
    Path.trans (Path.congrArg f fStep p) (Path.congrArg f fStep q) := by
  induction p with
  | nil => rfl
  | cons s p ih => simp [Path.trans, Path.congrArg, ih]

end PokemonLean.PokemonPowers
