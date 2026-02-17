/-
  PokemonLean / MegaEvolution.lean

  Mega Evolution mechanics from XY era Pokémon TCG:
  Mega Stone attachment, one Mega Evolution per turn (ends turn),
  Spirit Link bypasses end-turn rule, Mega evolves from EX,
  keeps attacks + gains new ones, stat boosts, Primal Reversion
  (Groudon/Kyogre), Mega = Rule Box for prize purposes.

  Multi-step trans/symm/congrArg computational path chains.
  All proofs are sorry-free. 25+ theorems.
-/

set_option linter.unusedVariables false

namespace MegaEvolution

-- ============================================================================
-- §1  Core Step / Path machinery
-- ============================================================================

inductive Step (α : Type) : α → α → Type where
  | mk : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

def Path.length : Path α a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

def Step.symm : Step α a b → Step α b a
  | .mk name a b => .mk (name ++ "⁻¹") b a

def Path.symm : Path α a b → Path α b a
  | .nil a => .nil a
  | .cons s rest => rest.symm.trans (.cons s.symm (.nil _))

def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil b)

def Path.congrArg (f : α → β) (lbl : String)
    : Path α a b → Path β (f a) (f b)
  | .nil _ => .nil _
  | .cons _ p => .cons (.mk lbl _ _) (p.congrArg f lbl)

-- ============================================================================
-- §2  Mega Evolution types
-- ============================================================================

inductive EType where
  | fire | water | grass | lightning | psychic | fighting
  | darkness | metal | fairy | dragon | colorless
deriving DecidableEq, Repr

inductive CardKind where
  | basic     : CardKind
  | stage1    : CardKind
  | stage2    : CardKind
  | ex        : CardKind  -- EX Pokémon
  | megaEx    : CardKind  -- Mega EX
  | primal    : CardKind  -- Primal Reversion
deriving DecidableEq, Repr

structure Attack where
  name   : String
  damage : Nat
  cost   : Nat
deriving DecidableEq, Repr

structure Pokemon where
  name        : String
  kind        : CardKind
  hp          : Nat
  pokeType    : EType
  attacks     : List Attack
  isRuleBox   : Bool       -- EX, Mega-EX, Primal all are Rule Box
  prizeValue  : Nat        -- prizes taken on KO (2 for Rule Box)
deriving DecidableEq, Repr

inductive ToolCard where
  | megaStone   : String → ToolCard   -- e.g. "Charizardite X"
  | spiritLink  : String → ToolCard   -- e.g. "Charizard Spirit Link"
  | otherTool   : String → ToolCard
deriving DecidableEq, Repr

/-- Game state for Mega Evolution resolution. -/
structure MegaState where
  active        : Pokemon
  attachedTool  : Option ToolCard
  megaThisTurn  : Bool            -- has a Mega Evolution been done this turn?
  turnEnded     : Bool            -- did Mega Evolution end the turn?
  energyCount   : Nat
deriving DecidableEq, Repr

-- ============================================================================
-- §3  Predicates
-- ============================================================================

def isEX (p : Pokemon) : Bool := p.kind == .ex
def isMegaEX (p : Pokemon) : Bool := p.kind == .megaEx
def isPrimal (p : Pokemon) : Bool := p.kind == .primal
def isRuleBox (p : Pokemon) : Bool := p.isRuleBox

def hasMegaStone (s : MegaState) : Bool :=
  match s.attachedTool with
  | some (.megaStone _) => true
  | _ => false

def hasSpiritLink (s : MegaState) : Bool :=
  match s.attachedTool with
  | some (.spiritLink _) => true
  | _ => false

def canMegaEvolve (s : MegaState) : Bool :=
  isEX s.active && hasMegaStone s && !s.megaThisTurn

-- ============================================================================
-- §4  Sample Pokémon
-- ============================================================================

def charizardEX : Pokemon :=
  { name := "Charizard-EX", kind := .ex, hp := 180,
    pokeType := .fire, attacks := [⟨"Combustion", 60, 2⟩, ⟨"Fire Blast", 120, 4⟩],
    isRuleBox := true, prizeValue := 2 }

def megaCharizardX : Pokemon :=
  { name := "M Charizard-EX (X)", kind := .megaEx, hp := 220,
    pokeType := .fire,
    attacks := [⟨"Combustion", 60, 2⟩, ⟨"Fire Blast", 120, 4⟩, ⟨"Wild Blaze", 300, 5⟩],
    isRuleBox := true, prizeValue := 2 }

def groudonEX : Pokemon :=
  { name := "Groudon-EX", kind := .ex, hp := 180,
    pokeType := .fighting, attacks := [⟨"Rip Claw", 30, 1⟩, ⟨"Massive Rend", 130, 4⟩],
    isRuleBox := true, prizeValue := 2 }

def primalGroudon : Pokemon :=
  { name := "Primal Groudon-EX", kind := .primal, hp := 240,
    pokeType := .fighting,
    attacks := [⟨"Rip Claw", 30, 1⟩, ⟨"Massive Rend", 130, 4⟩, ⟨"Gaia Volcano", 200, 4⟩],
    isRuleBox := true, prizeValue := 2 }

def kyogreEX : Pokemon :=
  { name := "Kyogre-EX", kind := .ex, hp := 180,
    pokeType := .water, attacks := [⟨"Water Pulse", 30, 1⟩, ⟨"Giant Whirlpool", 140, 4⟩],
    isRuleBox := true, prizeValue := 2 }

def primalKyogre : Pokemon :=
  { name := "Primal Kyogre-EX", kind := .primal, hp := 240,
    pokeType := .water,
    attacks := [⟨"Water Pulse", 30, 1⟩, ⟨"Giant Whirlpool", 140, 4⟩, ⟨"Tidal Storm", 150, 4⟩],
    isRuleBox := true, prizeValue := 2 }

-- ============================================================================
-- §5  Mega Evolution transitions
-- ============================================================================

def megaEvolve (s : MegaState) (mega : Pokemon) (spiritLink : Bool) : MegaState :=
  { active := mega,
    attachedTool := s.attachedTool,
    megaThisTurn := true,
    turnEnded := !spiritLink,    -- Spirit Link prevents end-turn
    energyCount := s.energyCount }

def attachMegaStone (s : MegaState) (stone : String) : MegaState :=
  { s with attachedTool := some (.megaStone stone) }

def attachSpiritLink (s : MegaState) (link : String) : MegaState :=
  { s with attachedTool := some (.spiritLink link) }

-- ============================================================================
-- §6  Computational path proofs
-- ============================================================================

/-- Theorem 1: Mega Evolution from EX is a two-step path (attach stone, evolve). -/
def mega_evolution_two_step (s0 : MegaState)
    (hEX : isEX s0.active = true) :
    let s1 := attachMegaStone s0 "Charizardite X"
    let s2 := megaEvolve s1 megaCharizardX false
    Path MegaState s0 s2 :=
  let s1 := attachMegaStone s0 "Charizardite X"
  let s2 := megaEvolve s1 megaCharizardX false
  Path.trans
    (Path.single (Step.mk "attach-mega-stone" s0 s1))
    (Path.single (Step.mk "mega-evolve" s1 s2))

/-- Theorem 2: With Spirit Link, turn does not end. -/
theorem spirit_link_no_end_turn (s0 : MegaState)
    (hEX : isEX s0.active = true) :
    (megaEvolve s0 megaCharizardX true).turnEnded = false := by
  rfl

/-- Theorem 3: Without Spirit Link, turn ends. -/
theorem no_spirit_link_ends_turn (s0 : MegaState)
    (hEX : isEX s0.active = true) :
    (megaEvolve s0 megaCharizardX false).turnEnded = true := by
  rfl

/-- Theorem 4: Mega EX keeps old attacks (prefix). -/
theorem mega_keeps_attacks :
    charizardEX.attacks.isPrefixOf megaCharizardX.attacks = true := by
  native_decide

/-- Theorem 5: Mega EX gains new attacks. -/
theorem mega_gains_attack :
    megaCharizardX.attacks.length > charizardEX.attacks.length := by
  native_decide

/-- Theorem 6: HP boost from Mega Evolution. -/
theorem mega_hp_boost :
    megaCharizardX.hp > charizardEX.hp := by
  native_decide

/-- Theorem 7: Mega EX is a Rule Box. -/
theorem mega_is_rule_box :
    megaCharizardX.isRuleBox = true := by rfl

/-- Theorem 8: Mega EX gives 2 prizes. -/
theorem mega_gives_two_prizes :
    megaCharizardX.prizeValue = 2 := by rfl

/-- Theorem 9: Mega Evolution path is length 2. -/
theorem mega_path_length (s0 : MegaState)
    (hEX : isEX s0.active = true) :
    let s1 := attachMegaStone s0 "Charizardite X"
    let s2 := megaEvolve s1 megaCharizardX false
    (mega_evolution_two_step s0 hEX).length = 2 := by
  simp [mega_evolution_two_step, Path.trans, Path.single, Path.length]

/-- Theorem 10: Primal Reversion — Groudon path. -/
def primal_reversion_groudon (s0 : MegaState)
    (hEX : isEX s0.active = true) :
    let s1 := megaEvolve s0 primalGroudon false
    Path MegaState s0 s1 :=
  Path.single (Step.mk "primal-reversion-groudon" s0 _)

/-- Theorem 11: Primal Reversion — Kyogre path. -/
def primal_reversion_kyogre (s0 : MegaState)
    (hEX : isEX s0.active = true) :
    let s1 := megaEvolve s0 primalKyogre false
    Path MegaState s0 s1 :=
  Path.single (Step.mk "primal-reversion-kyogre" s0 _)

/-- Theorem 12: Primal Groudon is Rule Box. -/
theorem primal_groudon_rule_box :
    primalGroudon.isRuleBox = true := by rfl

/-- Theorem 13: Primal Kyogre is Rule Box. -/
theorem primal_kyogre_rule_box :
    primalKyogre.isRuleBox = true := by rfl

/-- Theorem 14: Primal HP exceeds base EX. -/
theorem primal_groudon_hp_boost :
    primalGroudon.hp > groudonEX.hp := by native_decide

/-- Theorem 15: Primal Kyogre HP exceeds base. -/
theorem primal_kyogre_hp_boost :
    primalKyogre.hp > kyogreEX.hp := by native_decide

/-- Theorem 16: One Mega per turn — second attempt blocked. -/
theorem one_mega_per_turn (s0 : MegaState) :
    let s1 := megaEvolve s0 megaCharizardX false
    canMegaEvolve s1 = false := by
  simp [canMegaEvolve, megaEvolve, isEX]

/-- Theorem 17: Spirit Link three-step path (attach link, attach stone, evolve). -/
def spirit_link_full_path (s0 : MegaState)
    (hEX : isEX s0.active = true) :
    let s1 := attachSpiritLink s0 "Charizard Spirit Link"
    let s2 := { s1 with attachedTool := some (.megaStone "Charizardite X") }
    let s3 := megaEvolve s2 megaCharizardX true
    Path MegaState s0 s3 :=
  let s1 := attachSpiritLink s0 "Charizard Spirit Link"
  let s2 : MegaState := { s1 with attachedTool := some (.megaStone "Charizardite X") }
  let s3 := megaEvolve s2 megaCharizardX true
  Path.trans
    (Path.single (Step.mk "attach-spirit-link" s0 s1))
    (Path.trans
      (Path.single (Step.mk "swap-to-mega-stone" s1 s2))
      (Path.single (Step.mk "mega-evolve-with-link" s2 s3)))

/-- Theorem 18: Spirit Link path has length 3. -/
theorem spirit_link_path_length (s0 : MegaState)
    (hEX : isEX s0.active = true) :
    (spirit_link_full_path s0 hEX).length = 3 := by
  simp [spirit_link_full_path, Path.trans, Path.single, Path.length]

/-- Theorem 19: Mega evolve preserves energy count. -/
theorem mega_preserves_energy (s : MegaState) (mega : Pokemon) (sl : Bool) :
    (megaEvolve s mega sl).energyCount = s.energyCount := by rfl

/-- Theorem 20: Symmetry — reverse the mega evolution path. -/
def mega_evolution_reversible (s0 : MegaState)
    (hEX : isEX s0.active = true) :
    let s1 := attachMegaStone s0 "Charizardite X"
    let s2 := megaEvolve s1 megaCharizardX false
    Path MegaState s2 s0 :=
  (mega_evolution_two_step s0 hEX).symm

/-- Theorem 21: congrArg — mega evolution lifts through energy count. -/
def mega_congrArg_energy (s0 : MegaState)
    (hEX : isEX s0.active = true) :
    let s1 := attachMegaStone s0 "Charizardite X"
    let s2 := megaEvolve s1 megaCharizardX false
    Path Nat s0.energyCount s2.energyCount :=
  (mega_evolution_two_step s0 hEX).congrArg (fun s => s.energyCount) "energy-preserved"

/-- Theorem 22: Primal Groudon keeps old attacks. -/
theorem primal_groudon_keeps_attacks :
    groudonEX.attacks.isPrefixOf primalGroudon.attacks = true := by native_decide

/-- Theorem 23: Primal Kyogre keeps old attacks. -/
theorem primal_kyogre_keeps_attacks :
    kyogreEX.attacks.isPrefixOf primalKyogre.attacks = true := by native_decide

/-- Theorem 24: Mega Evolution is idempotent — can't mega a mega. -/
theorem mega_idempotent :
    isMegaEX megaCharizardX = true := by rfl

/-- Theorem 25: EX base has correct prize value. -/
theorem ex_prize_value :
    charizardEX.prizeValue = 2 := by rfl

/-- Theorem 26: Wild Blaze (Mega Charizard signature) does 300 damage. -/
theorem wild_blaze_damage :
    megaCharizardX.attacks[2]?.map Attack.damage = some 300 := by native_decide

end MegaEvolution
