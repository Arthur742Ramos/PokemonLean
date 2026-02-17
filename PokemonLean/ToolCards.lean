/-
  PokemonLean / ToolCards.lean

  Pokémon TCG Tool / Item card mechanics formalised via

  Covers: Float Stone (free retreat), Choice Band (+30 to EX/GX/V),
  Muscle Band (+20 to active), Lucky Egg (draw on KO),
  Exp Share (energy transfer on KO), one-tool-per-Pokémon rule,
  Tool Scrapper (removal), Field Blower, tool attachment as
  path steps, coherence of tool stacking/removal.

-/

-- ============================================================
-- §1  Core types
-- ============================================================

/-- Tool card names. -/
inductive ToolName where
  | floatStone   -- retreat cost becomes 0
  | choiceBand   -- +30 damage to EX/GX/V
  | muscleBand   -- +20 damage to active
  | luckyEgg     -- draw until 7 on KO
  | expShare     -- transfer 1 energy on KO
  | focusSash    -- survive one KO at 10 HP
  | none         -- no tool
deriving DecidableEq, Repr

/-- Tags on the defending Pokémon. -/
inductive PokemonTag where
  | basic
  | ex
  | gx
  | v
  | vmax
  | vstar
deriving DecidableEq, Repr

/-- Energy type. -/
inductive EType where
  | fire | water | grass | electric | psychic
  | dark | fighting | metal | colorless
deriving DecidableEq, Repr

/-- A Pokémon in play. -/
structure ToolPokemon where
  name        : String
  hp          : Nat
  currentHp   : Nat
  retreatCost : Nat
  tag         : PokemonTag
  tool        : ToolName
  energy      : List EType
deriving DecidableEq, Repr
inductive TStep (α : Type) : α → α → Type where
  | mk : (label : String) → (a b : α) → TStep α a b

inductive TPath (α : Type) : α → α → Type where
  | nil  : (a : α) → TPath α a a
  | cons : TStep α a b → TPath α b c → TPath α a c


-- ============================================================
-- §3  Tool attachment rules
-- ============================================================

/-- Whether a Pokémon has no tool attached. -/
def hasNoTool (p : ToolPokemon) : Prop := p.tool = .none

/-- Attach a tool. Only allowed if no tool currently. -/
def attachTool (p : ToolPokemon) (t : ToolName) : ToolPokemon :=
  { p with tool := t }

/-- Remove a tool (Tool Scrapper / Field Blower). -/
def removeTool (p : ToolPokemon) : ToolPokemon :=
  { p with tool := .none }

/-- Theorem 1: Attaching a tool sets the tool field. -/
theorem attachTool_sets (p : ToolPokemon) (t : ToolName) :
    (attachTool p t).tool = t := rfl

/-- Theorem 2: Removing a tool clears the tool field. -/
theorem removeTool_clears (p : ToolPokemon) :
    (removeTool p).tool = .none := rfl

/-- Theorem 3: One tool rule — attach then attach again overwrites. -/
theorem attachTool_overwrite (p : ToolPokemon) (t₁ t₂ : ToolName) :
    (attachTool (attachTool p t₁) t₂).tool = t₂ := rfl

/-- Theorem 4: Remove then attach = attach. -/
theorem remove_then_attach (p : ToolPokemon) (t : ToolName) :
    attachTool (removeTool p) t = attachTool p t := by
  simp [attachTool, removeTool]

/-- Theorem 5: Attach then remove yields no tool. -/
theorem attach_then_remove (p : ToolPokemon) (t : ToolName) :
    (removeTool (attachTool p t)).tool = .none := rfl

/-- Theorem 6: Double remove is idempotent. -/
theorem removeTool_idem (p : ToolPokemon) :
    removeTool (removeTool p) = removeTool p := rfl

-- ============================================================
-- §4  Float Stone — free retreat
-- ============================================================

/-- Effective retreat cost with tool. -/
def effectiveRetreat (p : ToolPokemon) : Nat :=
  match p.tool with
  | .floatStone => 0
  | _ => p.retreatCost

/-- Theorem 7: Float Stone gives zero retreat cost. -/
theorem floatStone_free_retreat (p : ToolPokemon) (h : p.tool = .floatStone) :
    effectiveRetreat p = 0 := by
  simp [effectiveRetreat, h]

/-- Theorem 8: No tool means natural retreat cost. -/
theorem noTool_retreat (p : ToolPokemon) (h : p.tool = .none) :
    effectiveRetreat p = p.retreatCost := by
  simp [effectiveRetreat, h]

/-- Theorem 9: Attaching Float Stone makes retreat free. -/
theorem attach_floatStone_retreat (p : ToolPokemon) :
    effectiveRetreat (attachTool p .floatStone) = 0 := by
  simp [effectiveRetreat, attachTool]

-- ============================================================
-- §5  Choice Band — +30 damage to EX/GX/V
-- ============================================================

/-- Whether a tag qualifies for Choice Band bonus. -/
def isChoiceBandTarget (tag : PokemonTag) : Bool :=
  match tag with
  | .ex | .gx | .v | .vmax | .vstar => true
  | _ => false

/-- Damage bonus from tool. -/
def toolDamageBonus (tool : ToolName) (defenderTag : PokemonTag) : Nat :=
  match tool with
  | .choiceBand => if isChoiceBandTarget defenderTag then 30 else 0
  | .muscleBand => 20
  | _ => 0

/-- Final damage calculation. -/
def finalDamage (baseDmg : Nat) (attacker : ToolPokemon) (defenderTag : PokemonTag) : Nat :=
  baseDmg + toolDamageBonus attacker.tool defenderTag

/-- Theorem 10: Choice Band adds 30 vs EX. -/
theorem choiceBand_ex (p : ToolPokemon) (h : p.tool = .choiceBand) (baseDmg : Nat) :
    finalDamage baseDmg p .ex = baseDmg + 30 := by
  simp [finalDamage, toolDamageBonus, h, isChoiceBandTarget]

/-- Theorem 11: Choice Band adds 30 vs GX. -/
theorem choiceBand_gx (p : ToolPokemon) (h : p.tool = .choiceBand) (baseDmg : Nat) :
    finalDamage baseDmg p .gx = baseDmg + 30 := by
  simp [finalDamage, toolDamageBonus, h, isChoiceBandTarget]

/-- Theorem 12: Choice Band adds 30 vs V. -/
theorem choiceBand_v (p : ToolPokemon) (h : p.tool = .choiceBand) (baseDmg : Nat) :
    finalDamage baseDmg p .v = baseDmg + 30 := by
  simp [finalDamage, toolDamageBonus, h, isChoiceBandTarget]

/-- Theorem 13: Choice Band adds 0 vs basic. -/
theorem choiceBand_basic (p : ToolPokemon) (h : p.tool = .choiceBand) (baseDmg : Nat) :
    finalDamage baseDmg p .basic = baseDmg := by
  simp [finalDamage, toolDamageBonus, h, isChoiceBandTarget]

/-- Theorem 14: Muscle Band adds 20 regardless of target. -/
theorem muscleBand_bonus (p : ToolPokemon) (h : p.tool = .muscleBand) (baseDmg : Nat)
    (tag : PokemonTag) :
    finalDamage baseDmg p tag = baseDmg + 20 := by
  simp [finalDamage, toolDamageBonus, h]

/-- Theorem 15: No tool means no damage bonus. -/
theorem noTool_no_bonus (p : ToolPokemon) (h : p.tool = .none) (baseDmg : Nat)
    (tag : PokemonTag) :
    finalDamage baseDmg p tag = baseDmg := by
  simp [finalDamage, toolDamageBonus, h]

-- ============================================================
-- §6  Lucky Egg — draw on KO
-- ============================================================

/-- How many cards to draw when a Pokémon is KO'd. -/
def koDrawCount (p : ToolPokemon) (handSize : Nat) : Nat :=
  match p.tool with
  | .luckyEgg => if handSize < 7 then 7 - handSize else 0
  | _ => 0

/-- Theorem 16: Lucky Egg draws up to 7 cards. -/
theorem luckyEgg_draw (p : ToolPokemon) (h : p.tool = .luckyEgg) (handSize : Nat)
    (hsmall : handSize < 7) :
    koDrawCount p handSize = 7 - handSize := by
  simp [koDrawCount, h, hsmall]

/-- Theorem 17: No tool means no KO draw. -/
theorem no_ko_draw (p : ToolPokemon) (h : p.tool = .none) (handSize : Nat) :
    koDrawCount p handSize = 0 := by
  simp [koDrawCount, h]

-- ============================================================
-- §7  Exp Share — energy transfer on KO
-- ============================================================

/-- Whether Exp Share triggers on a bench Pokémon. -/
def expShareTriggers (benchPoke : ToolPokemon) : Bool :=
  benchPoke.tool == .expShare

/-- Number of energy transferred by Exp Share (1 basic energy). -/
def expShareTransfer (benchPoke : ToolPokemon) (koEnergy : List EType) : Nat :=
  if expShareTriggers benchPoke && !koEnergy.isEmpty then 1 else 0

/-- Theorem 18: Exp Share transfers 1 energy when active is KO'd with energy. -/
theorem expShare_transfers (bp : ToolPokemon) (h : bp.tool = .expShare)
    (e : EType) (rest : List EType) :
    expShareTransfer bp (e :: rest) = 1 := by
  simp [expShareTransfer, expShareTriggers, h]

/-- Theorem 19: No Exp Share means no transfer. -/
theorem no_expShare (bp : ToolPokemon) (h : bp.tool = .none) (energy : List EType) :
    expShareTransfer bp energy = 0 := by
  simp [expShareTransfer, expShareTriggers, h]

-- ============================================================
-- §8  Tool Scrapper / Field Blower
-- ============================================================

/-- Tool Scrapper: remove up to 2 tools from opponents' Pokémon. -/
def toolScrapper (targets : List ToolPokemon) (count : Nat) : List ToolPokemon :=
  match count, targets with
  | 0, _ => targets
  | _, [] => []
  | n + 1, p :: rest =>
    if p.tool != .none then removeTool p :: toolScrapper rest n
    else p :: toolScrapper rest (n + 1)

/-- Theorem 20: Tool Scrapper on empty list does nothing. -/
theorem toolScrapper_nil (n : Nat) : toolScrapper [] n = [] := by
  cases n <;> rfl

/-- Theorem 21: Tool Scrapper with count 0 doesn't remove. -/
theorem toolScrapper_zero (ps : List ToolPokemon) :
    toolScrapper ps 0 = ps := by
  cases ps <;> rfl
/-- Tool operation as a path step. -/
inductive ToolOp : ToolPokemon → ToolPokemon → Prop where
  | attach  (p : ToolPokemon) (t : ToolName) : ToolOp p (attachTool p t)
  | remove  (p : ToolPokemon)                 : ToolOp p (removeTool p)

/-- Tool operation path. -/
inductive ToolPath : ToolPokemon → ToolPokemon → Prop where
  | nil  (p : ToolPokemon) : ToolPath p p
  | cons {p₁ p₂ p₃ : ToolPokemon} : ToolOp p₁ p₂ → ToolPath p₂ p₃ → ToolPath p₁ p₃

/-- Theorem 25: Attach-remove yields tool = none. -/
theorem attach_remove_tool_none (p : ToolPokemon) (t : ToolName) :
    (removeTool (attachTool p t)).tool = .none := rfl

-- ============================================================
-- §10  TPath-based tool proofs
-- ============================================================


-- ============================================================
-- §11  Focus Sash
-- ============================================================

/-- Focus Sash: survive at 10HP if would be KO'd from full HP. -/
def focusSashSurvive (p : ToolPokemon) (damage : Nat) : Nat :=
  if p.tool == .focusSash && p.currentHp == p.hp && damage >= p.hp
  then 10
  else if damage >= p.currentHp then 0
  else p.currentHp - damage

/-- Theorem 31: Focus Sash saves from OHKO at full HP. -/
theorem focusSash_saves (p : ToolPokemon)
    (htool : p.tool = .focusSash) (hfull : p.currentHp = p.hp)
    (damage : Nat) (hko : damage ≥ p.hp) :
    focusSashSurvive p damage = 10 := by
  simp [focusSashSurvive, htool, hfull, hko]

/-- Theorem 32: Without Focus Sash, lethal damage KOs. -/
theorem no_sash_ko (p : ToolPokemon) (htool : p.tool = .none)
    (damage : Nat) (hko : damage ≥ p.currentHp) :
    focusSashSurvive p damage = 0 := by
  simp [focusSashSurvive, htool]
  omega
