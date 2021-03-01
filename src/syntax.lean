inductive formula
| var : ℕ → formula
| bot : formula
| imp : formula → formula → formula
| box : formula → formula
infixr ` →ₘ `:65 := formula.imp
prefix `□`:70 := formula.box
notation `⊥ₘ` := formula.bot

def formula.neg (p : formula) : formula := p →ₘ ⊥ₘ
prefix `¬ₘ`:70 := formula.neg

def formula.and (p q : formula) : formula := ¬ₘ(p →ₘ ¬ₘq)
infixl ` ∧ₘ `:67 := formula.and

def formula.or (p q : formula) : formula := ¬ₘp →ₘ q
infixl ` ∨ₘ `:66 := formula.or

def formula.iff (p q : formula) : formula := (p →ₘ q) ∧ₘ (q →ₘ p)
infix ` ↔ₘ `:60 := formula.iff

def formula.dia (p : formula) : formula := ¬ₘ□¬ₘp
prefix `◇`:70 := formula.dia

instance nat_to_formula : has_coe ℕ formula := ⟨formula.var⟩
