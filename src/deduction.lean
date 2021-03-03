import syntax

def subst (p : ℕ) (φ : formula) : formula → formula
| (q : ℕ)  := if p = q then φ else q
| ⊥ₘ       := ⊥ₘ
| (ψ →ₘ χ) := subst ψ →ₘ subst χ
| □ψ       := □(subst ψ)

inductive prv (Γ : set formula) : set formula
| us {p φ ψ} : prv φ → prv (subst p ψ φ) 
| ax {φ}     : φ ∈ Γ → prv φ
| mp {φ ψ}   : prv (φ →ₘ ψ) → prv φ → prv ψ
| n {φ}      : prv φ → prv □φ
| ak {φ ψ}   : prv (φ →ₘ ψ →ₘ φ)
| as {φ ψ χ} : prv ((φ →ₘ ψ →ₘ χ) →ₘ (φ →ₘ ψ) →ₘ φ →ₘ χ)
| an {φ ψ}   : prv ((¬ₘφ →ₘ ¬ₘψ) →ₘ ψ →ₘ φ)
| k {φ ψ}    : prv (□(φ →ₘ ψ) →ₘ □φ →ₘ □ψ)
notation `𝐊` := prv
prefix `⊢ₖ`:55 := prv ∅
infix ` ⊢ `:55 := prv

def consistent (Γ : set formula) : Prop := ⊥ₘ ∉ 𝐊 Γ

