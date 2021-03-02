import syntax
import semantics

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
infix ` ⊢ₖ `:55 := prv

def consistent (Γ : set formula) : Prop := ⊥ₘ ∉ 𝐊 Γ

open semantics

universe variable u

variable {W : Type u}
variable F : kripke_frame W
variables p q : ℕ
variables φ ψ χ : formula
#check distribution
#check satisfy F

theorem us_semantics : F ⊧ φ → F ⊧ (subst p ψ φ) :=
begin
  intros h V w,
  let V' : ℕ → set W := fun e u, [F, V, u] ⊧ subst p ψ e,
  have i : ∀ v, ([F, V', v] ⊧ φ) ↔ ([F, V, v] ⊧ subst p ψ φ),
  { clear h,
    induction φ,
    { exact λ v, ⟨λ h₀, h₀, λ h₀, h₀⟩ },
    { exact λ v, ⟨λ h₀, h₀, λ h₀, h₀⟩ },
    { exact λ v, ⟨λ h₀ s, (φ_ih_ᾰ_1 v).1 (h₀ ((φ_ih_ᾰ v).2 s)), λ h₀ s, (φ_ih_ᾰ_1 v).2 (h₀ ((φ_ih_ᾰ v).1 s))⟩ },
    { exact λ v, ⟨λ h u rvu, (φ_ih u).1 (h u rvu), λ h u rvu, (φ_ih u).2 (h u rvu)⟩ } }, 
  have l : [F, V', w] ⊧ φ := h V' w,
  exact (i w).1 l
end

theorem mp_semantics : F ⊧ φ →ₘ ψ → F ⊧ φ → F ⊧ ψ :=
λ (h : F ⊧ φ →ₘ ψ) (h₀ : F ⊧ φ) (V : ℕ → set W) (w : W), (h V w) (h₀ V w) 

theorem ak_semantics : F ⊧ φ →ₘ ψ →ₘ φ := λ V w h h₀, h

theorem as_semantics : F ⊧ (φ →ₘ ψ →ₘ χ) →ₘ (φ →ₘ ψ) →ₘ φ →ₘ χ := λ V w h h₀ h₁, h h₁ (h₀ h₁)

theorem an_semantics : F ⊧ (¬ₘφ →ₘ ¬ₘψ) →ₘ ψ →ₘ φ :=
by { intros V w h, simp [satisfy], contrapose, exact h }

theorem soundness : ∅ ⊢ₖ φ → F ⊧ φ :=
begin
  assume h,
  induction h,
  { exact us_semantics _ h_p _ _ h_ih },
  { exfalso, exact h_ᾰ },
  { exact mp_semantics _ _ _ h_ih_ᾰ h_ih_ᾰ_1 },
  { exact necessitation _ _ h_ih },
  { exact ak_semantics _ _ _ },
  { exact as_semantics _ _ _ _ },
  { exact an_semantics _ _ _ },
  { exact distribution _ _ _ }
end

