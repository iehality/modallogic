import data.int.parity
import syntax
import deduction
open classical

universe variables u 

structure kripke_frame (W : Type u) :=
(relation : W → W → Prop)

inductive singleton : Type u 
| s : singleton

def trivial_frame : kripke_frame singleton := ⟨λ x y, true⟩

namespace rel

variable {W : Type u}
variable F :  kripke_frame W

def reflective := ∀ x, F.relation x x
def transitive := ∀ x y z, F.relation x y → F.relation y z → F.relation x z
def infinite_ascent := ∃ (z : ℕ → W), ∀ (n : ℕ), F.relation (z n) (z (n + 1))

end rel

def satisfy {W : Type u} (F : kripke_frame W) (V : ℕ → set W) : W → formula → Prop
| w (p : ℕ)   := w ∈ V p
| w ⊥ₘ        := false
| w (p →ₘ q) := satisfy w p → satisfy w q
| w □p       := ∀ v, F.relation w v → satisfy v p

def frames {W : Type u} (F : kripke_frame W) (p : formula) := ∀ V w, satisfy F V w p

notation `[`F`, `V`, `w`]` ` ⊧ `p := satisfy F V w p
infix ` ⊧ `:50 := frames

namespace semantics

variable {W : Type u}
variable F : kripke_frame W
variables p q : ℕ
variables φ ψ χ : formula
local infix ` ≺ `:50 := F.relation

theorem distribution : F ⊧ □(φ →ₘ ψ) →ₘ □φ →ₘ □ψ :=
λ (V : ℕ → set W)
  (w : W)
  (h₀ : [F, V, w] ⊧ □(φ →ₘ ψ))
  (h₁ : [F, V, w] ⊧ □φ)
  (v : W)
  (h₂ : w ≺ v),
h₀ v h₂ (h₁ v h₂)

theorem necessitation : F ⊧ φ → F ⊧ □φ :=
λ (h₀ : F ⊧ φ)
  (V : ℕ → set W)
  (w : W)
  (v : W)
  (h₁ : w ≺ v),
h₀ V v

/--
theorem trans_iff_4
  : rel.transitive F ↔ F ⊧ □p →ₘ □□p :=
begin
  split,
  { intros trans h₀ v h₁ u₀ r₀ u₁ r₁,
    apply h₁,
    exact (trans v u₀ u₁ r₀ r₁) },
  { intros h w v u rwv rvu,
    by_contradiction nr,
    have Vᵤ : ℕ → set W := λ e z, z ≠ u,
    specialize h Vᵤ w,
    have h₀ : [F, Vᵤ, w] ⊧ □p,
    { intros v' rwv',
      simp [satisfy],
      by_contradiction,
      sorry },
    sorry }
end
-/

lemma us_soundness : F ⊧ φ → F ⊧ (subst p ψ φ) :=
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

lemma mp_soundness : F ⊧ φ →ₘ ψ → F ⊧ φ → F ⊧ ψ := λ h h₀ V w, (h V w) (h₀ V w) 

lemma ak_soundness : F ⊧ φ →ₘ ψ →ₘ φ := λ V w h h₀, h

lemma as_soundness : F ⊧ (φ →ₘ ψ →ₘ χ) →ₘ (φ →ₘ ψ) →ₘ φ →ₘ χ := λ V w h h₀ h₁, h h₁ (h₀ h₁)

lemma an_soundness : F ⊧ (¬ₘφ →ₘ ¬ₘψ) →ₘ ψ →ₘ φ := by { intros V w h, simp [satisfy], contrapose, exact h }

theorem soundness : ∅ ⊢ₖ φ → F ⊧ φ :=
begin
  assume h,
  induction h,
  { exact us_soundness _ h_p _ _ h_ih },
  { exfalso, exact h_ᾰ },
  { exact mp_soundness _ _ _ h_ih_ᾰ h_ih_ᾰ_1 },
  { exact necessitation _ _ h_ih },
  { exact ak_soundness _ _ _ },
  { exact as_soundness _ _ _ _ },
  { exact an_soundness _ _ _ },
  { exact distribution _ _ _ }
end

theorem consis : consistent ∅ := λ h, soundness trivial_frame ⊥ₘ h (λ n, ∅) singleton.s

end semantics