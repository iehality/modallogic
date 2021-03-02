import data.int.parity
import syntax
open classical

universe variables u 

structure kripke_frame (W : Type u) :=
(relation : W → W → Prop)

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
variables φ ψ : formula
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

variable p : ℕ
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

end semantics
