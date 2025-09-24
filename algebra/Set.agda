open import Agda.Primitive
open import Data.Product using (Σ; _,_; Σ-syntax; ∃-syntax; _×_; proj₁)
open import Relation.Binary using (Rel; IsEquivalence)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Function.Base using (_∘_; id)

open import Irrelevance using (Spec)
open Spec

record Subset (S : Set) : Set₁ where
    field
        P : S → Set

    subset : Set
    subset = Spec S P

open Subset

record _≅_ (S₁ S₂ : Set) : Set where
    field
        from : S₁ → S₂
        to   : S₂ → S₁
        inverse : from ∘ to ≡ id × to ∘ from ≡ id

≅-trans : ∀ {S₁ S₂ S₃ : Set} → S₁ ≅ S₂ → S₂ ≅ S₃ → S₁ ≅ S₃
≅-trans
    record { from = f ; to = f⁻¹ ; inverse = (ff⁻¹=id , f⁻¹f=id) }
    record { from = g ; to = g⁻¹ ; inverse = (gg⁻¹=id , g⁻¹g=id) } =
    let h = g ∘ f
        h⁻¹ = f⁻¹ ∘ g⁻¹
        h-inverse1 : h ∘ h⁻¹ ≡ id
        h-inverse1 =
            begin
                (g ∘ f) ∘ (f⁻¹ ∘ g⁻¹)
            ≡⟨ cong (\i → g ∘ i ∘ g⁻¹) ff⁻¹=id ⟩
                g ∘ id ∘ g⁻¹
            ≡⟨ gg⁻¹=id ⟩
                id
            ∎
        h-inverse2 : h⁻¹ ∘ h ≡ id
        h-inverse2 =
            begin
                (f⁻¹ ∘ g⁻¹) ∘ (g ∘ f)
            ≡⟨ cong (\i → f⁻¹ ∘ i ∘ f) g⁻¹g=id ⟩
                f⁻¹ ∘ id ∘ f
            ≡⟨ f⁻¹f=id ⟩
                id
            ∎
    in record
        { from = h
        ; to   = h⁻¹
        ; inverse = h-inverse1 , h-inverse2
        }

≅-sym : ∀ {S₁ S₂ : Set} → S₁ ≅ S₂ → S₂ ≅ S₁
≅-sym
    record { from = f; to = f⁻¹; inverse = (ff⁻¹=id , f⁻¹f=id) } =
    record { from = f⁻¹; to = f; inverse = (f⁻¹f=id , ff⁻¹=id) }

record EquivRel (S : Set) : Set₁ where
    field
        R : Rel S lzero

        is_equiv : IsEquivalence R

record Quotient (S : Set) (Eqv : EquivRel S) : Set₁ where
    _~_ = EquivRel.R Eqv

    field
        C : Subset S

        complete : ∀ (x : S) → Σ[ c ∈ subset C ] (x ~ elem c)
        disjoint : ∀ (x y : subset C) → elem x ~ elem y → x ≡ y

proj : ∀ {S : Set} {~ : EquivRel S} (S/~ : Quotient S ~) → S → subset (Quotient.C S/~)
proj S/~ x = proj₁ (Quotient.complete S/~ x)
