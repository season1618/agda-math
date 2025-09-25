open import Agda.Primitive
open import Data.Product using (Σ; _,_; Σ-syntax; ∃-syntax; _×_; proj₁)
open import Relation.Binary using (Rel; IsEquivalence)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Function.Base using (_∘_; id)

-- specification
record Spec (A : Set) (P : A -> Set) : Set where
    constructor ⟨_,_⟩
    field
        elem : A
        .certificate : P elem

open Spec

cong-spec : {A : Set} {P : A → Set} → {x y : Spec A P} → Spec.elem x ≡ Spec.elem y → x ≡ y
cong-spec refl = refl

record Subset (S : Set) : Set₁ where
    field
        P : S → Set

    set : Set
    set = Spec S P

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
    is_equiv = EquivRel.is_equiv Eqv
    ~-refl = IsEquivalence.refl is_equiv
    ~-sym = IsEquivalence.sym is_equiv
    ~-trans = IsEquivalence.trans is_equiv

    field
        C : Subset S

        complete : ∀ (x : S) → Σ[ c ∈ set C ] (elem c ~ x)
        disjoint : ∀ (x y : set C) → elem x ~ elem y → x ≡ y

    c∈[c] : ∀ (c : set C) → proj₁ (complete (elem c)) ≡ c
    c∈[c] c =
        let c' , c'~c = complete (elem c)
        in disjoint c' c c'~c

    x~y→[x]=[y] : ∀ (x y : S) → x ~ y → proj₁ (complete x) ≡ proj₁ (complete y)
    x~y→[x]=[y] x y x~y =
        let c1 , c1~x = complete x
            c2 , c2~y = complete y
            c1~c2 = ~-trans (~-trans c1~x x~y) (~-sym c2~y) -- elem c1 ~ elem c2
        in disjoint c1 c2 c1~c2

    x~c→[x]=[c] : ∀ (x : S) (c : set C) → x ~ elem c → proj₁ (complete x) ≡ c
    x~c→[x]=[c] x c x~c = trans (x~y→[x]=[y] x (elem c) x~c) (c∈[c] c)

proj : ∀ {S : Set} {_~_ : EquivRel S} (S/~ : Quotient S _~_) → S → set (Quotient.C S/~)
proj S/~ x = proj₁ (Quotient.complete S/~ x)
