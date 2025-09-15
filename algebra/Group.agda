import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Function.Base using (_∘_; id)
open import Data.Product using (_×_; proj₁; proj₂)
import Data.Integer.Base as Int using (ℤ; +_; +0; _+_; -_; _*_)
import Data.Integer.Properties as Int using (+-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; +-comm; *-distribˡ-+)

record Group : Set₁ where
    field
        G : Set
        _*_ : G → G → G
        e : G
        / : G → G

        *-assoc : ∀ (x y z : G) → (x * y) * z ≡ x * (y * z)
        *-identityL : ∀ (x : G) → e * x ≡ x
        *-identityR : ∀ (x : G) → x * e ≡ x
        *-inverseL : ∀ (x : G) → / x * x ≡ e
        *-inverseR : ∀ (x : G) → x * / x ≡ e
    
    IdentityL : G → Set
    IdentityL e = ∀ (x : G) → e * x ≡ x

    IdentityR : G → Set
    IdentityR e = ∀ (x : G) → x * e ≡ x

    Identity : G → Set
    Identity e = IdentityL e × IdentityR e

    identity-unique : ∀ (e₁ e₂ : G) → Identity e₁ → Identity e₂ → e₁ ≡ e₂
    identity-unique e₁ e₂ identity1 identity2 =
        begin
            e₁
        ≡⟨ sym (proj₂ identity2 e₁) ⟩
            e₁ * e₂
        ≡⟨ proj₁ identity1 e₂ ⟩
            e₂
        ∎

    InverseL : G → G → Set
    InverseL x y = y * x ≡ e

    InverseR : G → G → Set
    InverseR x y = x * y ≡ e

    Inverse : G → G → Set
    Inverse x y = InverseL x y × InverseR x y

    inverse-unique : ∀ (x y₁ y₂ : G) → Inverse x y₁ → Inverse x y₂ → y₁ ≡ y₂
    inverse-unique x y₁ y₂ inverse1 inverse2 =
        begin
            y₁
        ≡⟨ sym (*-identityR y₁) ⟩
            y₁ * e
        ≡⟨ cong (_*_ y₁) (sym (proj₂ inverse2)) ⟩
            y₁ * (x * y₂)
        ≡⟨ sym (*-assoc y₁ x y₂) ⟩
            (y₁ * x) * y₂
        ≡⟨ cong (λ x → x * y₂) (proj₁ inverse1) ⟩
            e * y₂
        ≡⟨ *-identityL y₂ ⟩
            y₂
        ∎
    
    reductionL : ∀ (x y z : G) → x * y ≡ x * z → y ≡ z
    reductionL x y z xy=xz =
        begin
            y
        ≡⟨ sym (*-identityL y) ⟩
            e * y
        ≡⟨ cong (λ t → t * y) (sym (*-inverseL x)) ⟩
            (/ x * x) * y
        ≡⟨ *-assoc (/ x) x y ⟩
            / x * (x * y)
        ≡⟨ cong (_*_ (/ x)) xy=xz ⟩
            / x * (x * z)
        ≡⟨ sym (*-assoc (/ x) x z) ⟩
            (/ x * x) * z
        ≡⟨ cong (λ t → t * z) (*-inverseL x) ⟩
            e * z
        ≡⟨ *-identityL z ⟩
            z
        ∎
    
    reductionR : ∀ (x y z : G) → y * x ≡ z * x → y ≡ z
    reductionR x y z yx=zx =
        begin
            y
        ≡⟨ sym (*-identityR y) ⟩
            y * e
        ≡⟨ cong (_*_ y) (sym (*-inverseR x)) ⟩
            y * (x * / x)
        ≡⟨ sym (*-assoc y x (/ x)) ⟩
            (y * x) * / x
        ≡⟨ cong (λ t → t *  (/ x)) yx=zx ⟩
            (z * x) * / x
        ≡⟨ *-assoc z x (/ x) ⟩
            z * (x * / x)
        ≡⟨ cong (_*_ z) (*-inverseR x) ⟩
            z * e
        ≡⟨ *-identityR z ⟩
            z
        ∎

record AbelGroup : Set₁ where
    field
        G : Group
        *-comm : ∀ (x y : Group.G G) → (Group._*_ G) x y ≡ (Group._*_ G) y x

record Hom (G₁ G₂ : Group) : Set₁ where
    _*₁_ = Group._*_ G₁
    _*₂_ = Group._*_ G₂
    e₁ = Group.e G₁
    e₂ = Group.e G₂

    field
        hom : Group.G G₁ → Group.G G₂
        *-hom : ∀ (x y : Group.G G₁) → hom (x *₁ y) ≡ hom x *₂ hom y

    identity-preserve : hom e₁ ≡ e₂
    identity-preserve = Group.reductionL G₂ (hom e₁) (hom e₁) e₂ lemma where
        lemma : hom e₁ *₂ hom e₁ ≡ hom e₁ *₂ e₂
        lemma =
            begin
                hom e₁ *₂ hom e₁
            ≡⟨ sym (*-hom e₁ e₁) ⟩
                hom (e₁ *₁ e₁)
            ≡⟨ cong hom (Group.*-identityL G₁ e₁) ⟩
                hom e₁
            ≡⟨ sym (Group.*-identityR G₂ (hom e₁)) ⟩
                hom e₁ *₂ e₂
            ∎

record _≅_ (G₁ G₂ : Group) : Set₁ where
    field
        from : Hom G₁ G₂
        to   : Hom G₂ G₁
        inverse : let f = Hom.hom from in let g = Hom.hom to in (f ∘ g ≡ id) × (g ∘ f ≡ id)

Group-ℤ : Group
Group-ℤ = record
    { G = Int.ℤ
    ; _*_ = Int._+_
    ; e = Int.+0
    ; / = Int.-_

    ; *-assoc = Int.+-assoc
    ; *-identityL = Int.+-identityˡ
    ; *-identityR = Int.+-identityʳ
    ; *-inverseL = Int.+-inverseˡ
    ; *-inverseR = Int.+-inverseʳ
    }

AbelGroup-ℤ : AbelGroup
AbelGroup-ℤ = record
    { G = Group-ℤ
    ; *-comm = Int.+-comm
    }

twice : Int.ℤ → Int.ℤ
twice = Int._*_ (Int.+ 2)

twice-hom : Hom Group-ℤ Group-ℤ
twice-hom = record
    { hom = twice
    ; *-hom = Int.*-distribˡ-+ (Int.+ 2)
    }
