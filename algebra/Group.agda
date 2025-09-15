import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.Integer.Base using (ℤ; +0; _+_; -_)
open import Data.Integer.Properties using (+-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; +-comm)

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

record AbelGroup : Set₁ where
    field
        G : Group
        *-comm : ∀ (x y : Group.G G) → (Group._*_ G) x y ≡ (Group._*_ G) y x

Group-ℤ : Group
Group-ℤ = record
    { G = ℤ
    ; _*_ = _+_
    ; e = +0
    ; / = -_

    ; *-assoc = +-assoc
    ; *-identityL = +-identityˡ
    ; *-identityR = +-identityʳ
    ; *-inverseL = +-inverseˡ
    ; *-inverseR = +-inverseʳ
    }

AbelGroup-ℤ : AbelGroup
AbelGroup-ℤ = record
    { G = Group-ℤ
    ; *-comm = +-comm
    }

