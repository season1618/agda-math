import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
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

record AbelGroup : Set₁ where
    field
        G : Group
        *-comm : ∀ (x y : Group.G G) → (Group._*_ G) x y ≡ (Group._*_ G) y x

record Hom (G₁ G₂ : Group) : Set₁ where
    field
        hom : Group.G G₁ → Group.G G₂
        *-hom : ∀ (x y : Group.G G₁) → hom (Group._*_ G₁ x y) ≡ Group._*_ G₂ (hom x) (hom y)

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
