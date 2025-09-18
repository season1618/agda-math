module Irrelevance where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

postulate
    .irrAx : ∀ {ℓ} {A : Set ℓ} -> .A -> A

record Spec (A : Set) (P : A -> Set) : Set where
    constructor ⟨_,_⟩
    field
        x : A
        .certificate : P x

cong-spec : {A : Set} {P : A → Set} → (x : Spec A P) → (y : Spec A P) → Spec.x x ≡ Spec.x y → x ≡ y
cong-spec _ _ refl = refl