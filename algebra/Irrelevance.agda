module Irrelevance where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

postulate
    .irrAx : ∀ {l} {A : Set l} -> .A -> A

record IrrProduct (A B : Set) : Set where
    constructor _,_
    field
        fst : A
        .snd : B

record Spec (A : Set) (P : A -> Set) : Set where
    constructor ⟨_,_⟩
    field
        elem : A
        .certificate : P elem

cong-spec : {A : Set} {P : A → Set} → {x y : Spec A P} → Spec.elem x ≡ Spec.elem y → x ≡ y
cong-spec refl = refl