open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
    funExt : {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
