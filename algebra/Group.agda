open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; IsEquivalence)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Function.Base using (_∘_; id)
open import Data.Product using (_,_; ∃-syntax; _×_; proj₁; proj₂)
import Data.Integer.Base as Int using (ℤ; +_; +0; _+_; -_; _*_)
import Data.Integer.Properties as Int using (+-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; +-comm; *-distribˡ-+)

open import Extensionality using (funExt)
open import Irrelevance using (irrAx; IrrProduct; _,_)
open import Set using (Spec; ⟨_,_⟩; cong-spec; Subset)

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
        ≡⟨ cong (y₁ *_) (sym (proj₂ inverse2)) ⟩
            y₁ * (x * y₂)
        ≡⟨ sym (*-assoc y₁ x y₂) ⟩
            (y₁ * x) * y₂
        ≡⟨ cong (_* y₂) (proj₁ inverse1) ⟩
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
        ≡⟨ cong (_* y) (sym (*-inverseL x)) ⟩
            (/ x * x) * y
        ≡⟨ *-assoc (/ x) x y ⟩
            / x * (x * y)
        ≡⟨ cong (/ x *_) xy=xz ⟩
            / x * (x * z)
        ≡⟨ sym (*-assoc (/ x) x z) ⟩
            (/ x * x) * z
        ≡⟨ cong (_* z) (*-inverseL x) ⟩
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
        ≡⟨ cong (y *_) (sym (*-inverseR x)) ⟩
            y * (x * / x)
        ≡⟨ sym (*-assoc y x (/ x)) ⟩
            (y * x) * / x
        ≡⟨ cong (_* (/ x)) yx=zx ⟩
            (z * x) * / x
        ≡⟨ *-assoc z x (/ x) ⟩
            z * (x * / x)
        ≡⟨ cong (z *_) (*-inverseR x) ⟩
            z * e
        ≡⟨ *-identityR z ⟩
            z
        ∎

    x⁻¹xy=y : ∀ (x y : G) → / x * (x * y) ≡ y
    x⁻¹xy=y x y =
        begin
            / x * (x * y)
        ≡⟨ sym (*-assoc (/ x) x y) ⟩
            (/ x * x) * y
        ≡⟨ cong (_* y) (*-inverseL x) ⟩
            e * y
        ≡⟨ *-identityL y ⟩
            y
        ∎

    xx⁻¹y=y : ∀ (x y : G) → x * (/ x * y) ≡ y
    xx⁻¹y=y x y =
        begin
            x * (/ x * y)
        ≡⟨ sym (*-assoc x (/ x) y) ⟩
            (x * / x) * y
        ≡⟨ cong (_* y) (*-inverseR x) ⟩
            e * y
        ≡⟨ *-identityL y ⟩
            y
        ∎

    inverse-product : ∀ (x y : G) → / (x * y) ≡ / y * / x
    inverse-product x y = reductionL (x * y) (/ (x * y)) (/ y * / x) lemma where
        lemma : (x * y) * (/ (x * y)) ≡ (x * y) * (/ y * / x)
        lemma =
            begin
                (x * y) * / (x * y)
            ≡⟨ *-inverseR (x * y) ⟩
                e
            ≡⟨ sym (*-inverseR x) ⟩
                x * / x
            ≡⟨ cong (_* (/ x)) (sym (*-identityR x)) ⟩
                (x * e) * / x
            ≡⟨ cong (\t → (x * t) * / x) (sym (*-inverseR y)) ⟩
                (x * (y * / y)) * / x
            ≡⟨ cong (_* / x) (sym (*-assoc x y (/ y))) ⟩
                ((x * y) * / y) * / x
            ≡⟨ *-assoc (x * y) (/ y) (/ x) ⟩
                (x * y) * (/ y * / x)
            ∎
    
    inverse-identity : / e ≡ e
    inverse-identity = inverse-unique e (/ e) e (*-inverseL e , *-inverseR e) (*-identityL e , *-identityR e)

    inverse-inverse : ∀ (x : G) → / (/ x) ≡ x
    inverse-inverse x = reductionL (/ x) (/ (/ x)) x x⁻¹x⁻¹⁻¹=x⁻¹x where
        x⁻¹x⁻¹⁻¹=x⁻¹x : / x * / (/ x) ≡ / x * x
        x⁻¹x⁻¹⁻¹=x⁻¹x =
            begin
                / x * / (/ x)
            ≡⟨ *-inverseR (/ x) ⟩
                e
            ≡⟨ sym (*-inverseL x) ⟩
                / x * x
            ∎

record AbelGroup : Set₁ where
    field
        G : Group
        *-comm : ∀ (x y : Group.G G) → (Group._*_ G) x y ≡ (Group._*_ G) y x

record Subgroup (G : Group) : Set₁ where
    S = Group.G G
    _*_ = Group._*_ G
    e = Group.e G
    / = Group./ G

    field
        P : S → Set
        *-closure : ∀ (x y : S) → P x → P y → P (x * y)
        *-identity : P e
        *-inverse : ∀ (x : S) → P x → P (/ x)

    set : Set
    set = Spec S P

    group : Group
    group = record
        { G = T
        ; _*_ = _*'_
        ; e = e'
        ; / = /'

        ; *-assoc = \x y z → cong-spec (Group.*-assoc G (Spec.elem x) (Spec.elem y) (Spec.elem z))
        ; *-identityL = \x → cong-spec (Group.*-identityL G (Spec.elem x))
        ; *-identityR = \x → cong-spec (Group.*-identityR G (Spec.elem x))
        ; *-inverseL = \x → cong-spec (Group.*-inverseL G (Spec.elem x))
        ; *-inverseR = \x → cong-spec (Group.*-inverseR G (Spec.elem x))
        } where
            T : Set
            T = Spec S P

            _*'_ : T → T → T
            _*'_ ⟨ x , px ⟩ ⟨ y , py ⟩ = ⟨ x * y , *-closure x y px py ⟩

            e' : T
            e' = ⟨ e , *-identity ⟩

            /' : T → T
            /' ⟨ x , px ⟩ = ⟨ / x , *-inverse x px ⟩

record NormalSubgroup (G : Group) : Set₁ where
    S = Group.G G
    _*_ = Group._*_ G
    e = Group.e G
    / = Group./ G

    field
        P : S → Set
        *-closure : ∀ (x y : S) → P x → P y → P (x * y)
        *-identity : P e
        *-inverse : ∀ (x : S) → P x → P (/ x)
        *-normal : ∀ (g h : S) → P h → P ((g * h) * / g)
    
    subgroup : Subgroup G
    subgroup = record
        { P = P
        ; *-closure = *-closure
        ; *-identity = *-identity
        ; *-inverse = *-inverse
        }

module EquivBySubgroup (G : Group) (H : Subgroup G) where
    private
        S = Group.G G
        P = Subgroup.P H
        _*_ = Group._*_ G
        e = Group.e G
        / = Group./ G

    data _~_ : S → S → Set where
        evid : (x y : S) → .(P (/ x * y)) → x ~ y

    take : {x y : S} → x ~ y → IrrProduct (S × S) (P (/ x * y))
    take (evid x y x~y) = (x , y) , x~y

    ~-refl : Reflexive _~_
    ~-refl {x} = evid x x (subst P (sym (Group.*-inverseL G x)) (Subgroup.*-identity H))

    ~-sym : Symmetric _~_
    ~-sym {x} {y} (evid x y x~y) = evid y x (subst P /x⁻¹y=y⁻¹x (Subgroup.*-inverse H (/ x * y) x~y)) where
        /x⁻¹y=y⁻¹x : / (/ x * y) ≡ / y * x
        /x⁻¹y=y⁻¹x =
            begin
                / (/ x * y)
            ≡⟨ Group.inverse-product G (/ x) y ⟩
                / y * / (/ x)
            ≡⟨ cong (/ y *_) (Group.inverse-inverse G x) ⟩
                / y * x
            ∎

    ~-trans : Transitive _~_
    ~-trans {x} {y} {z} (evid x y x~y) (evid y z y~z) = evid x z (subst P x⁻¹yy⁻¹z=x⁻¹z (Subgroup.*-closure H (/ x * y) (/ y * z) x~y y~z)) where
        x⁻¹yy⁻¹z=x⁻¹z : (/ x * y) * (/ y * z) ≡ / x * z
        x⁻¹yy⁻¹z=x⁻¹z =
            begin
                (/ x * y) * (/ y * z)
            ≡⟨ Group.*-assoc G (/ x) y (/ y * z) ⟩
                / x * (y * (/ y * z))
            ≡⟨ cong (/ x *_) (sym (Group.*-assoc G y (/ y) z)) ⟩
                / x * ((y * / y) * z)
            ≡⟨ cong (\t → / x * (t * z)) (Group.*-inverseR G y) ⟩
                / x * (e * z)
            ≡⟨ cong (/ x *_) (Group.*-identityL G z) ⟩
                / x * z
            ∎
    
    ~-substL : (x y z : S) → x ~ y → x ≡ z → z ~ y
    ~-substL x y z (evid x y x~y) x=z = evid z y z~y where
        .z~y : P (/ z * y)
        z~y = subst P (cong (\t → / t * y) x=z) (irrAx x~y)

    ~-substR : (x y z : S) → x ~ y → y ≡ z → x ~ z
    ~-substR x y z (evid x y x~y) y=z = evid x z x~z where
        .x~z : P (/ x * z)
        x~z = subst P (cong (/ x *_) y=z) (irrAx x~y)

    x~y→zx~zy : ∀ (x y z : S) → x ~ y → (z * x) ~ (z * y)
    x~y→zx~zy x y z (evid x y x⁻¹y∈H) = evid (z * x) (z * y) x⁻¹z⁻¹zy∈H where
        x⁻¹z⁻¹zy=x⁻¹y : / (z * x) * (z * y) ≡ / x * y
        x⁻¹z⁻¹zy=x⁻¹y =
            begin
                / (z * x) * (z * y)
            ≡⟨ cong (_* (z * y)) (Group.inverse-product G z x) ⟩
                (/ x * / z) * (z * y)
            ≡⟨ Group.*-assoc G (/ x) (/ z) (z * y) ⟩
                / x * (/ z * (z * y))
            ≡⟨ cong (/ x *_) (sym (Group.*-assoc G (/ z) z y)) ⟩
                / x * ((/ z * z) * y)
            ≡⟨ cong (\t → / x * (t * y)) (Group.*-inverseL G z) ⟩
                / x * (e * y)
            ≡⟨ cong (/ x *_) (Group.*-identityL G y) ⟩
                / x * y
            ∎

        .x⁻¹z⁻¹zy∈H : P (/ (z * x) * (z * y))
        x⁻¹z⁻¹zy∈H = subst P (sym x⁻¹z⁻¹zy=x⁻¹y) (irrAx x⁻¹y∈H)

    g~gh : ∀ (g : S) → (h : Subgroup.set H) → g ~ (g * Spec.elem h)
    g~gh g ⟨ h , Ph ⟩ = evid g (g * h) (subst P (sym (Group.x⁻¹xy=y G g h)) Ph)

    Quotient : Set₁
    Quotient = Set.Quotient S Eqv
        where
            Eqv = record
                { R = _~_
                ; is_equiv = record
                    { refl = ~-refl
                    ; sym = ~-sym
                    ; trans = ~-trans
                    }
                }

    lagrange : (G/H : Quotient) →
        let T = Subgroup.set H
            U = Subset.set (Set.Quotient.C G/H)
        in S Set.≅ (T × U)
    lagrange G/H = record
        { from = from'
        ; to   = to'
        ; inverse = from∘to=id , to∘from=id
        } where
            T = Subgroup.set H
            U = Subset.set (Set.Quotient.C G/H)

            from' : S → T × U
            from' g =
                let ⟨ c , c∈U ⟩ , res = Set.Quotient.complete G/H g
                    _ , c~g = take res
                    h = / c * g
                in ⟨ h , c~g ⟩ , ⟨ c , c∈U ⟩

            to' : T × U → S
            to' ( ⟨ h , h∈T ⟩ , ⟨ c , c∈U ⟩ ) = c * h

            fromtox=x : ∀ (x : T × U) → (from' ∘ to') x ≡ x
            fromtox=x ( ⟨ h , h∈T ⟩ , ⟨ c , c∈U ⟩ ) =
                let [ch]=[c] = Set.Quotient.x~c→[x]=[c] G/H (c * h) ⟨ c , c∈U ⟩ (~-sym (g~gh c ⟨ h , h∈T ⟩))
                in cong₂ _,_
                    (cong-spec (trans (cong (\t → / (Spec.elem t) * (c * h)) [ch]=[c]) (Group.x⁻¹xy=y G c h)))
                    [ch]=[c]

            tofromx=x : ∀ (x : S) → (to' ∘ from') x ≡ x
            tofromx=x g =
                let c = Spec.elem (proj₁ (Set.Quotient.complete G/H g))
                in Group.xx⁻¹y=y G c g

            from∘to=id : from' ∘ to' ≡ id
            from∘to=id = funExt fromtox=x

            to∘from=id : to' ∘ from' ≡ id
            to∘from=id = funExt tofromx=x

module EquivByNormalSubgroup (G : Group) (N : NormalSubgroup G) where
    private
        S = Group.G G
        _*_ = Group._*_ G
        e = Group.e G
        / = Group./ G

        H = NormalSubgroup.subgroup N
        P = Subgroup.P H

        _~_ = EquivBySubgroup._~_ G H
        ~-sym = EquivBySubgroup.~-sym G H
        ~-trans = EquivBySubgroup.~-trans G H
        ~-substL = EquivBySubgroup.~-substL G H
        ~-substR = EquivBySubgroup.~-substR G H
        x~y→zx~zy = EquivBySubgroup.x~y→zx~zy G H

    x~y→xz~yz : ∀ (x y z : S) → x ~ y → (x * z) ~ (y * z)
    x~y→xz~yz x y z (EquivBySubgroup.evid x y x⁻¹y∈H) = EquivBySubgroup.evid (x * z) (y * z) z⁻¹x⁻¹yz∈H where
        lemma : / (x * z) * (y * z) ≡ ((/ z) * (/ x * y)) * / (/ z)
        lemma =
            begin
                / (x * z) * (y * z)
            ≡⟨ cong (_* (y * z)) (Group.inverse-product G x z) ⟩
                (/ z * / x) * (y * z)
            ≡⟨ Group.*-assoc G (/ z) (/ x) (y * z) ⟩
                / z * (/ x * (y * z))
            ≡⟨ cong (/ z *_) (sym (Group.*-assoc G (/ x) y z)) ⟩
                / z * ((/ x * y) * z)
            ≡⟨ sym (Group.*-assoc G (/ z) (/ x * y) z) ⟩
                (/ z * (/ x * y)) * z
            ≡⟨ cong ((/ z * (/ x * y)) *_) (sym (Group.inverse-inverse G z)) ⟩
                (/ z * (/ x * y)) * / (/ z)
            ∎
        
        .z⁻¹x⁻¹yz∈H : P (/ (x * z) * (y * z))
        z⁻¹x⁻¹yz∈H = subst P (sym lemma) (NormalSubgroup.*-normal N (/ z) (/ x * y) (irrAx x⁻¹y∈H))

    g~hg : ∀ (g : S) → (h : Subgroup.set H) → g ~ (Spec.elem h * g)
    g~hg g ⟨ h , h∈H ⟩ = EquivBySubgroup.evid g (h * g) g⁻¹hg∈H where
        lemma : (/ g) * (h * g) ≡ ((/ g) * h) * / (/ g)
        lemma =
            begin
                (/ g) * (h * g)
            ≡⟨ sym (Group.*-assoc G (/ g) h g) ⟩
                (/ g * h) * g
            ≡⟨ cong ((/ g * h) *_) (sym (Group.inverse-inverse G g)) ⟩
                (/ g * h) * / (/ g)
            ∎

        .g⁻¹hg∈H : P (/ g * (h * g))
        g⁻¹hg∈H = subst P (sym lemma) (NormalSubgroup.*-normal N (/ g) h (irrAx h∈H))

    QuotientGroup : (G/H : EquivBySubgroup.Quotient G H) → Group
    QuotientGroup G/H = record
        { G = C
        ; _*_ = _*'_
        ; e = e'
        ; / = /'

        ; *-assoc = *-assoc'
        ; *-identityL = *-identityL'
        ; *-identityR = *-identityR'
        ; *-inverseL = *-inverseL'
        ; *-inverseR = *-inverseR'
        } where
            C = Subset.set (Set.Quotient.C G/H)

            _*'_ : C → C → C
            ⟨ x , _ ⟩ *' ⟨ y , _ ⟩ = Set.proj G/H (x * y)

            e' : C
            e' = Set.proj G/H e

            /' : C → C
            /' ⟨ x , _ ⟩ = Set.proj G/H (/ x)

            *-assoc' : ∀ (x y z : C) → (x *' y) *' z ≡ x *' (y *' z)
            *-assoc' ⟨ x , px ⟩ ⟨ y , py ⟩ ⟨ z , pz ⟩ =
                let ⟨ [xy] , _ ⟩ , [xy]~xy = Set.Quotient.complete G/H (x * y)
                    ⟨ [[xy]z] , _ ⟩ , [[xy]z]~[xy]z = Set.Quotient.complete G/H ([xy] * z)
                    ⟨ [yz] , _ ⟩ , [yz]~yz = Set.Quotient.complete G/H (y * z)
                    ⟨ [x[yz]] , _ ⟩ , [x[yz]]~x[yz] = Set.Quotient.complete G/H (x * [yz])

                    [xy]z~xyz = x~y→xz~yz [xy] (x * y) z [xy]~xy
                    x[yz]~xyz = x~y→zx~zy [yz] (y * z) x [yz]~yz

                    [xy]z~x[yz] = ~-trans
                        (~-trans [xy]z~xyz lemma)
                        (~-sym x[yz]~xyz)

                in Set.Quotient.x~y→[x]=[y] G/H ([xy] * z) (x * [yz]) [xy]z~x[yz] where
                    lemma : ((x * y) * z) ~ (x * (y * z))
                    lemma = EquivBySubgroup.evid ((x * y) * z) (x * (y * z)) lemma' where
                        lemma' : P (/ ((x * y) * z) * (x * (y * z)))
                        lemma' = subst P (sym lemma'') (Subgroup.*-identity H) where
                            lemma'' : / ((x * y) * z) * (x * (y * z)) ≡ e
                            lemma'' =
                                begin
                                    / ((x * y) * z) * (x * (y * z))
                                ≡⟨ cong (\t → / t * (x * (y * z))) (Group.*-assoc G x y z) ⟩
                                    / (x * (y * z)) * (x * (y * z))
                                ≡⟨ Group.*-inverseL G (x * (y * z)) ⟩
                                    e
                                ∎

            *-identityL' : ∀ (x : C) → e' *' x ≡ x
            *-identityL' ⟨ x , x∈C ⟩ =
                let ⟨ h , h∈C ⟩ , h~e = Set.Quotient.complete G/H e
                    _ , h⁻¹e∈H = EquivBySubgroup.take G H h~e
                    .h∈H : P h
                    h∈H = subst P (Group.inverse-inverse G h) (Subgroup.*-inverse H (/ h) (subst P (Group.*-identityR G (/ h)) (irrAx h⁻¹e∈H)))
                    x~hx = g~hg x ⟨ h , h∈H ⟩
                in Set.Quotient.x~c→[x]=[c] G/H (h * x) ⟨ x , x∈C ⟩ (~-sym x~hx)

            *-identityR' : ∀ (x : C) → x *' e' ≡ x
            *-identityR' ⟨ x , x∈C ⟩ =
                let ⟨ h , h∈C ⟩ , h~e = Set.Quotient.complete G/H e
                    _ , h⁻¹e∈H = EquivBySubgroup.take G H h~e
                    .h∈H : P h
                    h∈H = subst P (Group.inverse-inverse G h) (Subgroup.*-inverse H (/ h) (subst P (Group.*-identityR G (/ h)) (irrAx h⁻¹e∈H)))
                    x~xh = EquivBySubgroup.g~gh G H x ⟨ h , h∈H ⟩
                in Set.Quotient.x~c→[x]=[c] G/H (x * h) ⟨ x , x∈C ⟩ (~-sym x~xh)

            *-inverseL' : ∀ (x : C) → (/' x) *' x ≡ e'
            *-inverseL' ⟨ x , x∈C ⟩ =
                let ⟨ h , h∈C ⟩ , h~e = Set.Quotient.complete G/H e
                    ⟨ [x⁻¹] , [x⁻¹]∈C ⟩ , [x⁻¹]~x⁻¹ = Set.Quotient.complete G/H (/ x)
                    [x⁻¹]x~x⁻¹x = x~y→xz~yz [x⁻¹] (/ x) x [x⁻¹]~x⁻¹
                    [x⁻¹]x~e = ~-substR ([x⁻¹] * x) (/ x * x) e [x⁻¹]x~x⁻¹x (Group.*-inverseL G x)
                in Set.Quotient.x~y→[x]=[y] G/H ([x⁻¹] * x) e [x⁻¹]x~e

            *-inverseR' : ∀ (x : C) → x *' (/' x) ≡ e'
            *-inverseR' ⟨ x , x∈C ⟩ =
                let ⟨ h , h∈C ⟩ , h~e = Set.Quotient.complete G/H e
                    ⟨ [x⁻¹] , [x⁻¹]∈C ⟩ , [x⁻¹]~x⁻¹ = Set.Quotient.complete G/H (/ x)
                    x[x⁻¹]~xx⁻¹ = x~y→zx~zy [x⁻¹] (/ x) x [x⁻¹]~x⁻¹
                    x[x⁻¹]~e = ~-substR (x * [x⁻¹]) (x * / x) e x[x⁻¹]~xx⁻¹ (Group.*-inverseR G x)
                in Set.Quotient.x~y→[x]=[y] G/H (x * [x⁻¹]) e x[x⁻¹]~e

record Hom (G₁ G₂ : Group) : Set₁ where
    S₁ = Group.G G₁
    S₂ = Group.G G₂
    _*₁_ = Group._*_ G₁
    _*₂_ = Group._*_ G₂
    e₁ = Group.e G₁
    e₂ = Group.e G₂
    /₁ = Group./ G₁
    /₂ = Group./ G₂

    field
        fun : S₁ → S₂
        *-preserve : ∀ (x y : S₁) → fun (x *₁ y) ≡ fun x *₂ fun y

    identity-preserve : fun e₁ ≡ e₂
    identity-preserve = Group.reductionL G₂ (fun e₁) (fun e₁) e₂ lemma where
        lemma : fun e₁ *₂ fun e₁ ≡ fun e₁ *₂ e₂
        lemma =
            begin
                fun e₁ *₂ fun e₁
            ≡⟨ sym (*-preserve e₁ e₁) ⟩
                fun (e₁ *₁ e₁)
            ≡⟨ cong fun (Group.*-identityL G₁ e₁) ⟩
                fun e₁
            ≡⟨ sym (Group.*-identityR G₂ (fun e₁)) ⟩
                fun e₁ *₂ e₂
            ∎

    inverse-preserve : ∀ (x : S₁) → fun (/₁ x) ≡ /₂ (fun x)
    inverse-preserve x = Group.reductionL G₂ (fun x) (fun (/₁ x)) (/₂ (fun x)) lemma where
        lemma : fun x *₂ fun (/₁ x) ≡ fun x *₂ /₂ (fun x)
        lemma =
            begin
                fun x *₂ fun (/₁ x)
            ≡⟨ sym (*-preserve x (/₁ x)) ⟩
                fun (x *₁ /₁ x)
            ≡⟨ cong fun (Group.*-inverseR G₁ x) ⟩
                fun e₁
            ≡⟨ identity-preserve ⟩
                e₂
            ≡⟨ sym (Group.*-inverseR G₂ (fun x)) ⟩
                fun x *₂ /₂ (fun x)
            ∎

    Ker : NormalSubgroup G₁
    Ker = record
        { P = \x → fun x ≡ e₂
        ; *-closure = *-closure'
        ; *-identity = identity-preserve
        ; *-inverse = *-inverse'
        ; *-normal = *-normal'
        } where
            *-closure' : ∀ (x y : S₁) → fun x ≡ e₂ → fun y ≡ e₂ → fun (x *₁ y) ≡ e₂
            *-closure' x y fx=e fy=e = fxy=e where
                fxy=e : fun (x *₁ y) ≡ e₂
                fxy=e =
                    begin
                        fun (x *₁ y)
                    ≡⟨ *-preserve x y ⟩
                        fun x *₂ fun y
                    ≡⟨ cong (_*₂ fun y) fx=e ⟩
                        e₂ *₂ fun y
                    ≡⟨ cong (e₂ *₂_) fy=e ⟩
                        e₂ *₂ e₂
                    ≡⟨ Group.*-identityL G₂ e₂ ⟩
                        e₂
                    ∎
            *-inverse' : ∀ (x : S₁) → fun x ≡ e₂ → fun (/₁ x) ≡ e₂
            *-inverse' x fx=e = fx⁻¹=e where
                fx⁻¹=e : fun (/₁ x) ≡ e₂
                fx⁻¹=e =
                    begin
                        fun (/₁ x)
                    ≡⟨ inverse-preserve x ⟩
                        /₂ (fun x)
                    ≡⟨ cong /₂ fx=e ⟩
                        /₂ e₂ 
                    ≡⟨ Group.inverse-identity G₂ ⟩
                        e₂
                    ∎
            *-normal' : ∀ (g h : S₁) → fun h ≡ e₂ → fun ((g *₁ h) *₁ /₁ g) ≡ e₂
            *-normal' g h fh=e =
                begin
                    fun ((g *₁ h) *₁ /₁ g)
                ≡⟨ *-preserve (g *₁ h) (/₁ g) ⟩
                    fun (g *₁ h) *₂ fun (/₁ g)
                ≡⟨ cong (_*₂ fun (/₁ g)) (*-preserve g h) ⟩
                    (fun g *₂ fun h) *₂ fun (/₁ g)
                ≡⟨ cong (\t → (fun g *₂ t) *₂ fun (/₁ g)) fh=e ⟩
                    (fun g *₂ e₂) *₂ fun (/₁ g)
                ≡⟨ cong (_*₂ fun (/₁ g)) (Group.*-identityR G₂ (fun g)) ⟩
                    fun g *₂ fun (/₁ g)
                ≡⟨ cong (fun g *₂_) (inverse-preserve g) ⟩
                    fun g *₂ /₂ (fun g)
                ≡⟨ Group.*-inverseR G₂ (fun g) ⟩
                    e₂
                ∎

    Im : Subgroup G₂
    Im = record
        { P = \x → ∃[ y ] fun y ≡ x
        ; *-closure = *-closure'
        ; *-identity = (e₁ , identity-preserve)
        ; *-inverse = *-inverse'
        } where
            *-closure' : ∀ (x y : S₂) → ∃[ x' ] fun x' ≡ x → ∃[ y' ] fun y' ≡ y → ∃[ xy' ] fun xy' ≡ x *₂ y
            *-closure' x y (x' , fx'=x) (y' , fy'=y) = (x' *₁ y' , fxy'=xy) where
                fxy'=xy : fun (x' *₁ y') ≡ x *₂ y
                fxy'=xy =
                    begin
                        fun (x' *₁ y')
                    ≡⟨ *-preserve x' y' ⟩
                        fun x' *₂ fun y'
                    ≡⟨ cong (_*₂ fun y') fx'=x ⟩
                        x *₂ fun y'
                    ≡⟨ cong (x *₂_) fy'=y ⟩
                        x *₂ y
                    ∎
            *-inverse' : ∀ (x : S₂) → ∃[ x' ] fun x' ≡ x → ∃[ /x' ] fun /x' ≡ /₂ x
            *-inverse' x (x' , fx'=x) = (/₁ x' , fx⁻¹'=x⁻¹) where
                fx⁻¹'=x⁻¹ : fun (/₁ x') ≡ /₂ x
                fx⁻¹'=x⁻¹ =
                    begin
                        fun (/₁ x')
                    ≡⟨ inverse-preserve x' ⟩
                        /₂ (fun x')
                    ≡⟨ cong /₂ fx'=x ⟩
                        /₂ x
                    ∎

record _≅_ (G₁ G₂ : Group) : Set₁ where
    field
        from : Hom G₁ G₂
        to   : Hom G₂ G₁
        inverse : let f = Hom.fun from in let g = Hom.fun to in (f ∘ g ≡ id) × (g ∘ f ≡ id)

_∘*_ : ∀ (G₁ G₂ G₃ : Group) → Hom G₂ G₃ → Hom G₁ G₂ → Hom G₁ G₃
_∘*_ G₁ G₂ G₃ ψ φ =
    let S₁ = Group.G G₁
        S₂ = Group.G G₂
        S₃ = Group.G G₃
        _*₁_ = Group._*_ G₁
        _*₂_ = Group._*_ G₂
        _*₃_ = Group._*_ G₃
        f = Hom.fun φ
        g = Hom.fun ψ
        h = g ∘ f
        h-hom : ∀ (x y : S₁) → h (x *₁ y) ≡ h x *₃ h y
        h-hom x y =
            begin
                (g ∘ f) (x *₁ y)
            ≡⟨ cong g (Hom.*-preserve φ x y) ⟩
                g (f x *₂ f y)
            ≡⟨ Hom.*-preserve ψ (f x) (f y) ⟩
                g (f x) *₃ g (f y)
            ∎
    in record
        { fun = h
        ; *-preserve = h-hom
        }

≅-trans : ∀ (G₁ G₂ G₃ : Group) → G₁ ≅ G₂ → G₂ ≅ G₃ → G₁ ≅ G₃
≅-trans G₁ G₂ G₃
    record { from = φ@record { fun = f } ; to = φ⁻¹@record{ fun = f⁻¹ } ; inverse = (ff⁻¹=id , f⁻¹f=id) }
    record { from = ψ@record { fun = g } ; to = ψ⁻¹@record{ fun = g⁻¹ } ; inverse = (gg⁻¹=id , g⁻¹g=id) } =
    let γ = _∘*_ G₁ G₂ G₃ ψ φ
        γ⁻¹ = _∘*_ G₃ G₂ G₁ φ⁻¹ ψ⁻¹
        h = g ∘ f
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
        { from = γ
        ; to   = γ⁻¹
        ; inverse = h-inverse1 , h-inverse2
        }

≅-sym : ∀ {G₁ G₂ : Group} → G₁ ≅ G₂ → G₂ ≅ G₁
≅-sym
    record { from = φ; to = φ⁻¹; inverse = (ff⁻¹=id , f⁻¹f=id) } =
    record { from = φ⁻¹; to = φ; inverse = (f⁻¹f=id , ff⁻¹=id) }

id-hom : (G : Group) → Hom G G
id-hom G = record
    { fun = id
    ; *-preserve = \_ _ → refl
    }

id-iso : (G : Group) → G ≅ G
id-iso G = record
    { from = id-hom G
    ; to   = id-hom G
    ; inverse = refl , refl
    }

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

twice-fun : Hom Group-ℤ Group-ℤ
twice-fun = record
    { fun = twice
    ; *-preserve = Int.*-distribˡ-+ (Int.+ 2)
    }
