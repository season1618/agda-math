import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Function.Base using (_∘_; id)
open import Data.Product using (_,_; ∃-syntax; _×_; proj₁; proj₂)
import Data.Integer.Base as Int using (ℤ; +_; +0; _+_; -_; _*_)
import Data.Integer.Properties as Int using (+-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; +-comm; *-distribˡ-+)

open import Irrelevance using (irrAx; Spec; ⟨_,_⟩; cong-spec)

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

    inverse-identity : / e ≡ e
    inverse-identity = inverse-unique e (/ e) e (*-inverseL e , *-inverseR e) (*-identityL e , *-identityR e)

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
        .*-closure : ∀ (x y : S) → P x → P y → P (x * y)
        *-identity : P e
        .*-inverse : ∀ (x : S) → P x → P (/ x)

    group : Group
    group = record
        { G = T
        ; _*_ = _*'_
        ; e = e'
        ; / = /'

        ; *-assoc = \x y z → cong-spec ((x *' y) *' z) (x *' (y *' z)) (Group.*-assoc G (Spec.elem x) (Spec.elem y) (Spec.elem z))
        ; *-identityL = \x → cong-spec (e' *' x) x (Group.*-identityL G (Spec.elem x))
        ; *-identityR = \x → cong-spec (x *' e') x (Group.*-identityR G (Spec.elem x))
        ; *-inverseL = \x → cong-spec (/' x *' x) e' (Group.*-inverseL G (Spec.elem x))
        ; *-inverseR = \x → cong-spec (x *' /' x) e' (Group.*-inverseR G (Spec.elem x))
        } where
            T : Set
            T = Spec S P

            _*'_ : T → T → T
            _*'_ ⟨ x , px ⟩ ⟨ y , py ⟩ = ⟨ x * y , *-closure x y px py ⟩

            e' : T
            e' = ⟨ e , *-identity ⟩

            /' : T → T
            /' ⟨ x , px ⟩ = ⟨ / x , *-inverse x px ⟩

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

    KerSubgroup : Subgroup G₁
    KerSubgroup = record
        { P = \x → fun x ≡ e₂
        ; *-closure = *-closure'
        ; *-identity = identity-preserve
        ; *-inverse = *-inverse'
        } where
            .*-closure' : ∀ (x y : S₁) → fun x ≡ e₂ → fun y ≡ e₂ → fun (x *₁ y) ≡ e₂
            *-closure' x y fx=e fy=e = fxy=e where
                .fxy=e : fun (x *₁ y) ≡ e₂
                fxy=e =
                    begin
                        fun (x *₁ y)
                    ≡⟨ *-preserve x y ⟩
                        fun x *₂ fun y
                    ≡⟨ cong (_*₂ fun y) (irrAx fx=e) ⟩
                        e₂ *₂ fun y
                    ≡⟨ cong (e₂ *₂_) (irrAx fy=e) ⟩
                        e₂ *₂ e₂
                    ≡⟨ Group.*-identityL G₂ e₂ ⟩
                        e₂
                    ∎
            .*-inverse' : ∀ (x : S₁) → fun x ≡ e₂ → fun (/₁ x) ≡ e₂
            *-inverse' x fx=e = fx⁻¹=e where
                .fx⁻¹=e : fun (/₁ x) ≡ e₂
                fx⁻¹=e =
                    begin
                        fun (/₁ x)
                    ≡⟨ inverse-preserve x ⟩
                        /₂ (fun x)
                    ≡⟨ cong /₂ (irrAx fx=e) ⟩
                        /₂ e₂ 
                    ≡⟨ Group.inverse-identity G₂ ⟩
                        e₂
                    ∎
    Ker : Group
    Ker = record
        { G = SetKer
        ; _*_ = _*'_
        ; e = e'
        ; / = /'

        ; *-assoc = \x y z → cong-spec ((x *' y) *' z) (x *' (y *' z)) (Group.*-assoc G₁ (Spec.elem x) (Spec.elem y) (Spec.elem z))
        ; *-identityL = \x → cong-spec (e' *' x) x (Group.*-identityL G₁ (Spec.elem x))
        ; *-identityR = \x → cong-spec (x *' e') x (Group.*-identityR G₁ (Spec.elem x))
        ; *-inverseL = \x → cong-spec (/' x *' x) e' (Group.*-inverseL G₁ (Spec.elem x))
        ; *-inverseR = \x → cong-spec (x *' /' x) e' (Group.*-inverseR G₁ (Spec.elem x))
        } where
            SetKer : Set
            SetKer = Spec S₁ (\x → fun x ≡ e₂)

            _*'_ : SetKer → SetKer → SetKer
            _*'_ ⟨ x , fx=e ⟩ ⟨ y , fy=e ⟩ = ⟨ x *₁ y , fxy=e ⟩ where
                .fxy=e : fun (x *₁ y) ≡ e₂
                fxy=e =
                    begin
                        fun (x *₁ y)
                    ≡⟨ *-preserve x y ⟩
                        fun x *₂ fun y
                    ≡⟨ cong (_*₂ fun y) (irrAx fx=e) ⟩
                        e₂ *₂ fun y
                    ≡⟨ cong (e₂ *₂_) (irrAx fy=e) ⟩
                        e₂ *₂ e₂
                    ≡⟨ Group.*-identityL G₂ e₂ ⟩
                        e₂
                    ∎
            
            e' : SetKer
            e' = ⟨ e₁ , identity-preserve ⟩

            /' : SetKer → SetKer
            /' ⟨ x , fx=e ⟩ = ⟨ /₁ x , fx⁻¹=e ⟩ where
                .fx⁻¹=e : fun (/₁ x) ≡ e₂
                fx⁻¹=e =
                    begin
                        fun (/₁ x)
                    ≡⟨ inverse-preserve x ⟩
                        /₂ (fun x)
                    ≡⟨ cong /₂ (irrAx fx=e) ⟩
                        /₂ e₂ 
                    ≡⟨ Group.inverse-identity G₂ ⟩
                        e₂
                    ∎
    
    ImSubgroup : Subgroup G₂
    ImSubgroup = record
        { P = \x → ∃[ y ] fun y ≡ x
        ; *-closure = *-closure'
        ; *-identity = (e₁ , identity-preserve)
        ; *-inverse = *-inverse'
        } where
            .*-closure' : ∀ (x y : S₂) → ∃[ x' ] fun x' ≡ x → ∃[ y' ] fun y' ≡ y → ∃[ xy' ] fun xy' ≡ x *₂ y
            *-closure' x y (x' , fx'=x) (y' , fy'=y) = (x' *₁ y' , fxy'=xy) where
                .fxy'=xy : fun (x' *₁ y') ≡ x *₂ y
                fxy'=xy =
                    begin
                        fun (x' *₁ y')
                    ≡⟨ *-preserve x' y' ⟩
                        fun x' *₂ fun y'
                    ≡⟨ cong (_*₂ fun y') (irrAx fx'=x) ⟩
                        x *₂ fun y'
                    ≡⟨ cong (x *₂_) (irrAx fy'=y) ⟩
                        x *₂ y
                    ∎
            .*-inverse' : ∀ (x : S₂) → ∃[ x' ] fun x' ≡ x → ∃[ /x' ] fun /x' ≡ /₂ x
            *-inverse' x (x' , fx'=x) = (/₁ x' , fx⁻¹'=x⁻¹) where
                .fx⁻¹'=x⁻¹ : fun (/₁ x') ≡ /₂ x
                fx⁻¹'=x⁻¹ =
                    begin
                        fun (/₁ x')
                    ≡⟨ inverse-preserve x' ⟩
                        /₂ (fun x')
                    ≡⟨ cong /₂ (irrAx fx'=x) ⟩
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
