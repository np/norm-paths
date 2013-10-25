module paths where

open import Function.NP hiding (_∋_)
open import Type using (★)
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum renaming ([_,_] to [[_,_]])
open import Data.Zero
open import Data.One
open import Data.Two

import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≢_; _≗_; _∙_; ap; !)

infix 0 _∋_ _⊢_ _⊢ⁿ_
infixl 6 _·_ _,_
infixr 6 _⇒_

private -- for instance arguments
    0₁,,0₁ : 𝟙 × 𝟙
    0₁,,0₁ = 0₁ ,, 0₁

data Ty : ★ where
  a b c : Ty
  _⇒_ : (A B : Ty) → Ty

data Ctx : ★ where
  ε : Ctx
  _,_ : (Γ : Ctx) (A : Ty) → Ctx

data _∋_ : Ctx → Ty → ★ where
  top : ∀ {Γ} A → (Γ , A) ∋ A
  pop : ∀ {Γ A} B → Γ ∋ A → (Γ , B) ∋ A
  
data _≠_ : ∀ {Γ A B} (x : Γ ∋ A) (y : Γ ∋ B) → ★ where
  top≠pop : ∀ {Γ A B} (x : Γ ∋ B) → top A ≠ pop A x
  pop≠top : ∀ {Γ A B} (x : Γ ∋ B) → pop A x ≠ top A
  pop≠pop : ∀ {Γ A B} {x y : Γ ∋ A} → x ≠ y → pop B x ≠ pop B y

pop-inj : ∀ {Γ A B} {x y : Γ ∋ A} → pop B x ≡ pop B y → x ≡ y
pop-inj ≡.refl = ≡.refl

-- ≠ is sound
≠→≢ : ∀ {Γ A} {x y : Γ ∋ A} → x ≠ y → x ≢ y
≠→≢ (top≠pop p) ()
≠→≢ (pop≠top p) ()
≠→≢ (pop≠pop p) q = ≠→≢ p (pop-inj q)

data _⊢_ : Ctx → Ty → ★ where
  V   : ∀ {Γ A}

        → Γ ∋ A
        ---------
        → Γ ⊢ A

  _·_ : ∀ {Γ A B}

        → Γ ⊢ A ⇒ B
        → Γ ⊢ A
        ------------
        → Γ ⊢ B

  ƛ   : ∀ {Γ A B}

        → Γ , A ⊢ B
        -------------
        → Γ ⊢ A ⇒ B

infix 0 _⇉_
_⇉_ : (Γ Δ : Ctx) → ★
Γ ⇉ Δ = ∀ {B} → Γ ∋ B → Δ ∋ B

ext⇉ : ∀ {Γ Δ A} → Γ ⇉ Δ → Γ , A ⇉ Δ , A
ext⇉ f (top A)   = top A
ext⇉ f (pop B x) = pop B (f x)

data _⊢ⁿ_   : Ctx → Ty → ★
data _⊢ˢ_↝_ : Ctx → Ty → Ty → ★

data _⊢ˢ_↝_ where

  []  : ∀ {Γ A}
        → Γ ⊢ˢ A ↝ A

  _∷_ : ∀ {Γ A B C}
        → Γ ⊢ⁿ A
        → Γ ⊢ˢ B ↝ C
        -------------------
        → Γ ⊢ˢ (A ⇒ B) ↝ C

data _⊢ⁿ_ where
  V   : ∀ {Γ A B}

        → Γ ∋ A
        → Γ ⊢ˢ A ↝ B
        ------------
        → Γ ⊢ⁿ B

  ƛ   : ∀ {Γ A B}

        → Γ , A ⊢ⁿ B
        -------------
        → Γ ⊢ⁿ A ⇒ B

module ⊢ⁿ→⊢ where
  [_·_]ˢ : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ˢ A ↝ B → Γ ⊢ B
  [_]ⁿ   : ∀ {Γ A}   → Γ ⊢ⁿ A → Γ ⊢ A

  [ h · []     ]ˢ = h
  [ h · t ∷ ts ]ˢ = [ (h · [ t ]ⁿ) · ts ]ˢ

  [ V x ts ]ⁿ = [ V x · ts ]ˢ
  [ ƛ t    ]ⁿ = ƛ [ t ]ⁿ

_++ˢ_ : ∀ {Γ A B C} → Γ ⊢ˢ A ↝ B → Γ ⊢ˢ B ↝ C → Γ ⊢ˢ A ↝ C
[]       ++ˢ us = us
(t ∷ ts) ++ˢ us = t ∷ (ts ++ˢ us)

module substⁿ where
    _$ⁿ_ : ∀ {Γ Δ A}   → Γ ⇉ Δ → Γ ⊢ⁿ A → Δ ⊢ⁿ A
    _$ˢ_ : ∀ {Γ Δ A B} → Γ ⇉ Δ → Γ ⊢ˢ A ↝ B → Δ ⊢ˢ A ↝ B

    f $ⁿ (V x ts) = V (f x) (f $ˢ ts)
    f $ⁿ (ƛ M)    = ƛ (ext⇉ f $ⁿ M)

    f $ˢ []       = []
    f $ˢ (x ∷ ts) = (f $ⁿ x) ∷ (f $ˢ ts)

    infix 0 _⇶ⁿ_
    _⇶ⁿ_ : (Γ Δ : Ctx) → ★
    Γ ⇶ⁿ Δ = ∀ {B} → Γ ∋ B → Δ ⊢ⁿ B

    ext⇶ⁿ : ∀ {Γ Δ A} → Γ ⇶ⁿ Δ → Γ , A ⇶ⁿ Δ , A
    ext⇶ⁿ f (top A)   = V (top A) []
    ext⇶ⁿ f (pop B x) = (λ Γ → pop B Γ) $ⁿ f x

    subst0 : ∀ {Γ A} → Γ ⊢ⁿ A → Γ , A ⇶ⁿ Γ
    subst0 M (top A)   = M
    subst0 M (pop B x) = V x []

    {-
    infix 8 _=<<ⁿ_ _=<<ˢ_
    _=<<ⁿ_ : ∀ {Γ Δ A} → Γ ⇶ⁿ Δ → Γ ⊢ⁿ A → Δ ⊢ⁿ A
    _=<<ˢ_ : ∀ {Γ Δ A B} → Γ ⇶ⁿ Δ → Γ ⊢ˢ A ↝ B → Δ ⊢ˢ A ↝ B

    _·ⁿ_ : ∀ {Γ A B} → Γ ⊢ⁿ A → Γ ⊢ˢ A ↝ B → Γ ⊢ⁿ B
    V x ts ·ⁿ us       = V x (ts ++ˢ us)
    ƛ t    ·ⁿ []       = ƛ t
    ƛ t    ·ⁿ (u ∷ us) = (subst0 u =<<ⁿ t) ·ⁿ us

    f =<<ˢ []     = []
    f =<<ˢ t ∷ ts = (f =<<ⁿ t) ∷ (f =<<ˢ ts)

    f =<<ⁿ V x ts  = f x ·ⁿ (f =<<ˢ ts)
    f =<<ⁿ ƛ M     = ƛ (ext⇶ⁿ f =<<ⁿ M)

    appⁿ : ∀ {Γ A B} → Γ ⊢ⁿ A ⇒ B → Γ ⊢ⁿ A → Γ ⊢ⁿ B
    appⁿ t u = t ·ⁿ (u ∷ [])

    cut : ∀ {Γ A B} → Γ , A ⊢ⁿ B → Γ ⊢ⁿ A → Γ ⊢ⁿ B
    cut M N = subst0 N =<<ⁿ M
    -}

    {-
module norm where
  open substⁿ

  nrm : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ⁿ A
  nrm (V x)   = V x []
  nrm (t · u) = appⁿ (nrm t) (nrm u)
  nrm (ƛ t)   = ƛ (nrm t)
  -}

data Ty[_] : Ty → ★ where
  []    : ∀ {A} → Ty[ A ]
  [_]⇒- : ∀ {A} (pᴬ : Ty[ A ]) {B : Ty} → Ty[ A ⇒ B ]
  -⇒[_] : ∀ {B} {A : Ty} (pᴮ : Ty[ B ]) → Ty[ A ⇒ B ]

[_]⇒_ : ∀ {A} (pᴬ : Ty[ A ]) (B : Ty) → Ty[ A ⇒ B ]
[ p ]⇒ _ = [ p ]⇒- 

_⇒[_] : ∀ {B} (A : Ty) (pᴮ : Ty[ B ]) → Ty[ A ⇒ B ]
_ ⇒[ p ] = -⇒[ p ]

data Ctx[_·_] : ∀ {Γ A} → Γ ∋ A → (pᴬ : Ty[ A ]) → ★ where
  [_],- : ∀ {Γ A} {A∈Γ : Γ ∋ A} {pᴬ : Ty[ A ]} (p : Ctx[ A∈Γ · pᴬ ]) {B : Ty} → Ctx[ pop B A∈Γ · pᴬ ]
  -,[_] : ∀ {Γ A} (pᴬ : Ty[ A ]) → Ctx[ top {Γ} A · pᴬ ]

[_],_ : ∀ {Γ A} {A∈Γ : Γ ∋ A} {pᴬ : Ty[ A ]} (p : Ctx[ A∈Γ · pᴬ ]) (B : Ty) → Ctx[ pop B A∈Γ · pᴬ ]
[ p ], _ = [ p ],-

_,[_] : ∀ (Γ : Ctx) {A : Ty} (pᴬ : Ty[ A ]) → Ctx[ top {Γ} A · pᴬ ]
_ ,[ p ] = -,[ p ]

infix 0 _[⊢]_ _⊢[_] [_]⊢_
infix 3 [_]⇒_ [_],_ _,[_]

data _[⊢]_ : ∀ Γ C → ★ where
  [_]⊢- : ∀ {Γ A} {x : Γ ∋ A} {pᴬ : Ty[ A ]} (p : Ctx[ x · pᴬ ]) {C : Ty} → Γ [⊢] C
  -⊢[_] : ∀ {Γ C} (pC : Ty[ C ]) → Γ [⊢] C

[_]⊢_ : ∀ {Γ A} {x : Γ ∋ A} {pᴬ : Ty[ A ]} (p : Ctx[ x · pᴬ ]) (C : Ty) → Γ [⊢] C
[ p ]⊢ _ = [ p ]⊢-

_⊢[_] : ∀ Γ {C} (pC : Ty[ C ]) → Γ [⊢] C
_ ⊢[ p ] = -⊢[ p ]

infix 0 _[⊢]2_
data _[⊢]2_ (Γ : Ctx) (A : Ty) : ★ where
  []    : Γ [⊢]2 A
  [_]   : (p   : Γ [⊢] A) → Γ [⊢]2 A
  [_&_] : (p q : Γ [⊢] A) → Γ [⊢]2 A

module _ {Γ A} where
    swp2 : Γ [⊢]2 A → Γ [⊢]2 A
    swp2 []        = []
    swp2 [ p ]     = [ p ]
    swp2 [ p & q ] = [ q & p ]

    [_⅋_] : (p q : Γ [⊢] A) → Γ [⊢]2 A
    [ p ⅋ q ] = [ q & p ]

module _ {Γ A B} where
    p·F : Γ [⊢] B → Γ [⊢] A ⇒ B
    p·F [ pΓ ]⊢- = [ pΓ ]⊢ _ ⇒ _
    p·F -⊢[ pB ] = _ ⊢[ _ ⇒[ pB ] ]

    p·F2 : Γ [⊢]2 B → Γ [⊢]2 A ⇒ B
    p·F2 []        = []
    p·F2 [ p ]     = [ p·F p ]
    p·F2 [ p & q ] = [ p·F p & p·F q ]

    pƛ↓ : Γ , A [⊢] B → Γ [⊢] A ⇒ B
    pƛ↓ [ [ pΓ ],- ]⊢- = [ pΓ ]⊢ _ ⇒ _
    pƛ↓ [ -,[ pA ] ]⊢- = _ ⊢[ [ pA ]⇒ _ ]
    pƛ↓ -⊢[ pB ]       = _ ⊢[ _ ⇒[ pB ] ]

    Ok : Γ [⊢] A ⇒ B → ★
    Ok -⊢[ [] ]       = 𝟘
    Ok [ p ]⊢-        = 𝟙
    Ok -⊢[ [ pC ]⇒- ] = 𝟙
    Ok -⊢[ -⇒[ pC ] ] = 𝟙

    Ok-pƛ↓ : (P : Γ , A [⊢] B) → Ok (pƛ↓ P)
    Ok-pƛ↓ [ [ _ ],- ]⊢- = _
    Ok-pƛ↓ [ -,[ _ ] ]⊢- = _
    Ok-pƛ↓ -⊢[ _ ]       = _
    {-
    module Ok-pƛ↓ where
      Ok-pƛ↓' : ∀ {P} → Ok (pƛ↓ P)
      Ok-pƛ↓' {P} = Ok-pƛ↓ P
    -}

    pƛ↑ : (p : Γ [⊢] A ⇒ B) →
          (ok : Ok p) →
          Γ , A [⊢] B
    pƛ↑ [ pΓ ]⊢- _ = [ [ pΓ ], _ ]⊢ _
    pƛ↑ -⊢[ [ pA ]⇒- ] _ = [ _ ,[ pA ] ]⊢ _
    pƛ↑ -⊢[ -⇒[ pB ] ] _ = _ , _ ⊢[ pB ]
    pƛ↑ -⊢[ [] ] ()

    pƛ↑pƛ↓ : (p : Γ , A [⊢] B) → pƛ↑ (pƛ↓ p) (Ok-pƛ↓ p) ≡ p
    pƛ↑pƛ↓   [ [ _ ],- ]⊢- = ≡.refl
    pƛ↑pƛ↓   [ -,[ _ ] ]⊢- = ≡.refl
    pƛ↑pƛ↓ -⊢[ _       ]   = ≡.refl

    pƛ↓pƛ↑ : (p : Γ [⊢] A ⇒ B) {{ok-p : Ok p}} → pƛ↓ (pƛ↑ p ok-p) ≡ p
    pƛ↓pƛ↑ [ p ]⊢-        {{_}} = ≡.refl
    pƛ↓pƛ↑ -⊢[ [ pC ]⇒- ] {{_}} = ≡.refl
    pƛ↓pƛ↑ -⊢[ -⇒[ pC ] ] {{_}} = ≡.refl
    pƛ↓pƛ↑ -⊢[ [] ]       {{()}}

    Ok2 : Γ [⊢]2 A ⇒ B → ★
    Ok2 []        = 𝟙
    Ok2 [ p ]     = Ok p
    Ok2 [ p & q ] = Ok p × Ok q

    pƛ2↑ : (p : Γ [⊢]2 A ⇒ B) →
           (ok : Ok2 p) →
           Γ , A [⊢]2 B
    pƛ2↑ []        o          = []
    pƛ2↑ [ p ]     o          = [ pƛ↑ p o ]
    pƛ2↑ [ p & q ] (op ,, oq) = [ pƛ↑ p op & pƛ↑ q oq ]

data Rapp {Γ A B} : (pΓAB : Γ [⊢]2 A ⇒ B)
                    (pΓA  : Γ [⊢]2 A)
                    (pΓB  : Γ [⊢]2 B)
                  → ★ where

  arg-fun∙ : ∀ {C} {pᴬ : Ty[ A ]}
               {x  : Γ ∋ C} {pC : Ty[ C ]} {pΓ : Ctx[ x · pC ]}
             → Rapp [ Γ ⊢[ [ pᴬ ]⇒ B ] ]
                    [ [ pΓ ]⊢ A & Γ ⊢[ pᴬ ] ]
                    [ [ pΓ ]⊢ B ]

  fun-arg∙ : ∀ {pᴬ : Ty[ A ]} {pΓB : Γ [⊢] B}
             → Rapp [ Γ ⊢[ [ pᴬ ]⇒ B ] & p·F pΓB ]
                    [ Γ ⊢[ pᴬ ] ]
                    [ pΓB ]

  fun-arg : ∀ {C} {pᴬ : Ty[ A ]}
              {x  : Γ ∋ C} {pC : Ty[ C ]} {pΓ : Ctx[ x · pC ]}
              {pΓB : Γ [⊢] B}
            → Rapp [ Γ ⊢[ [ pᴬ ]⇒ B ] & p·F pΓB ]
                   [ [ pΓ ]⊢ A        & Γ ⊢[ pᴬ ] ]
                   [ [ pΓ ]⊢ B        & pΓB ]

  arg-fun : ∀ {C} {pᴬ : Ty[ A ]}
              {x  : Γ ∋ C} {pC : Ty[ C ]} {pΓ : Ctx[ x · pC ]}
              {pΓB : Γ [⊢] B}
            → Rapp [ Γ ⊢[ [ pᴬ ]⇒ B ] & p·F pΓB ]
                   [ [ pΓ ]⊢ A        & Γ ⊢[ pᴬ ] ]
                   [ [ pΓ ]⊢ B        ⅋ pΓB ]

  fun : ∀ {pΓB : Γ [⊢]2 B}
        → Rapp (p·F2 pΓB)
               []
               pΓB

  arg : ∀ {C} {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
          {D} {y : Γ ∋ D} {pD↓ : Ty[ D ]} {pΓ↓ : Ctx[ y · pD↓ ]}
        → Rapp []
               [ [ pΓ↑ ]⊢ A & [ pΓ↓ ]⊢ A ]
               [ [ pΓ↑ ]⊢ B & [ pΓ↓ ]⊢ B ]

data _≈_ {Γ A} : (p2 q2 : Γ [⊢]2 A) → ★ where
  refl : ∀ {p2 : Γ [⊢]2 A} → p2 ≈ p2
  sym  : ∀ {p q : Γ [⊢] A} → [ p & q ] ≈ [ q & p ]

data Slice : ∀ {Γ : Ctx} {A : Ty} (M : Γ ⊢ A) → Γ [⊢]2 A → ★ where
  [] : ∀ {Γ A} {M : Γ ⊢ A}
       → Slice M []

  V : ∀ {Γ A} {x : Γ ∋ A} {pᴬ : Ty[ A ]} (pΓ : Ctx[ x · pᴬ ]) {p2}
      → p2 ≈ [ _ ⊢[ pᴬ ] & [ pΓ ]⊢ _ ]
      → Slice (V x) p2

  ƛ : ∀ {Γ A B} {M : Γ , A ⊢ B} p2 {{p2ok : Ok2 p2}}
      → Slice M     (pƛ2↑ p2 p2ok)
      → Slice (ƛ M) p2

  app : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
          {pΓAB : Γ [⊢]2 A ⇒ B}
          {pΓA  : Γ [⊢]2 A}
          {pΓB  : Γ [⊢]2 B}
          (r    : Rapp pΓAB pΓA pΓB)
          (PM   : Slice M pΓAB)
          (PN   : Slice N pΓA)
        → Slice (M · N) pΓB

record Path {Γ : Ctx} {A : Ty} (M : Γ ⊢ A) (p : Γ [⊢] A) : ★ where
  constructor path
  field
    endpoint? : Γ [⊢] A → 𝟚
  Endpoint : Γ [⊢] A → ★
  Endpoint = ✓ ∘ endpoint?
  field
    slices : ∀ q → Endpoint q → Slice M [ p & q ]
  {-
    endpoints : List (Γ [⊢] A) -- XXX: not distinct
    slices    : ∀ {q} → q ∈ endpoints → Slice M [ p & q ]
  -}
  --  ⊎ Slice M [ p ]

  {-
data _≈ˢ_ {Γ A} {M : Γ ⊢ A} {p : Γ [⊢] A} : (P Q : Slice M [ p & {!!} ]) → ★ where

data _≈ᴾ_ {Γ A} {M : Γ ⊢ A} {p : Γ [⊢] A} : (P Q : Path M p) → ★ where
  c : ∀ e? e?' → e? ≗ e?' → path e? {!!} ≈ᴾ path e?' {!!}
  -}
  
module _ {Γ A} where
    ≈-sym : {p2 q2 : Γ [⊢]2 A} → p2 ≈ q2 → q2 ≈ p2
    ≈-sym refl = refl
    ≈-sym sym  = sym

    ≈-trans : {p2 q2 r2 : Γ [⊢]2 A} → p2 ≈ q2 → q2 ≈ r2 → p2 ≈ r2
    ≈-trans refl qr   = qr
    ≈-trans pr   refl = pr
    ≈-trans sym sym   = refl

    ≈-swp : (p2 : Γ [⊢]2 A) → p2 ≈ swp2 p2
    ≈-swp []        = refl
    ≈-swp [ p ]     = refl
    ≈-swp [ p & q ] = sym

swp  : ∀ {Γ : Ctx} {A : Ty} {M : Γ ⊢ A} (p2 : Γ [⊢]2 A) → Slice M p2 → Slice M (swp2 p2)
swp [] P = P
swp [ p ] P = P
swp [ p  & q  ] (V pΓ x₁) = V pΓ (≈-trans (≈-swp _) x₁)
swp [ p  & q  ] (ƛ ._ {{_ ,, _}} P) = ƛ [ q & p ] {{… ,, …}} (swp [ pƛ↑ p … & pƛ↑ q … ] P)
swp [ ._ & q  ] (app fun-arg P Q) = app arg-fun P Q
swp [ p  & ._ ] (app arg-fun P Q) = app fun-arg P Q
swp [ p  & q  ] (app fun     P Q) = app fun (swp _ P) Q
swp [ ._ & ._ ] (app arg     P Q) = app arg P (swp _ Q)

{-
ƛ↓ : ∀ {Γ A B} {M : Γ , A ⊢ B} {p₀ p₁}
     → Slice M     [ p₀     & p₁     ]
     → Slice (ƛ M) [ pƛ↓ p₀ & pƛ↓ p₁ ]
ƛ↓ {Γ} {A} {B} {M} {p₀} {p₁} P = {!ƛ [ p₀ & p₁ ] {{Ok-pƛ↓ p₀ ,, Ok-pƛ↓ p₁}}
                                   ({!≡.subst (λ p → Slice M [ p & _ ]) (≡.sym (pƛ↑pƛ↓ p₀))
                                     (≡.subst (λ p → Slice M [ _ & p ]) (≡.sym (pƛ↑pƛ↓ p₁)) P!})!}
-}

_$™_ : ∀ {Γ Δ A} → Γ ⇉ Δ → Γ ⊢ A → Δ ⊢ A
f $™ (V x)   = V (f x)
f $™ (M · N) = f $™ M · f $™ N
f $™ (ƛ M)   = ƛ (ext⇉ f $™ M)

infix 0 _⇶_
_⇶_ : (Γ Δ : Ctx) → ★
Γ ⇶ Δ = ∀ {B} → Γ ∋ B → Δ ⊢ B

ext⇶ : ∀ {Γ Δ A} → Γ ⇶ Δ → Γ , A ⇶ Δ , A
ext⇶ f (top A)   = V (top A)
ext⇶ f (pop B x) = (λ Γ → pop B Γ) $™ f x

infix 8 _=<<™_
_=<<™_ : ∀ {Γ Δ A} → Γ ⇶ Δ → Γ ⊢ A → Δ ⊢ A
f =<<™ V x     = f x
f =<<™ (M · N) = f =<<™ M · f =<<™ N
f =<<™ ƛ M     = ƛ (ext⇶ f =<<™ M)

subst0 : ∀ {Γ A} → Γ ⊢ A → Γ , A ⇶ Γ
subst0 M (top A)   = M
subst0 M (pop B x) = V x

cut : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A → Γ ⊢ B
cut M N = subst0 N =<<™ M

infix 0 _↝_
data _↝_ : ∀ {Γ A} (M N : Γ ⊢ A) → ★ where
  β     : ∀ {Γ A B} {M : Γ , A ⊢ B} {N : Γ ⊢ A} → ƛ M · N ↝ cut M N
  [_]·_ : ∀ {Γ A B} {M M′ : Γ ⊢ A ⇒ B} {N : Γ ⊢ A} → M ↝ M′ → M · N ↝ M′ · N
  _·[_] : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N N′ : Γ ⊢ A} → N ↝ N′ → M · N ↝ M · N′
  ƛ     : ∀ {Γ A B} {M M′ : Γ , A ⊢ B} → M ↝ M′ → ƛ M ↝ ƛ M′

id™ : ∀ {Γ} → Γ ⊢ a ⇒ a
id™ = ƛ (V (top a))

pid : Slice id™ [ ε ⊢[ [ [] ]⇒ a ] & ε ⊢[ _ ⇒[ [] ] ] ]
pid = ƛ _ (V _ sym) -- by refines and agsy

id™′ : ε ⊢ a ⇒ a
id™′ = ƛ (id™ · V (top a))

id′↝id : id™′ ↝ id™
id′↝id = ƛ β

V0 : ∀ {Γ A} → Γ , A ⊢ A
V0 = V (top _)

V1 : ∀ {Γ A B} → Γ , A , B ⊢ A
V1 = V (pop _ (top _))

pV0 : ∀ {Γ A p} → Slice (V0 {Γ} {A}) [ Γ , A ⊢[ p ] & [ Γ ,[ p ] ]⊢ A ] 
pV0 = V (_ ,[ _ ]) refl

pV1 : ∀ {Γ A B p} → Slice (V1 {Γ} {A} {B}) [ _ ⊢[ p ] & [ [ Γ ,[ p ] ], B ]⊢ A ]
pV1 = V ([ _ ,[ _ ] ], _) refl

-- λ f. λ x. f x x
ex₀ : ε ⊢ (a ⇒ a ⇒ b) ⇒ a ⇒ b
ex₀ = ƛ (ƛ (V (pop _ (top (a ⇒ a ⇒ b))) · V (top a) · V (top a)))

p₀ex₀ : Slice ex₀ [ ε ⊢[ (a ⇒ a ⇒ b) ⇒[ [ [] ]⇒ b ] ]
                 & ε ⊢[ [ [ [] ]⇒ a ⇒ b ]⇒ a ⇒ b ] ]
p₀ex₀ = ƛ _ (ƛ _ (app fun (app fun-arg (V _ refl) (V _ sym)) []))

p₁ex₀ : Slice ex₀ [ _ ⊢[ _ ⇒[ [ [] ]⇒ _ ] ] & _ ⊢[ [ _ ⇒[ [ [] ]⇒ _ ] ]⇒ _ ] ]
p₁ex₀ = ƛ _ (ƛ _ (app fun-arg (app fun (V _ refl) []) (V _ sym)))

{-
data Unie {Γ A} : (p₀ p₁ q₀ q₁ : Γ [⊢] A) → ★ where
  id : ∀ {p q} → Unie p q p q
  sw : ∀ {p q} → Unie p q q p

Unie : ∀ {Γ A} (p₀ p₁ q₀ q₁ : Γ [⊢] A) → ★
Unie p₀ p₁ q₀ q₁ = (p₀ ≡ q₀ → p₁ ≡ q₁) ⊎ (p₀ ≡ q₁ → p₁ ≡ q₀)
  
Unie' : ∀ {Γ A} (p₀ p₁ q₀ q₁ : Γ [⊢] A) (pf : p₀ ≡ q₀ ⊎ p₀ ≡ q₁) → ★
Unie' p₀ p₁ q₀ q₁ (inj₁ x) = p₁ ≡ q₁
Unie' p₀ p₁ q₀ q₁ (inj₂ y) = p₁ ≡ q₀

Unie : ∀ {Γ A} (p₀ p₁ q₀ q₁ : Γ [⊢] A) → ★
Unie p₀ p₁ q₀ q₁ = (pf : p₀ ≡ q₀ ⊎ p₀ ≡ q₁) → Unie' p₀ p₁ q₀ q₁ pf
-}

module _ {Γ A B} where
    p·F-inj : ∀ {p q : Γ [⊢] B} → p·F {Γ} {A} p ≡ p·F {Γ} {A} q → p ≡ q
    p·F-inj {[ .p₁ ]⊢- } {[ p₁ ]⊢- } ≡.refl = ≡.refl
    p·F-inj {[ p ]⊢- } { -⊢[ pC ]} ()
    p·F-inj { -⊢[ pC ]} {[ p ]⊢- } ()
    p·F-inj { -⊢[ .pC₁ ]} { -⊢[ pC₁ ]} ≡.refl = ≡.refl

    pƛ↑-inj : ∀ {p q : Γ [⊢] A ⇒ B} (p-ok : Ok p) (q-ok : Ok q) → pƛ↑ p p-ok ≡ pƛ↑ q q-ok → p ≡ q
    pƛ↑-inj {p} {q} p-ok q-ok pf = !(pƛ↓pƛ↑ p) ∙ ap pƛ↓ pf ∙ pƛ↓pƛ↑ q

    {-
    pƛ↓-inj : ∀ {p q : Γ , A [⊢] B} → pƛ↓ p ≡ pƛ↓ q → p ≡ q
    pƛ↓-inj {p} {q} pf = !(pƛ↑pƛ↓ p) ∙ ap (λ x → pƛ↑ x ({!!})) pf ∙ pƛ↑pƛ↓ q
    -}

uniCtx : ∀ {Γ A} (x : Γ ∋ A) {pᴬ : Ty[ A ]} → (pΓ pΓ' : Ctx[ x · pᴬ ]) → pΓ ≡ pΓ'
uniCtx (top _) -,[ ._ ] -,[ _ ] = ≡.refl
uniCtx (pop _ x) [ pΓ ],- [ pΓ' ],- rewrite uniCtx x pΓ pΓ' = ≡.refl

--[]⊢-inj : 

{-
unie : ∀ {Γ} {A : Ty} {M : Γ ⊢ A} {b p q : Γ [⊢] A} (P : Slice M [ b & p ]) (Q : Slice M [ b & q ]) → p ≡ q
unie (V pΓ refl) (V pΓ₁ refl) rewrite uniCtx _ pΓ pΓ₁ = ≡.refl
unie (V .pΓ₁ sym) (V pΓ₁ sym) = ≡.refl
unie {b = b'} {p} {q} (ƛ ._ {{_ ,, _}} P) (ƛ ._ {{_ ,, _}} Q) = pƛ↑-inj … … (unie P Q)
unie (app r P P₁) (app r·AF₁ Q Q₁) = {!!}
unie (app r P P₁) (app fun Q Q₁) = {!!}
unie (app r P P₁) (app arg Q Q₁) = {!!}
unie (app fun P) (app r Q Q₁) = {!!}
unie (app fun P) (fun Q) = p·F-inj (unie P Q)
unie (app fun P) (arg Q) = {!!}
unie (arg P) (app r Q Q₁) = {!!}
unie (arg P) (fun Q) = {!!}
unie (arg P) (arg Q) = {![]⊢-inj (unie P Q)!}
-}

{-
unie : ∀ {Γ A} {M : Γ ⊢ A} {p₀ p₁ q₀ q₁ : Γ [⊢] A} (P : Slice M [ p₀ & p₁ ]) (Q : Slice M [ q₀ & q₁ ]) → Unie p₀ p₁ q₀ q₁
-}

--P same-path Q = ∃ (π : Iso (Γ [⊢] A)). Slice M [ b & p ] ∈ P → Slice M [ b & π p ] ∈ Q

uni : ∀ {Γ A} {M : Γ ⊢ A} {b : Γ [⊢] A} (P : Path M b) (Q : Path M b) → {!P !} -- Σ (e₀ ≡ e₁) (λ π → subst (λ e → Slice M [ b & e ]) π P ≡ Q)
uni P Q = {!-c cong!}
{-
uni P Q = {!-c cong!}
{-
uni (V[Γ&A] pΓ↑) (V[Γ&A] .pΓ↑) = refl
uni (V[Γ⅋A] pΓ↓) (V[Γ⅋A] .pΓ↓) = refl
uni (ƛ[A&A] P) (ƛ[A&A] Q) = cong ƛ[A&A] (uni P Q)
uni (ƛ[A&B] P) (ƛ[A&B] Q) = cong ƛ[A&B] (uni P Q)
uni (ƛ[A⅋B] P) (ƛ[A⅋B] Q) = cong ƛ[A⅋B] (uni P Q)
uni (ƛ[B&B] P) (ƛ[B&B] Q) = cong ƛ[B&B] (uni P Q)
uni (ƛ[Γ&A] P) (ƛ[Γ&A] Q) = cong ƛ[Γ&A] (uni P Q)
uni (ƛ[Γ⅋A] P) (ƛ[Γ⅋A] Q) = cong ƛ[Γ⅋A] (uni P Q)
uni (ƛ[Γ&B] P) (ƛ[Γ&B] Q) = cong ƛ[Γ&B] (uni P Q)
uni (ƛ[Γ⅋B] P) (ƛ[Γ⅋B] Q) = cong ƛ[Γ⅋B] (uni P Q)
uni (ƛ[Γ&Γ] P) (ƛ[Γ&Γ] Q) = cong ƛ[Γ&Γ] (uni P Q)
uni (P ·[B&B]) (Q ·[B&B]) = cong _·[B&B] (uni P Q)
uni ([Γ&Γ]· P) ([Γ&Γ]· Q) = cong [Γ&Γ]·_ (uni P Q)
uni ([Γ&Γ]· P) (Q ·[Γ&Γ]) = {!uni P Q!}
uni ([Γ&Γ]· P) (Q ·A[Γ&Γ] Q₁) = {!cong!}
uni ([Γ&Γ]· P) (Q ·A[Γ⅋Γ] Q₁) = {!cong!}
uni (P ·[Γ&Γ]) ([Γ&Γ]· Q) = {!cong!}
uni (P ·[Γ&Γ]) (Q ·[Γ&Γ]) = cong _·[Γ&Γ] (uni P Q)
uni (P ·[Γ&Γ]) (Q ·A[Γ&Γ] Q₁) = {!cong!}
uni (P ·[Γ&Γ]) (Q ·A[Γ⅋Γ] Q₁) = {!cong!}
uni (P ·[Γ&B]) (Q ·[Γ&B]) = cong _·[Γ&B] (uni P Q)
uni (P ·[Γ&B]) (Q ·A[Γ&B] Q₁) = {!cong!}
uni (P ·[Γ⅋B]) (Q ·[Γ⅋B]) = cong _·[Γ⅋B] (uni P Q)
uni (P ·[Γ⅋B]) (Q ·A[Γ⅋B] Q₁) = {!!}
uni (P ·A[Γ&B] P₁) (Q ·[Γ&B]) = {!!}
uni (P ·A[Γ&B] P₁) (Q ·A[Γ&B] Q₁) = {!uni P Q!} -- {!cong₂ _·A[Γ&B]_ (uni P Q) (uni P₁ Q₁)!}
uni (P ·A[Γ⅋B] P₁) (Q ·[Γ⅋B]) = {!!}
uni (P ·A[Γ⅋B] P₁) (Q ·A[Γ⅋B] Q₁) = {!!}
uni (P ·A[Γ&Γ] P₁) ([Γ&Γ]· Q) = {!!}
uni (P ·A[Γ&Γ] P₁) (Q ·[Γ&Γ]) = {!!}
uni (P ·A[Γ&Γ] P₁) (Q ·A[Γ&Γ] Q₁) = {!!}
uni (P ·A[Γ&Γ] P₁) (Q ·A[Γ⅋Γ] Q₁) = {!!}
uni (P ·A[Γ⅋Γ] P₁) ([Γ&Γ]· Q) = {!!}
uni (P ·A[Γ⅋Γ] P₁) (Q ·[Γ&Γ]) = {!!}
uni (P ·A[Γ⅋Γ] P₁) (Q ·A[Γ&Γ] Q₁) = {!!}
uni (P ·A[Γ⅋Γ] P₁) (Q ·A[Γ⅋Γ] Q₁) = {!!}
{-
{-
record CE : ★ where
  field
    Γ     : Ctx
    A     : Ty
    M     : Γ ⊢ A
    p0 p1 : Γ [⊢] A
    P0 P1 : Slice M [ p0 & p1 ]
    P0≢P1 : P0 ≢ P1

ce : CE
ce = ?
-}

module MCE where
    Γ : Ctx
    Γ = ε , a

    A : Ty
    A = a

    M : Γ ⊢ A
    M = (ƛ (ƛ (V (pop a (pop (a ⇒ a) (top a)))))) · ƛ (V (top a)) · V (top a)

    p0 : Γ [⊢] A
    p0 = [ ε ,[ [] ] ]⊢ _

    p1 : Γ [⊢] A
    p1 = _ ⊢[ [] ]

    P0 : Slice M [ p0 & p1 ]
    P0 = {!!} ·A[Γ&B] V[Γ&A] (ε ,[ [] ])

    {-
    P1-0 : Slice (V (pop a (pop (a ⇒ a) (top {ε} a)))) [ [ [ [ _ ,[ [] ] ], _ ], _ ]⊢ a & _ ⊢[ [] ] ]
    P1-0 = V[Γ&A] ([ [ ε ,[ [] ] ], a ⇒ a ], a)

    P1-1 : Slice (ƛ (V (pop a (pop (a ⇒ a) (top {ε} a))))) [ [ [ _ ,[ [] ] ], _ ]⊢ _ & _ ⊢[ _ ⇒[ [] ] ] ]
    P1-1 = ƛ[Γ&B] P1-0

    P1-2 : Slice (ƛ (ƛ (V (pop a (pop (a ⇒ a) (top {ε} a)))))) [ [ _ ,[ [] ] ]⊢ _ & _ ⊢[ _ ⇒[ _ ⇒[ [] ] ] ] ]
    P1-2 = ƛ[Γ&B] P1-1

    P1-3 : Slice (ƛ (ƛ (V (pop a (pop (a ⇒ a) (top {ε} a))))) · ƛ (V (top a))) [ [ _ ,[ [] ] ]⊢ _ & _ ⊢[ _ ⇒[ [] ] ] ]
    P1-3 = P1-2 ·[Γ&B]
    -}

    P1 : Slice M [ p0 & p1 ]
    P1 = (ƛ[B&B] (ƛ[A&B] {!!}) ·[B&B]) ·A[Γ&B] V[Γ&A] {!!}

    P0≢P1 : P0 ≢ P1
    P0≢P1 p = {!!}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
