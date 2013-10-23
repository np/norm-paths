module paths where

open import Function hiding (_∋_)
open import Type using (★)
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum renaming ([_,_] to [[_,_]])
open import Data.Zero
open import Data.One

import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≢_)

infix 0 _∋_ _⊢_ _⊢ⁿ_
infixl 6 _·_ _,_
infixr 6 _⇒_

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

  [] : ∀ {Γ A}
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

  --_ : ∀ {Γ A B} → Γ ⊢ⁿ A ⇒ B → Γ ⊢ⁿ A → Γ ⊢ⁿ B

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

-- _⊆_ : Ty → Ty → ★

data Ty[_] : Ty → ★ where
  ∙     : ∀ {A} → Ty[ A ]
  [_]⇒_ : ∀ {A} (pᴬ : Ty[ A ]) (B : Ty) → Ty[ A ⇒ B ]
  _⇒[_] : ∀ {B} (A : Ty) (pᴮ : Ty[ B ]) → Ty[ A ⇒ B ]

data Ctx[_·_] : ∀ {Γ A} → Γ ∋ A → (pᴬ : Ty[ A ]) → ★ where
  [_],_ : ∀ {Γ A} {A∈Γ : Γ ∋ A} {pᴬ : Ty[ A ]} (p : Ctx[ A∈Γ · pᴬ ]) (B : Ty) → Ctx[ pop B A∈Γ · pᴬ ]
  _,[_] : ∀ (Γ : Ctx) {A : Ty} (pᴬ : Ty[ A ]) → Ctx[ top {Γ} A · pᴬ ]

infix 0 _[⊢]_ _⊢[_] [_]⊢_
infix 3 [_]⇒_ [_],_ _,[_]

data _[⊢]_ : ∀ Γ C → ★ where
  [_]⊢_ : ∀ {Γ A} {x : Γ ∋ A} {pᴬ : Ty[ A ]} (p : Ctx[ x · pᴬ ]) (C : Ty) → Γ [⊢] C
  _⊢[_] : ∀ Γ {C} (pC : Ty[ C ]) → Γ [⊢] C

infix 0 _[⊢]2_
data _[⊢]2_ (Γ : Ctx) (A : Ty) : ★ where
  [_]   : (p : Γ [⊢] A) → Γ [⊢]2 A
  [_&_] : ∀ (p q : Γ [⊢] A) → Γ [⊢]2 A

p·F : ∀ {Γ A B} → Γ [⊢] B → Γ [⊢] A ⇒ B
p·F ([ pΓ ]⊢ ._) = [ pΓ ]⊢ _ ⇒ _
p·F (._ ⊢[ pB ]) = _ ⊢[ _ ⇒[ pB ] ]

p·F2 : ∀ {Γ A B} → Γ [⊢]2 B → Γ [⊢]2 A ⇒ B
p·F2 [ p ]     = [ p·F p ]
p·F2 [ p & q ] = [ p·F p & p·F q ]

pƛ↓ : ∀ {Γ A B} →
        Γ , A [⊢] B →
        Γ [⊢] A ⇒ B
pƛ↓ ([ [ pΓ ], _ ]⊢ _) = [ pΓ ]⊢ _ ⇒ _
pƛ↓ ([ _ ,[ pA ] ]⊢ _) = _ ⊢[ [ pA ]⇒ _ ]
pƛ↓ (._ ⊢[ pB ])       = _ ⊢[ _ ⇒[ pB ] ]

Ok : ∀ {Γ A B} → Γ [⊢] A ⇒ B → ★
Ok {Γ} {A} {B} ([ p ]⊢ .(A ⇒ B)) = 𝟙
Ok {Γ} (.Γ ⊢[ ∙ ]) = 𝟘
Ok {Γ} {A} {B} (.Γ ⊢[ [ pC ]⇒ .B ]) = 𝟙
Ok {Γ} {A} (.Γ ⊢[ .A ⇒[ pC ] ]) = 𝟙

module _ {Γ A B} where
    Ok-pƛ↓ : (P : Γ , A [⊢] B) → Ok (pƛ↓ P)
    Ok-pƛ↓ ([ [ _ ], ._ ]⊢ ._)  = _
    Ok-pƛ↓ ([ ._ ,[ ._ ] ]⊢ ._) = _
    Ok-pƛ↓ (._ ⊢[ _ ])          = _
    module Ok-pƛ↓ where
      Ok-pƛ↓' : ∀ {P} → Ok (pƛ↓ P)
      Ok-pƛ↓' {P} = Ok-pƛ↓ P

pƛ↑ : ∀ {Γ A B} →
        (p : Γ [⊢] A ⇒ B) →
        {{ok : Ok p}} →
        Γ , A [⊢] B
pƛ↑ ([ pΓ ]⊢ ._) = [ [ pΓ ], _ ]⊢ _
pƛ↑ (_ ⊢[ [ pA ]⇒ ._ ]) = [ _ ,[ pA ] ]⊢ _
pƛ↑ (_ ⊢[ ._ ⇒[ pB ] ]) = _ , _ ⊢[ pB ]
pƛ↑ (_ ⊢[ ∙ ]) = λ{{x}} → 𝟘-elim x

pƛ↑pƛ↓ : ∀ {Γ A B} (p : Γ , A [⊢] B) → pƛ↑ (pƛ↓ p) {{Ok-pƛ↓ p}} ≡ p
pƛ↑pƛ↓ {Γ} {A} {B} ([ [ p ], .A ]⊢ .B) = ≡.refl
pƛ↑pƛ↓ {Γ} {.A} {B} ([_]⊢_ {.(Γ , A)} {A} {.(top A)} {pᴬ} (.Γ ,[ .pᴬ ]) .B) = ≡.refl
pƛ↑pƛ↓ {Γ} {A} (.(Γ , A) ⊢[ pC ]) = ≡.refl

{-
pƛ↑pƛ : ∀ {Γ A B} (p : Γ [⊢] A ⇒ B) → pƛ↑ (pƛ↓ p) ≡ p
pƛ↑pƛ p = ?
-}

Ok2 : ∀ {Γ A B} → Γ [⊢]2 A ⇒ B → ★
Ok2 [ p ]     = Ok p
Ok2 [ p & q ] = Ok p × Ok q

pƛ2↑ : ∀ {Γ A B} →
         (p : Γ [⊢]2 A ⇒ B) →
         {{ok : Ok2 p}} →
         Γ , A [⊢]2 B
pƛ2↑ [ p ]     {{_}}      = [ pƛ↑ p ]
pƛ2↑ [ p & q ] {{_ ,, _}} = [ pƛ↑ p & pƛ↑ q ]

{-
data R·F : ∀ {Γ A B}
          (pΓAB₀ : Γ [⊢] A ⇒ B) (pΓAB₁ : Γ [⊢] A ⇒ B)
          (pΓB₀ : Γ [⊢] B) (pΓB₁ : Γ [⊢] B)
          → ★ where

  ·[B&B] : ∀ {Γ A B}
              {pᴮ↑ : Ty[ B ]} {pᴮ↓ : Ty[ B ]}
            → R·F (Γ ⊢[ A ⇒[ pᴮ↑ ] ]) (_ ⊢[ _ ⇒[ pᴮ↓ ] ])
                  (_ ⊢[ pᴮ↑ ])        (_ ⊢[ pᴮ↓ ])

  ·[Γ&Γ] : ∀ {Γ A B C D}
           {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
           {y : Γ ∋ D} {pD↓ : Ty[ D ]} {pΓ↓ : Ctx[ y · pD↓ ]}
         → R·F ([ pΓ↑ ]⊢ A ⇒ B) ([ pΓ↓ ]⊢ A ⇒ B)
               ([ pΓ↑ ]⊢ B)     ([ pΓ↓ ]⊢ B)

  ·[Γ&B] : ∀ {Γ A B C}
              {pᴮ↓ : Ty[ B ]}
              {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
            → R·F ([ pΓ↑ ]⊢ A ⇒ B) (Γ ⊢[ A ⇒[ pᴮ↓ ] ])
                  ([ pΓ↑ ]⊢ B)     (Γ ⊢[ pᴮ↓ ])

            {-
  -- swp _·[Γ&B]
  _·[Γ⅋B] : ∀ {Γ A B C} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
              {pᴮ↓ : Ty[ B ]}
              {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
            → Path M       [ [ pΓ↑ ]⊢ A ⇒ B ⅋ Γ ⊢[ A ⇒[ pᴮ↓ ] ] ]
            → Path (M · N) [ [ pΓ↑ ]⊢ B     ⅋ Γ ⊢[ pᴮ↓ ]        ]
            -}

            {-
  _·[B⅋B] : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
              {pᴮ↑ : Ty[ B ]} {pᴮ↓ : Ty[ B ]}
            → Path M       [ _ ⊢[ _ ⇒[ pᴮ↑ ] ] ⅋ _ ⊢[ _ ⇒[ pᴮ↓ ] ] ]
            → Path (M · N) [ _ ⊢[ pᴮ↑ ]        ⅋ _ ⊢[ pᴮ↓ ] ]
            -}
-}

data R·AF : ∀ {Γ A B}
              (pΓAB : Γ [⊢]2 A ⇒ B)
              (pΓA  : Γ [⊢]2 A)
              (pΓB  : Γ [⊢]2 B)
            → ★ where

  ·A[Γ&∙] : ∀ {Γ A B C} {pᴬ : Ty[ A ]}
              {x  : Γ ∋ C} {pC : Ty[ C ]} {pΓ : Ctx[ x · pC ]}
            → R·AF [ Γ ⊢[ [ pᴬ ]⇒ B ] ]
                   [ [ pΓ ]⊢ A & Γ ⊢[ pᴬ ] ]
                   [ [ pΓ ]⊢ B ]

  ·A[∙&] : ∀ {Γ A B} {pᴬ : Ty[ A ]} {pΓB : Γ [⊢] B}
           → R·AF [ Γ ⊢[ [ pᴬ ]⇒ B ] & p·F pΓB ]
                  [ Γ ⊢[ pᴬ ] ]
                  [ pΓB ]

  ·A[Γ&] : ∀ {Γ A B C} {pᴬ : Ty[ A ]}
             {x  : Γ ∋ C} {pC : Ty[ C ]} {pΓ : Ctx[ x · pC ]}
             {pΓB : Γ [⊢] B}
           → R·AF [ Γ ⊢[ [ pᴬ ]⇒ B ] & p·F pΓB ]
                  [ [ pΓ ]⊢ A        & Γ ⊢[ pᴬ ] ]
                  [ [ pΓ ]⊢ B        & pΓB ]
{-
  ·A[Γ&Γ] : ∀ {Γ A B C D}
             {pᴬ  : Ty[ A ]}
             {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
             {y : Γ ∋ D} {pD↓ : Ty[ D ]} {pΓ↓ : Ctx[ y · pD↓ ]}
           → R·AF [ Γ ⊢[ [ pᴬ ]⇒ B ] & [ pΓ↓ ]⊢ A ⇒ B ]
                  [ [ pΓ↑ ]⊢ A       & Γ ⊢[ pᴬ ] ]
                  [ [ pΓ↑ ]⊢ B       & [ pΓ↓ ]⊢ B ]
-}

                  {- subsumed by ·A[∙&]
  ·A[∙&B] : ∀ {Γ A B C}
             {pᴬ : Ty[ A ]}
             {pᴮ : Ty[ B ]}
             {x  : Γ ∋ C} {pC : Ty[ C ]} {pΓ : Ctx[ x · pC ]}
           → R·AF [ Γ ⊢[ [ pᴬ ]⇒ B ] & Γ ⊢[ A ⇒[ pᴮ ] ] ]
                  [ Γ ⊢[ pᴬ ] ]
                  [ Γ ⊢[ pᴮ ] ]

                   subsumed by ·A[∙&]
  ·A[∙&Γ] : ∀ {Γ A B C D}
             {pᴬ  : Ty[ A ]}
             {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
             {y : Γ ∋ D} {pD↓ : Ty[ D ]} {pΓ↓ : Ctx[ y · pD↓ ]}
           → R·AF [ Γ ⊢[ [ pᴬ ]⇒ B ] & [ pΓ↓ ]⊢ A ⇒ B ]
                  [ Γ ⊢[ pᴬ ] ]
                  [ [ pΓ↓ ]⊢ B ]
                  -}

           {-
  -- swp _·A[Γ&Γ]_
  _·A[Γ⅋Γ]_ : ∀ {Γ A B C D} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
             {pᴬ  : Ty[ A ]}
             {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
             {y : Γ ∋ D} {pD↓ : Ty[ D ]} {pΓ↓ : Ctx[ y · pD↓ ]}
           → Path M       [ Γ ⊢[ [ pᴬ ]⇒ B ] ⅋ [ pΓ↓ ]⊢ A ⇒ B ]
           → Path N       [ [ pΓ↑ ]⊢ A       ⅋ Γ ⊢[ pᴬ ]  ]
           → Path (M · N) [ [ pΓ↑ ]⊢ B       ⅋ [ pΓ↓ ]⊢ B ]
           -}

data _≈_ {Γ A} : (p2 q2 : Γ [⊢]2 A) → ★ where
  refl : ∀ {p2 : Γ [⊢]2 A} → p2 ≈ p2
  sym  : ∀ {p q : Γ [⊢] A} → [ p & q ] ≈ [ q & p ]

data Path : ∀ {Γ : Ctx} {A : Ty} (M : Γ ⊢ A) → Γ [⊢]2 A → ★ where
  -- V[Γ] : ∀ {Γ A B} {x : Γ ∋ A} {y : Γ ∋ B} {pᴮ↑ : Ty[ B ⁻]} (x≠y : x ≠ y) → (pΓ↑ : Ctx[ y · pᴮ↑ ]) → Path (V x) [ [ pΓ↑ ]⊢ ⁺]

 -- V {-[Γ&A]-} : ∀ {Γ A} {x : Γ ∋ A} {pᴬ : Ty[ A ]} (pΓ : Ctx[ x · pᴬ ]) → Path (V x) [ [ pΓ ]⊢ A & _ ⊢[ pᴬ ] ]
 -- Vswp        : ∀ {Γ A} {x : Γ ∋ A} {pᴬ : Ty[ A ]} (pΓ : Ctx[ x · pᴬ ]) {p q}  → Path (V x) [ _ ⊢[ pᴬ ] & [ pΓ ]⊢ _ ]
  V : ∀ {Γ A} {x : Γ ∋ A} {pᴬ : Ty[ A ]} (pΓ : Ctx[ x · pᴬ ]) {p2} → p2 ≈ [ _ ⊢[ pᴬ ] & [ pΓ ]⊢ _ ] → Path (V x) p2

  -- swp V[Γ&A]
  {-
  V[Γ⅋A] : ∀ {Γ A} {x : Γ ∋ A} {pᴬ : Ty[ A ⁻]} (pΓ : Ctx[ x · pᴬ ]) → Path (V x) [ [ pΓ ]⊢ _ ⅋ _ ⊢[ pᴬ ]  ]
  -}

  {-
  ƛ[A] : ∀ {Γ A B} {M : Γ , A ⊢ B} {pᴬ↑ : Ty[ A ]}
         → Path M     [ [ Γ ,[ pᴬ↑ ] ]⊢ B ]
         → Path (ƛ M) [ Γ ⊢[ [ pᴬ↑ ]⇒ B ] ]
         
  ƛ[B] : ∀ {Γ A B} {M : Γ , A ⊢ B}
           {pᴮ↑ : Ty[ B ]}
         → Path M     [ Γ , A ⊢[ pᴮ↑ ]    ]
         → Path (ƛ M) [ Γ ⊢[ A ⇒[ pᴮ↑ ] ] ]

  ƛ[Γ] : ∀ {Γ A B C} {M : Γ , A ⊢ B}
           {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
         → Path M     [ [ [ pΓ↑ ], A ]⊢ B ]
         → Path (ƛ M) [ [ pΓ↑ ]⊢ A ⇒ B    ]
  -}

  {-
  ƛ : ∀ {Γ A B} {M : Γ , A ⊢ B} {p2} {{p2ok : Ok2 p2}}
      → Path M     (pƛ2↑ p2)
      → Path (ƛ M) p2
  -}

  ƛ : ∀ {Γ A B} {M : Γ , A ⊢ B} {p₀ p₁} {{p₀ok : Ok p₀}} {{p₁ok : Ok p₁}}
      → Path M     [ pƛ↑ p₀ & pƛ↑ p₁ ]
      → Path (ƛ M) [ p₀     & p₁     ]

      {-
  ƛ : ∀ {Γ A B} {M : Γ , A ⊢ B} {s p₀ p₁ p₀' p₁'}
      → Rƛ p₀ p₀'
      → Rƛ p₁ p₁'
      → Path M     ^ _ [ p₀  & p₁  ]
      → Path (ƛ M) ^ s [ p₀' & p₁' ]
      -}

      {-
  ƛ[A&A] : ∀ {Γ A B} {M : Γ , A ⊢ B} {s}
             {pᴬ↑ : Ty[ A ]} {pᴬ↓ : Ty[ A ]}
           → Path M     ^ _ [ [ Γ ,[ pᴬ↑ ] ]⊢ B & [ Γ ,[ pᴬ↓ ] ]⊢ B ]
           → Path (ƛ M) ^ s [ Γ ⊢[ [ pᴬ↑ ]⇒ B ] & Γ ⊢[ [ pᴬ↓ ]⇒ B ] ]

           {-
  -- swp ƛ[A&A]
  ƛ[A⅋A] : ∀ {Γ A B} {M : Γ , A ⊢ B}
             {pᴬ↑ : Ty[ A ⁻]} {pᴬ↓ : Ty[ A ⁺]}
           → Path M     [ [ Γ ,[ pᴬ↑ ] ]⊢ B ⅋ [ Γ ,[ pᴬ↓ ] ]⊢ B ]
           → Path (ƛ M) [ Γ ⊢[ [ pᴬ↑ ]⇒ B ] ⅋ Γ ⊢[ [ pᴬ↓ ]⇒ B ] ]
           -}

  ƛ[A&B] : ∀ {Γ A B} {M : Γ , A ⊢ B} {s}
             {pᴬ : Ty[ A ]} {pᴮ : Ty[ B ]}
           → Path M     ^ _ [ [ Γ ,[ pᴬ ] ]⊢ B & Γ , A ⊢[ pᴮ ]    ]
           → Path (ƛ M) ^ s [ Γ ⊢[ [ pᴬ ]⇒ B ] & Γ ⊢[ A ⇒[ pᴮ ] ] ]

           {-
  -- swp ƛ[A&B]
  ƛ[A⅋B] : ∀ {Γ A B} {M : Γ , A ⊢ B}
             {pᴮ : Ty[ B ⁻]} {pᴬ : Ty[ A ⁻]}
           → Path M     [ [ Γ ,[ pᴬ ] ]⊢ B ⅋ Γ , A ⊢[ pᴮ ]    ]
           → Path (ƛ M) [ Γ ⊢[ [ pᴬ ]⇒ B ] ⅋ Γ ⊢[ A ⇒[ pᴮ ] ] ]
           -}

           {-
           → Path M     [ Γ , A ⊢[ pᴮ ]    & [ Γ ,[ pᴬ ] ]⊢ B   ]
           → Path (ƛ M) [ Γ ⊢[ A ⇒[ pᴮ ] ] & Γ ⊢[ [ pᴬ ]⇒ B ] ]
           -}
 
  ƛ[B&B] : ∀ {Γ A B} {M : Γ , A ⊢ B} {s}
             {pᴮ↑ : Ty[ B ]} {pᴮ↓ : Ty[ B ]}
           → Path M     ^ _ [ Γ , A ⊢[ pᴮ↑ ]    & Γ , A ⊢[ pᴮ↓ ]    ]
           → Path (ƛ M) ^ s [ Γ ⊢[ A ⇒[ pᴮ↑ ] ] & Γ ⊢[ A ⇒[ pᴮ↓ ] ] ]

           {-
  ƛ[B⅋B] : ∀ {Γ A B} {M : Γ , A ⊢ B}
             {pᴮ↑ : Ty[ B ^ _ ]} {pᴮ↓ : Ty[ B ^ _ ]}
           → Path M     [ Γ , A ⊢[ pᴮ↑ ]    ⅋ Γ , A ⊢[ pᴮ↓ ]    ]
           → Path (ƛ M) [ Γ ⊢[ A ⇒[ pᴮ↑ ] ] ⅋ Γ ⊢[ A ⇒[ pᴮ↓ ] ] ]
           -}

  ƛ[Γ&A] : ∀ {Γ A B C} {M : Γ , A ⊢ B} {s}
             {x : Γ ∋ C} {pC↑ : Ty[ C ^ _ ]} {pΓ↑ : Ctx[ x · pC↑ ]}
             {pᴬ↓ : Ty[ A ^ _ ]}
           → Path M     ^ _ [ [ [ pΓ↑ ], A ]⊢ B & [ Γ ,[ pᴬ↓ ] ]⊢ B ]
           → Path (ƛ M) ^ s [ [ pΓ↑ ]⊢ A ⇒ B    & Γ ⊢[ [ pᴬ↓ ]⇒ B ] ]

           {-
  -- swp ƛ[Γ&A]
  ƛ[Γ⅋A] : ∀ {Γ A B C} {M : Γ , A ⊢ B}
             {x : Γ ∋ C} {pC↑ : Ty[ C ^ _ ]} {pΓ↑ : Ctx[ x · pC↑ ]}
             {pᴬ↓ : Ty[ A ^ _ ]}
           → Path M     [ [ [ pΓ↑ ], A ]⊢ B ⅋ [ Γ ,[ pᴬ↓ ] ]⊢ B ]
           → Path (ƛ M) [ [ pΓ↑ ]⊢ A ⇒ B    ⅋ Γ ⊢[ [ pᴬ↓ ]⇒ B ] ]
           -}

  ƛ[Γ&B] : ∀ {Γ A B C} {M : Γ , A ⊢ B} {s}
             {x : Γ ∋ C} {pC↑ : Ty[ C ^ _ ]} {pΓ↑ : Ctx[ x · pC↑ ]}
             {pᴮ↓ : Ty[ B ^ _ ]}
           → Path M     ^ _ [ [ [ pΓ↑ ], A ]⊢ B & Γ , A ⊢[ pᴮ↓ ]    ]
           → Path (ƛ M) ^ s [ [ pΓ↑ ]⊢ A ⇒ B    & Γ ⊢[ A ⇒[ pᴮ↓ ] ] ]

           {-
  -- swp ƛ[Γ&B]
  ƛ[Γ⅋B] : ∀ {Γ A B C} {M : Γ , A ⊢ B}
             {x : Γ ∋ C} {pC↑ : Ty[ C ^ _ ]} {pΓ↑ : Ctx[ x · pC↑ ]}
             {pᴮ↓ : Ty[ B ]}
           → Path M     [ [ [ pΓ↑ ], A ]⊢ B ⅋ Γ , A ⊢[ pᴮ↓ ]    ]
           → Path (ƛ M) [ [ pΓ↑ ]⊢ A ⇒ B    ⅋ Γ ⊢[ A ⇒[ pᴮ↓ ] ] ]
           -}

  ƛ[Γ&Γ] : ∀ {Γ A B C D} {M : Γ , A ⊢ B} {s}
             {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
             {y : Γ ∋ D} {pD↓ : Ty[ D ]} {pΓ↓ : Ctx[ y · pD↓ ]}
           → Path M     ^ _ [ [ [ pΓ↑ ], A ]⊢ B & [ [ pΓ↓ ], A ]⊢ B ]
           → Path (ƛ M) ^ s [ [ pΓ↑ ]⊢ A ⇒ B    & [ pΓ↓ ]⊢ A ⇒ B    ]

           {-
  ƛ[Γ⅋Γ] : ∀ {Γ A B C D} {M : Γ , A ⊢ B}
             {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
             {y : Γ ∋ D} {pD↓ : Ty[ D ]} {pΓ↓ : Ctx[ y · pD↓ ]}
           → Path M     [ [ [ pΓ↑ ], A ]⊢ B ⅋ [ [ pΓ↓ ], A ]⊢ B ]
           → Path (ƛ M) [ [ pΓ↑ ]⊢ A ⇒ B    ⅋ [ pΓ↓ ]⊢ A ⇒ B    ]
           -}
  -}

  ·FA : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
          {pΓAB     : Γ [⊢]2 A ⇒ B}
          {pΓA      : Γ [⊢]2 A}
          {pΓB {-pΓB'-} : Γ [⊢]2 B}
          (r·AF : R·AF pΓAB pΓA pΓB)
         -- (pR : pΓB ≈ pΓB')
          (PM : Path M pΓAB)
          (PN : Path N pΓA)
        → Path (M · N) pΓB

  ·F : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
         {pΓB : Γ [⊢]2 B}
       → Path M       (p·F2 pΓB)
       → Path (M · N) pΓB

        {-
  ·F : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
          {pΓAB₀ : Γ [⊢] A ⇒ B} {pΓAB₁ : Γ [⊢] A ⇒ B}
          {pΓB₀ : Γ [⊢] B} {pΓB₁ : Γ [⊢] B}
        → R·F pΓAB₀ pΓAB₁ pΓB₀ pΓB₁
          ⊎
          R·F pΓAB₀ pΓAB₁ pΓB₁ pΓB₀
        → Path M       [ pΓAB₀ & pΓAB₁ ]
        → Path (M · N) [ pΓB₀  & pΓB₁ ]
-}
          {-
  ·A : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
          {pΓA₀ : Γ [⊢] A} {pΓA₁ : Γ [⊢] A}
          {pΓB₀ : Γ [⊢] B} {pΓB₁ : Γ [⊢] B}
        → R·A pΓA₀ pΓA₁ pΓB₀ pΓB₁
          ⊎
          R·A pΓA₀ pΓA₁ pΓB₁ pΓB₀
        → Path N       [ pΓA₀  & pΓA₁ ]
        → Path (M · N) [ pΓB₀  & pΓB₁ ]
        -}

  ·A : ∀ {Γ A B C D} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
         {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
         {y : Γ ∋ D} {pD↓ : Ty[ D ]} {pΓ↓ : Ctx[ y · pD↓ ]}
        → Path N       [ [ pΓ↑ ]⊢ A & [ pΓ↓ ]⊢ A ]
        → Path (M · N) [ [ pΓ↑ ]⊢ B & [ pΓ↓ ]⊢ B ]

 -- swp  : ∀ {Γ : Ctx} {A : Ty} {M : Γ ⊢ A} {s} {p : Γ [⊢ _ ] A} {q : Γ [⊢ _ ] A} → Path M ^ (op s) [ q & p ] → Path M ^ s [ p & opop⊢ q ]
--  swp' : {Γ : Ctx} {A : Ty} {M : Γ ⊢ A} {p : Γ [⊢ ⁺ ] A} {q : Γ [⊢ ⁻ ] A} → Path M [ p ⅋ q ] → Path M [ q & p ]
-- agsy: swp x = {!-c!}

swp2 : ∀ {Γ A} → Γ [⊢]2 A → Γ [⊢]2 A
swp2 [ p ] = [ p ]
swp2 [ p & q ] = [ q & p ]

swp  : ∀ {Γ : Ctx} {A : Ty} {M : Γ ⊢ A} (p2 : Γ [⊢]2 A) → Path M p2 → Path M (swp2 p2)
swp [ p ] (V pΓ x₁) = V pΓ x₁
swp [ p ] (·FA r·AF P P₁) = ·FA r·AF P P₁
swp [ p ] (·F P) = ·F P
swp [ p & q ] (V pΓ x₁) = {!!}
swp [ p & q ] (ƛ {{p₀ok}} {{p₁ok}} P) = {!ƛ (swp P)!}
swp [ p & q ] (·FA r·AF P P₁) = {!!}
swp [ p & q ] (·F P) = {!!}
swp {Γ} {A} [ .([ pΓ↑ ]⊢ A) & .([ pΓ↓ ]⊢ A) ] (·A {.Γ} {A₁} {.A} {C} {D} {M} {N} {x} {pC↑} {pΓ↑} {y} {pD↓} {pΓ↓} P) = {!!}

{-
swp (V pΓ x₁) = V pΓ {!!}
swp (ƛ {{p₀ok}} {{p₁ok}} P) = ƛ (swp P)
swp (·FA r·AF P P₁) = {!!}
swp (·F P) = {!swp P!}
swp (·A P) = {!!}
-}

{-
swp (V pΓ refl) = V pΓ sym
swp (V pΓ sym) = V pΓ refl
swp (ƛ P) = ƛ (swp P)
swp (·FA x P P₁) = ·FA {{!.Γ!}} {{!.A₁!}} {{!.A!}} {{!.M!}} {{!.N!}} {{!!}} {{!!}} {{![ .p & .q ]!}} {!!} {!swp P!} {!swp P₁!}
swp (·F P) = ·F (swp P)
swp (·A P) = ·A (swp P)

{-
swp (V x pΓ) = {!V ? pΓ!}
swp (ƛ {{p₀ok}} {{p₁ok}} P) = ƛ (swp P)
swp (·FA (inj₁ x) P P₁) = ·FA (inj₂ x) P P₁
swp (·FA (inj₂ y) P P₁) = ·FA (inj₁ y) P P₁
swp (·F (inj₁ x)) = ·F (inj₁ (swp x))
swp (·F (inj₂ y)) = ·F (inj₁ y)
swp (·A (inj₁ x₁)) = ·A (inj₁ (swp x₁))
swp (·A (inj₂ y₁)) = ·A (inj₁ y₁)

ƛ↓ : ∀ {Γ A B} {M : Γ , A ⊢ B} {p₀ p₁}
     → Path M     [ p₀     & p₁     ]
     → Path (ƛ M) [ pƛ↓ p₀ & pƛ↓ p₁ ]
ƛ↓ {Γ} {A} {B} {M} {p₀} {p₁} P = ƛ {{Ok-pƛ↓ p₀}} {{Ok-pƛ↓ p₁}}
                                   (≡.subst (λ p → Path M [ p & _ ]) (≡.sym (pƛ↑pƛ↓ p₀))
                                   (≡.subst (λ p → Path M [ _ & p ]) (≡.sym (pƛ↑pƛ↓ p₁)) P))

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
  β : ∀ {Γ A B} {M : Γ , A ⊢ B} {N : Γ ⊢ A} → ƛ M · N ↝ cut M N
  [_]·_ : ∀ {Γ A B} {M M′ : Γ ⊢ A ⇒ B} {N : Γ ⊢ A} → M ↝ M′ → M · N ↝ M′ · N
  _·[_] : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N N′ : Γ ⊢ A} → N ↝ N′ → M · N ↝ M · N′
  ƛ : ∀ {Γ A B} {M M′ : Γ , A ⊢ B} → M ↝ M′ → ƛ M ↝ ƛ M′

id™ : ∀ {Γ} → Γ ⊢ a ⇒ a
id™ = ƛ (V (top a))

{-
pid : Path id™ [ ε ⊢[ [ ∙ ]⇒ a ] & ε ⊢[ _ ⇒[ ∙ ] ] ]
pid = ƛ (V (ε ,[ ∙ ])) -- by refines and agsy

id™′ : ε ⊢ a ⇒ a
id™′ = ƛ (id™ · V (top a))

id′↝id : id™′ ↝ id™
id′↝id = ƛ β

V0 : ∀ {Γ A} → Γ , A ⊢ A
V0 = V (top _)

V1 : ∀ {Γ A B} → Γ , A , B ⊢ A
V1 = V (pop _ (top _))

pV0 : ∀ {Γ A p} → Path (V0 {Γ} {A}) [ [ Γ ,[ p ] ]⊢ A & Γ , A ⊢[ p ] ] 
pV0 = V (_ ,[ _ ])

pV1 : ∀ {Γ A B p} → Path (V1 {Γ} {A} {B}) [ [ [ Γ ,[ p ] ], B ]⊢ A & _ ⊢[ p ] ]
pV1 = V ([ _ ,[ _ ] ], _)

-- λ f. λ x. f x x
ex₀ : ε ⊢ (a ⇒ a ⇒ b) ⇒ a ⇒ b
ex₀ = ƛ (ƛ (V (pop _ (top (a ⇒ a ⇒ b))) · V (top a) · V (top a)))

p₀ex₀ : Path ex₀ [ ε ⊢[ (a ⇒ a ⇒ b) ⇒[ [ ∙ ]⇒ b ] ]
                 & ε ⊢[ [ [ ∙ ]⇒ a ⇒ b ]⇒ a ⇒ b ] ]
p₀ex₀ = ƛ (ƛ (·F (inj₂ (·FA (inj₂ ·A[Γ&Γ]) (V ? ([ ε ,[ [ ∙ ]⇒ a ⇒ b ] ], a)) (V (ε , (a ⇒ a ⇒ b) ,[ ∙ ]))))))

p₁ex₀ : Path ex₀ [ _ ⊢[ _ ⇒[ [ ∙ ]⇒ _ ] ] & _ ⊢[ [ _ ⇒[ [ ∙ ]⇒ _ ] ]⇒ _ ] ]
p₁ex₀ = ƛ (ƛ (·FA (inj₁ ·A[Γ&Γ]) (·F (inj₁ (V ? ([ ε ,[ a ⇒[ [ ∙ ]⇒ b ] ] ], a)))) (V (ε , (a ⇒ a ⇒ b) ,[ ∙ ]))))

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

unie : ∀ {Γ A} {M : Γ ⊢ A} {b p q : Γ [⊢] A} (P : Path M [ b & p ]) (Q : Path M [ b & q ]) → p ≡ q
unie P Q = {!!}

{-
unie (V pΓ) (V .pΓ) = refl
unie (Vswp pΓ) (Vswp pΓ₁) = {!!}
unie (ƛ {{p₀ok}} {{p₁ok}} P) (ƛ {{p₀ok₁}} {{p₁ok₁}} Q) = {!!}
unie (·FA x P P₁) (·FA x₁ Q Q₁) = {!!}
unie (·FA x P P₁) (·F x₁ Q) = {!!}
unie (·FA x₁ P P₁) (·A Q) = {!!}
unie (·FA x₁ P P₁) (·Aswp Q) = {!!}
unie (·F x P) (·FA x₁ Q Q₁) = {!!}
unie (·F x P) (·F x₁ Q) = {!!}
unie (·F x₁ P) (·A Q) = {!!}
unie (·F x₁ P) (·Aswp Q) = {!!}
unie (·A P) (·FA x₁ Q Q₁) = {!!}
unie (·A P) (·F x₁ Q) = {!!}
unie (·A P) (·A Q) = {!!}
unie (·A P) (·Aswp Q) = {!!}
unie (·Aswp P) (·FA x₁ Q Q₁) = {!!}
unie (·Aswp P) (·F x₁ Q) = {!!}
unie (·Aswp P) (·A Q) = {!!}
unie (·Aswp P) (·Aswp Q) = {!!}

{-
unie : ∀ {Γ A} {M : Γ ⊢ A} {p₀ p₁ q₀ q₁ : Γ [⊢] A} (P : Path M [ p₀ & p₁ ]) (Q : Path M [ q₀ & q₁ ]) → Unie p₀ p₁ q₀ q₁

{-
unie (V[Γ&A] pΓ↑) (V[Γ&A] pΓ↑₁) = inj₂ (λ ())
unie (V[Γ&A] pΓ↑) (V[Γ⅋A] pΓ↓) = inj₁ (λ ())
unie (V[Γ⅋A] pΓ↓) (V[Γ&A] pΓ↑) = inj₁ (λ ())
unie (V[Γ⅋A] pΓ↓) (V[Γ⅋A] pΓ↓₁) = inj₂ (λ ())
unie (ƛ[A&A] P) (ƛ[A&A] Q) = [[ inj₁ ∘ {!cong!} , {!!} ]] (unie P Q)
unie (ƛ[A&A] P) (ƛ[A&B] Q) = inj₂ (λ ())
unie (ƛ[A&A] P) (ƛ[A⅋B] Q) = inj₁ (λ ())
unie (ƛ[A&A] P) (ƛ[B&B] Q) = inj₁ (λ ())
unie (ƛ[A&A] P) (ƛ[Γ&A] Q) = inj₁ (λ ())
unie (ƛ[A&A] P) (ƛ[Γ⅋A] Q) = inj₂ (λ ())
unie (ƛ[A&A] P) (ƛ[Γ&B] Q) = inj₁ (λ ())
unie (ƛ[A&A] P) (ƛ[Γ⅋B] Q) = inj₁ (λ ())
unie (ƛ[A&A] P) (ƛ[Γ&Γ] Q) = inj₁ (λ ())
unie (ƛ[A&B] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[A&B] P) (ƛ[A&B] Q) = inj₂ (λ ())
unie (ƛ[A&B] P) (ƛ[A⅋B] Q) = inj₁ (λ ())
unie (ƛ[A&B] P) (ƛ[B&B] Q) = inj₁ (λ ())
unie (ƛ[A&B] P) (ƛ[Γ&A] Q) = inj₁ (λ ())
unie (ƛ[A&B] P) (ƛ[Γ⅋A] Q) = inj₂ (λ ())
unie (ƛ[A&B] P) (ƛ[Γ&B] Q) = inj₁ (λ ())
unie (ƛ[A&B] P) (ƛ[Γ⅋B] Q) = inj₁ (λ ())
unie (ƛ[A&B] P) (ƛ[Γ&Γ] Q) = inj₁ (λ ())
unie (ƛ[A⅋B] P) (ƛ[A&A] Q) = inj₁ (λ ())
unie (ƛ[A⅋B] P) (ƛ[A&B] Q) = inj₁ (λ ())
unie (ƛ[A⅋B] P) (ƛ[A⅋B] Q) = inj₂ (λ ())
unie (ƛ[A⅋B] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[A⅋B] P) (ƛ[Γ&A] Q) = inj₁ (λ ())
unie (ƛ[A⅋B] P) (ƛ[Γ⅋A] Q) = inj₁ (λ ())
unie (ƛ[A⅋B] P) (ƛ[Γ&B] Q) = inj₁ (λ ())
unie (ƛ[A⅋B] P) (ƛ[Γ⅋B] Q) = inj₂ (λ ())
unie (ƛ[A⅋B] P) (ƛ[Γ&Γ] Q) = inj₁ (λ ())
unie (ƛ[B&B] P) (ƛ[A&A] Q) = inj₁ (λ ())
unie (ƛ[B&B] P) (ƛ[A&B] Q) = inj₁ (λ ())
unie (ƛ[B&B] P) (ƛ[A⅋B] Q) = inj₂ (λ ())
unie (ƛ[B&B] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[B&B] P) (ƛ[Γ&A] Q) = inj₁ (λ ())
unie (ƛ[B&B] P) (ƛ[Γ⅋A] Q) = inj₁ (λ ())
unie (ƛ[B&B] P) (ƛ[Γ&B] Q) = inj₁ (λ ())
unie (ƛ[B&B] P) (ƛ[Γ⅋B] Q) = inj₂ (λ ())
unie (ƛ[B&B] P) (ƛ[Γ&Γ] Q) = inj₁ (λ ())
unie (ƛ[Γ&A] P) (ƛ[A&A] Q) = inj₁ (λ ())
unie (ƛ[Γ&A] P) (ƛ[A&B] Q) = inj₁ (λ ())
unie (ƛ[Γ&A] P) (ƛ[A⅋B] Q) = inj₁ (λ ())
unie (ƛ[Γ&A] P) (ƛ[B&B] Q) = inj₁ (λ ())
unie (ƛ[Γ&A] P) (ƛ[Γ&A] Q) = {!!}
unie (ƛ[Γ&A] P) (ƛ[Γ⅋A] Q) = inj₁ (λ ())
unie (ƛ[Γ&A] P) (ƛ[Γ&B] Q) = inj₂ (λ ())
unie (ƛ[Γ&A] P) (ƛ[Γ⅋B] Q) = inj₁ (λ ())
unie (ƛ[Γ&A] P) (ƛ[Γ&Γ] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[A&B] Q) = inj₂ (λ ())
unie (ƛ[Γ⅋A] P) (ƛ[A⅋B] Q) = inj₁ (λ ())
unie (ƛ[Γ⅋A] P) (ƛ[B&B] Q) = inj₁ (λ ())
unie (ƛ[Γ⅋A] P) (ƛ[Γ&A] Q) = inj₁ (λ ())
unie (ƛ[Γ⅋A] P) (ƛ[Γ⅋A] Q) = inj₂ (λ ())
unie (ƛ[Γ⅋A] P) (ƛ[Γ&B] Q) = inj₁ (λ ())
unie (ƛ[Γ⅋A] P) (ƛ[Γ⅋B] Q) = inj₁ (λ ())
unie (ƛ[Γ⅋A] P) (ƛ[Γ&Γ] Q) = inj₁ (λ ())
unie (ƛ[Γ&B] P) (ƛ[A&A] Q) = inj₁ (λ ())
unie (ƛ[Γ&B] P) (ƛ[A&B] Q) = inj₁ (λ ())
unie (ƛ[Γ&B] P) (ƛ[A⅋B] Q) = inj₁ (λ ())
unie (ƛ[Γ&B] P) (ƛ[B&B] Q) = inj₁ (λ ())
unie (ƛ[Γ&B] P) (ƛ[Γ&A] Q) = inj₂ (λ ())
unie (ƛ[Γ&B] P) (ƛ[Γ⅋A] Q) = inj₁ (λ ())
unie (ƛ[Γ&B] P) (ƛ[Γ&B] Q) = inj₂ (λ ())
unie (ƛ[Γ&B] P) (ƛ[Γ⅋B] Q) = inj₁ (λ ())
unie (ƛ[Γ&B] P) (ƛ[Γ&Γ] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[A&A] Q) = inj₁ (λ ())
unie (ƛ[Γ⅋B] P) (ƛ[A&B] Q) = inj₁ (λ ())
unie (ƛ[Γ⅋B] P) (ƛ[A⅋B] Q) = inj₂ (λ ())
unie (ƛ[Γ⅋B] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[Γ&A] Q) = inj₁ (λ ())
unie (ƛ[Γ⅋B] P) (ƛ[Γ⅋A] Q) = inj₁ (λ ())
unie (ƛ[Γ⅋B] P) (ƛ[Γ&B] Q) = inj₁ (λ ())
unie (ƛ[Γ⅋B] P) (ƛ[Γ⅋B] Q) = inj₂ (λ ())
unie (ƛ[Γ⅋B] P) (ƛ[Γ&Γ] Q) = inj₁ (λ ())
unie (ƛ[Γ&Γ] P) (ƛ[A&A] Q) = inj₁ (λ ())
unie (ƛ[Γ&Γ] P) (ƛ[A&B] Q) = inj₁ (λ ())
unie (ƛ[Γ&Γ] P) (ƛ[A⅋B] Q) = inj₁ (λ ())
unie (ƛ[Γ&Γ] P) (ƛ[B&B] Q) = inj₁ (λ ())
unie (ƛ[Γ&Γ] P) (ƛ[Γ&A] Q) = inj₂ (λ ())
unie (ƛ[Γ&Γ] P) (ƛ[Γ⅋A] Q) = inj₁ (λ ())
unie (ƛ[Γ&Γ] P) (ƛ[Γ&B] Q) = inj₂ (λ ())
unie (ƛ[Γ&Γ] P) (ƛ[Γ⅋B] Q) = inj₁ (λ ())
unie (ƛ[Γ&Γ] P) (ƛ[Γ&Γ] Q) = {!!}
unie (P ·[B&B]) (Q ·[B&B]) = {!!}
unie (P ·[B&B]) ([Γ&Γ]· Q) = inj₁ (λ ())
unie (P ·[B&B]) (Q ·[Γ&Γ]) = inj₁ (λ ())
unie (P ·[B&B]) (Q ·[Γ&B]) = inj₁ (λ ())
unie (P ·[B&B]) (Q ·[Γ⅋B]) = inj₂ (λ ())
unie (P ·[B&B]) (Q ·A[Γ&B] Q₁) = inj₁ (λ ())
unie (P ·[B&B]) (Q ·A[Γ⅋B] Q₁) = inj₂ (λ ())
unie (P ·[B&B]) (Q ·A[Γ&Γ] Q₁) = inj₁ (λ ())
unie (P ·[B&B]) (Q ·A[Γ⅋Γ] Q₁) = inj₁ (λ ())
unie ([Γ&Γ]· P) (Q ·[B&B]) = inj₁ (λ ())
unie ([Γ&Γ]· P) ([Γ&Γ]· Q) = {!!}
unie ([Γ&Γ]· P) (Q ·[Γ&Γ]) = {!!}
unie ([Γ&Γ]· P) (Q ·[Γ&B]) = inj₂ (λ ())
unie ([Γ&Γ]· P) (Q ·[Γ⅋B]) = inj₁ (λ ())
unie ([Γ&Γ]· P) (Q ·A[Γ&B] Q₁) = inj₂ (λ ())
unie ([Γ&Γ]· P) (Q ·A[Γ⅋B] Q₁) = inj₁ (λ ())
unie ([Γ&Γ]· P) (Q ·A[Γ&Γ] Q₁) = {!!}
unie ([Γ&Γ]· P) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie (P ·[Γ&Γ]) (Q ·[B&B]) = inj₁ (λ ())
unie (P ·[Γ&Γ]) ([Γ&Γ]· Q) = {!!}
unie (P ·[Γ&Γ]) (Q ·[Γ&Γ]) = {!!}
unie (P ·[Γ&Γ]) (Q ·[Γ&B]) = {!!}
unie (P ·[Γ&Γ]) (Q ·[Γ⅋B]) = {!!}
unie (P ·[Γ&Γ]) (Q ·A[Γ&B] Q₁) = {!!}
unie (P ·[Γ&Γ]) (Q ·A[Γ⅋B] Q₁) = {!!}
unie (P ·[Γ&Γ]) (Q ·A[Γ&Γ] Q₁) = {!!}
unie (P ·[Γ&Γ]) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie (P ·[Γ&B]) (Q ·[B&B]) = {!!}
unie (P ·[Γ&B]) ([Γ&Γ]· Q) = {!!}
unie (P ·[Γ&B]) (Q ·[Γ&Γ]) = {!!}
unie (P ·[Γ&B]) (Q ·[Γ&B]) = {!!}
unie (P ·[Γ&B]) (Q ·[Γ⅋B]) = {!!}
unie (P ·[Γ&B]) (Q ·A[Γ&B] Q₁) = {!!}
unie (P ·[Γ&B]) (Q ·A[Γ⅋B] Q₁) = {!!}
unie (P ·[Γ&B]) (Q ·A[Γ&Γ] Q₁) = {!!}
unie (P ·[Γ&B]) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie (P ·[Γ⅋B]) (Q ·[B&B]) = {!!}
unie (P ·[Γ⅋B]) ([Γ&Γ]· Q) = {!!}
unie (P ·[Γ⅋B]) (Q ·[Γ&Γ]) = {!!}
unie (P ·[Γ⅋B]) (Q ·[Γ&B]) = {!!}
unie (P ·[Γ⅋B]) (Q ·[Γ⅋B]) = {!!}
unie (P ·[Γ⅋B]) (Q ·A[Γ&B] Q₁) = {!!}
unie (P ·[Γ⅋B]) (Q ·A[Γ⅋B] Q₁) = {!!}
unie (P ·[Γ⅋B]) (Q ·A[Γ&Γ] Q₁) = {!!}
unie (P ·[Γ⅋B]) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie (P ·A[Γ&B] P₁) (Q ·[B&B]) = {!!}
unie (P ·A[Γ&B] P₁) ([Γ&Γ]· Q) = {!!}
unie (P ·A[Γ&B] P₁) (Q ·[Γ&Γ]) = {!!}
unie (P ·A[Γ&B] P₁) (Q ·[Γ&B]) = {!!}
unie (P ·A[Γ&B] P₁) (Q ·[Γ⅋B]) = {!!}
unie (P ·A[Γ&B] P₁) (Q ·A[Γ&B] Q₁) = {!!}
unie (P ·A[Γ&B] P₁) (Q ·A[Γ⅋B] Q₁) = {!!}
unie (P ·A[Γ&B] P₁) (Q ·A[Γ&Γ] Q₁) = {!!}
unie (P ·A[Γ&B] P₁) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie (P ·A[Γ⅋B] P₁) (Q ·[B&B]) = {!!}
unie (P ·A[Γ⅋B] P₁) ([Γ&Γ]· Q) = {!!}
unie (P ·A[Γ⅋B] P₁) (Q ·[Γ&Γ]) = {!!}
unie (P ·A[Γ⅋B] P₁) (Q ·[Γ&B]) = {!!}
unie (P ·A[Γ⅋B] P₁) (Q ·[Γ⅋B]) = {!!}
unie (P ·A[Γ⅋B] P₁) (Q ·A[Γ&B] Q₁) = {!!}
unie (P ·A[Γ⅋B] P₁) (Q ·A[Γ⅋B] Q₁) = {!!}
unie (P ·A[Γ⅋B] P₁) (Q ·A[Γ&Γ] Q₁) = {!!}
unie (P ·A[Γ⅋B] P₁) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie (P ·A[Γ&Γ] P₁) (Q ·[B&B]) = {!!}
unie (P ·A[Γ&Γ] P₁) ([Γ&Γ]· Q) = {!!}
unie (P ·A[Γ&Γ] P₁) (Q ·[Γ&Γ]) = {!!}
unie (P ·A[Γ&Γ] P₁) (Q ·[Γ&B]) = {!!}
unie (P ·A[Γ&Γ] P₁) (Q ·[Γ⅋B]) = {!!}
unie (P ·A[Γ&Γ] P₁) (Q ·A[Γ&B] Q₁) = {!!}
unie (P ·A[Γ&Γ] P₁) (Q ·A[Γ⅋B] Q₁) = {!!}
unie (P ·A[Γ&Γ] P₁) (Q ·A[Γ&Γ] Q₁) = {!!}
unie (P ·A[Γ&Γ] P₁) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie (P ·A[Γ⅋Γ] P₁) (Q ·[B&B]) = {!!}
unie (P ·A[Γ⅋Γ] P₁) ([Γ&Γ]· Q) = {!!}
unie (P ·A[Γ⅋Γ] P₁) (Q ·[Γ&Γ]) = {!!}
unie (P ·A[Γ⅋Γ] P₁) (Q ·[Γ&B]) = {!!}
unie (P ·A[Γ⅋Γ] P₁) (Q ·[Γ⅋B]) = {!!}
unie (P ·A[Γ⅋Γ] P₁) (Q ·A[Γ&B] Q₁) = {!!}
unie (P ·A[Γ⅋Γ] P₁) (Q ·A[Γ⅋B] Q₁) = {!!}
unie (P ·A[Γ⅋Γ] P₁) (Q ·A[Γ&Γ] Q₁) = {!!}
unie (P ·A[Γ⅋Γ] P₁) (Q ·A[Γ⅋Γ] Q₁) = {!!}
-}

{-
unie (V[Γ&A] pΓ↑) (V[Γ&A] .pΓ↑) = refl
unie (V[Γ⅋A] pΓ↓) (V[Γ⅋A] pΓ↓₁) = {!!}
unie (ƛ[A&A] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[A&A] P) (ƛ[A&B] Q) = {!!}
unie (ƛ[A&A] P) (ƛ[Γ⅋A] Q) = {!!}
unie (ƛ[A&B] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[A&B] P) (ƛ[A&B] Q) = {!!}
unie (ƛ[A&B] P) (ƛ[Γ⅋A] Q) = {!!}
unie (ƛ[A⅋B] P) (ƛ[A⅋B] Q) = {!!}
unie (ƛ[A⅋B] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[A⅋B] P) (ƛ[Γ⅋B] Q) = {!!}
unie (ƛ[B&B] P) (ƛ[A⅋B] Q) = {!!}
unie (ƛ[B&B] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[B&B] P) (ƛ[Γ⅋B] Q) = {!!}
unie (ƛ[Γ&A] P) (ƛ[Γ&A] Q) = {!!}
unie (ƛ[Γ&A] P) (ƛ[Γ&B] Q) = {!!}
unie (ƛ[Γ&A] P) (ƛ[Γ&Γ] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[A&B] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[Γ⅋A] Q) = {!!}
unie (ƛ[Γ&B] P) (ƛ[Γ&A] Q) = {!!}
unie (ƛ[Γ&B] P) (ƛ[Γ&B] Q) = {!!}
unie (ƛ[Γ&B] P) (ƛ[Γ&Γ] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[A⅋B] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[Γ⅋B] Q) = {!!}
unie (ƛ[Γ&Γ] P) (ƛ[Γ&A] Q) = {!!}
unie (ƛ[Γ&Γ] P) (ƛ[Γ&B] Q) = {!!}
unie (ƛ[Γ&Γ] P) (ƛ[Γ&Γ] Q) = {!!}
unie (P ·[B&B]) (Q ·[B&B]) = {!!}
unie (P ·[B&B]) (Q ·[Γ⅋B]) = {!!}
unie (P ·[B&B]) (Q ·A[Γ⅋B] Q₁) = {!!}
unie ([Γ&Γ]· P) ([Γ&Γ]· Q) = {!!}
unie ([Γ&Γ]· P) (Q ·[Γ&Γ]) = {!!}
unie ([Γ&Γ]· P) (Q ·[Γ&B]) = {!!}
unie ([Γ&Γ]· P) (Q ·A[Γ&B] Q₁) = {!!}
unie ([Γ&Γ]· P) (Q ·A[Γ&Γ] Q₁) = {!!}
unie ([Γ&Γ]· P) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie (P ·[Γ&Γ]) ([Γ&Γ]· Q) = {!!}
unie (P ·[Γ&Γ]) (Q ·[Γ&Γ]) = {!!}
unie (P ·[Γ&Γ]) (Q ·[Γ&B]) = {!!}
unie (P ·[Γ&Γ]) (Q ·A[Γ&B] Q₁) = {!!}
unie (P ·[Γ&Γ]) (Q ·A[Γ&Γ] Q₁) = {!!}
unie (P ·[Γ&Γ]) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie (P ·[Γ&B]) ([Γ&Γ]· Q) = {!!}
unie (P ·[Γ&B]) (Q ·[Γ&Γ]) = {!!}
unie (P ·[Γ&B]) (Q ·[Γ&B]) = {!!}
unie (P ·[Γ&B]) (Q ·A[Γ&B] Q₁) = {!!}
unie (P ·[Γ&B]) (Q ·A[Γ&Γ] Q₁) = {!!}
unie (P ·[Γ&B]) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie (P ·[Γ⅋B]) (Q ·[B&B]) = {!!}
unie (P ·[Γ⅋B]) (Q ·[Γ⅋B]) = {!!}
unie (P ·[Γ⅋B]) (Q ·A[Γ⅋B] Q₁) = {!!}
unie (P ·A[Γ&B] P₁) ([Γ&Γ]· Q) = {!!}
unie (P ·A[Γ&B] P₁) (Q ·[Γ&Γ]) = {!!}
unie (P ·A[Γ&B] P₁) (Q ·[Γ&B]) = {!!}
unie (P ·A[Γ&B] P₁) (Q ·A[Γ&B] Q₁) = {!!}
unie (P ·A[Γ&B] P₁) (Q ·A[Γ&Γ] Q₁) = {!!}
unie (P ·A[Γ&B] P₁) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie (P ·A[Γ⅋B] P₁) (Q ·[B&B]) = {!!}
unie (P ·A[Γ⅋B] P₁) (Q ·[Γ⅋B]) = {!!}
unie (P ·A[Γ⅋B] P₁) (Q ·A[Γ⅋B] Q₁) = {!!}
unie (P ·A[Γ&Γ] P₁) ([Γ&Γ]· Q) = {!!}
unie (P ·A[Γ&Γ] P₁) (Q ·[Γ&Γ]) = {!!}
unie (P ·A[Γ&Γ] P₁) (Q ·[Γ&B]) = {!!}
unie (P ·A[Γ&Γ] P₁) (Q ·A[Γ&B] Q₁) = {!!}
unie (P ·A[Γ&Γ] P₁) (Q ·A[Γ&Γ] Q₁) = {!!}
unie (P ·A[Γ&Γ] P₁) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie (P ·A[Γ⅋Γ] P₁) ([Γ&Γ]· Q) = {!!}
unie (P ·A[Γ⅋Γ] P₁) (Q ·[Γ&Γ]) = {!!}
unie (P ·A[Γ⅋Γ] P₁) (Q ·[Γ&B]) = {!!}
unie (P ·A[Γ⅋Γ] P₁) (Q ·A[Γ&B] Q₁) = {!!}
unie (P ·A[Γ⅋Γ] P₁) (Q ·A[Γ&Γ] Q₁) = {!!}
unie (P ·A[Γ⅋Γ] P₁) (Q ·A[Γ⅋Γ] Q₁) = {!!}

{-
uni : ∀ {Γ A} {M : Γ ⊢ A} {b e₀ e₁ : Γ [⊢] A} (P : Path M [ b & e₀ ]) (Q : Path M [ b & e₁ ]) → Σ (e₀ ≡ e₁) (λ π → subst (λ e → Path M [ b & e ]) π P ≡ Q)
-- uni P Q = {!-c cong!}
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
    P0 P1 : Path M [ p0 & p1 ]
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
    p0 = [ ε ,[ ∙ ] ]⊢ _

    p1 : Γ [⊢] A
    p1 = _ ⊢[ ∙ ]

    P0 : Path M [ p0 & p1 ]
    P0 = {!!} ·A[Γ&B] V[Γ&A] (ε ,[ ∙ ])

    {-
    P1-0 : Path (V (pop a (pop (a ⇒ a) (top {ε} a)))) [ [ [ [ _ ,[ ∙ ] ], _ ], _ ]⊢ a & _ ⊢[ ∙ ] ]
    P1-0 = V[Γ&A] ([ [ ε ,[ ∙ ] ], a ⇒ a ], a)

    P1-1 : Path (ƛ (V (pop a (pop (a ⇒ a) (top {ε} a))))) [ [ [ _ ,[ ∙ ] ], _ ]⊢ _ & _ ⊢[ _ ⇒[ ∙ ] ] ]
    P1-1 = ƛ[Γ&B] P1-0

    P1-2 : Path (ƛ (ƛ (V (pop a (pop (a ⇒ a) (top {ε} a)))))) [ [ _ ,[ ∙ ] ]⊢ _ & _ ⊢[ _ ⇒[ _ ⇒[ ∙ ] ] ] ]
    P1-2 = ƛ[Γ&B] P1-1

    P1-3 : Path (ƛ (ƛ (V (pop a (pop (a ⇒ a) (top {ε} a))))) · ƛ (V (top a))) [ [ _ ,[ ∙ ] ]⊢ _ & _ ⊢[ _ ⇒[ ∙ ] ] ]
    P1-3 = P1-2 ·[Γ&B]
    -}

    P1 : Path M [ p0 & p1 ]
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
