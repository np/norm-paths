module paths where

open import Function hiding (_∋_)
open import Type using (★)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum renaming ([_,_] to [[_,_]])

infix 0 _∋_ _⊢_
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
pop-inj refl = refl

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

-- _⊆_ : Ty → Ty → ★

data Pol : ★ where
  ⁺ ⁻ : Pol

op : Pol → Pol
op ⁻ = ⁺
op ⁺ = ⁻

data Ty[_^_] : Ty → Pol → ★ where
  ∙     : ∀ {A} → Ty[ A ^ ⁺ ]
  [_]⇒_ : ∀ {A s} (pᴬ : Ty[ A ^ op s ]) (B : Ty) → Ty[ A ⇒ B ^ s ]
  _⇒[_] : ∀ {B s} (A : Ty) (pᴮ : Ty[ B ^ s ]) → Ty[ A ⇒ B ^ s ]

  {-
data Ty[_⁺] : Ty → ★
data Ty[_⁻] : Ty → ★

data Ty[_⁺] where
  ∙     : ∀ {A} → Ty[ A ⁺]
  [_]⇒_ : ∀ {A} (pᴬ : Ty[ A ⁻]) (B : Ty) → Ty[ A ⇒ B ⁺]
  _⇒[_] : ∀ {B} (A : Ty) (pᴮ : Ty[ B ⁺]) → Ty[ A ⇒ B ⁺]

data Ty[_⁻] where
  -- ∙     : ∀ {A} → Ty[ A ⁻]
  [_]⇒_ : ∀ {A} (pᴬ : Ty[ A ⁺]) (B : Ty) → Ty[ A ⇒ B ⁻]
  _⇒[_] : ∀ {B} (A : Ty) (pᴮ : Ty[ B ⁻]) → Ty[ A ⇒ B ⁻]
  -}

  {-
Ty[_^_] : Ty → Pol → ★
Ty[ A ^ ⁻ ] = Ty[ A ⁻]
Ty[ A ^ ⁺ ] = Ty[ A ⁺]
-}

Ty[_] : Ty → {pol : Pol} → ★
Ty[_] A {pol} = Ty[ A ^ pol ]

data Ctx[_·_] : ∀ {Γ A s} → Γ ∋ A → (pᴬ : Ty[ A ^ s ]) → ★ where
  [_],_ : ∀ {Γ A s} {A∈Γ : Γ ∋ A} {pᴬ : Ty[ A ^ s ]} (p : Ctx[ A∈Γ · pᴬ ]) (B : Ty) → Ctx[ pop B A∈Γ · pᴬ ]
  _,[_] : ∀ {s} (Γ : Ctx) {A : Ty} (pᴬ : Ty[ A ^ s ]) → Ctx[ top {Γ} A · pᴬ ]

infix 0 _[⊢_]_ _⊢[_] [_]⊢_ -- _[⊢]2_
infix 3 [_]⇒_ [_],_ _,[_]

{-
data Op : Pol → Pol → ★ where
  ⁺⁻ : Op ⁺ ⁻
  ⁻⁺ : Op ⁻ ⁺
  -}

data _[⊢_]_ : ∀ Γ s C → ★ where
  [_]⊢_ : ∀ {Γ s A} {x : Γ ∋ A} {pᴬ : Ty[ A ^ op s ]} (p : Ctx[ x · pᴬ ]) (C : Ty) → Γ [⊢ s ] C
  _⊢[_] : ∀ {s} Γ {C} (pC : Ty[ C ^ s ]) → Γ [⊢ s ] C

--module _ {⁺' ⁻' : Pol} {sop : Op ⁺' ⁻'} where
--module _ {⁺' : Pol} where
-- ⁻' = op ⁺'
{-
data _[⊢]2_ (Γ : Ctx) (A : Ty) : ★ where
  -- [_]   : ∀ {s} (p : Γ [⊢ s ] A) → Γ [⊢]2 A
  {-
  [_⁻]   : (p : Γ [⊢ ⁻ ] A) → Γ [⊢]2 A
  [_⁺]   : (p : Γ [⊢ ⁺ ] A) → Γ [⊢]2 A
  -}
  -- [_^_&_] : ∀ s (p↑ : Γ [⊢ op s ] A) (q↓ : Γ [⊢ s ] A) → Γ [⊢]2 A
  [_&_] : ∀ {s} (p : Γ [⊢ op s ] A) (q : Γ [⊢ s ] A) → Γ [⊢]2 A
 
  --[_&_] : (p : Γ [⊢ ⁻ ] A) (q : Γ [⊢ ⁺ ] A) → Γ [⊢]2 A

  -- [_&_] : (p↑ : Γ [⊢ ⁻ ] A) (q↓ : Γ [⊢ ⁺ ] A) → Γ [⊢]2 A
  --[_⅋_] : (p↑ : Γ [⊢ ⁺ ] A) (q↓ : Γ [⊢ ⁻ ] A) → Γ [⊢]2 A
  -}

  {-
[_⅋_] : ∀ {Γ A d} → (p : Γ [⊢ d ] A) (q : Γ [⊢ op d ] A) → Γ [⊢]2 A
[_⅋_] {Γ} {A} {⁺} p q = [ _ ^ q & p ]
[_⅋_] {Γ} {A} {⁻} p q = [ _ ^ q & p ]
-}

{-
foo : ∀ {s} → Op s (op s)
foo {⁺} = ⁺⁻
foo {⁻} = ⁻⁺
-}

opop : ∀ s → op (op s) ≡ s
opop ⁺ = refl
opop ⁻ = refl

--opopTy : ∀ {A s} → Ty[ A ^ op (op s) ] → Ty[ A ^ s ]
--opopTy = subst (λ s → Ty[ _ ^ s ]) (opop _)

opopTy : ∀ {A s} → Ty[ A ^ s ] → Ty[ A ^ op (op s) ]
opopTy = subst (λ s → Ty[ _ ^ s ]) (sym (opop _))

op² = op ∘ op

opop⊢ : ∀ {Γ A s} → Γ [⊢ op² s ] A → Γ [⊢ s ] A
opop⊢ {Γ} {A} = subst (λ s → Γ [⊢ s ] A) (opop _)

data Path_^_[_&_] : ∀ {Γ : Ctx} {A : Ty} (M : Γ ⊢ A) s → Γ [⊢ op s ] A → Γ [⊢ s ] A → ★ where
  -- V[Γ] : ∀ {Γ A B} {x : Γ ∋ A} {y : Γ ∋ B} {pᴮ↑ : Ty[ B ⁻]} (x≠y : x ≠ y) → (pΓ↑ : Ctx[ y · pᴮ↑ ]) → Path (V x) [ [ pΓ↑ ]⊢ ⁺]

  V[Γ&A] : ∀ {Γ A} {x : Γ ∋ A} {s} {pᴬ : Ty[ A ^ s ]} (pΓ : Ctx[ x · opopTy pᴬ ]) → Path (V x) ^ s [ [ pΓ ]⊢ A & _ ⊢[ pᴬ ] ]

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

  _·[B&B] : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A} {s}
              {pᴮ↑ : Ty[ B ]} {pᴮ↓ : Ty[ B ]}
            → Path M       ^ _ [ _ ⊢[ _ ⇒[ pᴮ↑ ] ] & _ ⊢[ _ ⇒[ pᴮ↓ ] ] ]
            → Path (M · N) ^ s [ _ ⊢[ pᴮ↑ ]        & _ ⊢[ pᴮ↓ ] ]

            {-
  _·[B⅋B] : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
              {pᴮ↑ : Ty[ B ]} {pᴮ↓ : Ty[ B ]}
            → Path M       [ _ ⊢[ _ ⇒[ pᴮ↑ ] ] ⅋ _ ⊢[ _ ⇒[ pᴮ↓ ] ] ]
            → Path (M · N) [ _ ⊢[ pᴮ↑ ]        ⅋ _ ⊢[ pᴮ↓ ] ]
            -}

  [Γ&Γ]·_ : ∀ {Γ A B C D} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A} {s}
           {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
           {y : Γ ∋ D} {pD↓ : Ty[ D ]} {pΓ↓ : Ctx[ y · pD↓ ]}
         → Path N       ^ _ [ [ pΓ↑ ]⊢ A & [ pΓ↓ ]⊢ A ]
         → Path (M · N) ^ s [ [ pΓ↑ ]⊢ B & [ pΓ↓ ]⊢ B ]

  _·[Γ&Γ] : ∀ {Γ A B C D} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A} {s}
           {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
           {y : Γ ∋ D} {pD↓ : Ty[ D ]} {pΓ↓ : Ctx[ y · pD↓ ]}
         → Path M       ^ _ [ [ pΓ↑ ]⊢ A ⇒ B & [ pΓ↓ ]⊢ A ⇒ B ]
         → Path (M · N) ^ s [ [ pΓ↑ ]⊢ B     & [ pΓ↓ ]⊢ B ]

  _·[Γ&B] : ∀ {Γ A B C} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A} {s}
              {pᴮ↓ : Ty[ B ]}
              {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
            → Path M       ^ _ [ [ pΓ↑ ]⊢ A ⇒ B & Γ ⊢[ A ⇒[ pᴮ↓ ] ] ]
            → Path (M · N) ^ s [ [ pΓ↑ ]⊢ B     & Γ ⊢[ pᴮ↓ ]        ]

            {-
  -- swp _·[Γ&B]
  _·[Γ⅋B] : ∀ {Γ A B C} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
              {pᴮ↓ : Ty[ B ]}
              {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
            → Path M       [ [ pΓ↑ ]⊢ A ⇒ B ⅋ Γ ⊢[ A ⇒[ pᴮ↓ ] ] ]
            → Path (M · N) [ [ pΓ↑ ]⊢ B     ⅋ Γ ⊢[ pᴮ↓ ]        ]
            -}

  _·A[Γ&B]_ : ∀ {Γ A B C} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A} {s}
             {pᴬ : Ty[ A ^ s ]}
             {pᴮ : Ty[ B ^ s ]}
             {x  : Γ ∋ C} {pC : Ty[ C ^ op (op s) ]} {pΓ : Ctx[ x · pC ]}
           → Path M       ^ _ [ Γ ⊢[ [ opopTy pᴬ ]⇒ B ] & Γ ⊢[ A ⇒[ pᴮ ] ] ]
           → Path N       ^ _ [ [ pΓ ]⊢ A               & Γ ⊢[ pᴬ ]  ]
           → Path (M · N) ^ s [ [ pΓ ]⊢ B               & Γ ⊢[ pᴮ ] ]

           {-
  -- swp _·A[Γ&B]_
  _·A[Γ⅋B]_ : ∀ {Γ A B C} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
             {pᴬ  : Ty[ A ]}
             {pᴮ↓ : Ty[ B ]}
             {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
           → Path M       [ Γ ⊢[ [ pᴬ ]⇒ B ] ⅋ Γ ⊢[ A ⇒[ pᴮ↓ ] ] ]
           → Path N       [ [ pΓ↑ ]⊢ A       ⅋ Γ ⊢[ pᴬ ]  ]
           → Path (M · N) [ [ pΓ↑ ]⊢ B       ⅋ Γ ⊢[ pᴮ↓ ] ]
           -}

  _·A[Γ&Γ]_ : ∀ {Γ A B C D} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A} {s}
             {pᴬ  : Ty[ A ]}
             {x : Γ ∋ C} {pC↑ : Ty[ C ]} {pΓ↑ : Ctx[ x · pC↑ ]}
             {y : Γ ∋ D} {pD↓ : Ty[ D ]} {pΓ↓ : Ctx[ y · pD↓ ]}
           → Path M       ^ _ [ Γ ⊢[ [ opopTy pᴬ ]⇒ B ] & [ pΓ↓ ]⊢ A ⇒ B ]
           → Path N       ^ _ [ [ pΓ↑ ]⊢ A       & Γ ⊢[ pᴬ ]  ]
           → Path (M · N) ^ s [ [ pΓ↑ ]⊢ B       & [ pΓ↓ ]⊢ B ]

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

  swp  : ∀ {Γ : Ctx} {A : Ty} {M : Γ ⊢ A} {s} {p : Γ [⊢ _ ] A} {q : Γ [⊢ _ ] A} → Path M ^ (op s) [ q & p ] → Path M ^ s [ p & opop⊢ q ]
--  swp' : {Γ : Ctx} {A : Ty} {M : Γ ⊢ A} {p : Γ [⊢ ⁺ ] A} {q : Γ [⊢ ⁻ ] A} → Path M [ p ⅋ q ] → Path M [ q & p ]
-- agsy: swp x = {!-c!}

_⇉_ : (Γ Δ : Ctx) → ★
Γ ⇉ Δ = ∀ {B} → Γ ∋ B → Δ ∋ B

ext⇉ : ∀ {Γ Δ A} → Γ ⇉ Δ → Γ , A ⇉ Δ , A
ext⇉ f (top A)   = top A
ext⇉ f (pop B x) = pop B (f x)

_$™_ : ∀ {Γ Δ A} → Γ ⇉ Δ → Γ ⊢ A → Δ ⊢ A
f $™ (V x)   = V (f x)
f $™ (M · N) = f $™ M · f $™ N
f $™ (ƛ M)   = ƛ (ext⇉ f $™ M)

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

infix 0 _↝_ _⇉_ _⇶_
data _↝_ : ∀ {Γ A} (M N : Γ ⊢ A) → ★ where
  β : ∀ {Γ A B} {M : Γ , A ⊢ B} {N : Γ ⊢ A} → ƛ M · N ↝ cut M N
  [_]·_ : ∀ {Γ A B} {M M′ : Γ ⊢ A ⇒ B} {N : Γ ⊢ A} → M ↝ M′ → M · N ↝ M′ · N
  _·[_] : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N N′ : Γ ⊢ A} → N ↝ N′ → M · N ↝ M · N′
  ƛ : ∀ {Γ A B} {M M′ : Γ , A ⊢ B} → M ↝ M′ → ƛ M ↝ ƛ M′

id™ : ∀ {Γ} → Γ ⊢ a ⇒ a
id™ = ƛ (V (top a))

pid : Path id™ ^ _ [ ε ⊢[ [ ∙ ]⇒ a ] & ε ⊢[ _ ⇒[ ∙ ] ] ]
pid = ƛ[A&B] (V[Γ&A] (ε ,[ ∙ ])) -- by agsy

id™′ : ε ⊢ a ⇒ a
id™′ = ƛ (id™ · V (top a))

id′↝id : id™′ ↝ id™
id′↝id = ƛ β

V0 : ∀ {Γ A} → Γ , A ⊢ A
V0 = V (top _)

V1 : ∀ {Γ A B} → Γ , A , B ⊢ A
V1 = V (pop _ (top _))

{-
pV0 : ∀ {s Γ A p} → Path (V0 {Γ} {A}) ^ {!s!} [ [ Γ ,[ p ] ]⊢ A & Γ , A ⊢[ p ] ] 
pV0 = V[Γ&A] (_ ,[ _ ])

pV1 : ∀ {s Γ A B p} → Path (V1 {Γ} {A} {B}) ^ {!s!} [ [ [ Γ ,[ p ] ], B ]⊢ A & _ ⊢[ p ] ]
pV1 = V[Γ&A] ([ _ ,[ _ ] ], _)
-}

-- λ f. λ x. f x x
ex₀ : ε ⊢ (a ⇒ a ⇒ b) ⇒ a ⇒ b
ex₀ = ƛ (ƛ (V (pop _ (top (a ⇒ a ⇒ b))) · V (top a) · V (top a)))

p₀ex₀ : Path ex₀ ^ _ [ ε ⊢[ (a ⇒ a ⇒ b) ⇒[ [ ∙ ]⇒ b ] ]
                 & ε ⊢[ [ [ ∙ ]⇒ a ⇒ b ]⇒ a ⇒ b ] ]
p₀ex₀ = swp (ƛ[A&B] (ƛ[Γ&A] (swp ((swp (V[Γ&A] _) ·A[Γ&Γ] V[Γ&A] _) ·[Γ&Γ]))))

p₁ex₀ : Path ex₀ ^ _ [ _ ⊢[ _ ⇒[ [ ∙ ]⇒ _ ] ] & _ ⊢[ [ _ ⇒[ [ ∙ ]⇒ _ ] ]⇒ _ ] ]
p₁ex₀ = swp (ƛ[A&B] (ƛ[Γ&A] (swp (swp (V[Γ&A] _ ·[Γ&B]) ·A[Γ&Γ] V[Γ&A] _))))

{-

{-
data Unie {Γ A} : (p₀ p₁ q₀ q₁ : Γ [⊢] A) → ★ where
  id : ∀ {p q} → Unie p q p q
  sw : ∀ {p q} → Unie p q q p

Unie : ∀ {Γ A} (p₀ p₁ q₀ q₁ : Γ [⊢] A) → ★
Unie p₀ p₁ q₀ q₁ = (p₀ ≡ q₀ → p₁ ≡ q₁) ⊎ (p₀ ≡ q₁ → p₁ ≡ q₀)
  -}
  
Unie' : ∀ {Γ A} (p₀ p₁ q₀ q₁ : Γ [⊢] A) (pf : p₀ ≡ q₀ ⊎ p₀ ≡ q₁) → ★
Unie' p₀ p₁ q₀ q₁ (inj₁ x) = p₁ ≡ q₁
Unie' p₀ p₁ q₀ q₁ (inj₂ y) = p₁ ≡ q₀

Unie : ∀ {Γ A} (p₀ p₁ q₀ q₁ : Γ [⊢] A) → ★
Unie p₀ p₁ q₀ q₁ = (pf : p₀ ≡ q₀ ⊎ p₀ ≡ q₁) → Unie' p₀ p₁ q₀ q₁ pf
-}

unie : ∀ {s Γ A} {M : Γ ⊢ A} {b : Γ [⊢ _ ] A} {p q : Γ [⊢ _ ] A} (P : Path M ^ s [ b & p ]) (Q : Path M ^ s [ b & q ]) → p ≡ q
unie {⁺} (V[Γ&A] pΓ) (V[Γ&A] .pΓ) = refl
unie {⁺} (V[Γ&A] pΓ) (swp Q) = {!!}
unie {⁺} (ƛ[A&A] P) (ƛ[A&A] Q) = {!unie P Q!}
unie {⁺} (ƛ[A&A] P) (ƛ[A&B] Q) = {!!}
unie {⁺} (ƛ[A&A] P) (swp Q) = {!!}
unie {⁺} (ƛ[A&B] P) (ƛ[A&A] Q) = {!!}
unie {⁺} (ƛ[A&B] P) (ƛ[A&B] Q) = {!!}
unie {⁺} (ƛ[A&B] P) (swp Q) = {!!}
unie {⁺} (ƛ[B&B] P) (ƛ[B&B] Q) = {!!}
unie {⁺} (ƛ[B&B] P) (swp Q) = {!!}
unie {⁺} (ƛ[Γ&A] P) (ƛ[Γ&A] Q) = {!!}
unie {⁺} (ƛ[Γ&A] P) (ƛ[Γ&B] Q) = {!!}
unie {⁺} (ƛ[Γ&A] P) (ƛ[Γ&Γ] Q) = {!!}
unie {⁺} (ƛ[Γ&A] P) (swp Q) = {!!}
unie {⁺} (ƛ[Γ&B] P) (ƛ[Γ&A] Q) = {!!}
unie {⁺} (ƛ[Γ&B] P) (ƛ[Γ&B] Q) = {!!}
unie {⁺} (ƛ[Γ&B] P) (ƛ[Γ&Γ] Q) = {!!}
unie {⁺} (ƛ[Γ&B] P) (swp Q) = {!!}
unie {⁺} (ƛ[Γ&Γ] P) (ƛ[Γ&A] Q) = {!!}
unie {⁺} (ƛ[Γ&Γ] P) (ƛ[Γ&B] Q) = {!!}
unie {⁺} (ƛ[Γ&Γ] P) (ƛ[Γ&Γ] Q) = {!!}
unie {⁺} (ƛ[Γ&Γ] P) (swp Q) = {!!}
unie {⁺} (P ·[B&B]) (Q ·[B&B]) = {!!}
unie {⁺} (P ·[B&B]) (swp Q) = {!!}
unie {⁺} ([Γ&Γ]· P) ([Γ&Γ]· Q) = {!!}
unie {⁺} ([Γ&Γ]· P) (Q ·[Γ&Γ]) = {!!}
unie {⁺} ([Γ&Γ]· P) (Q ·[Γ&B]) = {!!}
unie {⁺} ([Γ&Γ]· P) (Q ·A[Γ&B] Q₁) = {!!}
unie {⁺} ([Γ&Γ]· P) (Q ·A[Γ&Γ] Q₁) = {!!}
unie {⁺} ([Γ&Γ]· P) (swp Q) = {!!}
unie {⁺} (P ·[Γ&Γ]) ([Γ&Γ]· Q) = {!!}
unie {⁺} (P ·[Γ&Γ]) (Q ·[Γ&Γ]) = {!!}
unie {⁺} (P ·[Γ&Γ]) (Q ·[Γ&B]) = {!!}
unie {⁺} (P ·[Γ&Γ]) (Q ·A[Γ&B] Q₁) = {!!}
unie {⁺} (P ·[Γ&Γ]) (Q ·A[Γ&Γ] Q₁) = {!!}
unie {⁺} (P ·[Γ&Γ]) (swp Q) = {!!}
unie {⁺} (P ·[Γ&B]) ([Γ&Γ]· Q) = {!!}
unie {⁺} (P ·[Γ&B]) (Q ·[Γ&Γ]) = {!!}
unie {⁺} (P ·[Γ&B]) (Q ·[Γ&B]) = {!!}
unie {⁺} (P ·[Γ&B]) (Q ·A[Γ&B] Q₁) = {!!}
unie {⁺} (P ·[Γ&B]) (Q ·A[Γ&Γ] Q₁) = {!!}
unie {⁺} (P ·[Γ&B]) (swp Q) = {!!}
unie {⁺} (P ·A[Γ&B] P₁) ([Γ&Γ]· Q) = {!!}
unie {⁺} (P ·A[Γ&B] P₁) (Q ·[Γ&Γ]) = {!!}
unie {⁺} (P ·A[Γ&B] P₁) (Q ·[Γ&B]) = {!!}
unie {⁺} (P ·A[Γ&B] P₁) (Q ·A[Γ&B] Q₁) = {!!}
unie {⁺} (P ·A[Γ&B] P₁) (Q ·A[Γ&Γ] Q₁) = {!!}
unie {⁺} (P ·A[Γ&B] P₁) (swp Q) = {!!}
unie {⁺} (P ·A[Γ&Γ] P₁) ([Γ&Γ]· Q) = {!!}
unie {⁺} (P ·A[Γ&Γ] P₁) (Q ·[Γ&Γ]) = {!!}
unie {⁺} (P ·A[Γ&Γ] P₁) (Q ·[Γ&B]) = {!!}
unie {⁺} (P ·A[Γ&Γ] P₁) (Q ·A[Γ&B] Q₁) = {!!}
unie {⁺} (P ·A[Γ&Γ] P₁) (Q ·A[Γ&Γ] Q₁) = {!!}
unie {⁺} (P ·A[Γ&Γ] P₁) (swp Q) = {!!}
unie {⁺} (swp P) (V[Γ&A] pΓ) = {!!}
unie {⁺} (swp P) (ƛ[A&A] Q) = {!!}
unie {⁺} (swp P) (ƛ[A&B] Q) = {!!}
unie {⁺} (swp P) (ƛ[B&B] Q) = {!!}
unie {⁺} (swp P) (ƛ[Γ&A] Q) = {!!}
unie {⁺} (swp P) (ƛ[Γ&B] Q) = {!!}
unie {⁺} (swp P) (ƛ[Γ&Γ] Q) = {!!}
unie {⁺} (swp P) (Q ·[B&B]) = {!!}
unie {⁺} (swp P) ([Γ&Γ]· Q) = {!!}
unie {⁺} (swp P) (Q ·[Γ&Γ]) = {!!}
unie {⁺} (swp P) (Q ·[Γ&B]) = {!!}
unie {⁺} (swp P) (Q ·A[Γ&B] Q₁) = {!!}
unie {⁺} (swp P) (Q ·A[Γ&Γ] Q₁) = {!!}
unie {⁺} (swp P) (swp Q) = {!!}
unie {⁻} (V[Γ&A] pΓ) (V[Γ&A] .pΓ) = {!!}
unie {⁻} (V[Γ&A] pΓ) (swp Q) = {!!}
unie {⁻} (ƛ[A&A] P) (ƛ[A&A] Q) = {!!}
unie {⁻} (ƛ[A&A] P) (ƛ[A&B] Q) = {!!}
unie {⁻} (ƛ[A&A] P) (swp Q) = {!!}
unie {⁻} (ƛ[A&B] P) (ƛ[A&A] Q) = {!!}
unie {⁻} (ƛ[A&B] P) (ƛ[A&B] Q) = {!!}
unie {⁻} (ƛ[A&B] P) (swp Q) = {!!}
unie {⁻} (ƛ[B&B] P) (ƛ[B&B] Q) = {!!}
unie {⁻} (ƛ[B&B] P) (swp Q) = {!!}
unie {⁻} (ƛ[Γ&A] P) (ƛ[Γ&A] Q) = {!!}
unie {⁻} (ƛ[Γ&A] P) (ƛ[Γ&B] Q) = {!!}
unie {⁻} (ƛ[Γ&A] P) (ƛ[Γ&Γ] Q) = {!!}
unie {⁻} (ƛ[Γ&A] P) (swp Q) = {!!}
unie {⁻} (ƛ[Γ&B] P) (ƛ[Γ&A] Q) = {!!}
unie {⁻} (ƛ[Γ&B] P) (ƛ[Γ&B] Q) = {!!}
unie {⁻} (ƛ[Γ&B] P) (ƛ[Γ&Γ] Q) = {!!}
unie {⁻} (ƛ[Γ&B] P) (swp Q) = {!!}
unie {⁻} (ƛ[Γ&Γ] P) (ƛ[Γ&A] Q) = {!!}
unie {⁻} (ƛ[Γ&Γ] P) (ƛ[Γ&B] Q) = {!!}
unie {⁻} (ƛ[Γ&Γ] P) (ƛ[Γ&Γ] Q) = {!!}
unie {⁻} (ƛ[Γ&Γ] P) (swp Q) = {!!}
unie {⁻} (P ·[B&B]) (Q ·[B&B]) = {!!}
unie {⁻} (P ·[B&B]) (swp Q) = {!!}
unie {⁻} ([Γ&Γ]· P) ([Γ&Γ]· Q) = {!!}
unie {⁻} ([Γ&Γ]· P) (Q ·[Γ&Γ]) = {!!}
unie {⁻} ([Γ&Γ]· P) (Q ·[Γ&B]) = {!!}
unie {⁻} ([Γ&Γ]· P) (Q ·A[Γ&B] Q₁) = {!!}
unie {⁻} ([Γ&Γ]· P) (Q ·A[Γ&Γ] Q₁) = {!!}
unie {⁻} ([Γ&Γ]· P) (swp Q) = {!!}
unie {⁻} (P ·[Γ&Γ]) ([Γ&Γ]· Q) = {!!}
unie {⁻} (P ·[Γ&Γ]) (Q ·[Γ&Γ]) = {!!}
unie {⁻} (P ·[Γ&Γ]) (Q ·[Γ&B]) = {!!}
unie {⁻} (P ·[Γ&Γ]) (Q ·A[Γ&B] Q₁) = {!!}
unie {⁻} (P ·[Γ&Γ]) (Q ·A[Γ&Γ] Q₁) = {!!}
unie {⁻} (P ·[Γ&Γ]) (swp Q) = {!!}
unie {⁻} (P ·[Γ&B]) ([Γ&Γ]· Q) = {!!}
unie {⁻} (P ·[Γ&B]) (Q ·[Γ&Γ]) = {!!}
unie {⁻} (P ·[Γ&B]) (Q ·[Γ&B]) = {!!}
unie {⁻} (P ·[Γ&B]) (Q ·A[Γ&B] Q₁) = {!!}
unie {⁻} (P ·[Γ&B]) (Q ·A[Γ&Γ] Q₁) = {!!}
unie {⁻} (P ·[Γ&B]) (swp Q) = {!!}
unie {⁻} (P ·A[Γ&B] P₁) ([Γ&Γ]· Q) = {!!}
unie {⁻} (P ·A[Γ&B] P₁) (Q ·[Γ&Γ]) = {!!}
unie {⁻} (P ·A[Γ&B] P₁) (Q ·[Γ&B]) = {!!}
unie {⁻} (P ·A[Γ&B] P₁) (Q ·A[Γ&B] Q₁) = {!!}
unie {⁻} (P ·A[Γ&B] P₁) (Q ·A[Γ&Γ] Q₁) = {!!}
unie {⁻} (P ·A[Γ&B] P₁) (swp Q) = {!!}
unie {⁻} (P ·A[Γ&Γ] P₁) ([Γ&Γ]· Q) = {!!}
unie {⁻} (P ·A[Γ&Γ] P₁) (Q ·[Γ&Γ]) = {!!}
unie {⁻} (P ·A[Γ&Γ] P₁) (Q ·[Γ&B]) = {!!}
unie {⁻} (P ·A[Γ&Γ] P₁) (Q ·A[Γ&B] Q₁) = {!!}
unie {⁻} (P ·A[Γ&Γ] P₁) (Q ·A[Γ&Γ] Q₁) = {!!}
unie {⁻} (P ·A[Γ&Γ] P₁) (swp Q) = {!!}
unie {⁻} (swp P) (V[Γ&A] pΓ) = {!!}
unie {⁻} (swp P) (ƛ[A&A] Q) = {!!}
unie {⁻} (swp P) (ƛ[A&B] Q) = {!!}
unie {⁻} (swp P) (ƛ[B&B] Q) = {!!}
unie {⁻} (swp P) (ƛ[Γ&A] Q) = {!!}
unie {⁻} (swp P) (ƛ[Γ&B] Q) = {!!}
unie {⁻} (swp P) (ƛ[Γ&Γ] Q) = {!!}
unie {⁻} (swp P) (Q ·[B&B]) = {!!}
unie {⁻} (swp P) ([Γ&Γ]· Q) = {!!}
unie {⁻} (swp P) (Q ·[Γ&Γ]) = {!!}
unie {⁻} (swp P) (Q ·[Γ&B]) = {!!}
unie {⁻} (swp P) (Q ·A[Γ&B] Q₁) = {!!}
unie {⁻} (swp P) (Q ·A[Γ&Γ] Q₁) = {!!}
unie {⁻} (swp P) (swp Q) = {!!}

{-
unie : ∀ {Γ A} {M : Γ ⊢ A} {p₀ p₁ q₀ q₁ : Γ [⊢] A} (P : Path M [ p₀ & p₁ ]) (Q : Path M [ q₀ & q₁ ]) → Unie p₀ p₁ q₀ q₁
unie (V[Γ&A] pΓ↑) (V[Γ&A] pΓ↑₁) = {!!}
unie (V[Γ&A] pΓ↑) (V[Γ⅋A] pΓ↓) = {!!}
unie (V[Γ⅋A] pΓ↓) (V[Γ&A] pΓ↑) = {!!}
unie (V[Γ⅋A] pΓ↓) (V[Γ⅋A] pΓ↓₁) = {!!}
unie (ƛ[A&A] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[A&A] P) (ƛ[A&B] Q) = {!!}
unie (ƛ[A&A] P) (ƛ[A⅋B] Q) = {!!}
unie (ƛ[A&A] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[A&A] P) (ƛ[Γ&A] Q) = {!!}
unie (ƛ[A&A] P) (ƛ[Γ⅋A] Q) = {!!}
unie (ƛ[A&A] P) (ƛ[Γ&B] Q) = {!!}
unie (ƛ[A&A] P) (ƛ[Γ⅋B] Q) = {!!}
unie (ƛ[A&A] P) (ƛ[Γ&Γ] Q) = {!!}
unie (ƛ[A&B] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[A&B] P) (ƛ[A&B] Q) = {!!}
unie (ƛ[A&B] P) (ƛ[A⅋B] Q) = {!!}
unie (ƛ[A&B] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[A&B] P) (ƛ[Γ&A] Q) = {!!}
unie (ƛ[A&B] P) (ƛ[Γ⅋A] Q) = {!!}
unie (ƛ[A&B] P) (ƛ[Γ&B] Q) = {!!}
unie (ƛ[A&B] P) (ƛ[Γ⅋B] Q) = {!!}
unie (ƛ[A&B] P) (ƛ[Γ&Γ] Q) = {!!}
unie (ƛ[A⅋B] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[A⅋B] P) (ƛ[A&B] Q) = {!!}
unie (ƛ[A⅋B] P) (ƛ[A⅋B] Q) = {!!}
unie (ƛ[A⅋B] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[A⅋B] P) (ƛ[Γ&A] Q) = {!!}
unie (ƛ[A⅋B] P) (ƛ[Γ⅋A] Q) = {!!}
unie (ƛ[A⅋B] P) (ƛ[Γ&B] Q) = {!!}
unie (ƛ[A⅋B] P) (ƛ[Γ⅋B] Q) = {!!}
unie (ƛ[A⅋B] P) (ƛ[Γ&Γ] Q) = {!!}
unie (ƛ[B&B] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[B&B] P) (ƛ[A&B] Q) = {!!}
unie (ƛ[B&B] P) (ƛ[A⅋B] Q) = {!!}
unie (ƛ[B&B] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[B&B] P) (ƛ[Γ&A] Q) = {!!}
unie (ƛ[B&B] P) (ƛ[Γ⅋A] Q) = {!!}
unie (ƛ[B&B] P) (ƛ[Γ&B] Q) = {!!}
unie (ƛ[B&B] P) (ƛ[Γ⅋B] Q) = {!!}
unie (ƛ[B&B] P) (ƛ[Γ&Γ] Q) = {!!}
unie (ƛ[Γ&A] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[Γ&A] P) (ƛ[A&B] Q) = {!!}
unie (ƛ[Γ&A] P) (ƛ[A⅋B] Q) = {!!}
unie (ƛ[Γ&A] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[Γ&A] P) (ƛ[Γ&A] Q) = {!!}
unie (ƛ[Γ&A] P) (ƛ[Γ⅋A] Q) = {!!}
unie (ƛ[Γ&A] P) (ƛ[Γ&B] Q) = {!!}
unie (ƛ[Γ&A] P) (ƛ[Γ⅋B] Q) = {!!}
unie (ƛ[Γ&A] P) (ƛ[Γ&Γ] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[A&B] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[A⅋B] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[Γ&A] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[Γ⅋A] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[Γ&B] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[Γ⅋B] Q) = {!!}
unie (ƛ[Γ⅋A] P) (ƛ[Γ&Γ] Q) = {!!}
unie (ƛ[Γ&B] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[Γ&B] P) (ƛ[A&B] Q) = {!!}
unie (ƛ[Γ&B] P) (ƛ[A⅋B] Q) = {!!}
unie (ƛ[Γ&B] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[Γ&B] P) (ƛ[Γ&A] Q) = {!!}
unie (ƛ[Γ&B] P) (ƛ[Γ⅋A] Q) = {!!}
unie (ƛ[Γ&B] P) (ƛ[Γ&B] Q) = {!!}
unie (ƛ[Γ&B] P) (ƛ[Γ⅋B] Q) = {!!}
unie (ƛ[Γ&B] P) (ƛ[Γ&Γ] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[A&B] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[A⅋B] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[Γ&A] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[Γ⅋A] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[Γ&B] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[Γ⅋B] Q) = {!!}
unie (ƛ[Γ⅋B] P) (ƛ[Γ&Γ] Q) = {!!}
unie (ƛ[Γ&Γ] P) (ƛ[A&A] Q) = {!!}
unie (ƛ[Γ&Γ] P) (ƛ[A&B] Q) = {!!}
unie (ƛ[Γ&Γ] P) (ƛ[A⅋B] Q) = {!!}
unie (ƛ[Γ&Γ] P) (ƛ[B&B] Q) = {!!}
unie (ƛ[Γ&Γ] P) (ƛ[Γ&A] Q) = {!!}
unie (ƛ[Γ&Γ] P) (ƛ[Γ⅋A] Q) = {!!}
unie (ƛ[Γ&Γ] P) (ƛ[Γ&B] Q) = {!!}
unie (ƛ[Γ&Γ] P) (ƛ[Γ⅋B] Q) = {!!}
unie (ƛ[Γ&Γ] P) (ƛ[Γ&Γ] Q) = {!!}
unie (P ·[B&B]) (Q ·[B&B]) = {!!}
unie (P ·[B&B]) ([Γ&Γ]· Q) = {!!}
unie (P ·[B&B]) (Q ·[Γ&Γ]) = {!!}
unie (P ·[B&B]) (Q ·[Γ&B]) = {!!}
unie (P ·[B&B]) (Q ·[Γ⅋B]) = {!!}
unie (P ·[B&B]) (Q ·A[Γ&B] Q₁) = {!!}
unie (P ·[B&B]) (Q ·A[Γ⅋B] Q₁) = {!!}
unie (P ·[B&B]) (Q ·A[Γ&Γ] Q₁) = {!!}
unie (P ·[B&B]) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie ([Γ&Γ]· P) (Q ·[B&B]) = {!!}
unie ([Γ&Γ]· P) ([Γ&Γ]· Q) = {!!}
unie ([Γ&Γ]· P) (Q ·[Γ&Γ]) = {!!}
unie ([Γ&Γ]· P) (Q ·[Γ&B]) = {!!}
unie ([Γ&Γ]· P) (Q ·[Γ⅋B]) = {!!}
unie ([Γ&Γ]· P) (Q ·A[Γ&B] Q₁) = {!!}
unie ([Γ&Γ]· P) (Q ·A[Γ⅋B] Q₁) = {!!}
unie ([Γ&Γ]· P) (Q ·A[Γ&Γ] Q₁) = {!!}
unie ([Γ&Γ]· P) (Q ·A[Γ⅋Γ] Q₁) = {!!}
unie (P ·[Γ&Γ]) (Q ·[B&B]) = {!!}
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
