\documentclass{report}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{ℤ}{\ensuremath{\mathbb{Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathbb{Q}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_s}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_i}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_o}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^u}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{≡}{\ensuremath{\mathnormal{\equiv}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\land}}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^b}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{∸}{\ensuremath{\mathnormal{\divdot}}}
\newunicodechar{∎}{\ensuremath{\mathnormal{\blacksquare}}}
\newunicodechar{⟨}{\ensuremath{\mathnormal{\langle}}}
\newunicodechar{⟩}{\ensuremath{\mathnormal{\rangle}}}
\newunicodechar{𝓁}{\ensuremath{\mathcal{l}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal{\ell}}}
\newunicodechar{⊃}{\ensuremath{\mathnormal{\supset}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\cmene{VVXtAdventure.Funky}

\title{la'o zoi.\ \texttt{\cmene}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.\ ja co'e}
ni'o la'o zoi.\ \texttt{\cmene}\ .zoi. vasru le velcki be lo fancu be fi la'oi .\F{GameData}.\ ja zo'e

\section{le me'oi .preamble.\ ja co'e}

\begin{code}
{-# OPTIONS --safe #-}

module VVXtAdventure.Funky where

import Level
import Agda.Builtin.Unit as ABU

open import Data.Fin
  using (
    Fin;
    suc;
    zero
  )
open import Data.Nat
  using (
    _∸_;
    _+_;
    ℕ
  )
open import Data.Sum
open import Function
open import Data.Bool
  renaming (
    if_then_else_ to if
  )
  hiding (
    _≤_;
    _≟_
  )
open import Data.List
  using (
    mapMaybe;
    List;
    _∷_;
    []
  )
  renaming (
    lookup to _!_;
    filter to filterₗ
  )
open import Data.Maybe
  using (
    is-just;
    fromMaybe;
    maybe;
    Maybe;
    just;
    nothing
  )
open import Data.String
  hiding (
    length;
    _≤_;
    _≟_
  )
open import Data.Product
  using (
    Σ;
    proj₁;
    proj₂;
    _×_;
    _,_
  )
open import Relation.Nullary
  using (
    yes;
    no
  )
open import VVXtAdventure.Base
open import Truthbrary.Data.Fin
  using (
    mink
  )
open import Truthbrary.Record.Eq
open import Truthbrary.Record.LLC
  using (
    length;
    map
  )
open import Truthbrary.Category.Monad
open import Truthbrary.Data.List.Loom
  using (
    ual
  )
open import Data.List.Relation.Unary.Any
  using (
    any?
  )
open import Relation.Binary.PropositionalEquality

import Data.Fin.Properties as DFP
import Data.Nat.Properties as DNP
import Data.List.Properties as DLP
import Data.Maybe.Properties as DMP

open ≡-Reasoning
\end{code}

\chapter{le mu'oi glibau.\ low-level .glibau.}

\section{la'o zoi.\ \F{movePawn} .zoi.}
ni'o tu'a la'o zoi.\ \F{movePawn} \B q \B m \B n .zoi.\ .indika lo du'u lo selsni be la'o zoi.\ \F{Data.List.lookup} (\F{GameData.haters} \B q) \B h .zoi.\ cu zvati ko'a goi lo selsni be la'o zoi.\ \F{Data.List.lookup} (\F{GameData.rooms} \B q) \B n .zoi.

\begin{code}
movePawn : (q : GameData)
         → Fin $ Data.List.length $ GameData.haters q
         → Fin $ Data.List.length $ GameData.rooms q
         → GameData
movePawn gd h r = record gd {haters = proj₁ xat; player' = player''}
  where
  cninykumfa = λ x → record x {room = r}
  updateAtₗ : ∀ {a} → {A : Set a}
           → (L : List A) → Fin $ length L → (A → A) → List A
  updateAtₗ (x ∷ xs) (suc n) f = x ∷ updateAtₗ xs n f
  updateAtₗ (x ∷ xs) zero f = f x ∷ xs
  htrs = GameData.haters gd
  xat = ual htrs h cninykumfa
  haters' = updateAtₗ htrs h cninykumfa
  player'' = mink (GameData.player' gd) $ proj₁ $ proj₂ xat
\end{code}

\section{la'o zoi.\ \F{wieldPawn}\ .zoi.}
ni'o tu'a la'o zoi.\ \F{wieldPawn} \B q \B m \B n \F{refl}\ .zoi.\ .indika lo du'u zo'e ja lo selsni be la'o zoi.\ \F{Data.List.lookup} (\F{GameData.haters} \B q) \B m .zoi.\ cu me'oi .wield.\ lo selsni be la'o zoi.\ \F{Data.List.lookup} (\F{Character.inventory} \Sym \$ \F{Data.List.lookup} (\F{GameData.haters} \B q) \B m) \B n .zoi.

\begin{code}
wieldPawn : (q : GameData)
          → let x = GameData.haters in
            let 𝓁 = Data.List.length in
            let iv = Character.inventory in
            (j : Fin $ 𝓁 $ x q)
          → (i : Fin $ 𝓁 $ Character.inventory $ x q ! j)
          → (_≡_ true $ is-just $ Item.weapwn $ _!_ (iv $ x q ! j) i)
          → Σ GameData $ λ q'
            → Σ (𝓁 (x q) ≡ 𝓁 (x q')) $ λ ℓ
            → Σ (𝓁 (iv $ x q ! j) ≡ 𝓁 (iv $ x q' ! mink j ℓ)) $ λ ℓ₂
            → (_≡_
                (just i)
                (Data.Maybe.map
                  (λ t → mink (proj₁ t) $ sym ℓ₂)
                  (Character.wieldedct $ x q' ! mink j ℓ)))
wieldPawn gd j i t = gd' , proj₂ z
  where
  z : Σ (List $ Character $ GameData.rooms gd) $ λ t
      → let x = GameData.haters in
        let 𝓁 = Data.List.length in
        let iv = Character.inventory in
        Σ (𝓁 (x gd) ≡ 𝓁 t) $ λ ℓ
      → Σ (𝓁 (iv $ x gd ! j) ≡ 𝓁 (iv $ t ! mink j ℓ)) $ λ ℓ₂
      → (_≡_
          (just i)
          (Data.Maybe.map
            (λ t → mink (proj₁ t) $ sym ℓ₂)
            (Character.wieldedct $ t ! mink j ℓ)))
  z = xen' , xenlen , xendj , sym tivos
    where
    𝓁 = Data.List.length
    xen = GameData.haters gd
    lenkat : ∀ {a} → {A : Set a}
           → (xs₁ : List A)
           → (x : A)
           → (xs₂ : List A)
           → 𝓁 (xs₁ Data.List.++ x ∷ xs₂) ≡ 𝓁 xs₁ + ℕ.suc (𝓁 xs₂)
    lenkat xs₁ x xs₂ = begin
      𝓁 (xs₁ Data.List.++ x ∷ xs₂) ≡⟨ DLP.length-++ xs₁ ⟩
      𝓁 xs₁ + 𝓁 (x ∷ xs₂) ≡⟨ cong (_+_ $ length xs₁) refl ⟩
      𝓁 xs₁ + ℕ.suc (𝓁 xs₂) ∎
    x₁ = Data.List.take (Data.Fin.toℕ j) xen
    x₂ = record (xen ! j) {wieldedct = just $ i , t}
    x₃ = Data.List.drop (ℕ.suc $ Data.Fin.toℕ j) xen
    xen' = x₁ Data.List.++ x₂ ∷ x₃

    xenlen = begin
      𝓁 xen ≡⟨ cong 𝓁 $ sym $ DLP.take++drop j' xen ⟩
      𝓁 (x₁ Data.List.++ d₂) ≡⟨ DLP.length-++ x₁ ⟩
      𝓁 x₁ + 𝓁 d₂ ≡⟨ cong (_+_ $ 𝓁 x₁) $ DLP.length-drop j' xen ⟩
      𝓁 x₁ + (𝓁 xen ∸ j') ≡⟨ cong (_+_ $ 𝓁 x₁) $ sym xex ⟩
      𝓁 x₁ + 𝓁 (x₂ ∷ x₃) ≡⟨ cong (_+_ $ 𝓁 x₁) refl ⟩
      𝓁 x₁ + ℕ.suc (𝓁 x₃) ≡⟨ sym $ lenkat x₁ x₂ x₃ ⟩
      𝓁 xen' ∎
      where
      j' = Data.Fin.toℕ j
      d₂ = Data.List.drop j' xen
      xex = begin
        𝓁 (x₂ ∷ x₃) ≡⟨ refl ⟩
        ℕ.suc (𝓁 $ ℕ.suc j' ↓ xen) ≡⟨ dropsuc xen j ⟩
        𝓁 (j' ↓ xen) ≡⟨ DLP.length-drop j' xen ⟩
        𝓁 xen ∸ j' ∎
        where
        _↓_ = Data.List.drop
        dropsuc : ∀ {a} → {A : Set a}
                → (x : List A)
                → (n : Fin $ length x)
                → let n' = Data.Fin.toℕ n in
                  ℕ.suc (𝓁 $ ℕ.suc n' ↓ x) ≡ 𝓁 (n' ↓ x)
        dropsuc (x ∷ xs) (Fin.zero) = refl
        dropsuc (x ∷ xs) (Fin.suc n) = dropsuc xs n
    xendj : let iv = Character.inventory in
            let 𝓁 = Data.List.length in
            𝓁 (iv $ xen ! j) ≡ 𝓁 (iv $ xen' ! mink j xenlen)
    xendj = cong length $ DMP.just-injective x₂d
      where
      _↓_ = Data.List.drop
      iv = Character.inventory
      dropkat : ∀ {a} → {A : Set a}
              → (xs ys : List A)
              → (𝓁 xs) ↓ (xs Data.List.++ ys) ≡ ys
      dropkat [] _ = refl
      dropkat (_ ∷ xs) ys = dropkat xs ys
      x₂d : just (iv $ xen ! j) ≡ just (iv $ xen' ! mink j xenlen)
      x₂d = begin
        just (iv $ xen ! j) ≡⟨ refl ⟩
        just (iv x₂) ≡⟨ refl ⟩
        mapₘ iv (⊃ $ x₂ ∷ x₃) ≡⟨ cong (mapₘ iv ∘ ⊃) $ dropsim ⟩
        mapₘ iv (⊃ $ (𝓁 x₁) ↓ xen') ≡⟨ cong (mapₘ iv) xent ⟩
        just (iv $ xen' ! mink j xenlen) ∎
        where
        toℕ = Data.Fin.toℕ
        mapₘ = Data.Maybe.map
        ⊃ = Data.List.head
        dropsim = sym $ dropkat x₁ $ x₂ ∷ x₃
        xent : ⊃ ((𝓁 x₁) ↓ xen') ≡ just (xen' ! mink j xenlen)
        xent = sym $ dropind xen' (mink j xenlen) (𝓁 x₁) xil
          where
          dropind : ∀ {a} → {A : Set a}
                  → (xs : List A)
                  → (n : Fin $ 𝓁 xs)
                  → (m : ℕ)
                  → Data.Fin.toℕ n ≡ m
                  → just (xs ! n) ≡ Data.List.head (m ↓ xs)
          dropind (x ∷ xs) Fin.zero (ℕ.zero) refl = refl
          dropind (x ∷ xs) (Fin.suc n) (ℕ.suc m) refl = ret
            where
            ret = dropind xs n m refl
          teikgek : ∀ {a} → {A : Set a}
                  → (xs : List A)
                  → (n : ℕ)
                  → n Data.Nat.≤ 𝓁 xs
                  → 𝓁 (Data.List.take n xs) ≡ n
          teikgek _ 0 _ = refl
          teikgek (x ∷ xs) (ℕ.suc n) (Data.Nat.s≤s q) = ret
            where
            ret = cong ℕ.suc $ teikgek xs n q
          mindut : (m n : ℕ)
                 → (o : Fin m)
                 → (x : m ≡ n)
                 → toℕ (mink o x) ≡ toℕ o
          mindut m n o refl = refl
          lisfis : ∀ {a} → {A : Set a}
                 → (xs : List A)
                 → (n : Fin $ 𝓁 xs)
                 → Σ ℕ $ _≡_ (𝓁 xs) ∘ ℕ.suc
          lisfis (_ ∷ xs) j = 𝓁 xs , refl
          _≤_ = Data.Nat._≤_
          tuik : toℕ j ≤ 𝓁 xen
          tuik = subst (_≤_ _) kix $ DNP.≤-step slex
            where
            d = proj₂ $ lisfis xen j
            j' = DFP.≤fromℕ $ mink j $ proj₂ $ lisfis xen j
            slex : toℕ j ≤ _
            slex = subst (flip _≤_ _) (mindut _ _ j d) j'
            kix : ℕ.suc _ ≡ 𝓁 xen
            kix = tif _ _ $ sym $ proj₂ $ lisfis xen j
              where
              tif : (m n : ℕ)
                  → m ≡ n
                  → toℕ (Data.Fin.fromℕ m) ≡ n
              tif ℕ.zero ℕ.zero refl = refl
              tif (ℕ.suc m) (ℕ.suc n) refl = ret
                where
                ret = cong ℕ.suc $ tif m n refl
          xil : toℕ (mink j xenlen) ≡ 𝓁 x₁
          xil = begin
            toℕ (mink j xenlen) ≡⟨ mindut _ _ j xenlen ⟩
            toℕ j ≡⟨ sym $ teikgek xen (toℕ j) tuik ⟩
            𝓁 x₁ ∎
    tivos = begin
      mapₘ (λ t → mink (proj₁ t) $ sym xendj) uxij ≡⟨ komp (uxij) _ _ ⟩
      mapₘ (λ t → mink t $ sym xendj) (mapₘ proj₁ $ uxij) ≡⟨ xenkik ⟩
      mapₘ proj₁ (uid x₂) ≡⟨ refl ⟩
      just i ∎
      where
      j' = mink j xenlen
      mapₘ = Data.Maybe.map
      komp : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
           → (x : Maybe A)
           → (f : A → B)
           → (g : B → C)
           → mapₘ (g ∘ f) x ≡ mapₘ g (mapₘ f x)
      komp {_} {A} {B} {C} nothing f g = refl
      komp {_} {A} {B} {C} (just t) f g = refl
      kix : ∀ {a} → {A : Set a}
          → (xs : List A)
          → (x : A)
          → {n : A → ℕ}
          → (f : (a : A) → Maybe $ Fin $ n a)
          → (i : Fin $ 𝓁 xs)
          → (d : n (xs ! i) ≡ n x)
          → mapₘ (λ t → mink t d) (f $ xs ! i) ≡ f x
      kix xs x f i d = {!!}
      xij = xen' ! mink j xenlen
      uid = Character.wieldedct
      uxij = uid xij
      xenkik = kix xen' x₂ (mapₘ proj₁ ∘ uid) j' $ sym xendj
  z₁ = proj₁ z
  z₂ = proj₁ $ proj₂ z
  p' = mink (GameData.player' gd) z₂
  gd' = record gd {haters = z₁; player' = p'}
\end{code}

\chapter{le mu'oi glibau.\ high-level .glibau.}

\section{le fancu poi tu'a ke'a na rinka lo nu lo ctaipe be la'oi .\F{GameData}.\ cu na binxo pe'a ru'e}

\subsection{la'oi .\F{epicwin?}.}
ni'o ga jonai ga je tu'a la'o zoi.\ \B a .zoi.\ .indika le du'u jinga gi ga je la'o zoi.\ \B b .zoi.\ du lo xatra ja co'e poi tu'a ke'a cusku pe'a ru'e le du'u jinga gi ko'a goi la'o zoi.\ \F{epicwin?} \B a .zoi. du la'o zoi.\ \B b , \B a .zoi.\ gi ko'a du la'oi .\F{nothing}.

\begin{code}
epicwin? : GameData → COut
epicwin? = scrimmage GameData.epicwin
  where
  jasat = "YOU HAVE ACCOMPLISHED\n\
          \THE MISSION.\n\
          \YOU ARE THE VERY PREVAILER\n\
          \THAT PROTECT RIGHT\n\
          \AND JUSTICE.\n\
          \I WOULD EXPRESS MY SINCERE.\n\
          \THANKS TO YOU.\n\n\
          \\
          \TAKE GOOD REST !\n\n\
          \\
          \\tGENERAL KAWASAKI"
  scrimmage : (GameData → Bool) → GameData → COut
  scrimmage f g = if (f g) (just $ jasat , g) nothing
\end{code}

\subsection{la'oi .\F{inspect?}.}
ni'o ga jonai ga je ga je la'oi .\F{inspect?}.\ djuno pe'a ru'e lo du'u tu'a la'o zoi.\ \B a .zoi.\ .indika lo du'u djica lo nu skicu la'o zoi.\ B b .zoi.\ gi cumki fa lo nu skicu la'o zoi.\ \B b .zoi.\ gi ga je la'o zoi.\ \B q .zoi.\ velski la'o zoi.\ \B b .zoi.\ gi ko'a goi la'o zoi.\ \F{inspect?} \B a \B{godDamn} .zoi.\ du la'o zoi.\ \F{just} \Sym \$ \B b \Sym , \B{godDamn} .zoi.\ gi ga jonai ga je la'oi .\F{inspect?}.\ djuno pe'a ru'e lo du'u la'o zoi.\ \B a .zoi.\ mabla gi ga je la'o zoi.\ \B i .zoi.\ te skuxai gi ko'a du la'o zoi.\ \F{just} \Sym \$ \B i \Sym , \B{godDamn} .zoi.\ gi ko'a du la'oi .\F{nothing}.

\begin{code}
inspect? : Com
inspect? (c ∷ f) dang = if methch (getDown f) nothing
  where
  methch = c ≡ᵇ "INSPECT"
  getDown : List String → COut
  getDown ("POCKETS" ∷ []) = just $ m , dang
    where
    m = "Hey, asshole, you're using an abstraction.  \
        \Stop worrying about your damned pockets and \
        \play by the rules."
  getDown ("POCKET" ∷ []) = getDown ("POCKETS" ∷ [])
  getDown (n ∷ []) = gd' $ filterₗ (_≟_ n ∘ Item.name) inv
    where
    inv = Character.inventory $ GameData.player dang
    gd' : List Item → COut
    gd' (q ∷ []) = just $ Item.hlDescr q , dang
    gd' (_ ∷ _ ∷ _) = just $ m , dang
      where
      m = "You're going to have to be more specific.  \
          \Sure, I could choose some arbitrary matching \
          \item, but that would probably piss you off, \
          \and I'm already insulting you right and left."
    gd' [] = just $ "I'm not seeing it." , dang
  getDown (_ ∷ _ ∷ _) = just $ m , dang
    where
    m = "I can't handle any more of your inane \
        \gibberish.\n\
        \If you want to search for multiple things, \
        \then tell me the shortnames of the things \
        \individually.\n\
        \Alternatively, you might have tried to \
        \search for a full name which contains \
        \multiple spaces, which is illegal.  \
        \Do it $n$ more times, and I will send the \
        \police to your doorstep.  I'm trying to \
        \help you, but you're really testing my \
        \patience now."
  getDown [] = just $ m , dang
    where
    m = "nothing : ∀ {a} → {A : Set a} → Maybe A"
inspect? [] _ = nothing
\end{code}

\subsection{la'oi .\F{scream?}.}
ni'o ga jonai ga je la'oi .\F{scream?}.\ djuno pe'a ru'e lo du'u tu'a la'o zoi.\ \B a .zoi.\ .indika lo du'u lo kelci cu djica lo nu krixa fa ko'a goi lo krixa ke xarpre ja co'e po la'o zoi.\ \B b .zoi.\ gi ga je tu'a la'o zoi.\ \B c .zoi.\ .indika lo du'u ko'a krixa gi ko'e goi la'o zoi.\ \F{scream?} \B a \B b .zoi.\ du la'o zoi.\ \F{just} \Sym \$ c \Sym , b .zoi.\ gi ko'e du la'oi .\F{nothing}.

\begin{code}
scream? : Com
scream? ("SCREAM" ∷ []) q = just $ "AARGH!!!" , q
scream? _ _ = nothing
\end{code}

\subsection{la'oi .\F{sayless?}.}
ni'o ga jonai ga je la'o zoi.\ \B a .zoi.\ kunti gi ga je tu'a la'o zoi.\ \B c .zoi.\ .indika le du'u mabla fa lo nu samci'a lo kunti gi ko'a goi la'o zoi.\ \F{sayless?} \B a \B b .zoi.\ du la'o zoi.\ \F{just} \Sym \$ \B c \Sym , \B b .zoi.\ gi ko'a du la'oi .\F{nothing}.

\begin{code}
sayless? : List String → GameData → COut
sayless? [] = just ∘ _,_ "The silent treatment won't work here."
sayless? _ = const nothing
\end{code}

\subsection{la'oi .\F{lp?}.}
ni'o ga jonai ga je ga je la'o zoi.\ \B c .zoi.\ na vajni gi ko'a goi la'o zoi.\ \F{lp?} \B a \B b .zoi.\ du la'o zoi.\ \F{just} \B c \B b .zoi.\ gi ko'a du la'oi .\F{nothing}.

\begin{code}
lp? : Com
lp? ("WHO" ∷ "ARE" ∷ "YOU?" ∷ []) q = just $ m , q
  where
  m = "I really want to know."
lp? ("I'M" ∷ "A" ∷ "WINNER" ∷ []) q = just $ m , q
  where
  m = "Actually, refl is a proof of GameData.epicwin \
      \q ≡ false.  You have not won The Game.\n\n\
      \You were probably expecting something else."
lp? _ _ = nothing
\end{code}

\section{la'oi .\F{travel?}.}
ni'o ga jonai ga je la'o zoi.\ \F{travel?} .zoi.\ djuno ja co'e lo du'u lo nu co'e ko'a goi zoi zoi.\ \F{travel?} \B r \B g .zoi.\ cu nu cpedu lo nu lo kelci ke xarpre ja co'e cu klama lo kumfa poi la'o zoi.\ \B K .zoi.\ sinxa ke'a gi ga jonai ga je la'o zoi.\ \F{Room.travis} \Sym \$ \F{Character.room} \Sym \$ \F{GameData.player} \B g .zoi.\ vasru la'o zoi.\ \B K .zoi.\ gi ko'a broda cei sinxa ja co'e lo me'oi .product.\ be lo velski be lo nu klama bei zo'e poi tu'a ke'a .indika lo du'u lo kelci ke xarpre ja co'e cu zvati zo'e poi djica lo nu zvati ke'a xi re gi ko'a broda lo me'oi .product.\ be lo te skuxai ja zo'e bei la'o zoi.\ \B g .zoi.\ gi ko'a broda la'oi .\F{nothing}.

\begin{code}
travel? : Com
travel? [] _ = nothing
travel? (x₁ ∷ xs₁) = if realShit (travel' xs₁) $ const nothing
  where
  realShit = x₁ ≡ᵇ "TRAVEL"
  travel' : Com
  travel' [] q = just $ m , q
    where
    m = "Don't tell me to break the rules, fucker!"
  travel' (x ∷ []) q = maybe just tryfind $ alreadythere?
    where
    F = Fin $ length $ GameData.rooms q
    cur = GameData.rooms q ! Character.room (GameData.player q)
    alreadythere? = if at (just $ m , q) nothing
      where
      at = x ≡ᵇ Room.cname cur
      m = "Damn, that's some fast travel.  \
          \You're already there!"
    tryfind = [_,_] (just ∘ flip _,_ q) iusyf mathch
      where
      -- | We'll just have to live with that possibility.
      iusyf = maybe youse fail ∘ Data.List.head
        where
        fail = just $ m , q
          where
          m = "That room is not in your immediate vicinity."
        youse = just ∘ _,_ m ∘ q'
          where
          q' = movePawn q (GameData.player' q)
          m = "You travel successfully."
      mathch = travelable $ methching $ zipfin $ GameData.rooms q
        where
        zipfin = λ l → Data.List.zip (Data.List.allFin $ length l) l
        methching = Data.List.filter $ _≟_ x ∘ Room.cname ∘ proj₂
        travelable : List $ F × Room → String ⊎ List F
        travelable [] = inj₁ m
          where
          m = "Did you take your pills this morning?  \
              \I don't think that that room exists."
        travelable (x ∷ xs) = inj₂ $ pj1s $ Data.List.filter tr $ x ∷ xs
          where
          pj1s = Data.List.map proj₁
          cnq = λ a b → Room.cname (proj₂ a) ≟ b
          tr = λ a → any? (cnq a) $ Room.travis cur
  travel' (_ ∷ _ ∷ _) q = just $ m , q
    where
    m = "I strongly doubt that the concept of \"super\
        \position\" applies to a creature of your mass."
\end{code}

\section{la'oi .\F{wield?}.}
ni'o ga jonai ga je ga je la'oi .\F{wield?}.\ djuno pe'a ru'e lo du'u tu'a la'o zoi.\ \B a .zoi.\ .indika lo du'u lo kelci cu djica lo nu ko'a goi lo kelci ke xarpre ja co'e cu me'oi .wield.\ ko'e goi zo'e poi la'o zoi.\ \B c .zoi.\ mu'oi glibau.\ \F{Item.cname} .glibau.\ lo sinxa be ke'a gi ga jonai ga je li pa nilzilcmi lo'i selvau be lo me'oi .inventory.\ be ko'a be'o be'o poi la'o zoi.\ \B c .zoi.\ mu'oi glibau.\ \F{Item.cname} .glibau.\ ke'a je poi curmi lo nu me'oi .wield.\ ke'a gi tu'a la'o zoi.\ \B x .zoi.\ lu'u je tu'a la'o zoi.\ \B y .zoi.\ cu .indika lo du'u ko'a me'oi .wield.\ ko'e gi ko'i goi la'o zoi.\ \F{wield?} \B a \B b .zoi.\ du la'o zoi.\ \F{just} \Sym \$ \B x \Sym , \B y .zoi.\ gi ga je skuxai ja co'e la'o zoi.\ \B x .zoi.\ gi ko'a du la'o zoi.\ \F{just} \Sym \$ \B x \Sym , \B b .zoi.\ gi ko'a du la'oi .\F{nothing}.

\begin{code}
wield? : Com
wield? [] = const nothing
wield? (x ∷ xs) dang = if (realShit x) (troci xs) nothing
  where
  inv = Character.inventory $ GameData.player dang
  wisyj = Data.Maybe.is-just ∘ Item.weapwn ∘ Data.List.lookup inv
  realShit = _≡ᵇ_ "WIELD"
  troci : List String → Maybe $ String × GameData
  troci [] = just $ m , dang
    where m = "Bitch, you'd best tell me what you \
              \want to wield, or I'll wield \
              \your bones as clubs."
  troci (_ ∷ _ ∷ _) = just $ m , dang
    where
    m = "You are giving me useless information."
  troci (y ∷ []) with flt $ mapMaybe mapti? $ Data.List.allFin _
    where
    flt = Data.List.filter (_≟_ y ∘ cname ∘ proj₁)
      where
      cname = Item.cname ∘ Data.List.lookup inv
    mapti? : _ → Maybe $ Σ (Fin _) $ _≡_ true ∘ wisyj
    mapti? n with true Data.Bool.≟ wisyj n
    ... | yes x = just $ n , x
    ... | no _ = nothing
  ... | [] = just $ m , dang
    where
    m = "You need to stop chugging PCP or whatever.  \
        \Your hallucinations are pissing me off."
  ... | (selpli ∷ []) = just $ wieldMsg , proj₁ wieldData
    where
    wieldMsg = fromMaybe "You wield the weapon." xarcynotci
      where
      items = Character.inventory $ GameData.player dang
      xarci = Item.weapwn $ Data.List.lookup items $ proj₁ selpli
      xarcynotci = xarci Data.Maybe.>>= WeaponInfo.wieldMsg
    wieldData = wieldPawn dang p (proj₁ selpli) $ proj₂ selpli
      where
      p = GameData.player' dang
  ... | (_ ∷ _ ∷ _) = just $ m , dang
    where
    m = "Your query matches multiple items, although \
        \a proof of that your bag only contains items \
        \which have unique names exists.\n\
        \Something is mad fucked, and you might \
        \actually be innocent this time."
\end{code}
\end{document}
