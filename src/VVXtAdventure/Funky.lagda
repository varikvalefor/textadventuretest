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
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_s}}}
\newunicodechar{ₜ}{\ensuremath{\mathnormal{_t}}}
\newunicodechar{ᵤ}{\ensuremath{\mathnormal{_u}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_i}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_o}}}
\newunicodechar{ₙ}{\ensuremath{\mathnormal{_n}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^u}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{≡}{\ensuremath{\mathnormal{\equiv}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\land}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^b}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{∸}{\ensuremath{\mathnormal{\divdot}}}
\newunicodechar{⍨}{\raisebox{-0.25ex}{$\ddot\sim$}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal{\ell}}}
\newunicodechar{∋}{\ensuremath{\mathnormal{\ni}}}
\newunicodechar{∈}{\ensuremath{\mathnormal{\in}}}
\newunicodechar{∉}{\ensuremath{\mathnormal{\notin}}}
\newunicodechar{∎}{\ensuremath{\mathnormal{\blacksquare}}}
\newunicodechar{⟨}{\ensuremath{\mathnormal{\langle}}}
\newunicodechar{⟩}{\ensuremath{\mathnormal{\rangle}}}
\newunicodechar{𝔦}{\ensuremath{\mathfrak{i}}}
\newunicodechar{𝔪}{\ensuremath{\mathfrak{m}}}

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
import Data.List.Properties as DLP

open import Data.Fin
  using (
    Fin;
    suc;
    zero
  )
open import Data.Nat
  using (
    ℕ;
    _+_
  )
open import Data.Sum
  using (
    _⊎_;
    inj₁;
    inj₂;
    [_,_]
  )
open import Function
open import Data.Bool
  renaming (
    if_then_else_ to if
  )
  hiding (
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
    _≟_
  )
open import Data.Product
  using (
    Σ;
    map₂;
    proj₁;
    proj₂;
    _×_;
    _,_
  )
open import Relation.Unary
  using (
    Pred
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    no
  )
open import VVXtAdventure.Base
open import Truthbrary.Record.Eq
open import Truthbrary.Record.LLC
  using (
    nu,iork;
    length;
    _∉_;
    map
  )
open import Truthbrary.Category.Monad
  using (
  )
open import Data.List.Relation.Unary.Any
  using (
    any?
  )
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
\end{code}

\chapter{le mu'oi glibau.\ low-level .glibau.}

\section{la'o zoi.\ \F{movePawn} .zoi.}
ni'o tu'a la'o zoi.\ \F{movePawn} \B q (\F{just} \B m) \B n .zoi.\ .indika lo du'u lo selsni be la'o zoi.\ \F{flip} \F{Data.List.lookup} \B h \Sym \$ \F{GameData.haters} \B{gd} .zoi.\ cu zvati ko'a goi lo selsni be la'o zoi.\ \F{flip} \F{Data.List.lookup} \B n \Sym \$ \F{GameData.rooms} \B{gd} .zoi.  .i tu'a la'o zoi.\ \F{movePawn} \B q \F{nothing} \B n .zoi.\ .indika lo du'u lo kelci ke xarpre ja co'e cu zvati ko'a

\begin{code}
movePawn : (q : GameData)
         → Maybe $ Fin $ Data.List.length $ GameData.haters q
         → Fin $ Data.List.length $ GameData.rooms q
         → GameData
movePawn gd h' r = maybe moveHater movePlayer h'
  where
  cninykumfa = λ x → record x {room = r}
  movePlayer = record gd {player = cninykumfa $ GameData.player gd}
  moveHater = λ h → record gd {haters = updateAtₗ htrs h cninykumfa}
    where
    updateAtₗ : ∀ {a} → {A : Set a}
             → (L : List A) → Fin $ length L → (A → A) → List A
    updateAtₗ (x ∷ xs) (suc n) f = x ∷ updateAtₗ xs n f
    updateAtₗ (x ∷ xs) zero f = f x ∷ xs
    htrs = GameData.haters gd
\end{code}

\section{la'o zoi.\ \F{takeHater}\ .zoi.}
ni'o tu'a la'o zoi.\ \F{takeHater} \B q \B m \B n .zoi.\ cu .indika lo du'u lo me'oi .inventory.\ be lo selsni be la'o zoi.\ \F{GameData.haters} \B q \Sym ! \B m\ .zoi.\ cu vasru lo selsni be la'o zoi.\ (\F{GameData.itemsInRoomOf} \B q \B m) \Sym ! n\ .zoi... kei je zo'e

ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu la .varik.\ cu ciksi la'oi .\F{mink}.\ ja la'o zoi.\ \F{\_⍨}\ .zoi.\ bau la .lojban.

\begin{code}
private
  mink : {m n : ℕ} → Fin m → m ≡ n → Fin n
  mink a refl = a
  
  _⍨ = flip

takeHater : (q : GameData)
          → (m : Fin $ length $ GameData.haters q)
          → (n : Fin $ length $ GameData.itemsInRoomOf q m)
          → Σ GameData $ λ q'
            → Σ ((_≡_ on length ∘ GameData.rooms) q q') $ λ r
            → Σ ((_≡_ on length ∘ GameData.haters) q q') $ λ x
            → (_≡_
                (map Item.cname $ GameData.inventOf q' $ mink m x)
                ((_∷_ ⍨)
                  (map Item.cname $ GameData.inventOf q m)
                  (Item.cname $ GameData.itemsInRoomOf q m ! n)))
takeHater q m n = q' , dus , dis , nyfin
  where
  tr : ∀ {a} → {A : Set a} → {x y : A} → x ≡ y → y ≡ x
  tr refl = refl
  ual : ∀ {a} → {A : Set a}
      → (l : List A) → (n : Fin $ length l) → (f : A → A)
      → Σ (List A) $ λ l'
        → Σ (length l ≡ length l') $ λ ℓ
        → l' ! mink n ℓ ≡ f (l ! n)
  ual (x ∷ xs) Fin.zero f = f x ∷ xs , refl , refl
  ual (x ∷ xs) (Fin.suc n) f = x ∷ proj₁ r₁ , r₂ , r₃
    where
    r₁ = ual xs n f
    r₂ = cong ℕ.suc $ proj₁ $ proj₂ r₁
    r₃ = indus misuk $ adus (proj₁ r₁) x $ proj₂ $ proj₂ r₁
      where
      adus : ∀ {a} → {A : Set a}
           → {x : A}
           → (l : List A)
           → {n : Fin $ length l}
           → (z : A)
           → l ! n ≡ x
           → (z ∷ l) ! suc n ≡ x
      adus l z = id
      indus : ∀ {a} → {A : Set a}
            → {l : List A}
            → {m n : Fin $ length l}
            → {k : A}
            → m ≡ n
            → l ! m ≡ k
            → l ! n ≡ k
      indus refl = id
      misuk : suc (mink n $ proj₁ $ proj₂ r₁) ≡ mink (suc n) r₂
      misuk = sukmi n $ proj₁ $ proj₂ r₁
        where
        sukmi : {m n : ℕ}
              → (f : Fin m)
              → (x : m ≡ n)
              → suc (mink f x) ≡ mink (suc f) (cong ℕ.suc x)
        sukmi f refl = refl
  lb = GameData.haters q ! m
  sl = Room.items (GameData.rooms q ! Character.room lb) ! n
  k'' : Σ (List Room) $ λ l
        → Σ (length (GameData.rooms q) ≡ length l) _
  k'' = ual (GameData.rooms q) (Character.room lb) vimcu
    where
    nadu = Data.Bool._≟_ false ∘ _≡ᵇ_ (Item.cname sl) ∘ Item.cname
    vimcu = λ x → record x {items = filterₗ nadu $ Room.items x}
  k' = proj₁ k''
  kumbi'o = λ x → record {
    forename = Character.forename x;
    surname = Character.surname x;
    nicknames = Character.nicknames x;
    room = mink (Character.room x) $ proj₁ $ proj₂ k'';
    inventory = Character.inventory x;
    wieldedct = Character.wieldedct x;
    yourfloorisnowclean = Character.yourfloorisnowclean x
    }
  lb! : Character k' → Character k'
  lb! x = record x {
    inventory = sl ∷ Character.inventory x;
    wieldedct = Data.Maybe.map f $ Character.wieldedct x;
    yourfloorisnowclean = iofink
    }
    where
    iofink = f i (Item.cname sl) n₁ {!!}
      where
      n₁ = Character.yourfloorisnowclean x
      i = Data.List.map Item.cname $ Character.inventory x
      f : ∀ {a} → {A : Set a}
        → ⦃ _ : Eq A ⦄
        → (x : List A)
        → (s : A)
        → nu,iork x
        → s ∉ x
        → nu,iork $ s ∷ x
      f x s n nin = {!!}
    f = λ (l , k) → Fin.suc l , k
  ualmap : ∀ {a} → {A B : Set a}
         → (x : List A)
         → (f : A → B)
         → (g : B → B)
         → (k : Fin $ length x)
         → Σ (List B) $ λ l
           → Σ (length x ≡ length l) $ λ ℓ
           → g (f $ x ! k) ≡ l ! mink k ℓ
  ualmap {_} {_} {B} x f g k = proj₁ l , p₂ , tr p₃
    where
    lum : ∀ {a b} → {A : Set a} → {B : Set b}
        → (l : List A)
        → (f : A → B)
        → (n : Fin $ length l)
        → (_≡_
            (Data.List.map f l ! mink n (tr $ DLP.length-map f l))
            (f $ l ! n))
    lum (x ∷ xs) f zero = begin
      Data.List.map f (x ∷ xs) ! (mink zero ℓ) ≡⟨ cong x∷xs! $ zil ℓ ⟩
      Data.List.map f (x ∷ xs) ! zero ≡⟨⟩
      f x ∎
      where
      ℓ = tr $ DLP.length-map f $ x ∷ xs
      x∷xs! = _!_ $ Data.List.map f $ x ∷ xs
      zil : {m n : ℕ}
          → (x : ℕ.suc m ≡ ℕ.suc n)
          → mink zero x ≡ zero
      zil refl = refl
    lum (x ∷ xs) f (suc n) = begin
      mef (x ∷ xs) ! mink (suc n) tryks ≡⟨ kong $ 𝔪 n tryk tryks ⟩
      mef (x ∷ xs) ! suc (mink n tryk) ≡⟨ 𝔦 x xs f $ mink n tryk ⟩
      mef xs ! mink n tryk ≡⟨ lum xs f n ⟩
      f (xs ! n) ∎
      where
      mef = Data.List.map f
      kong = cong $ _!_ $ mef $ x ∷ xs
      tryk = tr $ DLP.length-map f xs
      tryks = tr $ DLP.length-map f $ x ∷ xs
      𝔪 : {m n : ℕ}
        → (t : Fin m)
        → (x : m ≡ n)
        → (d : ℕ.suc m ≡ ℕ.suc n)
        → mink (suc t) d ≡ suc (mink t x)
      𝔪 t refl refl = refl
      𝔦 : ∀ {a b} → {A : Set a} → {B : Set b}
        → (x : A)
        → (xs : List A)
        → (f : A → B)
        → (n : Fin $ length $ Data.List.map f xs)
        → (_≡_
            (Data.List.map f (x ∷ xs) ! (suc n))
            (Data.List.map f xs ! n))
      𝔦 x xs f n = refl
    mifix = Data.List.map f x
    ℓ : length x ≡ length mifix
    ℓ = tr $ DLP.length-map f x
    k₂ = mink k ℓ
    l : Σ (List B) $ λ l'
        → Σ (length mifix ≡ length l') $ λ ℓ
        → l' ! mink k₂ ℓ ≡ g (mifix ! k₂)
    l = ual mifix k₂ g
    p₂ = begin
      length x ≡⟨ tr $ DLP.length-map f x ⟩
      length (Data.List.map f x) ≡⟨ proj₁ $ proj₂ l ⟩
      length (proj₁ l) ∎
    p₃ = begin
      proj₁ l ! mink k p₂ ≡⟨ cong (_!_ $ proj₁ l) $ M k ℓ ℓ₂ xlulf ⟩
      proj₁ l ! mink k₂ (proj₁ $ proj₂ l) ≡⟨ proj₂ $ proj₂ l ⟩
      g (Data.List.map f x ! k₂) ≡⟨ cong g $ lum x f k ⟩
      g (f $ x ! k) ∎
      where
      -- .i xu fegli fa ko'a goi le velcki be
      -- la'o zoi. p₃ .zoi.  .i ko'a se pagbu
      -- zo'e je le velcki be la'oi .M.
      ℓ₂ = proj₁ $ proj₂ l
      xlulf = begin
        length x ≡⟨ ℓ ⟩
        length (Data.List.map f x) ≡⟨ ℓ₂ ⟩
        length (proj₁ l) ∎
      M : {l m n : ℕ}
        → (k : Fin l)
        → (v : l ≡ m)
        → (x : m ≡ n)
        → (xov : l ≡ n)
        → mink k xov ≡ mink (mink k v) x
      M k refl refl refl = refl
  x'' : Σ (List $ Character k') $ λ x'
        → Σ (length (GameData.haters q) ≡ length x') $ λ ℓ
        → _
  x'' = ualmap (GameData.haters q) kumbi'o lb! m
  q' = record {
    epicwin = GameData.epicwin q;
    rooms = k';
    haters = proj₁ x'';
    yourfloorisnowclean = bricon nu,iork kac kec {!!} iofink;
    player = record {
      forename = Character.forename p;
      surname = Character.surname p;
      nicknames = Character.nicknames p;
      room = mink (Character.room p) $ proj₁ $ proj₂ k'';
      inventory = Character.inventory p;
      wieldedct = Character.wieldedct p;
      yourfloorisnowclean = Character.yourfloorisnowclean p
      }
    }
    where
    p = GameData.player q
    kac = Data.List.map Room.cname $ GameData.rooms q
    kec = Data.List.map Room.cname k'
    iofink = GameData.yourfloorisnowclean q
    bricon : ∀ {a p} → {A : Set a}
           → (P : Pred (List A) p)
           → (l l' : List A)
           → l ≡ l'
           → P l
           → P l'
    bricon P l l' refl = id
  dus = proj₁ $ proj₂ k''
  dis = proj₁ $ proj₂ x''
  nyfin = f (inv lb) (inv lb') sl Item.cname $ cong inv $ proj₂ $ proj₂ x''
    where
    lb' = proj₁ x'' ! mink m (proj₁ $ proj₂ x'')
    inv = Character.inventory
    f : ∀ {a b} → {A : Set a} → {B : Set b}
      → (b c : List A) → (x : A) → (f : A → B) → x ∷ b ≡ c
      → map f c ≡ f x ∷ map f b
    f b c x g refl = refl
\end{code}

\chapter{le mu'oi glibau.\ high-level .glibau.}

\section{le fancu poi tu'a ke'a na rinka lo nu lo ctaipe be la'oi .\F{GameData}.\ cu na binxo pe'a ru'e}

\subsection{la'oi .\F{epicwin?}.}
ni'o ga jonai ga je tu'a la'o zoi.\ \B a .zoi.\ .indika le du'u jinga gi ga je la'o zoi.\ \B b .zoi.\ xatra ja co'e poi ke'a cusku pe'a ru'e le du'u jinga gi ko'a goi la'o zoi.\ \F{epicwin?} \B a .zoi. du la'o zoi.\ \B b , \B a .zoi.\ gi ko'a du la'oi .\F{nothing}.

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
          play = GameData.player q
          q' = λ r → record q {player = record play {room = r}}
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
          cnq = λ a b → Room.cname (proj₂ a) ≟ Room.cname b
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
  ... | (selpli ∷ []) = just $ wieldMsg , wieldData
    where
    wieldMsg = fromMaybe "You wield the weapon." xarcynotci
      where
      items = Character.inventory $ GameData.player dang
      xarci = Item.weapwn $ Data.List.lookup items $ proj₁ selpli
      xarcynotci = xarci Data.Maybe.>>= WeaponInfo.wieldMsg
    wieldData = record dang {player = pl}
      where
      d = "You wield the weapon."
      pl = record (GameData.player dang) {wieldedct = just selpli}
  ... | (_ ∷ _ ∷ _) = just $ m , dang
    where
    m = "Your query matches multiple items, although \
        \a proof of that your bag only contains items \
        \which have unique names exists.\n\
        \Something is mad fucked, and you might \
        \actually be innocent this time."
\end{code}
\end{document}
