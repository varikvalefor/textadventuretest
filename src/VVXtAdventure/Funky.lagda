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
\newunicodechar{ₜ}{\ensuremath{\mathnormal{_t}}}
\newunicodechar{ᵤ}{\ensuremath{\mathnormal{_u}}}
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
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^b}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{∸}{\ensuremath{\mathnormal{\divdot}}}
\newunicodechar{⍨}{\raisebox{-0.25ex}{$\ddot\sim$}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal{\ell}}}
\newunicodechar{∈}{\ensuremath{\mathnormal{\in}}}

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
    updateAt;
    length;
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
  mink : {c d : Data.Nat.ℕ} → Fin c → c ≡ d → Fin d
  mink a refl = a
  
  _⍨ = flip

takeHater : (q : GameData)
          → (m : Fin $ length $ GameData.haters q)
          → (n : Fin $ length $ GameData.itemsInRoomOf q m)
          → Σ GameData $ λ o
            → Σ (_≡_
                 (length $ GameData.rooms q)
                 (length $ GameData.rooms o)) $ λ r
            → Σ (_≡_
                 (length $ GameData.haters q)
                 (length $ GameData.haters o)) $ λ x
            → (_≡_
                (map Item.cname $ GameData.inventOf o $ mink m x)
                ((_∷_ ⍨)
                  (map Item.cname $ GameData.inventOf q m)
                  (Item.cname
                    $ GameData.itemsInRoomOf q m ! n)))
takeHater q m n = q' , dus , dis , nyfin
  where
  ual : ∀ {a} → {A : Set a}
      → (l : List A) → Fin $ length l → (A → A)
      → Σ (List A) $ _≡_ (length l) ∘ length
  ual (x ∷ xs) Fin.zero f = f x ∷ xs , refl
  ual (x ∷ xs) (Fin.suc n) f = x ∷ proj₁ (ual xs n f) , rif
    where
    rif = cong Data.Nat.suc $ proj₂ $ ual xs n f
  lb = GameData.haters q ! m
  sl = Room.items (GameData.rooms q ! Character.room lb) ! n
  k'' : Σ (List Room) $ _≡_ on length $ GameData.rooms q
  k'' = ual (GameData.rooms q) (Character.room lb) vimcu
    where
    nadu = Data.Bool._≟_ false ∘ _≡ᵇ_ (Item.cname sl) ∘ Item.cname
    vimcu = λ x → record x {items = filterₗ nadu $ Room.items x}
  k' = proj₁ k''
  nakalci : Character k'
  nakalci = record {
    forename = Character.forename p;
    surname = Character.surname p;
    nicknames = Character.nicknames p;
    room = mink (Character.room p) $ proj₂ k'';
    inventory = Character.inventory p;
    wieldedct = Character.wieldedct p;
    yourfloorisnowclean = Character.yourfloorisnowclean p
    }
    where
    p = GameData.player q
  x'' : Σ (List $ Character k') $ λ x'
        → length (GameData.haters q) ≡ length x'
  x'' = map₂ kibix $ ual (proj₁ ckic) (mink m $ proj₂ ckic) lb!
    where
    tr : ∀ {a} → {A : Set a} → {x y : A}
       → x ≡ y → y ≡ x
    tr refl = refl
    ualmap : ∀ {a} → {A B : Set a}
           → (x : List A)
           → (f : A → B)
           → (g : B → B)
           → (q : Fin $ length x)
           → (ℓ : length (Data.List.map f x) ≡ length x)
           → _≡_
               (length x)
               (length $ proj₁
                $ ual (Data.List.map f x) (mink q $ tr ℓ) g)
    ualmap x f g q e = step-≡ (Data.List.length x) n₁ (tr e)
      where
      n₁ = proj₂ $ ual (Data.List.map f x) (mink q $ tr e) g
      step-≡ = ≡-Reasoning.step-≡
    lb! : Character k' → Character k'
    lb! x = record x {
      inventory = sl ∷ Character.inventory x;
      wieldedct = Data.Maybe.map f $ Character.wieldedct x;
      yourfloorisnowclean = {!!}
      }
      where
      gimp : ∀ {a p} → {A : Set a}
           → (P : Pred A p)
           → (q : List A)
           → (n : Fin $ length q)
           → P $ q ! n
           → (x : A)
           → P $ (x ∷ q) ! (Fin.suc n)
      gimp P q n c x = fic P xₜ xₛ xᵤ c
        where
        xₜ = q ! n
        xₛ = (x ∷ q) ! (Fin.suc n)
        xᵤ : xₜ ≡ xₛ
        xᵤ = blax q n x
          where
          blax : ∀ {a} → {A : Set a}
               → (l : List A)
               → (n : Fin $ length l)
               → (x : A)
               → l ! n ≡ (x ∷ l) ! (Fin.suc n)
          blax l n x = {!!}
        fic : ∀ {a p} → {A : Set a}
            → (P : Pred A p)
            → (x y : A)
            → x ≡ y
            → P x
            → P y
        fic P x y d g = {!!}
      f = λ (l , k) → Fin.suc l , gimp isWeapon inv l k sl
        where
        isWeapon = _≡_ true ∘ is-just ∘ Item.weapwn
        inv = Character.inventory x
    kumbi'o = λ x → record {
      forename = Character.forename x;
      surname = Character.surname x;
      nicknames = Character.nicknames x;
      room = mink (Character.room x) $ proj₂ k'';
      inventory = Character.inventory x;
      wieldedct = Character.wieldedct x;
      yourfloorisnowclean = Character.yourfloorisnowclean x
      }
    ckic : Σ (List $ Character k') $ λ lex
           → length (GameData.haters q) ≡ length lex
    ckic = ck , ℓₘ
      where
      ck = Data.List.map kumbi'o $ GameData.haters q
      ℓₘ = tr $ DLP.length-map kumbi'o $ GameData.haters q
    kibix = ualmap {!!} kumbi'o lb! {!!}
  q' = record {
     epicwin = GameData.epicwin q;
     yourfloorisnowclean = {!!};
     player = nakalci;
     haters = proj₁ x'';
     rooms = k'
     }
  dus : length (GameData.rooms q) ≡ length k'
  dus = proj₂ k''
  dis : length (GameData.haters q) ≡ length (proj₁ x'')
  dis = proj₂ x''
  nyfin = {!!}
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
