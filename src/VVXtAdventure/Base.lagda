\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{≡}{\ensuremath{\mathnormal{\equiv}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{∈}{\ensuremath{\mathnormal{\in}}}
\newunicodechar{∃}{\ensuremath{\mathnormal{\exists}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\cmene{VVXtAdventure.Base}

\title{la'o zoi.\ \texttt{\cmene}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.\ ja co'e}
ni'o la'o zoi.\ \texttt{\cmene}\ .zoi.\ vasru le velcki be vu'oi le me'oi .\AgdaKeyword{record}.\ je zo'e vu'o poi ke'a vajni la .tat.\ je poi mutce lo ka ce'u pilno ke'a

\section{le me'oi .preamble.\ ja co'e}

\begin{code}
{-# OPTIONS --safe #-}

module VVXtAdventure.Base where

open import Data.Fin
  using (
    Fin
  )
open import Function
  using (
    _$_;
    _∘_
  )
open import Data.Bool
  using (
    Bool;
    true
  )
open import Data.List
  using (
    lookup;
    List;
    _∷_;
    []
  )
open import Data.Maybe
  using (
    Maybe;
    nothing;
    just;
    is-just
  )
open import Data.String
  using (
    String
  )
open import Data.Product
  using (
    proj₁;
    _×_;
    ∃;
    Σ
  )
open import Truthbrary.Record.Eq
  using (
  )
open import Truthbrary.Record.LLC
  using (
    nu,iork;
    _∈_
  )
open import Relation.Binary.PropositionalEquality
  using (
    refl;
    _≡_
  )
\end{code}

\section{le me'oi .\AgdaKeyword{record}.}

\subsection{la'oi .\F{WeaponInfo}.}
ni'o ga jo la'o zoi.\ \B a .zoi.\ srana lo selsnu be ko'a goi lo ctaipe be la'oi .\F{Item}.\ gi\ldots
\begin{itemize}
	\item ga jo la'o zoi.\ \F{WeaponInfo.wieldMsg} \B a .zoi.\ du la'o zoi.\ \F{just} \B b .zoi.\ gi cadga fa lo nu cusku la'o zoi.\ \B b .zoi.\ ca lo nu lo kelci ke xarpre ja co'e cu binxo lo me'oi .wield.\ be ko'a
\end{itemize}

\begin{code}
record WeaponInfo : Set
  where
  field
    wieldMsg : Maybe String
\end{code}

\subsection{la'oi .\F{Item}.}

ni'o ga jo ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'oi .\F{Item}.\ gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \F{Item.name} \B a .zoi.\ mu'oi glibau.\ display name .glibau.\ ko'a gi
	\item ga je ga je ko'e goi la'o zoi.\ \F{Item.cname} \B a .zoi.\ cmene ko'a gi cadga fa lo nu lo kelci cu pilno ko'e tu'a ko'a gi
        \item ga je ga jonai ga je ko'a sinxa lo me'oi .weapon.\ gi ko'e goi la'o zoi.\ \F{weapwn} \B a .zoi.\ me'oi .\F{just}.\ lo velski be ko'a gi ko'e du la'oi .\F{nothing}.\ gi
	\item cadga fa lo nu ga naja ga je lo kelci cu cpedu lo nu skicu lo selsni be ko'a gi curmi lo nu skicu lo selsni be ko'a gi\ldots
	\begin{itemize}
		\item ga jonai ga je lo me'oi .inventory.\ be lo kelci xarpre ja co'e cu vasru lo selsni be ko'a gi pilno la'o zoi.\ \F{hlDescr} \B a .zoi.\ gi
		\item ga jonai ga je ga je cpedu lo nu skicu kei ca lo nu lo kelci xarpre ja co'e cu zvati zo'e poi la'o zoi.\ \B C .zoi.\ mu'oi glibau.\ \F{Room.cname} .glibau.\ lo sinxa be ke'a gi la'o zoi.\ \F{rmDescr} \B a .zoi.\ vasru la'o zoi.\ \B C \Sym , \B d .zoi.\ gi pilno la'o zoi.\ \B d .zoi.\ gi
		\item pilno la'o zoi.\ \F{dfDescr} \B a .zoi.
	\end{itemize}
\end{itemize}

.i la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la'o zoi.\ \F{Item.yourfloorisnowclean} .zoi.\ bau la .lojban.

\begin{code}
record Item : Set
  where
  field
    name : String
    cname : String
    weapwn : Maybe WeaponInfo
    rmDescr : List $ String × String
    dfDescr : String
    hlDescr : String
    yourfloorisnowclean : nu,iork $ Data.List.map proj₁ rmDescr
\end{code}

\subsection{la'oi .\F{Room}.}
ni'o ga jo la'o zoi.\ \B S .zoi.\ fa'u ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'oi .\F{Set}.\ fa'u la'o zoi.\ \F{Room} \B S .zoi.\ gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \F{Room.name} \B a .zoi.\ cmene lo selsni be ko'a gi
	\item ga je cadga fa lo nu lo kelci cu pilno la'o zoi.\ \F{Room.cname} \B a .zoi.\ tu'a ko'a gi
        \item ga je ga jo curmi lo nu sampu klama lo selsni be ko'a lo selsni be la'o zoi.\ \B q .zoi.\ gi la'o zoi.\ \F{Room.travis} \B a .zoi.\ vasru lo mu'oi glibau.\ \F{Room.cname}\ .glibau.\ be la'o zoi.\ \B q .zoi.\ gi
	\item la'o zoi.\ \F{Room.items} \B a .zoi.\ liste lo'i selvau be lo selsni be ko'a be'o poi ke'a ba'e na prenu
\end{itemize}

\begin{code}
record Room : Set
  where
  inductive
  field
    name : String
    cname : String
    items : List Item
    travis : List String
\end{code}

\subsection{la'oi .\F{Character}.}
ni'o ga jo la'o zoi.\ \B K .zoi.\ ctaipe la'o zoi.\ \F{List} \F{Room} .zoi.\ gi la'o zoi.\ \F{Character} \B K .zoi.\ se ctaipe lo sinxa be lo xarpre ja co'e

.i ga jo la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \F{Character} \B q .zoi.\ gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \F{Character.forename} \B a .zoi.\ du'acme ko'a goi lo selsni be la'o zoi.\ \B a .zoi.\ gi
	\item ga je la'o zoi.\ \F{Character.surname} \B a .zoi.\ lazme'e ko'a gi
	\item ga je la'o zoi.\ \F{Character.cname} \B a .zoi.\ du lo cmene be ko'a be'o poi cadga fa lo nu lo kelci cu pilno ke'a tu'a ko'a gi
	\item ga je la'o zoi.\ \F{Character.nicknames} \B a .zoi.\ liste lo'i datcme be ko'a gi
	\item ga je tu'a la'o zoi.\ \B a .zoi.\ .indika lo du'u ko'a zvati lo selsni be la'o zoi.\ \F{lookup} \B q \F \$ \F{Character.room} \B a .zoi.\ gi
	\item ga je la'o zoi.\ \F{Character.inventory} \B a .zoi.\ liste lo'i ro se ralte be lo selsni be ko'a gi
        \item ga naja la'o zoi.\ \B i .zoi.\ du la'o zoi.\ \F{Character.inventory} \B a .zoi.\footnote{ni'o pilno zo'e pe zo du mu'i le su'u djica lo nu lo me'oi .hbox.\ cu na me'oi .overfull.}\ gi la'o zoi.\ \F{Data.Maybe.map} (\F{lookup} \B i) \Sym \$ \F{Character.wielded} \B a .zoi.\ du la'oi .\F{nothing}.\ jonai cu me'oi .\F{just}.\ lo sinxa be lo se me'oi .wield.\ be ko'a
\end{itemize}

.i la .varik.\ cu na jinvi le du'u sarcu fa lo nu jmina lo .lojban.\ velcki be la'o zoi.\ \F{Character.yourfloorisnowclean} .zoi.

\begin{code}
record Character (q : List Room) : Set
  where
  private
    isWeapon = _≡_ true ∘ is-just ∘ Item.weapwn
  field
    forename : String
    surname : String
    cname : String
    nicknames : List String
    room : Fin $ Data.List.length q
    inventory : List Item
    wieldedct : Maybe $ ∃ $ isWeapon ∘ lookup inventory
    yourfloorisnowclean : nu,iork $ Data.List.map Item.cname inventory
  wielded = Data.Maybe.map proj₁ wieldedct
\end{code}

\subsection{la'oi .\F{GameData}.}
ni'o ga jo ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'oi .\F{GameData} .zoi.\ gi\ldots
\begin{itemize}
        \item ga je ga jo la'o zoi.\ \F{GameData.epicwin} \B a .zoi.\ du la'oi .\F{true}.\ gi ga je le kelci cu jinga gi le selkei cu mulno ja co'e gi
        \item ga je la'o zoi.\ \F{GameData.rooms} \B a .zoi.\ liste lo'i velski be lo'i co'e poi cumki fa lo nu zvati ke'a gi
        \item ga je la'o zoi.\ \F{GameData.haters} \B a .zoi.\ liste lo'i sinxa be lo'i xarpre ja co'e po ko'a gi
        \item la'o zoi.\ \F{Data.List.lookup} (\F{GameData.xebni} \B a) \Sym \$ \F{GameData.player} \B a .zoi.\ velski lo kelci ke xarpre ja co'e po ko'a gi
        \end{itemize}

.i la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la'o zoi.\ \F{GameData.yourfloorisnowclean}\ .zoi.\ bau la .lojban.

\begin{code}
record GameData : Set
  where
  field
    epicwin : Bool
    rooms : List Room
    haters : List $ Character rooms
    player' : Fin $ Data.List.length haters
    yourfloorisnowclean : nu,iork $ Data.List.map Room.cname rooms
  player = Data.List.lookup haters player'
\end{code}

\section{le sampu}

\subsection{la'oi .\F{COut}.}

ni'o ro da poi ke'a midnoi ja co'e zo'u ga jonai ga je lo se pruce cu mapti da gi da me'oi .\F{just}.\ pruce fi lo ctaipe be la'o zoi.\ \F{String} \Sym × \F{GameData} .zoi.\ be'o noi cagda fa lo nu ciska lo se .orsi be ke'a lo mu'oi glibau.\ standard output .glibau.\ kei je lo nu me'oi .\F{main}.\ pilno lo te .orsi be ke'a gi da du la'oi .\F{nothing}.

.i la'oi .\F{COut}.\ na mutce lo ka ce'u smimlu fo la .varik.\ fe la'oi .\texttt{cout}.\ po la'o zoi.\ C++ .zoi.

\begin{code}
COut = Maybe $ String × GameData
\end{code}

\subsection{la'oi .\F{Com}.}

ni'o la'oi .\F{Com}.\ se ctaipe lo so'i midnoi fancu pe la .tat.

.i ga naja ko'a goi lo kelci cu mu'oi glibau.\ standard input .glibau.\ samci'a la'o zoi.\ \B g .zoi.\ gi lakne fa lo nu cadga fa lo nu ga je lo ctaipe be la'o zoi.\ \F{List String} .zoi.\ cu du la'o zoi.\ \F{words} \B g .zoi.\  gi lo ctaipe be la'oi .\F{GameData}.\ cu velcki lo selkei be ko'a

\begin{code}
Com = List String → GameData → COut
\end{code}
\end{document}
