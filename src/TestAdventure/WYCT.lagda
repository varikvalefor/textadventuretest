\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{selnolig}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\nolig{>>}{>|>}
\nolig{<<}{<|<}

\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_\AgdaFontStyle{i}}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_\AgdaFontStyle{o}}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\cmene{\texttt{WYCT}}

\title{la'o zoi.\ \cmene{}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o la'o zoi.\ \cmene{}\ .zoi.\ vasru le velcki be le kelci datni be le me'oi .default.\ ja me'oi .demo.\ ja co'e po la .tat.

\section{le me'oi .preamble.\ ja co'e}

\begin{code}
{-# OPTIONS --safe #-}

module TestAdventure.WYCT where

open import Data.Bool
  using (
    true;
    false
  )
open import Data.List
  using (
    List;
    _∷_;
    []
  )
open import Data.Maybe
  using (
    just;
    nothing
  )
open import Data.String
  using (
    String
  )
open import Data.Product
  using (
    _,_
  )
open import VVXtAdventure.Base
open import Relation.Binary.PropositionalEquality
  using (
    refl
  )

import Data.Fin
import Data.Rational as ℚ
\end{code}

\section{le ctaipe be la'oi .\AgdaRecord{Item}.}

\subsection{la'oi .\F{colorfun}.}
ni'o zo'oi .COLOUR.\ selneimau fi la .varik.\ldots jenai ku'i cu cmene le samselkei\ldots pe'a sai\ldots noi ke'a selcme zoi glibau.\ Color Fun .glibau.

\begin{code}
colorfun : Item
colorfun = record {
  name = "COLORFUN";
  cname = "COLORFUN";
  rmDescr = [];
  weapwn = nothing;
  smashInfo = nothing;
  yourfloorisnowclean = refl;
  hlDescr = m;
  dfDescr = m}
  where
  m = "It's blue.  IT'S GOD-DAMNED GREEN!"
\end{code}

\subsection{la'oi .\F{defstick}.}
ni'o grana fa ko'a goi la'oi .\F{defstick}.  .i ca lo nu tolsti kei ko'a selvau le me'oi .inventory.\ be le kelci ke xarpre ja co'e pe la'oi .TestAventure.

\begin{code}
defstick : Item
defstick = record {
  name = "SHITTY-ASS STICK";
  cname = "DEFSTICK";
  rmDescr = [];
  yourfloorisnowclean = refl;
  weapwn = just wi;
  smashInfo = nothing;
  dfDescr = "You see the stick which is dropped by you.";
  hlDescr = m}
  where
  wi = record {
    wieldMsg = just "You firmly grasp the stick."
    }
  m = "This stupid thing is a stick.  For whatever \
      \reason, you absolutely refuse to let go of \
      \this stick.  You insist that this stick shall \
      \SOMEDAY be useful.  But I'll be honest.  \
      \Everyone within a 100-yard radius doubts your \
      \inane claim... but welcomes that you \
      \demonstrate that we are wrong."
\end{code}

\subsection{la'oi .\F{macguffin}.}
ni'o la'oi .\F{macguffin}.\ me'oi .coupon. lo mu'oi glibau.\ leafblower .glibau.

\begin{code}
macguffin : Item
macguffin = record {
  name = "LEAFBLOWER COUPON";
  cname = "LEBLOCO";
  rmDescr = [];
  yourfloorisnowclean = refl;
  weapwn = nothing;
  smashInfo = nothing;
  dfDescr = "You see a coupon (for a leafblower) \
            \which is ludicrously detailed.";
  hlDescr = m}
  where
  m = "You hold a coupon for a \"super-bitchin' XL \
      \DAX and BLEXER High-Throughput Leafblower \
      \476.5: Beefcake Edition\".  Most prenu whom \
      \you know insist that the naming scheme is a \
      \bit ridiculous... but can still respect the \
      \perceived quality of DAX AND BLEXER's \
      \products.\n\n\
      \You find that this coupon is noteworthy \
      \partially because you suspect that the \
      \creators of the coupon probably wanted to \
      \create a brochure or something, as opposed \
      \to a simple coupon.\n\n\
      \Anyway, the full text of the coupon is as \
      \follows:\n\n\
      \Hey, asshole.  Are you sick of those leaves \
      \blowing onto the driveway of your awesome \
      \penthouse/dungeon/library combo resort?  \
      \Don't bother answering.  Here at DAX AND \
      \BLEXER, we can always successfully read \
      \minds 82.3745 PERCENT OF THE TIME.  We KNOW \
      \that you're sick of those punk-ass leaves, \
      \and, frankly, we're sick of those punk-ass \
      \leaves, as well.  The whole situation makes \
      \us at DAX and BLEXER want to spew chunks all \
      \over this pig sty.  That's why we're \
      \offering you the following SWEET-ASS \
      \OPPORTUNITY: You can get this SUPER-BITCHIN' \
      \DAX and BLEXER High-Throughput Leafblower \
      \476.5: Beefcake Edition... for only $3200.99\
      \!  We are offering you a discount of 79%.  \
      \This is the discount of a lifetime, man.  \
      \Half of the poor bastards who tested this \
      \ended up dead as a result of the sheer \
      \power, but we at DAX and BLEXER believe that \
      \you, sir, ma'am, or disembodied fish head, \
      \are capable of successfully wielding this \
      \fucking monster.\n\n\
      \COUPON ID: GEbAhcurrjPROix7inD6YmY4W0szXtB35v\
      \EJluAqHLDdPFJVIu3N23lQEzVPWv81FpRcq\n\n\
      \This paragraph marks the end of the \
      \transcription.  Some additional information \
      \follows.\n\n\
      \The upper-left portion of the coupon \
      \is a photograph whose subject is a sweating \
      \body-builder who is using a leafblower.  The \
      \brand name of the leafblower is conveniently \
      \obscured.\n\n\
      \Additionally, a cheesy \"word art\" pop-out \
      \star which reads \"HOLY SHIT!\" is placed on \
      \the right margin of the small coupon.  Lines \
      \which connect this star to the sequences \
      \\"82.3745\" and \"79%\" are drawn."
\end{code}

\section{le tolsti co'e}

\subsection{la'oi .\F{rooms}.}

\begin{code}
rooms : List Room
rooms = dingyliv ∷ dingycos ∷ []
  where
  dingycos : Room
  dingycos = record {
    name = "BROOM CLOSET";
    cname = "DINGYLIVCLST";
    travis = "DINGYLIVRM" ∷ [];
    items = [];
    velski = "This broom closet is attached to your \
             \living room.  The ceiling is low, the room \
             \has a low area, and the walls are not even \
             \parallel.  What fucking idiot builds a room \
             \which is this shit?"
    }
  dingyliv : Room
  dingyliv = record {
    name = "A DINGY LIVING ROOM";
    cname = "DINGYLIVRM";
    travis = "DINGYLIVCLST" ∷ [];
    items = lamp ∷ table ∷ colorfun ∷ [];
    velski = "This room marks the beginning of this \
             \part of your adventure.  The carpet \
             \could use a good cleaning, and that \
             \wallpaper is just rancid."}
    where
    table : Item
    table = record {
      name = "FLIMSY TABLE";
      cname = "DINGYLIVRMTBL";
      weapwn = nothing;
      smashInfo = nothing;
      rmDescr = ("DINGYLIVRM" , lvdsc) ∷ [];
      dfDescr = "You see a flimsy-looking table.";
      hlDescr = "For some reason, you remove (from \
                \your living room) this flimsy-\
                \looking table.  Possible is that \
                \excessive carrying causes the \
                \degradation of the table; this thing \
                \looks like a real piece.\n\n\
                \The copious amounts (of duct tape, \
                \glue, and string) are the result of \
                \compensation for potential damage \
                \which may be the result of \
                \potentially excessive partying and \
                \whatnot.  Hackathons can be wild.";
      yourfloorisnowclean = refl
      }
      where
      lvdsc = "A flimsy-looking table is in the middle \
              \of the room.  Glue, duct tape, and other \
              \go-to tools of kludgers are attached to \
              \the table."
    lamp : Item
    lamp = record {
      name = "LAMP";
      cname = "DINGYLIVRMLMP";
      weapwn = nothing;
      smashInfo = nothing;
      rmDescr = ("DINGYLIVRM" , lvdsc) ∷ [];
      dfDescr = "You see a lamp.";
      hlDescr = "You took (from the living room \
                \which marks the beginning of your \
                \adventure) this mediocre lamp.";
      yourfloorisnowclean = refl}
      where
      lvdsc = "A pretty mediocre-looking lamp is \
              \nearby."
\end{code}

\subsection{la'oi .\F{winmsg}.}

\begin{code}
winmsg : String
winmsg = "YOU HAVE ACCOMPLISHED\n\
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

\end{code}

\subsection{la'oi .\F{initialD}.}

\begin{code}
initialD : GameData
initialD = record {
  rooms = rooms;
  epicwin = false;
  haters = kelci ∷ [];
  player' = Data.Fin.zero;
  yourfloorisnowclean = refl}
  where
  kelci = record {
    forename = "HARRIET";
    surname = "TUBMANN";
    cname = "XITAS";
    nicknames = "THE O.G. MEATBALL" ∷ [];
    health = ℚ.1ℚ;
    room = Data.Fin.zero;
    inventory = defstick ∷ [];
    wieldedct = nothing;
    yourfloorisnowclean = refl}
\end{code}
\end{document}
