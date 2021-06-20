module TestAdventure.Messages.Death where

-- | mDeathSpontComb is the message which is printed to the terminal if
-- the player character spontaneously combusts.
spontComb :: String;
spontComb = "You spontaneously combust, thereby losing the game and making yourself look like a bit of a jack-ass in the process."

-- | answerAff is output if the player answers a nonexistent question in
-- the affirmative.
answerAff :: String;
answerAff ="You answer no one in the affirmative.\nNo one responds with a swift punch to the sternum.\n\"Gah!\"\nYou collapse to the ground, slowly melting into cheese.\nJust before dying, you awaken from your wack-ass dream and remember that you are actually the great BRIAN W. KERNIGHAN.";

-- | winMsg is printed to the terminal iff the player wins the "game".
winMsg :: String;
winMsg = "YOU HAVE ACCOMPLISHED\nTHE MISSION.\nYOU ARE THE VERY PREVAILER\nTHAT PROTECT RIGHT\nAND JUSTICE.\nI WOULD EXPRESS MY SINCERE.\nTHANKS TO YOU.\n\nTAKE GOOD REST !\n\n\tGENERAL KAWASAKI";

-- | standard is printed to the terminal if the player dies for some
-- lame-ass reason.
standard :: String;
standard = "Aw, you dead.";
