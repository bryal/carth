module Front.Literate (untangleOrg) where

import Data.Char
import Data.List

untangleOrg :: String -> String
untangleOrg s = unlines (untangleOrg' False (lines s))
  where
    untangleOrg' inSrc = \case
        [] -> []
        x : xs -> if inSrc
            then if endSrc x then "" : untangleOrg' False xs else x : untangleOrg' True xs
            else "" : untangleOrg' (beginSrc x) xs

beginSrc :: String -> Bool
beginSrc l =
    let ws = words l
    in  (length ws >= 2)
            && (map toLower (head ws) == "#+begin_src")
            && (ws !! 1 == "carth")
            && case elemIndex ":tangle" ws of
                   Just i -> length ws >= i + 2 && ws !! (i + 1) == "yes"
                   Nothing -> True

endSrc :: String -> Bool
endSrc = (\ws -> null ws && map toLower (head ws) == "#+end_src") . words
