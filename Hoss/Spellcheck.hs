module Spellcheck (createMap, cleanUpWord, spellcheck) where

import Data.List (inits, tails, nub, dropWhile)
import Data.Char
import FileCons
import Data.Maybe
import System.IO
import Data.Binary
import Control.Monad
import System.Random.Shuffle
import Prelude hiding (lookup)

-- This uses a technique described in http://blog.faroo.com/2012/06/07/improved-edit-distance-based-spelling-correction/
-- Word list taken from http://www-01.sil.org/linguistics/wordlists/english/

deletions s = zipWith (++) (inits s) (tail (tails s))

wordsEn = liftM lines (readFile "wordsEn.txt")

twoLevelDeletions s = s : deletions s ++ concat (zipWith (\s2 -> map (s2 ++)) (inits s) (map deletions (tail (tails s))))

createMap :: [String] -> IO ()
createMap words = do
	hdl <- openHandle "words.dat"
	shuffled <- shuffleM words
	mapM_ (\s -> let s' = newStr hdl s in
		mapM_ (\s2 -> do
			cons <- lookupSingle cmpr s2 hdl
			referent <- first cons
			when (isInt referent) $ setFirst cons $ list [newStr hdl s2, newInt hdl 0, newInt hdl 0, newInt hdl 0]
			referent <- first cons
			kcons <- second referent
			ls <- first kcons
			setFirst kcons $ newCons s' ls) $ twoLevelDeletions s) shuffled
	closeHandle hdl

dropEllipsis ('.':'.':'.':s) = s
dropEllipsis s = s

cleanUpWord = map toLower . reverse . dropWhile isPunctuation . reverse . dropEllipsis . tail

spellcheck :: String -> IO [String]
spellcheck word = if isDigit (head word) then
	return [word]
	else do
	hdl <- openHandle "words.dat"
	result <- liftM (nub . concat) $ mapM (\s -> do
		cons <- lookupSingle cmpr s hdl >>= first
		if isInt cons then
				return []
			else
				nth 1 cons >>= toList >>= mapM str) $ twoLevelDeletions word
	closeHandle hdl
	return result
