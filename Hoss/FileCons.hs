{-# LANGUAGE CPP, ScopedTypeVariables #-}

module FileCons (Cons, openHandle, closeHandle, newCons, newInt, newStr, isInt, isStr, isPair, first, second, setFirst, setSecond, int, str, getPtr, list, toList, nth, shw, followPtr, cmpr, cmpr2, dlookup, lookupSingle, dinsert, deleteFindMin, deleteFindMax, delete, traverse, depth, size) where

import System.IO.Unsafe
import Control.Monad
import Data.Bits
import Data.Char
import Data.Word
import Foreign.Ptr
import Foreign.Storable
import Data.IORef
import System.IO
import Control.Exception
import System.IO.MMap
import Data.String.UTF8 (toRep, fromRep, toString, fromString)
import Prelude hiding (catch)

-- This module stores a single value in a file. The value is a tree structure like Lisp's
-- conses. The value in the file can be changed while sharing structure with values
-- that were once in the file.

data Cons = Cons !FilePath !(IORef (Ptr Int, Int, Int)) !Int deriving Eq

toUTF :: String -> [Word8]
toUTF = toRep . fromString

fromUTF :: [Word8] -> String
fromUTF = toString . fromRep

openHandle path = do
	fl <- openBinaryFile path ReadWriteMode
	hClose fl
	(p, sz, _, _) <- mmapFilePtr path ReadWrite Nothing
	ref <- newIORef (p, sz, sz)
	let cons = Cons path ref 0
	when (sz == 0) $ newCons (newInt cons 0) (newInt cons 0) `seq` return ()
	return cons

closeHandle (Cons path ref _) = do
	(p, used, sz) <- readIORef ref
	munmapFilePtr p sz
	fl <- openBinaryFile path ReadWriteMode
	hSetFileSize fl (toInteger used)
	hClose fl

makeSpace (Cons path ref _) n = do
	(p, used, sz) <- readIORef ref
	(p, sz) <- if used + n > sz then do
			munmapFilePtr p sz
			(p, sz, _, _) <- mmapFilePtr path ReadWriteEx (Just (0, sz + 10000))
			return (p, sz)
		else
			return (p, sz)
	writeIORef ref (p, used + n, sz)
	return (p, used)

-- Functions for building and taking apart values.

newCons cons@(Cons path ref i) (Cons path2 _ j)
#ifdef DEBUG
	| path /= path2	= error "newCons: have to come from same file"
#endif
	| otherwise	= unsafePerformIO $ do
		(p, used) <- makeSpace cons 8
		poke (p `plusPtr` used) i
		poke (p `plusPtr` (used + 4)) j
		return $! Cons path ref used
{-# INLINE newCons #-}

newInt cons@(Cons path ref _) n = Cons path ref (-(n + 1))
{-# INLINE newInt #-}

newStr cons@(Cons path ref _) s = unsafePerformIO $ do
	(p, used) <- makeSpace cons (length s + 5)
	poke (p `plusPtr` used) (4 :: Int)
	let
		loop p (x:xs) = do
			poke p x
			loop (p `plusPtr` 1) xs
		loop p [] = poke p 0
	loop (castPtr $ p `plusPtr` (used + 4) :: Ptr Word8) (map fromIntegral (toUTF s))
	return $! Cons path ref used

isInt (Cons _ _ i) = i < 0
{-# INLINE isInt #-}

isStr (Cons _ ref i) = unsafePerformIO $ do
	(p, _, _) <- readIORef ref
	n <- peek (p `plusPtr` i)
	return (n == (4 :: Int))
{-# INLINE isStr #-}

isPair c = not (isInt c || isStr c)
{-# INLINE isPair #-}

first c@(Cons path ref i)
#ifdef DEBUG
	| not (isPair c)	= do
		s <- shw c
		error $ "first: not a pair: " ++ s
#endif
	| otherwise	= do
		(p, _, _) <- readIORef ref
		n <- peek (p `plusPtr` i)
		return $! Cons path ref n
{-# INLINE first #-}

second c@(Cons path ref i)
#ifdef DEBUG
	| not (isPair c)	= do
		s <- shw c
		error $ "second: not a pair: " ++ s
#endif
	| otherwise	= do
		(p, _, _) <- readIORef ref
		n <- peek (p `plusPtr` (i + 4))
		return $! Cons path ref n
{-# INLINE second #-}

int c@(Cons _ _ i)
#ifdef DEBUG
	| i >= 0	= error $ "int: not an int: " ++ unsafePerformIO (shw c)
#endif
	| otherwise	= -(i + 1)

str c@(Cons _ ref i)
#ifdef DEBUG
	| not (isStr c)	= do
		s <- shw c
		error $ "str: not an str: " ++ s
#endif
	| otherwise	= do
		(p, _, _) <- readIORef ref
		let loop p acc = do
			c <- peek p
			if c == 0 then
				return (reverse acc)
			else
				loop (p `plusPtr` 1) (c : acc)
		liftM (fromUTF . map fromIntegral) $ loop (castPtr $ p `plusPtr` (i + 4) :: Ptr Word8) []
{-# INLINE str #-}

getPtr (Cons _ _ i) = i
{-# INLINE getPtr #-}

setFirst c@(Cons path ref i) (Cons path2 _ j)
#ifdef DEBUG
	| not (isPair c)	= do
		s <- str c
		error $ "setFirst: not a pair: " ++ show s
	| path /= path2	= error "setFirst: have to come from same file"
#endif
	| otherwise	= do
		(p, used, _) <- readIORef ref
		poke (p `plusPtr` i) j
{-# INLINE setFirst #-}

setSecond c@(Cons path ref i) (Cons path2 _ j)
#ifdef DEBUG
	| not (isPair c)	= do
		s <- str c
		error $ "setSecond: not a pair: " ++ show s
	| path /= path2	= error "setSecond: have to come from same file"
#endif
	| otherwise	= do
		(p, used, _) <- readIORef ref
		poke (p `plusPtr` (i + 4)) j
{-# INLINE setSecond #-}

list [x] = newCons x (newInt x 0)
list (x:xs) = newCons x (list xs)

toList = rec [] where
	rec acc cons = if isPair cons then
		do
		x <- first cons
		s <- second cons
		rec (x : acc) s
		else
			return (reverse acc)

nth 0 cons = first cons
nth n cons = second cons >>= nth (n - 1)
{-# INLINE nth #-}

shw cons = if isInt cons then
		return (show (int cons))
	else if isStr cons then
		liftM show (str cons)
	else do
		f <- first cons >>= shw
		s <- second cons >>= shw
		return $ "Cons (" ++ f ++ ") (" ++ s ++ ")"

-- Pointers between files

createPtr c (Cons path _ i) = newCons (newStr c path) (newInt c i)

followPtr cons = do
	f <- first cons
	s <- second cons
	path <- str f
	Cons _ ref _ <- openHandle path
#ifdef DEBUG
	(_, used, _) <- readIORef ref
	when (int s >= used) $ error "followPtr: bad ptr"
#endif
	return $! Cons path ref $ int s

-- Dictionary operations, adapted from Data.Map

cmpr s c = liftM (compare s) (str c)

cmpr2 c c2 = liftM2 compare (str c) (str c2)

dlookup cmp k k2 t
	| isPair t	= do
		f <- first t
		val <- nth 1 t
		ord <- cmp k f
		case ord of
			LT -> do
				v2 <- nth 2 t >>= dlookup cmp k k2
				ord2 <- cmp k2 f
				case ord2 of
					LT -> return v2
					EQ -> return $ v2 ++ [val]
					GT -> liftM (\v3 -> v2 ++ val : v3) (nth 3 t >>= dlookup cmp k k2)
			EQ -> do
				ord2 <- cmp k2 f
				case ord2 of
					LT -> return []
					EQ -> return [val]
					GT -> liftM (val:) (nth 3 t >>= dlookup cmp k k2)
			GT -> nth 3 t >>= dlookup cmp k k2
	| otherwise	= return []

lookupSingle cmp k t = do
	referent <- first t
	if isPair referent then
		do
		f <- first referent
		ord <- cmp k f
		case ord of
			LT -> second referent >>= second >>= lookupSingle cmp k
			EQ -> return t 
			GT -> second referent >>= second >>= second >>= lookupSingle cmp k
		else
			return t

dinsert cmp kx x t = do
	referent <- first t
	if isPair referent then do	
		val <- first referent
		ord <- cmp kx val
		case ord of
			LT -> second referent >>= second >>= dinsert cmp kx x
			GT -> second referent >>= second >>= second >>= dinsert cmp kx x
			EQ -> do
				second referent >>= \s -> setFirst s x
	else
		setFirst t (list [kx, x, newInt x 0, newInt x 0])

deleteFindMin t = do
	l <- first t >>= second >>= second
	r <- first t >>= second >>= second >>= second
	fl <- first l
	fr <- first r
	if isPair fl then
			deleteFindMin l
		else do
			k <- first t >>= first
			x <- first t >>= second >>= first
			setFirst t fr
			return (k, x)

deleteFindMax t = do
	l <- first t >>= second >>= second
	r <- first t >>= second >>= second >>= second
	fl <- first l
	fr <- first r
	if isPair fr then
			deleteFindMax r
		else do
			k <- first t >>= first
			x <- first t >>= second >>= first
			setFirst t fl
			return (k, x)

delete cmpr k t = do
	referent <- first t
	when (isPair referent) $ do
	l <- second referent >>= second
	r <- second referent >>= second >>= second
	fl <- first l
	fr <- first r
	k2 <- first referent
	val <- first referent >>= second
	ord <- cmpr k k2
	case ord of
		LT -> delete cmpr k l
		GT -> delete cmpr k r
		EQ -> if isPair fl then do
				(k, x) <- deleteFindMax l
				setFirst referent k
				setFirst val x
			else if isPair fr then do
				(k, x) <- deleteFindMin r
				setFirst referent k
				setFirst val x
			else
				setFirst t (newInt t 0)

traverse f t = when (isPair t) $ do
	nth 2 t >>= traverse f
	k <- nth 0 t
	v <- nth 1 t
	f k v
	nth 3 t >>= traverse f

depth idx = if isPair idx then
	liftM2 (\x y -> 1 + max x y) (nth 2 idx >>= depth) (nth 3 idx >>= depth)
	else
	return 0

size idx = if isPair idx then
	liftM2 (+) (nth 2 idx >>= size) (nth 3 idx >>= size)
	else
	return 1

