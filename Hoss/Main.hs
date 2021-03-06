{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import Graphics.Layout
import Graphics.Win32
import System.Win32.DLL
import System.Win32.Mem
import System.IO.Unsafe
import System.Exit
import Data.ByteString.Unsafe
import qualified Data.ByteString as SB
import qualified Data.ByteString.Lazy as LB
import Control.Arrow
import Data.IORef
import Data.Char
import Data.List (find, transpose, findIndex)
import Data.Int
import Data.Bits
import Data.Array (Ix(..))
import Data.Maybe
import Control.Monad
import Graphics.Layout
import Graphics.Displayable hiding (Selection, selection)
import Graphics.FrameWindow
import Graphics.Print
import Graphics.Win32Extras
import Unsafe.Coerce
import Control.Exception
import Codec.BMP
import Data.Binary hiding (Word)
import Foreign.Marshal.Utils
import Foreign.Ptr
import Foreign.Storable
import System.FilePath.Windows
import Control.Monad.Identity

import Test.QuickCheck
import Test.QuickCheck.Gen
import System.Random

-- Invariants: Each paragraph ends with a word containing the empty string.
-- Every other word starts with a space. At least one element in the document
-- should have either a caret or selection. There should be only one caret.
-- The caret or selection should be at the head of aft.

type Zipper t = ([Paragraph t], Just, [(t, Floated)], [(t, Floated)], [Paragraph t])

data Selection = Unselected | Selected | Caret deriving (Eq, Show)

data Word = Word {
	font :: String,
	size :: Int32,
	color :: COLORREF,
	bold :: Bool,
	italic :: Bool,
	underline :: Bool,
	string :: String } deriving Eq

type Table = [(Int32, [[Paragraph Object]])]

data Link = Link { path :: String, linkObj :: BMP } deriving Show

data Object = Object {
	position :: Int,
	selection :: Selection,
	obj :: Either Word (Either Table Link),
	mousedown :: (Int32, Int32) -> (Int32, Int32) -> Object -> IO (),
	mousemove :: (Int32, Int32) -> (Int32, Int32) -> Object -> IO (),
	mouseup :: IO () }

data Command = Insert Int [Paragraph Object] | Delete Int Int | Alter Int String | InTable Int Int Int Command | NewCol Int Int (Int32, [[Paragraph Object]]) | NewRow Int Int [[Paragraph Object]] | DelCol Int Int | DelRow Int Int deriving Show

instance Binary Word where
	put (Word font size clr bold italic underline string) = do
		put font
		put size
		put clr
		put bold
		put italic
		put underline
		put string
	get = do
		font <- get
		size <- get
		color <- get
		bold <- get
		italic <- get
		underline <- get
		string <- get
		return $ Word font size color bold italic underline string

instance Binary Link where
	put (Link path _) = put path
	get = do
		path <- get
		return (Link path undefined)

instance Binary Object where
	put (Object _ _ obj _ _ _) = put obj
	get = do
		obj <- get
		return (Object undefined Unselected obj undefined undefined undefined)

instance Binary Just where
	put L = put (0 :: Word8)
	put Center = put (1 :: Word8)
	put R = put (2 :: Word8)
	put Justified = put (3 :: Word8)
	get = do
		(n :: Word8) <- get
		return $ case n of
			0 -> L
			1 -> Center
			2 -> R
			3 -> Justified

instance Binary Floated where
	put Inline = put (0 :: Word8)
	put FloatLeft = put (1 :: Word8)
	put FloatRight = put (2 :: Word8)
	get = do
		(n :: Word8) <- get
		return $ case n of
			0 -> Inline
			1 -> FloatLeft
			2 -> FloatRight

instance Binary Command where
	put (Insert n ls) = do
		put (0 :: Word8)
		put n
		put ls
	put (Delete n m) = do
		put (1 :: Word8)
		put n
		put m
	put (Alter n str) = do
		put (2 :: Word8)
		put n
		put str
	put (InTable n col row cmd) = do
		put (3 :: Word8)
		put n
		put col
		put row
		put cmd
	put (NewCol n m para) = do
		put (4 :: Word8)
		put n
		put m
		put para
	put (NewRow n m para) = do
		put (5 :: Word8)
		put n
		put m
		put para
	put (DelCol n m) = do
		put (6 :: Word8)
		put n
		put m
	put (DelRow n m) = do
		put (7 :: Word8)
		put n
		put m
	get = do
		(i :: Word8) <- get
		case i of
			0 -> liftM2 Insert get get
			1 -> liftM2 Delete get get
			2 -> liftM2 Alter get get
			3 -> liftM4 InTable get get get get
			4 -> liftM3 NewCol get get get
			5 -> liftM3 NewRow get get get
			6 -> liftM2 DelCol get get
			7 -> liftM2 DelRow get get

invertDelete n m zip = Insert n $ inv $ if null aft then aftBig else (L, aft) : aftBig where
	(_, _, _, aft, aftBig) = goto n zip
	inv ((just, ls):xs) = if m < position (fst (head ls)) then
			[]
		else
			(just, takeWhile ((<m) . position . fst) ls) : inv xs
	inv [] = []

changeAt n f ls = take n ls ++ f (ls !! n) : drop (n + 1) ls

invert (Insert n ls) _ = Delete n (n + length (concatMap snd ls))
invert (Delete n m) textVal = invertDelete n m textVal
invert (Alter n _) textVal = Alter n (let Left wrd = obj (fst (headI bef)) in string wrd) where
	(_, _, bef, _, _) = goto n textVal
invert (InTable n col row cmd) textVal = InTable n col row $ invert cmd $ toZipper $ snd ((let Right (Left tbl) = obj (fst (toView textVal !! n)) in tbl) !! col) !! row
invert (NewCol n m _) _ = DelCol n m
invert (NewRow n m _) _ = DelRow n m
invert (DelCol n m) textVal = NewCol n m $ let Right (Left contents) = obj (fst (toView textVal !! n)) in second (map clearSelection0) $ contents !! m
invert (DelRow n m) textVal = NewRow n m $ let Right (Left contents) = obj (fst (toView textVal !! n)) in map clearSelection0 $ transpose (map snd contents) !! m

perform (Insert n ls) textVal = renumber $ insert ls (goto n textVal)
perform (Delete n m) textVal = renumber $ delete m (goto n textVal)
perform (Alter n s) textVal = alterBef n (\(Left x) -> Left $ x { string = s }) textVal
perform (InTable n col row cmd) textVal = alter n (\(Right (Left contents)) -> Right $ Left $ changeAt col (second $ changeAt row $ fromZipper . perform cmd . toZipper) contents) textVal
perform (NewCol n m paras) textVal = alter n (\x -> let Right (Left contents) = x in
	Right $ Left $ take m contents ++ second (take (length $ snd $ head contents)) paras : drop m contents)
	textVal
perform (NewRow n m paras) textVal = alter n (\x -> let Right (Left contents) = x in
	Right $ Left $ map (\(i, pr) -> second (\x -> take m x ++ paras !! i : drop m x) pr) (zip [0..] contents))
	textVal
perform (DelCol n m) textVal = alter n (\x -> let Right (Left contents) = x in
	Right $ Left $ take m contents ++ drop (m + 1) contents) textVal
perform (DelRow n m) textVal = alter n (\x -> let Right (Left contents) = x in
	Right $ Left $ map (second $ \ls -> take m ls ++ drop (m + 1) ls) contents) textVal

createAFont dc font size bold italic underline = createFont (size * 96 `div` 72) 0 0 0 (if bold then fW_BOLD else fW_NORMAL) italic underline False dEFAULT_CHARSET oUT_DEFAULT_PRECIS cLIP_DEFAULT_PRECIS dEFAULT_QUALITY fF_DONTCARE font

drawCaret dc (x, y) obj@(Object _ selected _ _ _ _) = when (selected == Caret) $ do
	let (wd, ht) = flowMeasure obj
	moveToEx dc x y
	lineTo dc x (y + ht)

drawBorder dc pr obj selected = when (selected == Selected) $ do
	pen <- createPen pS_SOLID 5 0
	oldPen <- selectPen dc pen
	brush <- getStockBrush nULL_BRUSH
	oldBrush <- selectBrush dc brush
	rectangle dc (fst pr) (snd pr) (fst pr + width obj) (snd pr + height obj)
	selectBrush dc oldBrush
	selectPen dc oldPen
	deletePen pen

withCells (xPos, yPos) tbl f = foldM_ (\y (rowN, row) -> do
	let ht = maximum (map (\(col, cell) -> measureCell (fst (tbl !! col)) cell) (zip [0..] row))
	foldM_ (\x (col, val) -> do
		let wid = fst (tbl !! col)
		f val col rowN x y wid ht
		return (x + wid + padding))
		(xPos + padding)
		(zip [0..] row)
	return (y + ht + padding))
	(yPos + padding)
	(zip [0..] (transpose (map snd tbl)))

getCell0 (x, y) pr ob = case obj ob of
	Right (Left tbl) -> do
		cell <- newIORef Nothing
		withCells pr tbl $ \val col row x2 y2 wid ht -> when (x2 <= x && x < x2 + wid && y2 <= y && y < y2 + ht) $ maybe
			(return ())
			(\(x, y, (el, _)) -> writeIORef cell (Just (col, row, x2 + x, y2 + y, el)))
			(hitTest (x - x2, y - y2) (layout wid ((0, 0), (wid, 0), 0) val))
		liftM (maybe (Nothing, fst pr, snd pr, ob) (\(col, row, x, y, el) -> (Just (position ob, col, row), x, y, el))) (readIORef cell)
	_ -> return (Nothing, fst pr, snd pr, ob)

getCell pr pr2 ob = do
	(may, x, y, ob2) <- getCell0 pr pr2 ob
	maybe
		(return ([], x, y, ob2))
		(\z -> do
			(ls, x, y, ob2) <- getCell pr (x, y) ob2
			return (z:ls, x, y, ob2))
		may

getCellEdge (x, _) pr ob = case obj ob of
	Right (Left contents) -> findIndex (\x2 -> x2 <= x && x < x2 + 5) (tail (scanl (\x y -> x + y + 5) (fst pr) (map fst contents)))
	_ -> Nothing

getBitmapInfo3 bmp = case bmpBitmapInfo bmp of
	InfoV3 bi -> bi
	InfoV4 bi -> dib4InfoV3 bi
	InfoV5 bi -> dib4InfoV3 (dib5InfoV4 bi)

instance Displayable Object where
	measure _ = (0, 0)
	flowMeasure (Object _ _ (Left (Word font size _ bold italic underline s)) _ _ _) = unsafePerformIO $ do
		dc <- getDC Nothing
		font <- createAFont dc font size bold italic underline
		oldFont <- selectFont dc font
		(x, y) <- getTextExtentPoint32 dc (if null s then " " else s)
		selectFont dc oldFont
		deleteFont font
		releaseDC Nothing dc
		return (if null s then 0 else x, y)
	flowMeasure (Object _ _ (Right (Left contents)) _ _ _) = (padding + sum (map ((+padding) . fst) contents),
		padding + sum (map (\(col, ls) -> padding + maximum (map (measureCell (fst (contents !! col))) ls)) $ zip [0..] $ transpose $ map snd contents))
	flowMeasure (Object _ _ (Right (Right (Link _ ob))) _ _ _) = ((fromIntegral . dib3Width) &&& (fromIntegral . dib3Height)) (getBitmapInfo3 ob)
	draw dc (x, y) obj@(Object _ selected (Left (Word font size clr bold italic underline s)) _ _ _) = do
		if selected == Selected then do
				c_SetBkColor dc (rgb 0 0 0)
				c_SetBkMode dc oPAQUE
				c_SetTextColor dc (rgb 255 255 255)
			else do
				c_SetBkMode dc tRANSPARENT
				c_SetTextColor dc clr
		font <- createAFont dc font size bold italic underline
		oldFont <- selectFont dc font
		textOut dc x y s
		selectFont dc oldFont
		deleteFont font
		drawCaret dc (x, y) obj
	draw dc pr obj@(Object _ selected (Right (Left tbl)) _ _ _) = do
		withCells pr tbl $ \val _ _ x y wid ht -> do
			rectangle dc (x - 3) (y - 3) (x + wid + 3) (y + ht + 3)
			let lay = layout wid ((0, 0), (wid, 0), 0) val
			mapM_ (\(x2, y2, (el, _)) -> draw dc (x + x2, y + y2) el)
				lay
		drawBorder dc pr obj selected
		drawCaret dc pr obj
	draw dc pr ob@(Object _ selected (Right (Right (Link _ link))) _ _ _) = do
		draw dc pr link
		drawBorder dc pr ob selected
		drawCaret dc pr ob
	mouse MouseDown _ _ pr pr2 ob = mousedown ob pr pr2 ob
	mouse MouseMove _ _ pr pr2 ob = mousemove ob pr pr2 ob
	mouse MouseUp _ _ _ _ obj = mouseup obj

toView0 ls = concatMap snd ls

toView ls = toView0 (fromZipper ls) 

fromView0 ((just, ls):xs) view = (just, take (length ls) view) : fromView0 xs (drop (length ls) view)
fromView0 [] _ = []

fromView zip@(_, _, _, aft, _) view = goto (position (fst (headF aft))) $ toZipper $ fromView0 (fromZipper zip) view

headR [] = error "headR"
headR (x:_) = x

headG [] = error "headG"
headG (x:_) = x

headH [] = error "headH"
headH (x:_) = x

headF [] = error "headF"
headF (x:_) = x

headZ [] = error "headZ"
headZ (x:_) = x

headB [] = error "headB"
headB (x:_) = x

headE [] = error "headE"
headE (x:_) = x

headI [] = error "headI"
headI (x:_) = x

headP [] = error "headP"
headP (x:_) = x

headA [] = error "headA"
headA (x:_) = x

renumber0 n ls = first (runIdentity . doOnAll0 (return . fromZipper . renumber . toZipper) return) $ renum n ls [] where
	renum n (x:xs) acc = renum (n + 1) xs (first (\x -> x { position = n }) x : acc)
	renum n [] acc = (reverse acc, n)

renumber (befBig, just, bef, aft, aftBig) = (befBig, just, reverse bef', aft', aftBig') where
	(bef', m) = renumber0 (if null befBig then 0 else position (fst $ last $ snd $ headR befBig) + 1) (reverse bef)
	(aft', x) = renumber0 m aft
	aftBig' = map fst $ tail $ scanl (\(_, m) (just, ls) -> first ((,) just) $ renumber0 m ls) (undefined, x) aftBig

alterBef n f zip = (befBig, just, first (\x -> x { obj = f (obj x) }) (headA bef) : tail bef, aft, aftBig) where
	(befBig, just, bef, aft, aftBig) = goto n zip

alter n f zip = backwards $ alterBef (n + 1) f zip

insert ins (befBig, just, bef, aft, aftBig) = if null (tail ins) then
		(befBig, just, bef, snd (head ins) ++ aft, aftBig)
	else
		(befBig, just, bef, snd (head ins), init (tail ins) ++ second (++aft) (last ins) : aftBig)

delete n (befBig, just, bef, aft, aftBig) = (befBig, just, bef, aft', aftBig') where
	del ((just, ls):xs) = if null xs || n < position (fst $ head $ snd $ head xs) then
			(dropWhile ((<n) . position . fst) ls, xs)
	 	else
			del xs
	del [] = ([], [])
	(aft', aftBig') = del ((just, aft) : aftBig)

toZipper ((just, ls):xs) = ([], just, [], ls, xs)

fromZipper (befBig, just, bef, aft, aftBig) = reverse befBig ++ (just, reverse bef ++ aft) : aftBig

forwards (befBig, just, bef, aft, aftBig) = if null (tail aft) then
		((just, reverse bef ++ aft) : befBig, fst (headF aftBig), [], snd (headF aftBig), tail aftBig)
	else
		(befBig, just, headF aft : bef, tail aft, aftBig)

backwards (befBig, just, bef, aft, aftBig) = if null bef then
		(tail befBig, fst (headB befBig), tail (reverse (snd (headB befBig))), [last (snd (headB befBig))], (just, aft) : aftBig)
	else
		(befBig, just, tail bef, headB bef : aft, aftBig)

goto n zip@(_, _, _, aft, aftBig) = if position (fst (headG aft)) > n then
		goto n (backwards zip)
	else if position (fst (headG aft)) < n then
		goto n (forwards zip)
	else
		zip

doOnHead f (befBig, just, bef, aft, aftBig) = (befBig, just, bef, first f (headH aft) : tail aft, aftBig)

doOnAll0 f g = mapM (\(x, flt) -> case obj x of
	Right (Left contents) -> do
		ls <- mapM (\(wid, ls) -> liftM ((,) wid) (mapM f ls)) contents
		g (x { obj = Right $ Left ls }, flt)
	_ -> g (x, flt))

doOnAll f = doOnAll0 (\ls -> liftM (fromView0 ls) $ doOnAll f $ toView0 ls) f

enterKey zip@(_, just, _, aft, _) = Insert (position (fst (headE aft))) [(L, [(funOnWord (\x -> x { string = "" }) $ fst $ findWord zip, Inline)]), (just, [])]

funOnWord f (Object a b (Left wrd) c d e) = Object a b (Left (f wrd)) c d e
funOnWord _ ob = ob

isLeft (Left _) = True
isLeft _ = False

findWord (_, _, bef, aft, _) = fromJust $ find (isLeft . obj . fst) (bef ++ aft)

setCaret location zip = doOnHead (\ob -> ob { selection = Caret }) (goto location zip)

setSelection0 n m selState zip = sel (goto (m - 1) zip) where
	sel zip@(_, _, _, aft, _) = (if position (fst (head aft)) <= n then
			id
		else
			sel . backwards) $ doOnHead (\x -> x { selection = selState }) zip

setSelection n m = if n == m then
		setCaret n
	else if n > m then
		setSelection0 m n Selected
	else
		setSelection0 n m Selected

clearSelection0 ls = fromView0 ls $ runIdentity $ doOnAll (\(x, flt) -> return (x { selection = Unselected }, flt)) $ toView0 ls

clearSelection textVal = (if null ls then setSelection0 n (m + 1) Unselected else id)
	$ doOnHead (\x -> case obj x of
		Right (Left tbl) -> x { obj = Right $ Left $ map (second $ map clearSelection0) tbl }
		_ -> x) textVal where
	(ls, n, m) = findSelection textVal

setJustif just n m zip = justif (goto n zip) where
	justif zip@(befBig, _, bef, aft, aftBig) = (if m <= position (fst (head aft)) then
			id
		else
			justif . forwards) (befBig, just, bef, aft, aftBig)

untilM f g x = do
	b <- f x
	if b then
		return x
	else do
		y <- g x
		untilM f g y

measureCell wid cell = maximum $ map (\(_, y, (el, _)) -> y + height el) $ layout wid ((0, 0), (wid, 0), 0) cell

oneColTable ob = null (tail contents) where
	Right (Left contents) = obj ob

oneRowTable ob = null (tail (snd (head contents))) where
	Right (Left contents) = obj ob

tableList (InTable n col row cmd) = (n, col, row) : tableList cmd
tableList _ = []

innerCommand (InTable _ _ _ cmd) = innerCommand cmd
innerCommand cmd = cmd

findSelection0 ((x, _):xs) = case obj x of
		Right (Left tbl) -> foldr mplus mzero $ concat $ zipWith (\(_, col) colN -> zipWith (\cell row -> do
			(ls, y, z) <- findSelection0 $ toView0 cell
			return ((position x, colN, row):ls, y, z)) col [0..]) tbl [0..]
		_ -> Nothing
	`mplus` case selection x of
		Selected -> Just ([], position x, position $ fst $ fromJust $ find ((==Unselected) . selection . fst) xs)
		Caret -> Just ([], position x, position x)
		Unselected -> findSelection0 xs
findSelection0 [] = Nothing

findSelection (_, _, _, aft, aftBig) = maybe ([], 0, 0) id $ findSelection0 $ toView ([], L, [], aft, aftBig)

toolbarHeight = 40

createAButton path x cmd wnd hdl sz = do
	Right bmp <- readBMP path
	ref <- newIORef bmp
	let name = mkClassName "Frame"
	wnd2 <- createWindow name "" (wS_VISIBLE .|. wS_CHILD) (Just x) (Just ((toolbarHeight - sz) `div` 2)) (Just sz) (Just sz) (Just wnd) Nothing hdl $ \wnd msg wParam lParam -> if msg == wM_LBUTTONUP then do
			cmd
			return 0
		else
			defWindowProc (Just wnd) msg wParam lParam
	attachDisplay ref wnd2
	return wnd2

filt = "Hoss Files (*.hos)\0*.hos\0All Files\0*.*\0"

padding = 5

insetProc format fontRef sizeRef clrRef mousedown mousemove mouseup wnd msg wParam lParam n m get put setSelection performCommand = if msg == wM_GETDLGCODE then
		return (dLGC_WANTCHARS .|. dLGC_WANTARROWS)
	else if msg == wM_KEYDOWN then do
		textVal@(_, _, bef, aft, aftBig) <- get
		if n /= m then
			if wParam == vK_BACK || wParam == vK_DELETE then do
					performCommand (Delete n m)
				else
					return ()
			else
				if wParam == vK_LEFT then
					setSelection ((m - 1) `max` 0) ((m - 1) `max` 0)
				else if wParam == vK_RIGHT then
					unless (null (tail aft) && null aftBig) $ setSelection (m + 1) (m + 1)
				else if wParam == vK_SPACE then
					performCommand (Insert m [(L, [first (funOnWord (\x -> x { string = " " })) (findWord (goto m textVal))])])
				else if wParam == vK_BACK then
					when (m /= 0) $ performCommand $ if null bef then
							Delete (m - 1) m
						else case obj (fst (headP bef)) of
							Left wrd -> if length (string wrd) <= 1 then
									Delete (m - 1) m
								else
									Alter m (init (string wrd))
							Right _ -> Delete (m - 1) m
				else
					return ()
		return 0
	else if msg == wM_LBUTTONUP then do
		setFocus wnd
		return 0
	else if msg == wM_CHAR && wParam /= 8 && wParam /= 32 then do
		textVal@(_, _, bef, _, _) <- get
		caret <- if null bef || not (isLeft $ obj $ fst $ headP bef) then do
				performCommand (Insert m [(L, [(funOnWord (\x -> x { string = " " }) $ fst $ findWord (goto m textVal), Inline)])])
				return (m + 1)
			else
				return m
		(_, _, bef, _, _) <- get
		performCommand (Alter caret (let Left wrd = obj (fst (headP bef)) in string wrd ++ [chr (fromIntegral wParam)]))
		return 0
	else
		defWindowProc (Just wnd) msg wParam lParam

showAndHide b (ctrl, ctrl2) = do
	showWindow ctrl (if b then sW_HIDE else sW_SHOW)
	showWindow ctrl2 (if b then sW_SHOW else sW_HIDE)

main = do
	textLs <- newIORef undefined
	text <- newIORef undefined
	select <- newIORef Nothing
	undo <- newIORef undefined
	drag <- newIORef undefined
	onChange <- newIORef undefined
	inset <- newIORef undefined
	fontRef <- newIORef undefined
	sizeRef <- newIORef undefined
	clrRef <- newIORef undefined
	clrRef2 <- newIORef undefined
	undoRef <- newIORef undefined
	redoRef <- newIORef undefined
	delColRef <- newIORef undefined
	delRowRef <- newIORef undefined
	changed <- newIORef False
	format <- registerClipboardFormat "HossText"
	Right missing <- readBMP "Missing.bmp"
	let
	    execOnChange = do
		textVal <- readIORef text
		writeIORef textLs (fromZipper textVal)
		readIORef onChange >>= id
		(bef, aft) <- readIORef undo
		undo <- readIORef undoRef
		redo <- readIORef redoRef
		delCol <- readIORef delColRef
		delRow <- readIORef delRowRef
		showAndHide (null bef) undo
		showAndHide (null aft) redo
		let (ls, _, _) = findSelection textVal
		showAndHide (null ls) delCol
		showAndHide (null ls) delRow
		doOnTables ls $ \get _ _ _ -> do
			(_, _, _, aft, _) <- get
			let (x, _) = head aft
			case obj x of
				Left x -> do
					fontCtrl <- readIORef fontRef
					sizeCtrl <- readIORef sizeRef
					setWindowText fontCtrl (font x)
					setWindowText sizeCtrl (show (size x))
					writeIORef clrRef (color x)
					clrCtrl <- readIORef clrRef2
					invalidateRect (Just clrCtrl) Nothing True
				_ -> return ()
	    performCommand2 x textVal = do
		writeIORef text (perform x textVal)
		writeIORef drag Nothing
		writeIORef select Nothing
		let (ls, _, _) = findSelection textVal
		when (ls == tableList x) $ doOnTables ls $ \_ _ setSelection _ -> case innerCommand x of
			Insert n ls -> setSelection (n + length (concatMap snd ls)) (n + length (concatMap snd ls))
			Delete n _ -> setSelection n n
			_ -> return ()
	    undoCommand = do
		(x:bef, aft) <- readIORef undo
		textVal <- readIORef text
		writeIORef undo (bef, invert x textVal : aft)
		performCommand2 x textVal
		execOnChange
	    redoCommand = do
		(bef, x:aft) <- readIORef undo
		textVal <- readIORef text
		writeIORef undo (invert x textVal : bef, aft)
		performCommand2 x textVal
		execOnChange
	    performCommand x = do
		(bef, _) <- readIORef undo
		writeIORef undo (bef, [x])
		redoCommand
		(bef, _) <- readIORef undo

		-- Make it so that multiple alters of the same word are compressed into a single entry in the undo list
		case bef of
			x:y:_ -> when (tableList x == tableList y) $ writeIORef undo (case (innerCommand x, innerCommand y) of
				(Alter n _, Alter m _) | n == m -> tail bef
				_ -> bef, [])
			_ -> return ()
		writeIORef changed True
	    doOnTables0 ((n, col, row):xs) = (\textVal -> let
				(_, _, _, aft, _) = goto n textVal
				Right (Left tbl) = obj (fst (head aft)) in
			get $ toZipper $ snd (tbl !! col) !! row,
		\newText -> alter n (\(Right (Left contents)) -> Right $ Left $ changeAt col (second $ changeAt row $ fromZipper . put newText . toZipper) contents),
		InTable n col row . makeCommand) where
		(get, put, makeCommand) = doOnTables0 xs
	    doOnTables0 [] = (id, const, id)
	    doOnTables :: [(Int, Int, Int)] -> (IO (Zipper Object) -> (Zipper Object -> IO ()) -> (Int -> Int -> IO ()) -> (Command -> IO ()) -> IO t) -> IO t
	    doOnTables ls f = do
		let (get, put, makeCommand) = doOnTables0 ls
		f
			(do
				textVal <- readIORef text
				let gotten = get textVal
				let (_, m, _) = findSelection gotten
				return $ goto m gotten)
			(\newText -> modifyIORef text (put newText) >> execOnChange)
			(\m x -> do
				modifyIORef text $ \textVal -> put (setSelection m x $ (if null ls then clearSelection else toZipper . clearSelection0 . fromZipper) $ get textVal) $ clearSelection textVal
				execOnChange)
			(performCommand . makeCommand)
	let mousemove (x, y) pr ob = do
		textVal <- readIORef text
		dragVal <- readIORef drag
		case dragVal of
			Just (ls, n, col, interval) -> doOnTables ls $ \get put _ _ -> liftM (alter n (\(Right (Left contents)) -> Right $ Left $ changeAt col (first $ const $ (interval + x) `div` 10 * 10) contents)) get >>= put
			Nothing -> do
				may <- readIORef select
				(ls, xPos, yPos, ob2) <- getCell (x, y) pr ob
				maybe
					(return ())
					(\(ls2, n, _) -> when (ls == ls2) $ doOnTables ls $ \_ _ setSelection _ -> setSelection n (position ob2))
					may
	let mousedown pr pr2 ob = do
		textVal <- readIORef text
		(ls, x, y, ob2) <- getCell pr pr2 ob
		case getCellEdge pr (x, y) ob2 of
			Just i -> let Right (Left contents) = obj ob2 in
				writeIORef drag $ Just (ls, position ob2, i, fst (contents !! i) - fst pr)
			Nothing -> do
				(ls, _, _, ob2) <- getCell pr pr2 ob
				writeIORef select $ Just (ls, position ob2, position ob2)
		mousemove pr pr2 ob
	let mouseup = do
		writeIORef drag Nothing
		writeIORef select Nothing
	let initialObject selection = (Object 0 selection (Left $ Word "Times New Roman" 12 0 False False False "") mousedown mousemove mouseup, Inline)
	let initialParagraph selection = [(L, [initialObject selection])]
	let newTable = do
		textVal <- readIORef text
		let (ls, _, m) = findSelection textVal
		doOnTables ls $ \_ _ _ performCommand -> do
			let ob = Object 0 Unselected (Right $ Left [(100, [initialParagraph Unselected])]) mousedown mousemove mouseup
			performCommand $ Insert m [(L, [(ob, Inline)])]
	let newCol = do
		textVal <- readIORef text
		let (ls, _, _) = findSelection textVal
		let (n, col, _) = last ls
		if null ls then
				newTable
			else doOnTables (init ls) $ \_ _ _ performCommand ->
				performCommand $ NewCol n col (100, repeat (initialParagraph Unselected))
	let newRow = do
		textVal <- readIORef text
		let (ls, _, _) = findSelection textVal
		let (n, _, row) = last ls
		if null ls then
				newTable
			else doOnTables (init ls) $ \_ _ _ performCommand ->
				performCommand $ NewRow n row (repeat (initialParagraph Unselected))
	let delCol = do
		textVal <- readIORef text
		let (ls, _, _) = findSelection textVal
		let (n, col, _) = last ls
		doOnTables (init ls) $ \get _ _ performCommand -> do
			textVal <- get
			performCommand $ if oneColTable (fst (toView textVal !! n)) then
					Delete n (n + 1)
				else
					DelCol n col
	let delRow = do
		textVal <- readIORef text
		let (ls, _, _) = findSelection textVal
		let (n, _, row) = last ls
		doOnTables (init ls) $ \get _ _ performCommand -> do
			textVal <- get
			performCommand $ if oneColTable (fst (toView textVal !! n)) then
					Delete n (n + 1)
				else
					DelCol n row
	let doSave wnd = fileSave wnd filt "hos" >>= maybe
		(return False)
		(\path -> do
			textVal <- readIORef text
			undoVal <- readIORef undo
			encodeFile path (fromZipper $ fromView textVal $ map (first $ \x -> case obj x of
				Right (Right (Link path2 _)) -> x { obj = Right (Right (Link (makeRelative (takeDirectory path) path2) undefined)) }
				_ -> x) $ toView textVal, undoVal)
			writeIORef changed False
			setWindowText wnd $ "Hoss - " ++ path
			return True)
	let promptForSave wnd m = do
		b <- readIORef changed
		if b then do
				res <- messageBox' wnd "File has not been saved. Do you want to save it?" "Warning" (mB_ICONEXCLAMATION .|. mB_YESNOCANCEL)
				if res == iDYES then do
						saved <- doSave wnd
						when saved m
					else if res == iDNO then
						m
					else
						return ()
			else
				m
	let loadBitmap path = catch (liftM (either (const missing) id) $ readBMP path) (\(_ :: SomeException) -> return missing)
	let realize = doOnAll (\(ob, flt) -> case obj ob of
		Right (Right (Link path _)) -> do
			bmp <- loadBitmap path
			return (ob { obj = Right $ Right $ Link path bmp }, flt)
		_ -> return (ob, flt))
		. map (first $ \x -> x { mousedown = mousedown, mousemove = mousemove, mouseup = mouseup })
	let doOpen wnd = promptForSave wnd $ fileOpen wnd filt "hos" >>= maybe
		(return ())
		(\path -> do
			(textVal, undoVal) <- decodeFile path
			realized <- liftM (fromView0 textVal) $ realize $ map (first $ \x -> case obj x of
				Right (Right (Link path2 _)) -> x { obj = Right (Right (Link (combine (takeDirectory path) path2) undefined)) }
				_ -> x) $ toView0 textVal
			writeIORef text $ renumber $ toZipper realized
			writeIORef undo undoVal
			writeIORef drag Nothing
			writeIORef select Nothing
			writeIORef changed False
			setWindowText wnd $ "Hoss - " ++ path
			execOnChange)
	let newFile wnd = promptForSave wnd $ do
		writeIORef text ([], L, [], [initialObject Caret], [])
		writeIORef undo ([], [])
		writeIORef drag Nothing
		writeIORef select Nothing
		writeIORef changed False
		execOnChange
	let copy = do
		textVal <- readIORef text
		let (ls, n, m) = findSelection textVal
		doOnTables ls $ \get _ _ _ -> do
			textVal <- get
			let bytestring = SB.pack $ LB.unpack $ encode $ let Insert _ ls = invertDelete n m textVal in ls
			hdl <- globalAlloc gMEM_MOVEABLE (fromIntegral (SB.length bytestring) + 4)
			p <- globalLock hdl
			pokeByteOff p 0 (SB.length bytestring)
			unsafeUseAsCString bytestring $ \p2 -> copyBytes (p `plusPtr` 4) (castPtr p2) (fromIntegral $ SB.length bytestring)
			globalUnlock' hdl
			insetWnd <- readIORef inset
			openClipboard insetWnd
			setClipboardData format hdl
			closeClipboard
	let cut = do
		textVal <- readIORef text
		let (ls, n, m) = findSelection textVal
		doOnTables ls $ \_ _ _ performCommand -> do
			copy
			performCommand (Delete n m)
	let paste = do
		textVal <- readIORef text
		let (ls, n, _) = findSelection textVal
		doOnTables ls $ \get _ _ performCommand -> do
			textVal <- get
			insetWnd <- readIORef inset
			openClipboard insetWnd
			catch (finally (do
				hdl <- getClipboardData format
				p <- globalLock hdl
				len <- peekByteOff p 0
				bytestring <- unsafePackCStringLen (p `plusPtr` 4, len)
				let ls = decode $ LB.fromChunks [bytestring]
				realized <- liftM (fromView0 ls) $ realize $ toView0 ls
				performCommand $ Insert n realized
				globalUnlock' hdl
				return ())
				closeClipboard)
				(\(_ :: SomeException) -> return ())
	let setJustification just = do
		textVal <- readIORef text
		let (ls, n, m) = findSelection textVal
		doOnTables ls $ \get put _ _ -> do
			textVal <- get
			put $ setJustif just n m textVal
	let setFloated flt' = do
		textVal <- readIORef text
		let (ls, _, _) = findSelection textVal
		doOnTables ls $ \get put _ _ -> do
			textVal <- get
			put $ fromView textVal $ map (\(x, flt) -> (x, if not (isLeft (obj x)) && selection x == Selected then flt' else flt)) (toView textVal)
	let setStyle hasStyle setStyle = do
		textVal <- readIORef text
		let (ls, _, _) = findSelection textVal
		doOnTables ls $ \get put _ _ -> do
			textVal <- get
			let hasIt = all (\(x, _) -> selection x == Unselected || case obj x of
				Left wrd -> hasStyle wrd
				_ -> True) (toView textVal)
			put $ fromView textVal $ map (\x -> if selection (fst x) /= Unselected then first (funOnWord (setStyle (not hasIt))) x else x) (toView textVal)
	let printing = catch (do
		textVal <- readIORef text
		printer $ \printerDC -> untilM (\(_, _, _, aft, aftBig) -> return $ null aft && null aftBig)
			(\textVal -> do
				let lay = layout 624 ((0, 0), (624, 0), 0) (fromZipper textVal)
				let cutoff = maybe lay (\n -> take (n `max` 1) lay) (findIndex (\(_, y, (el, _)) -> y + height el > 864) lay)
				startPage printerDC
				mapM_ (\(x, y, (el, _)) -> draw printerDC (x + 96, y + 96) el) cutoff
				endPage printerDC
				let (_, _, (el, _)) = last cutoff
				return $ delete (position el + 1) textVal)
			$ toZipper $ clearSelection0 $ fromZipper textVal)
		(\(_ :: SomeException) -> return ())
	let link = do
		insetWnd <- readIORef inset
		textVal <- readIORef text
		let (ls, n, _) = findSelection textVal
		fileOpen insetWnd "Bitmaps (*.bmp)\0*.bmp\0" "bmp" >>= maybe
			(return ())
				(\path -> doOnTables ls $ \_ _ _ performCommand -> do
				bmp <- loadBitmap path
				performCommand (Insert n [(L, [(Object 0 Unselected (Right $ Right $ Link path bmp) mousedown mousemove mouseup, Inline)])]))
	let initControls wnd hdl = do
		font <- createEditWindow "" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) 0 (Just 10) (Just 10) (Just 200) (Just 20) wnd Nothing hdl
		writeIORef fontRef font
		size <- createEditWindow "" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) 0 (Just 220) (Just 10) (Just 20) (Just 20) wnd Nothing hdl
		writeIORef sizeRef size
		let name = mkClassName "Frame"
		clr <- createWindow name "" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) (Just 250) (Just 10) (Just 20) (Just 20) (Just wnd) Nothing hdl $ \wnd2 msg wParam lParam ->
			if msg == wM_LBUTTONUP || msg == wM_KEYUP && wParam == vK_SPACE then do
				clr <- readIORef clrRef
				chooseColor wnd2 clr >>= maybe
					(return 0)
					(\clr -> do
						writeIORef clrRef clr
						invalidateRect (Just wnd2) Nothing True
						sendMessage wnd wM_COMMAND iDOK 0)
			else if msg == wM_PAINT then
				allocaPAINTSTRUCT $ \ps -> do
					dc <- beginPaint wnd2 ps
					clr <- readIORef clrRef
					brush <- createSolidBrush clr
					fillRect dc (0, 0, 20, 20) brush
					deleteBrush brush
					endPaint wnd2 ps
					return 0
			else
				defWindowProc (Just wnd2) msg wParam lParam
		writeIORef clrRef2 clr
		dc <- getDC Nothing
		fnt <- createAFont dc "Tahoma" 12 False False False
		releaseDC Nothing dc
		mapM_ (\wnd -> sendMessage wnd wM_SETFONT (unsafeCoerce fnt) 0) [font, size]
		createAButton "Left.bmp" 280 (setJustification L) wnd hdl 20
		createAButton "Center.bmp" (280 + 20) (setJustification Center) wnd hdl 20
		createAButton "Right.bmp" (280 + 2 * 20) (setJustification R) wnd hdl 20
		createAButton "Justified.bmp" (280 + 3 * 20) (setJustification Justified) wnd hdl 20
		createAButton "Bold.bmp" 370 (setStyle bold (\b x -> x { bold = b })) wnd hdl 20
		createAButton "Italic.bmp" (370 + 20) (setStyle italic (\b x -> x { italic = b })) wnd hdl 20
		createAButton "Underline.bmp" (370 + 2 * 20) (setStyle underline (\b x -> x { underline = b })) wnd hdl 20
		createAButton "Inline.bmp" 440 (setFloated Inline) wnd hdl 20
		createAButton "FloatLeft.bmp" (440 + 20) (setFloated FloatLeft) wnd hdl 20
		createAButton "FloatRight.bmp" (440 + 2 * 20) (setFloated FloatRight) wnd hdl 20
		createAButton "New.bmp" 510 (newFile wnd) wnd hdl 32
		createAButton "Open.bmp" (510 + 32) (doOpen wnd) wnd hdl 32
		createAButton "Save.bmp" (510 + 2 * 32) (doSave wnd) wnd hdl 32
		createAButton "Cut.bmp" (510 + 3 * 32) cut wnd hdl 32
		createAButton "Copy.bmp" (510 + 4 * 32) copy wnd hdl 32
		createAButton "Paste.bmp" (510 + 5 * 32) paste wnd hdl 32 
		undo <- createAButton "Undo.bmp" (510 + 6 * 32) undoCommand wnd hdl 32
		redo <- createAButton "Redo.bmp" (510 + 7 * 32) redoCommand wnd hdl 32
		undo2 <- createAButton "UndoDis.bmp" (510 + 6 * 32) (return ()) wnd hdl 32
		redo2 <- createAButton "RedoDis.bmp" (510 + 7 * 32) (return ()) wnd hdl 32
		createAButton "Newtable.bmp" (510 + 8 * 32) newTable wnd hdl 32
		createAButton "Newcol.bmp" (510 + 9 * 32) newCol wnd hdl 32
		createAButton "Newrow.bmp" (510 + 10 * 32) newRow wnd hdl 32 
		delCol <- createAButton "Delcol.bmp" (510 + 11 * 32) delCol wnd hdl 32
		delRow <- createAButton "Delrow.bmp" (510 + 12 * 32) delRow wnd hdl 32
		delCol2 <- createAButton "DelcolDis.bmp" (510 + 11 * 32) (return ()) wnd hdl 32
		delRow2 <- createAButton "DelrowDis.bmp" (510 + 12 * 32) (return ()) wnd hdl 32
		createAButton "Print.bmp" (510 + 13 * 32) printing wnd hdl 32
		createAButton "OLE.bmp" (510 + 14 * 32) link wnd hdl 32
		writeIORef undoRef (undo, undo2)
		writeIORef redoRef (redo, redo2)
		writeIORef delColRef (delCol, delCol2)
		writeIORef delRowRef (delRow, delRow2)
	frameWindow "Hoss" Nothing Nothing $ \dialogs wnd msg wParam lParam -> if msg == wM_CREATE then do
			hdl <- getModuleHandle Nothing
 			initControls wnd hdl
			let name = mkClassName "Frame"
			insetWnd <- createWindow name "" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) Nothing Nothing Nothing Nothing (Just wnd) Nothing hdl (\wnd msg wParam lParam -> do
				textVal <- readIORef text
				let (ls, n, m) = findSelection textVal
				doOnTables ls (insetProc format fontRef sizeRef clrRef mousedown mousemove mouseup wnd msg wParam lParam n m))
			writeIORef inset insetWnd
			proc <- attachLayout textLs insetWnd
			writeIORef onChange proc
			newFile wnd
			modifyIORef dialogs (wnd:)
			sendMessage wnd wM_SIZE 0 0
			return 0
		else if msg == wM_COMMAND then do
			focus <- getFocus
			insetWnd <- readIORef inset
			textVal <- readIORef text
			let (ls, n, m) = findSelection textVal
			when (loWord wParam == iDOK) $ doOnTables ls $ \get put _ performCommand -> do
				textVal <- get
				if focus == Just insetWnd then
						performCommand (enterKey (goto n textVal))
					else do
						fontCtrl <- readIORef fontRef
						sizeCtrl <- readIORef sizeRef
						clr <- readIORef clrRef
						fnt <- getWindowText fontCtrl
						sz <- getWindowText sizeCtrl
						catch
							(do
							n <- readIO sz
							put $ fromView textVal $ map (\x -> if selection (fst x) /= Unselected then first (funOnWord (\y -> y { font = fnt, size = n, color = clr })) x else x) (toView textVal))
							(\(_ :: SomeException) -> return ())
			return 0
		else if msg == wM_SIZE then do
			insetCtrl <- readIORef inset
			(_, _, wd, ht) <- getClientRect wnd
			moveWindow insetCtrl 0 toolbarHeight (fromIntegral wd) (fromIntegral ht - toolbarHeight) True
			return 0
		else if msg == wM_ERASEBKGND then do
			brush <- getSysColorBrush cOLOR_3DFACE
			fillRect (unsafeCoerce wParam) (0, 0, 32767, 32767) brush
			return 1
		else if msg == wM_CLOSE || msg == wM_ENDSESSION then do
			promptForSave wnd exitSuccess
			return 0
		else
			defWindowProc (Just wnd) msg wParam lParam

-- Debugging stuff

instance Show Word where
	show wrd = show (string wrd)

instance Eq Link where
	x == y = path x == path y

instance Eq Object where
	x == y = position x == position y && obj x == obj y

instance Show Object where
	show x = "Object " ++ show (position x) ++ " " ++ show (selection x) ++ " " ++ show (obj x) ++ " _ _ _"

makeWord s = Word "" 0 0 False False False s

makeObject sel s = Object undefined sel (Left (makeWord s)) undefined undefined undefined 

instance Arbitrary Word where
	arbitrary = liftM (makeWord . show) (arbitrary :: Gen Int)
	shrink _ = []

instance Arbitrary Selection where
	arbitrary = MkGen $ \gen _  -> case fst (randomR (0, 2) gen) :: Int of
		0 -> Unselected
		1 -> Caret
		2 -> Selected
	shrink _ = []

instance Arbitrary Object where
	arbitrary = do
		b <- arbitrary
		x <- if b then do
			(wid :: Int) <- arbitrary
			(ht :: Int) <- arbitrary
			liftM (Right . Left) $ mapM (const $ liftM ((,) 100) $ mapM (const arbitrary) [1..ht]) [1..wid]
		else
			liftM Left arbitrary
		return $ Object 0 Unselected x undefined undefined undefined
	shrink _ = []

instance Arbitrary Just where
	arbitrary = MkGen $ \gen _ -> case fst (randomR (0, 3) gen) of
		(0 :: Int) -> L
		1 -> Center
		2 -> R
		3 -> Justified
	shrink _ = []

instance Arbitrary Floated where
	arbitrary = MkGen $ \gen _ -> case fst (randomR (0, 2) gen) of
		(0 :: Int) -> Inline
		1 -> FloatLeft
		2 -> FloatRight
	shrink _ = []

instance Arbitrary Command where
	arbitrary = do
		x <- elements [0..7]
		case x of
			(0 :: Int) -> do
				y <- elements [0..5]
				z <- arbitrary
				return $ Insert y (map (second $ map (first $ \x -> x { selection = Unselected })) (conformToInvariant z))
			1 -> do
				y <- elements [0..5]
				z <- elements [0..5]
				return $ Delete y (y + z)
			2 -> do
				y <- elements [0..5]
				z <- elements [0..1000]
				return $ Alter y (' ' : show z)
			3 -> do
				y <- elements [0..5]
				z <- elements [0..5]
				a <- elements [0..5]
				b <- arbitrary
				return $ InTable y z a b
			4 -> do
				y <- elements [0..5]
				z <- elements [0..5]
				return $ DelCol y z
			5 -> do
				y <- elements [0..5]
				z <- elements [0..5]
				return $ DelRow y z
			6 -> do
				y <- elements [0..5]
				z <- elements [0..5]
				a <- arbitrary
				return $ NewCol y z a
			7 -> do
				y <- elements [0..5]
				z <- elements [0..5]
				a <- arbitrary
				return $ NewRow y z a
	shrink _ = []

conformToInvariant textVal = fromZipper $ renumber $ toZipper $ (L, [(makeObject Unselected "", Inline)]) : map (\(just, ls) -> (just, map (first $ \(Object a b ob _ _ _) -> Object a b (case ob of
		Left wrd -> Left (wrd { string = ' ' : string wrd })
		Right (Left contents) -> Right $ Left $ map (second $ map conformToInvariant) contents) undefined undefined undefined) ls ++ [(makeObject Unselected "", Inline)])) textVal

laxInvariant ls = not (null ls) && all (\(_, ls) -> null ls || all (\(ob, _) -> case obj ob of
	Left wrd -> not (null (string wrd)) && head (string wrd) == ' '
	Right _ -> True) (init ls)) ls

invariant ls = laxInvariant ls && all (\(_, ls) -> not (null ls) && case obj (fst (last ls)) of
	Left wrd -> null (string wrd)
	Right _ -> False)
	ls && all (uncurry (==)) (zip [0..] (map (position . fst) (toView0 ls)))

validCommand (Insert n ls) (textVal :: [Paragraph Object]) = n >= 1 && not (null ls) && n + length ls <= position (fst (last (toView0 textVal))) + 1 && if null (tail ls) then
		laxInvariant ls
	else
		invariant (tail (init ls)) && laxInvariant [head ls] && laxInvariant [last ls]
validCommand (Delete n m) textVal = n <= m && m <= position (fst (last (toView0 textVal))) + 1
validCommand (Alter n s) textVal = n >= 1 && n <= position (fst (last (toView0 textVal))) && not (null s) && head s == ' '
validCommand (InTable n col row cmd) textVal = n < position (fst (last (toView0 textVal))) && case obj (fst (toView0 textVal !! n)) of
	Right (Left contents) -> length contents > col && length (snd (contents !! col)) > row && validCommand cmd (snd (contents !! col) !! row)
	_ -> False
validCommand (DelCol n m) textVal = n < position (fst (last (toView0 textVal))) && case obj (fst (toView0 textVal !! n)) of
	Right (Left contents) -> length contents > m
	_ -> False
validCommand (DelRow n m) textVal = n < position (fst (last (toView0 textVal))) && case obj (fst (toView0 textVal !! n)) of
	Right (Left contents) -> length (snd (head contents)) > m
	_ -> False
validCommand (NewCol n m _) textVal = n < position (fst (last (toView0 textVal))) && case obj (fst (toView0 textVal !! n)) of
	Right (Left contents) -> length contents > m
	_ -> False
validCommand (NewRow n m _) textVal = n < position (fst (last (toView0 textVal))) && case obj (fst (toView0 textVal !! n)) of
	Right (Left contents) -> length (snd (head contents)) > m
	_ -> False

theForwards cmd textVal = perform cmd (toZipper (conformToInvariant textVal))

theInverse cmd textVal = perform (invert cmd (toZipper (conformToInvariant textVal))) (theForwards cmd textVal)

inverse cmd textVal = not (null textVal) ==> validCommand cmd (conformToInvariant textVal) ==> fromZipper (theInverse cmd textVal) == conformToInvariant textVal

overlapping (x1, y1, x2, y2) (x3, y3, x4, y4) = (x1 <= x3 && x3 < x2 || x1 < x4 && x4 <= x2) && (y1 <= y3 && y3 < y2 || y1 < y4 && y4 <= y2)

toRect (x, y, (el, _)) = (x, y, x + width el, y + height el)

overlap :: [Paragraph Object] -> Bool
overlap ls = all (\(n, x) -> all (\(m, y) -> n == m || not (overlapping (toRect x) (toRect y))) (zip [0..] lay)) (zip [0..] lay) where
	lay = layout 200 ((0, 0), (200, 0), 0) ls

