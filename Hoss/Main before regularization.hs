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

import Test.QuickCheck
import Test.QuickCheck.Gen
import System.Random

-- Invariants: Each paragraph begins with a word containing the empty string.
-- Every other word starts with a space. At least one element in the document
-- should have either a caret or selection. There should be only one caret.
-- The bef parameter of each zipper should have an element.

type Zipper t = ([Paragraph t], Just, [(t, Floated)], [(t, Floated)], [Paragraph t])

data Selection = Unselected | Selected | Caret deriving (Eq, Show)

data Table = Table { contents :: [(Int32, [[Paragraph Object]])] } deriving (Eq, Show)

data Word = Word {
	font :: String,
	size :: Int32,
	color :: COLORREF,
	bold :: Bool,
	italic :: Bool,
	underline :: Bool,
	string :: String } deriving Eq

data Object = Object {
	position :: Int,
	selection :: Selection,
	obj :: Either Word (Either Table ()),
	mousedown :: (Int32, Int32) -> (Int32, Int32) -> Object -> IO (),
	mousemove :: (Int32, Int32) -> (Int32, Int32) -> Object -> IO (),
	mouseup :: IO () }

data Command = Insert Int [Paragraph Object] | Delete Int Int | Alter Int String | InTable Int Int Int Command | NewCol Int Int (Int32, [[Paragraph Object]]) | NewRow Int Int [[Paragraph Object]] | DelCol Int Int | DelRow Int Int

instance Binary Table where
	put (Table contents) = put contents
	get = do
		ls <- get
		return (Table ls)

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
	(_, _, _, aft, aftBig) = goto (n - 1) zip
	inv ((just, ls):xs) = if m <= position (fst (head ls)) then
			[]
		else
			(just, takeWhile ((<m) . position . fst) ls) : inv xs
	inv [] = []

changeAt n f ls = take n ls ++ f (ls !! n) : drop (n + 1) ls

invert (Insert n ls) _ = Delete n (n + length (concatMap snd ls))
invert (Delete n m) textVal = invertDelete n m textVal
invert (Alter n _) textVal = Alter n (let Left wrd = obj (fst (toView textVal !! n)) in string wrd)
invert (InTable n col row cmd) textVal = InTable n col row $ invert cmd $ toZipper $ snd (contents (let Right (Left tbl) = obj (fst (toView textVal !! n)) in tbl) !! col) !! row
invert (NewCol n m _) _ = DelCol n m
invert (NewRow n m _) _ = DelRow n m
invert (DelCol n m) textVal = NewCol n m $ let Right (Left (Table contents)) = obj (fst (toView textVal !! n)) in second (map (map (second clearSelection))) $ contents !! m
invert (DelRow n m) textVal = NewRow n m $ let Right (Left (Table contents)) = obj (fst (toView textVal !! n)) in map (map (second clearSelection)) $ transpose (map snd contents) !! m

perform (Insert n ls) textVal = renumber $ insert ls (goto (n - 1) textVal)
perform (Delete n m) textVal = renumber $ delete m (goto ((n - 1) `max` 0) textVal)
perform (Alter n s) textVal = alter n (\(Left x) -> Left $ x { string = s }) textVal
perform (InTable n col row cmd) textVal = alter n (\(Right (Left tbl)) -> Right $ Left $ Table $ changeAt col (second $ changeAt row $ fromZipper . perform cmd . toZipper) (contents tbl)) textVal
perform (NewCol n m paras) textVal = alter n (\x -> let Right (Left (Table contents)) = x in
	Right $ Left $ Table $ take m contents ++ second (take (length $ snd $ head contents)) paras : drop m contents)
	textVal
perform (NewRow n m paras) textVal = alter n (\x -> let Right (Left (Table contents)) = x in
	Right $ Left $ Table $ map (\(i, pr) -> second (\x -> take m x ++ paras !! i : drop m x) pr) (zip [0..] contents))
	textVal
perform (DelCol n m) textVal = alter n (\x -> let Right (Left (Table contents)) = x in
	Right $ Left $ Table $ take m contents ++ drop (m + 1) contents) textVal
perform (DelRow n m) textVal = alter n (\x -> let Right (Left (Table contents)) = x in
	Right $ Left $ Table $ map (second $ \ls -> take m ls ++ drop (m + 1) ls) contents) textVal

createAFont dc font size bold italic underline = do
	logy <- getDeviceCaps dc lOGPIXELSY
	createFont (size * logy `div` 72) 0 0 0 (if bold then fW_BOLD else fW_NORMAL) italic underline False dEFAULT_CHARSET oUT_DEFAULT_PRECIS cLIP_DEFAULT_PRECIS dEFAULT_QUALITY fF_DONTCARE font

drawCaret dc (x, y) obj@(Object _ selected _ _ _ _) = when (selected == Caret) $ do
	let (wd, ht) = flowMeasure obj
	moveToEx dc (x + wd - 2) y
	lineTo dc (x + wd - 2) (y + ht)

withCells (xPos, yPos) tbl f = foldM_ (\y (rowN, row) -> do
	let ht = maximum (map (\(col, cell) -> measureCell (fst (contents tbl !! col)) cell) (zip [0..] row))
	foldM_ (\x (col, val) -> do
		let wid = fst (contents tbl !! col)
		f val col rowN x y wid ht
		return (x + wid + padding))
		(xPos + padding)
		(zip [0..] row)
	return (y + ht + padding))
	(yPos + padding)
	(zip [0..] (transpose (map snd (contents tbl))))

getCell (x, y) pr ob = case obj ob of
	Right (Left tbl) -> do
		cell <- newIORef Nothing
		withCells pr tbl $ \val col row x2 y2 wid ht -> when (x2 <= x && x < x2 + wid && y2 <= y && y < y2 + ht) $ maybe
			(return ())
			(\(x, y, (el, _)) -> writeIORef cell (Just (col, row, x2 + x, y2 + y, el)))
			(hitTest (x - x2, y - y2) (layout wid ((0, 0), (wid, 0), 0) val))
		liftM (maybe (Nothing, fst pr, snd pr, position ob) (\(col, row, x, y, el) -> (Just (position ob, col, row), x, y, position el))) (readIORef cell)
	_ -> return (Nothing, fst pr, snd pr, position ob)

getCellEdge (x, _) pr ob = case obj ob of
	Right (Left tbl) -> findIndex (\x2 -> x2 <= x && x < x2 + 5) (tail (scanl (\x y -> x + y + 5) (fst pr) (map fst (contents tbl))))
	_ -> Nothing

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
		return (if null s then 0 else x + 3, y)
	flowMeasure (Object _ _ (Right (Left (Table contents))) _ _ _) = (padding + sum (map ((+padding) . fst) contents),
		padding + sum (map (\(col, ls) -> padding + maximum (map (measureCell (fst (contents !! col))) ls)) $ zip [0..] $ transpose $ map snd contents))
	draw dc (x, y) obj@(Object _ selected (Left (Word font size clr bold italic underline s)) _ _ _) = do
		if selected == Selected then do
				c_SetBkColor dc (rgb 0 0 0)
				c_SetTextColor dc (rgb 255 255 255)
			else do
				c_SetBkColor dc (rgb 255 255 255)
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
		when (selected == Selected) $ do
			pen <- createPen pS_SOLID 5 0
			oldPen <- selectPen dc pen
			brush <- getStockBrush nULL_BRUSH
			oldBrush <- selectBrush dc brush
			rectangle dc (fst pr) (snd pr) (fst pr + width obj) (snd pr + height obj)
			selectBrush dc oldBrush
			selectPen dc oldPen
			deletePen pen
		drawCaret dc pr obj
	mouse MouseDown _ _ pr pr2 ob = mousedown ob pr pr2 ob
	mouse MouseMove _ _ pr pr2 ob = mousemove ob pr pr2 ob
	mouse MouseUp _ _ _ _ obj = mouseup obj

toView0 ls = concatMap snd ls

toView ls = toView0 (fromZipper ls) 

fromView0 ((just, ls):xs) view = (just, take (length ls) view) : fromView0 xs (drop (length ls) view)
fromView0 [] _ = []

fromView zip@(_, _, bef, _, _) view = goto (position (fst (head bef))) $ toZipper $ fromView0 (fromZipper zip) view

renumber0 n ls = renum n ls [] where
	renum n (x:xs) acc = renum (n + 1) xs (first (\x -> x { position = n }) x : acc)
	renum n [] acc = (reverse acc, n)

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

renumber (befBig, just, bef, aft, aftBig) = (befBig, just, reverse bef', aft', aftBig') where
	(bef', m) = renumber0 (if null befBig then 0 else position (fst $ headR $ snd $ headR befBig) + 1) (reverse bef)
	(aft', x) = renumber0 m aft
	aftBig' = map fst $ tail $ scanl (\(_, m) (just, ls) -> first ((,) just) $ renumber0 m ls) (undefined, x) aftBig

alter n f zip = doOnHead f (goto n zip)

insert ins (befBig, just, bef, aft, aftBig) = if null (tail ins) then
		(befBig, just, bef, snd (head ins) ++ aft, aftBig)
	else
		(befBig, just, bef, snd (head ins), init (tail ins) ++ second (++aft) (last ins) : aftBig)

delete n zip@(befBig, just, bef, aft, aftBig) =
	let (aft', aftBig') = del ((just, aft) : aftBig) in
		{-if onBoundary zip then
			(count, tail befBig, fst (head befBig), reverse $ snd $ head befBig, aft', aftBig')
		else
			-}(befBig, just, bef, aft', aftBig') where
	del ((just, ls):xs) = if null xs || n <= position (fst $ head $ snd $ head xs) then
			(dropWhile ((<n) . position . fst) ls, xs)
	 	else
			del xs
	del [] = ([], [])

toZipper ((just, ls):xs) = ([], just, [head ls], tail ls, xs)

fromZipper (befBig, just, bef, aft, aftBig) = reverse befBig ++ (just, reverse bef ++ aft) : aftBig

forwards (befBig, just, bef, aft, aftBig) = if null aft then
		((just, reverse bef) : befBig, fst (headF aftBig), [headF (snd (headF aftBig))], tail (snd (headF aftBig)), tail aftBig)
	else
		(befBig, just, headF aft : bef, tail aft, aftBig)

backwards (befBig, just, bef, aft, aftBig) = if null (tail bef) then
		(tail befBig, fst (headB befBig), reverse (snd (headB befBig)), [], (just, reverse bef ++ aft) : aftBig)
	else
		(befBig, just, tail bef, headB bef : aft, aftBig)

goto n zip@(_, _, bef, aft, aftBig) = if position (fst (headG bef)) > n then
		goto n (backwards zip)
	else if position (fst (headG bef)) < n then
		if null aft && null aftBig then zip else goto n (forwards zip)
	else
		zip

doOnHead f (befBig, just, bef, aft, aftBig) = (befBig, just, ((fst (headH bef)) { obj = f (obj (fst (headH bef))) }, snd (headH bef)) : tail bef, aft, aftBig)

doOnHead2 f (befBig, just, bef, aft, aftBig) = (befBig, just, first f (headH bef) : tail bef, aft, aftBig)

clearSelection ls = map (first $ \x -> (case obj x of
	Right (Left (Table contents)) -> x { obj = Right $ Left $ Table $ map (second $ map (map (second clearSelection))) contents }
	_ -> x) { selection = Unselected }) ls

enterKey zip@(_, just, bef, _, _) = Insert (position (fst (head bef))) [(L, []), (just, [(funOnWord (\x -> x { string = "" }) $ fst $ findWord zip, Inline)])]

onBoundary (_, _, bef, _, _) = null (tail bef)

funOnWord f (Object a b (Left wrd) c d e) = Object a b (Left (f wrd)) c d e
funOnWord _ obj = obj

isLeft (Left _) = True
isLeft _ = False

findWord (_, _, bef, _, _) = fromJust $ find (isLeft . obj . fst) bef

setCaret location zip = doOnHead2 (\ob -> ob { selection = Caret }) (goto location zip)

setSelection0 n m zip = sel (goto (m - 1) zip) where
	sel zip@(_, _, bef, _, _) = (if position (fst (head bef)) <= n then
			id
		else
			sel . backwards) $ doOnHead2 (\x -> x { selection = Selected }) zip

setSelection n m = if n == m then
		setCaret n
	else if n > m then
		setSelection0 m n
	else
		setSelection0 n m

setJustif just n m zip = justif (goto n zip) where
	justif zip@(befBig, _, bef, aft, aftBig) = (if m <= position (fst (head bef)) then
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
	Right (Left (Table contents)) = obj ob

oneRowTable ob = null (tail (snd (head contents))) where
	Right (Left (Table contents)) = obj ob

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

initControls wnd hdl fontRef sizeRef clrRef clrRef2 undoRef redoRef delColRef delRowRef setJustification setFloated execOnChange mousedown mousemove mouseup undoCommand redoCommand doSave doOpen newFile cut copy paste newCol newRow delCol delRow printing text undo = do
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
	createAButton "Inline.bmp" 370 (setFloated Inline) wnd hdl 20
	createAButton "FloatLeft.bmp" (370 + 20) (setFloated FloatLeft) wnd hdl 20
	createAButton "FloatRight.bmp" (370 + 2 * 20) (setFloated FloatRight) wnd hdl 20
	createAButton "New.bmp" 440 (newFile wnd) wnd hdl 32
	createAButton "Open.bmp" (440 + 32) (doOpen wnd) wnd hdl 32
	createAButton "Save.bmp" (440 + 2 * 32) (doSave wnd) wnd hdl 32
	createAButton "Cut.bmp" (440 + 3 * 32) cut wnd hdl 32
	createAButton "Copy.bmp" (440 + 4 * 32) copy wnd hdl 32
	createAButton "Paste.bmp" (440 + 5 * 32) paste wnd hdl 32 
	undo <- createAButton "Undo.bmp" (440 + 6 * 32) undoCommand wnd hdl 32
	redo <- createAButton "Redo.bmp" (440 + 7 * 32) redoCommand wnd hdl 32 
	createAButton "Newcol.bmp" (440 + 8 * 32) newCol wnd hdl 32
	createAButton "Newrow.bmp" (440 + 9 * 32) newRow wnd hdl 32 
	delCol <- createAButton "Delcol.bmp" (440 + 10 * 32) delCol wnd hdl 32
	delRow <- createAButton "Delrow.bmp" (440 + 11 * 32) delRow wnd hdl 32
	createAButton "Print.bmp" (440 + 12 * 32) printing wnd hdl 32
	writeIORef undoRef undo
	writeIORef redoRef redo
	writeIORef delColRef delCol
	writeIORef delRowRef delRow

padding = 5

insetProc format fontRef sizeRef clrRef mousedown mousemove mouseup wnd msg wParam lParam n m get put setSelection performCommand = if msg == wM_GETDLGCODE then
		return (dLGC_WANTCHARS .|. dLGC_WANTARROWS)
	else if msg == wM_KEYDOWN then do
		textVal@(_, _, bef, aft, aftBig) <- get
		if n /= m then
			if wParam == vK_BACK || wParam == vK_DELETE then do
					performCommand (if m < n then Delete m n else Delete n m)
				else
					return ()
			else
				if wParam == vK_LEFT then
					setSelection ((m - 1) `max` 0) ((m - 1) `max` 0)
				else if wParam == vK_RIGHT then
					unless (null aft && null aftBig) $ setSelection (m + 1) (m + 1)
				else if wParam == vK_SPACE then
					performCommand (Insert (m + 1) [(L, [first (funOnWord (\x -> x { string = " " })) (findWord (goto (m + 1) textVal))])])
				else if wParam == vK_BACK then
					when (m /= 0) $ performCommand $ case obj (fst (head bef)) of
						Left wrd -> if length (string wrd) <= 1 then
								Delete m (m + 1)
							else
								Alter m (init (string wrd))
						Right _ -> Delete m (m + 1)
				else
					return ()
		return 0
	else if msg == wM_LBUTTONUP then do
		setFocus wnd
		return 0
	else if msg == wM_CHAR && wParam /= 8 && wParam /= 32 then do
		textVal <- get
		caret <- if onBoundary textVal then do
				performCommand (Insert (m + 1) [(L, [(funOnWord (\x -> x { string = " " }) $ fst $ findWord (goto (m + 1) textVal), Inline)])])
				return (m + 1)
			else
				return m
		(_, _, bef, _, _) <- get
		performCommand (Alter caret (let Left wrd = obj (fst (head bef)) in string wrd ++ [chr (fromIntegral wParam)]))
		return 0
	else
		defWindowProc (Just wnd) msg wParam lParam

main = do
	textLs <- newIORef undefined
	text <- newIORef undefined
	undo <- newIORef undefined
	select <- newIORef (False, Nothing, 0, 0)
	drag <- newIORef Nothing
	onChange <- newIORef undefined
	inset <- newIORef undefined
	fontRef <- newIORef undefined
	sizeRef <- newIORef undefined
	clrRef <- newIORef (rgb 0 0 0)
	clrRef2 <- newIORef undefined
	undoRef <- newIORef undefined
	redoRef <- newIORef undefined
	delColRef <- newIORef undefined
	delRowRef <- newIORef undefined
	changed <- newIORef False
	format <- registerClipboardFormat "HossText"
	let
	    execOnChange = do
		textVal <- readIORef text
		writeIORef textLs (fromZipper textVal)
		readIORef onChange >>= id
		(bef, aft) <- readIORef undo
		undoCtrl <- readIORef undoRef
		redoCtrl <- readIORef redoRef
		delCol <- readIORef delColRef
		delRow <- readIORef delRowRef
		showWindow undoCtrl (if null bef then sW_HIDE else sW_SHOW)
		showWindow redoCtrl (if null aft then sW_HIDE else sW_SHOW)
		(_, may, _, _) <- readIORef select
		if isNothing may then do
				showWindow delCol sW_HIDE
				showWindow delRow sW_HIDE
			else do
				showWindow delCol sW_SHOW
				showWindow delRow sW_SHOW
		doOnTables $ \get _ _ _ -> do
			(_, _, bef, _, _) <- get
			let (x, _) = head bef
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
	    setSel n m = do
		modifyIORef text (\textVal -> setSelection n m (fromView textVal (clearSelection (toView textVal))))
		modifyIORef select (\(b, _, _, _) -> (b, Nothing, n, m))
		execOnChange
	    setSelTable n col row may m x = do
		modifyIORef text $ \textVal -> alter n (\(Right (Left tbl)) -> Right $ Left $ Table $ changeAt col (second $ changeAt row $ fromZipper . setSelection m x . toZipper) (contents tbl)) (fromView textVal (clearSelection (toView textVal)))
		modifyIORef select (\(b, _, _, _) -> (b, may, m, x))
		execOnChange
	    performCommand2 x textVal = do
		writeIORef text (perform x textVal)
		(b, may, y, z) <- readIORef select
		case may of
			Just (n, col, row) -> case x of
				NewCol m col2 _ -> when (n == m && col2 <= col) $ writeIORef select (b, Just (n, col + 1, row), y, z)
				NewRow m row2 _ -> when (n == m && row2 <= row) $ writeIORef select (b, Just (n, col, row + 1), y, z)
				DelCol m col2 -> when (n == m) $ if col2 < col then
						writeIORef select (b, Just (n, col - 1, row), y, z)
					else if col2 == col then
						writeIORef select (b, Nothing, n, n)
					else
						return ()
				DelRow m row2 -> when (n == m) $ if row2 < row then
						writeIORef select (b, Just (n, col, row - 1), y, z)
					else if row2 == row then
						writeIORef select (b, Nothing, n, n)
					else
						return ()
				InTable n col row (Insert m _) -> setSelTable n col row may m m
				InTable n col row (Delete m _) -> setSelTable n col row may ((m - 1) `max` 0) ((m - 1) `max` 0)
				_ -> return ()
			Nothing -> case x of
				Insert n _ -> setSel n n
				Delete n _ -> setSel ((n - 1) `max` 0) ((n - 1) `max` 0)
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
		writeIORef changed True
	    doOnTables :: (IO (Zipper Object) -> (Zipper Object -> IO ()) -> (Int -> Int -> IO ()) -> (Command -> IO ()) -> IO t) -> IO t
	    doOnTables f = do
		(_, may, y, _) <- readIORef select
		maybe
			(f (readIORef text) (\x -> writeIORef text x >> execOnChange) setSel performCommand)
			(\(n, col, row) -> f (do
					textVal <- readIORef text
					let Right (Left tbl) = obj (fst (toView textVal !! n))
					return $ goto y $ toZipper $ snd (contents tbl !! col) !! row)
				(\newText -> do
					modifyIORef text $ alter n (\(Right (Left tbl)) -> Right $ Left $ Table $ changeAt col (second $ changeAt row $ const $ fromZipper newText) (contents tbl))
					execOnChange)
				(setSelTable n col row may)
				(\cmd -> performCommand (InTable n col row cmd)))
			may
	let mousemove (x, y) pr ob = do
		textVal <- readIORef text
		dragVal <- readIORef drag
		case dragVal of
			Just (n, col, interval) -> do
				writeIORef text $ fromView textVal $ changeAt n (first $ \ob -> ob { obj = let Right (Left (Table contents)) = obj ob in Right $ Left $ Table $ changeAt col (first $ const $ (interval + x) `div` 10 * 10) contents }) (toView textVal)
				execOnChange
			Nothing -> do
				(b, may, n, _) <- readIORef select
				(may2, xPos, yPos, idx) <- getCell (x, y) pr ob
				when (b && may == may2) $ doOnTables $ \get _ setSelection _ -> do
					(_, _, bef, _, _) <- get
					let m = idx + if x < xPos + width (fst (head bef)) && y < yPos + height (fst (head bef)) then 0 else 1
					setSelection n m
	let mousedown pr pr2 ob = do
		textVal <- readIORef text
		case getCellEdge pr pr2 ob of
			Just i -> let Right (Left (Table contents)) = obj ob in
				writeIORef drag $ Just (position ob, i, fst (contents !! i) - fst pr)
			Nothing -> do
				(may, _, _, pos) <- getCell pr pr2 ob
				writeIORef select (True, may, pos, pos)
		mousemove pr pr2 ob
	let mouseup = do
		writeIORef drag Nothing
		modifyIORef select (\(_, may, n, m) -> (False, may, n, m))
	let initialObject selection = (Object 0 selection (Left $ Word "Times New Roman" 12 0 False False False "") mousedown mousemove mouseup, Inline)
	let initialParagraph selection = [(L, [initialObject selection])]
	let newTable = do
		textVal <- readIORef text
		(_, may, _, m) <- readIORef select
		maybe
			(do
				let ob = Object 0 Unselected (Right $ Left $ Table [(100, [initialParagraph Unselected])]) mousedown mousemove mouseup
				performCommand $ Insert (m + 1) [(L, [(ob, Inline)])])
			(const (return ()))
			may
	let newCol = do
		textVal <- readIORef text
		(_, may, _, m) <- readIORef select
		maybe
			newTable
			(\(n, col, _) -> performCommand $ NewCol n col (100, repeat (initialParagraph Unselected)))
			may
	let newRow = do
		textVal <- readIORef text
		(_, may, _, m) <- readIORef select
		maybe
			newTable
			(\(n, _, row) -> performCommand $ NewRow n row (repeat (initialParagraph Unselected)))
			may
	let delCol = do
		textVal <- readIORef text
		(_, Just (n, col, _), _, _) <- readIORef select
		performCommand $ if oneColTable (fst (toView textVal !! n)) then
				Delete n (n + 1)
			else
				DelCol n col
	let delRow = do
		textVal <- readIORef text
		(_, Just (n, _, row), _, _) <- readIORef select
		performCommand $ if oneRowTable (fst (toView textVal !! n)) then do
				Delete n (n + 1)
			else
				DelRow n row
	let doSave wnd = fileSave wnd filt "hos" >>= maybe
		(return False)
		(\path -> do
			textVal <- readIORef text
			undoVal <- readIORef undo
			encodeFile path (fromZipper textVal, undoVal)
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
	let doOpen wnd = promptForSave wnd $ fileOpen wnd filt "hos" >>= maybe
		(return ())
		(\path -> do
			(textVal, undoVal) <- decodeFile path
			writeIORef text $ fromView (renumber (toZipper textVal)) $ map (first $ \x -> x { mousedown = mousedown, mousemove = mousemove, mouseup = mouseup }) $ toView $ renumber (toZipper textVal)
			writeIORef undo undoVal
			writeIORef changed False
			setWindowText wnd $ "Hoss - " ++ path
			execOnChange)
	let newFile wnd = promptForSave wnd $ do
		writeIORef text ([], L, [initialObject Caret], [], [])
		writeIORef undo ([], [])
		writeIORef changed False
		execOnChange
	let copy = do
		textVal <- readIORef text
		(_, may, n, m) <- readIORef select
		doOnTables $ \get _ _ _ -> do
			textVal <- get
			let bytestring = SB.pack $ LB.unpack $ encode (let Insert _ ls = invertDelete n m textVal in ls)
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
		(_, _, n, m) <- readIORef select
		doOnTables $ \_ _ _ performCommand -> do
			copy
			performCommand (if m < n then Delete m n else Delete n m)
	let paste = do
		textVal <- readIORef text
		(_, _, _, n) <- readIORef select
		doOnTables $ \get _ _ performCommand -> do
			textVal <- get
			insetWnd <- readIORef inset
			openClipboard insetWnd
			catch (finally (do
				hdl <- getClipboardData format
				p <- globalLock hdl
				len <- peekByteOff p 0
				bytestring <- unsafePackCStringLen (p `plusPtr` 4, len)
				let ls = decode $ LB.fromChunks [bytestring]
				performCommand $ Insert (n + 1) $ fromView0 ls $ map (first $ \x -> x { mousedown = mousedown, mousemove = mousemove, mouseup = mouseup }) $ toView0 ls
				globalUnlock' hdl
				return ())
				closeClipboard)
				(\(_ :: SomeException) -> return ())
	let setJustification just = do
		textVal <- readIORef text
		(_, may, n, m) <- readIORef select
		doOnTables $ \get put _ _ -> do
			textVal <- get
			put $ setJustif just n m textVal
	let setFloated flt' = do
		textVal <- readIORef text
		doOnTables $ \get put _ _ -> do
			textVal <- get
			put $ fromView textVal $ map (\(x, flt) -> (x, if not (isLeft (obj x)) && selection x == Selected then flt' else flt)) (toView textVal)
	let printing = do
		textVal <- readIORef text
		printer $ \printerDC -> untilM (\(_, _, _, aft, aftBig) -> return $ null aft && null aftBig)
			(\textVal -> do
				let lay = layout 2250 ((0, 0), (2250, 0), 0) (fromZipper textVal)
				let cutoff = maybe lay (\n -> take (n `max` 1) lay) (findIndex (\(_, y, (el, _)) -> y + height el > 2700) lay)
				startPage printerDC
				mapM_ (\(x, y, (el, _)) -> draw printerDC (x + 300, y + 300) el) cutoff
				endPage printerDC
				let (_, _, (el, _)) = last cutoff
				return $ delete (position el + 1) textVal)
			(goto 0 textVal)
	frameWindow "Hoss" Nothing Nothing $ \dialogs wnd msg wParam lParam -> if msg == wM_CREATE then do
			hdl <- getModuleHandle Nothing
 			initControls wnd hdl fontRef sizeRef clrRef clrRef2 undoRef redoRef delColRef delRowRef setJustification setFloated execOnChange mousedown mousemove mouseup undoCommand redoCommand doSave doOpen newFile cut copy paste newCol newRow delCol delRow printing text undo
			let name = mkClassName "Frame"
			insetWnd <- createWindow name "" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) Nothing Nothing Nothing Nothing (Just wnd) Nothing hdl (\wnd msg wParam lParam -> do
				textVal <- readIORef text
				(_, _, n, m) <- readIORef select
				doOnTables (insetProc format fontRef sizeRef clrRef mousedown mousemove mouseup wnd msg wParam lParam n m))
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
			(_, _, n, m) <- readIORef select
			when (loWord wParam == iDOK) $ doOnTables $ \get put _ performCommand -> do
				textVal <- get
				if focus == Just insetWnd then
						performCommand (enterKey (goto (n + 1) textVal))
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

instance Eq Object where
	x == y = obj x == obj y

instance Show Object where
	show x = case obj x of
		Left wrd -> "makeObject " ++ show (selection x) ++ " " ++ show (string wrd)
		_ -> "Object _ " ++ show (selection x) ++ " " ++ show (obj x) ++ " _ _ _"

makeWord s = Word "" 0 0 False False False s

makeObject sel s = Object undefined sel (Left (makeWord s)) undefined undefined undefined 

instance Arbitrary Word where
	arbitrary = MkGen $ \gen _ -> makeWord (show (fst (random gen) :: Int))
	shrink _ = []

instance Arbitrary Selection where
	arbitrary = MkGen $ \gen _  -> case fst (randomR (0, 2) gen) :: Int of
		0 -> Unselected
		1 -> Caret
		2 -> Selected
	shrink _ = []

instance Arbitrary Object where
	arbitrary = liftM2 (\x y -> Object 0 x (Left y) undefined undefined undefined) arbitrary arbitrary

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

{-instance Arbitrary Command where
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
				return $ Alter y (show z)
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
	shrink _ = []-}
