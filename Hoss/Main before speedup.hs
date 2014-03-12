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

data SelectionState = None | Sel (Maybe (Int, Int, Int)) Int | Drag Int Int Int32

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

data Command = Insert Int [Paragraph Object] | Delete Int Int | Alter Int String | InTable Int Int Int Command | NewCol Int Int (Int32, [[Paragraph Object]]) | NewRow Int Int [[Paragraph Object]] | DelCol Int Int | DelRow Int Int deriving (Eq, Show)

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

invertDelete n m ((just, ls):xs) = if null xs || n <= position (fst (head (snd (head xs)))) then
		Insert n $ (L, takeWhile ((<m) . position . fst) (dropWhile ((<n) . position . fst) ls)) : inv xs
	else
		invertDelete n m xs where
	inv ((just, ls):xs) = if m <= position (fst (head ls)) then
			[]
		else
			(just, takeWhile ((<m) . position . fst) ls) : inv xs
	inv [] = []

changeAt n f ls = take n ls ++ f (ls !! n) : drop (n + 1) ls

invert (Insert n ls) _ = Delete n (n + length (concatMap snd ls))
invert (Delete n m) textVal = invertDelete n m textVal
invert (Alter n _) textVal = Alter n (let Left wrd = obj (fst (toView textVal !! n)) in string wrd)
invert (InTable n col row cmd) textVal = InTable n col row $ invert cmd $ snd (contents (let Right (Left tbl) = obj (fst (toView textVal !! n)) in tbl) !! col) !! row
invert (NewCol n m _) _ = DelCol n m
invert (NewRow n m _) _ = DelRow n m
invert (DelCol n m) textVal = NewCol n m $ let Right (Left (Table contents)) = obj (fst (toView textVal !! n)) in second (map clearSelection) $ contents !! m
invert (DelRow n m) textVal = NewRow n m $ let Right (Left (Table contents)) = obj (fst (toView textVal !! n)) in map clearSelection $ transpose (map snd contents) !! m

perform (Insert n ls) textVal = setCaret n $ insert n ls textVal
perform (Delete n m) textVal = setCaret ((n - 1) `max` 0) $ delete n m textVal
perform (Alter n s) textVal = alter n (\(Left x) -> Left $ x { string = s }) textVal
perform (InTable n col row cmd) textVal = alter n (\(Right (Left tbl)) -> Right $ Left $ Table $ changeAt col (second $ changeAt row $ perform cmd) (contents tbl)) textVal
perform (NewCol n m paras) textVal = alter n (\x -> let Right (Left (Table contents)) = x in
	Right $ Left $ Table $ take m contents ++ second (take (length $ snd $ head contents)) paras : drop m contents)
	textVal
perform (NewRow n m paras) textVal = alter n (\x -> let Right (Left (Table contents)) = x in
	Right $ Left $ Table $ map (\(i, pr) -> second (\x -> take m x ++ paras !! i : drop m x) pr) (zip [0..] contents))
	textVal
perform (DelCol n m) textVal = maybe altered (\(x, col, _) -> if x == n && col == m then setCaret x altered else altered) may where
	(may, n2, m2) = fromJust $ getSelection $ toView textVal
	altered = alter n (\x -> let Right (Left (Table contents)) = x in
		Right $ Left $ Table $ take m contents ++ drop (m + 1) contents) textVal
perform (DelRow n m) textVal = maybe altered (\(x, _, row) -> if x == n && row == m then setCaret x altered else altered) may where
	(may, n2, m2) = fromJust $ getSelection $ toView textVal
	altered = alter n (\x -> let Right (Left (Table contents)) = x in
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
		return (x + 3, y)
	flowMeasure (Object _ _ (Right (Left (Table contents))) _ _ _) = (padding + sum (map ((+padding) . fst) contents),
		padding + sum (map (\(col, ls) -> padding + maximum (map (measureCell (fst (contents !! col))) ls)) $ zip [0..] $ transpose $ map snd contents))
	draw dc (x, y) obj@(Object _ selected (Left (Word font size clr bold italic underline s)) _ _ _) = do
		if selected == Selected then do
				c_SetBkColor dc 0
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

toView ls = concatMap snd ls 

fromView ((just, ls):xs) view = (just, take (length ls) view) : fromView xs (drop (length ls) view)
fromView [] _ = []

renumber n ((just, ls):xs) = (just, zipWith (\(x, f) i -> (x { position = i, obj = case obj x of
	Left _ -> obj x
	Right (Left (Table contents)) -> Right $ Left $ Table $ map (second (map (renumber 0))) contents }, f)) ls [n..]) : renumber (n + length ls) xs
renumber _ [] = []

insert i ins ((just, ls):xs) = if null xs || i <= position (fst (head (snd (head xs)))) then
		let j = i - position (fst (head ls)) in
		if null (tail ins) then
			(just, take j ls ++ snd (head ins) ++ drop j ls) : xs
		else
			(just, take j ls ++ snd (head ins)) : init (tail ins) ++ second (++drop j ls) (last ins) : xs
	else
		(just, ls) : insert i ins xs

delete n m ((just, ls):xs) = if null xs || n <= position (fst (head (snd (head xs)))) then
		let (toJoin, rest) = del ((just, ls) : xs) in
			(just, takeWhile ((<n) . position . fst) ls ++ toJoin) : rest
	else
		(just, ls) : delete n m xs where
	del ((just, ls):xs) = if null xs || m <= position (fst (head (snd (head xs)))) then
			(dropWhile ((<m) . position . fst) ls, xs)
		else
			del xs
	del [] = ([], [])

alter i f ls = fromView ls (take i (toView ls) ++ first (\x -> x { obj = f (obj x) }) (toView ls !! i) : drop (i + 1) (toView ls))

clearSelection ls = fromView ls $ map (first $ \x -> (case obj x of
	Right (Left (Table contents)) -> x { obj = Right $ Left $ Table $ map (second $ map clearSelection) contents }
	_ -> x) { selection = Unselected }) $ toView ls

enterKey i ((just, x):xs) = if null xs || i <= position (fst (head (snd (head xs)))) then
		Insert i [(L, []), (just, [(funOnWord (\x -> x { string = "" }) $ fst $ findWord (length x) x, Inline)])]
	else
		enterKey i xs

onBoundary _ [] = False
onBoundary 0 _ = True
onBoundary n ((_, ls):xs) = if n < length ls then
		False
	else
		onBoundary (n - length ls) xs

funOnWord f (Object a b (Left wrd) c d e) = Object a b (Left (f wrd)) c d e
funOnWord _ obj = obj

isLeft (Left _) = True
isLeft _ = False

findWord caret txt = fromJust $ find (isLeft . obj . fst) $ reverse $ take caret txt

setCaret location ls = fromView ls (take location (toView (clearSelection ls)) ++ first (\x -> x { selection = Caret }) (toView ls !! location) : drop (location + 1) (toView (clearSelection ls)))

setSelection n m ls = fromView ls (take n (toView (clearSelection ls)) ++ map (first (\x -> x { selection = Selected })) (take (m - n) (drop n (toView ls))) ++ drop m (toView (clearSelection ls)))

getSelection ((x, flt):xs) = case selection x of
	Selected -> Just (Nothing, position x, sel ((x, flt):xs))
	Caret -> Just (Nothing, position x, position x)
	Unselected -> case obj x of
			Right (Left (Table contents)) -> foldr mplus mzero $ concatMap (\(colN, (_, col)) -> map (\(row, y) -> fmap (\(_, n, m) -> (Just (position x, colN, row), n, m)) $ getSelection $ toView y) (zip [0..] col)) (zip [0..] contents)
			_ -> Nothing
		`mplus` getSelection xs
	where
		sel [(x, _)] = if selection x == Unselected then
				position x
			else
				position x + 1
		sel ((x, _):xs) = if selection x == Unselected then
			position x
		else
			sel xs
getSelection [] = Nothing

setJustif just' n m ((just, ls):xs) = if null xs || n <= position (fst (head (snd (head xs)))) then
		justif ((just, ls) : xs)
	else
		(just, ls) : setJustif just' n m xs where
	justif ((just, ls):xs) = if m <= position (fst (head ls)) then
			(just, ls) : xs
		else
			(just', ls) : justif xs
	justif [] = []

untilM f g x = do
	b <- f x
	if b then
		return x
	else do
		y <- g x
		untilM f g y

measureCell wid cell = maximum $ map (\(_, y, (el, _)) -> y + height el) $ layout wid ((0, 0), (wid, 0), 0) cell

oneCellTable ob = null (tail contents) && null (tail (snd (head contents))) where
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

insetProc format fontRef sizeRef clrRef mousedown mousemove mouseup wnd msg wParam lParam n m get put _ performCommand = if msg == wM_GETDLGCODE then
		return (dLGC_WANTCHARS .|. dLGC_WANTARROWS)
	else if msg == wM_KEYDOWN then do
		textVal <- get
		if n /= m then
			if wParam == vK_BACK || wParam == vK_DELETE then do
					performCommand (if m < n then Delete m n else Delete n m)
				else
					return ()
			else
				if wParam == vK_LEFT then
					put $ setCaret ((m - 1) `max` 0) textVal
				else if wParam == vK_RIGHT then
					put $ setCaret ((m + 1) `min` (length (toView textVal) - 1)) textVal
				else if wParam == vK_SPACE then
					performCommand (Insert (m + 1) [(L, [first (funOnWord (\x -> x { string = " " })) (findWord (m + 1) (toView textVal))])])
				else if wParam == vK_BACK then
					when (m /= 0) $ performCommand $ case obj (fst (toView textVal !! m)) of
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
		caret <- if onBoundary m textVal then do
				performCommand (Insert (m + 1) [(L, [(funOnWord (\x -> x { string = " " }) $ fst $ findWord (m + 1) (toView textVal), Inline)])])
				return (m + 1)
			else
				return m
		textVal <- get
		performCommand (Alter caret (let Left wrd = obj (fst (toView textVal !! caret)) in string wrd ++ [chr (fromIntegral wParam)]))
		return 0
	else
		defWindowProc (Just wnd) msg wParam lParam

main = do
	text <- newIORef []
	undo <- newIORef ([], [])
	select <- newIORef None
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
		readIORef onChange >>= id
		(bef, aft) <- readIORef undo
		undoCtrl <- readIORef undoRef
		redoCtrl <- readIORef redoRef
		delCol <- readIORef delColRef
		delRow <- readIORef delRowRef
		showWindow undoCtrl (if null bef then sW_HIDE else sW_SHOW)
		showWindow redoCtrl (if null aft then sW_HIDE else sW_SHOW)
		textVal <- readIORef text
		let (may, n, _) = fromJust $ getSelection $ toView textVal
		if isNothing may then do
				showWindow delCol sW_HIDE
				showWindow delRow sW_HIDE
			else do
				showWindow delCol sW_SHOW
				showWindow delRow sW_SHOW
		doOnTables may $ \get _ _ _ -> do
			textVal <- get
			let (x, _) = toView textVal !! n
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
	    undoCommand = do
		(x:bef, aft) <- readIORef undo
		textVal <- readIORef text
		writeIORef undo (bef, invert x textVal : aft)
		writeIORef text (renumber 0 (perform x textVal))
		execOnChange
	    redoCommand = do
		(bef, x:aft) <- readIORef undo
		textVal <- readIORef text
		writeIORef undo (invert x textVal : bef, aft)
		writeIORef text (renumber 0 (perform x textVal))
		execOnChange
	    performCommand x = do
		(bef, _) <- readIORef undo
		writeIORef undo (bef, [x])
		redoCommand
		writeIORef changed True
	    doOnTables :: Maybe (Int, Int, Int) -> (IO [Paragraph Object] -> ([Paragraph Object] -> IO ()) -> ([Paragraph Object] -> IO ()) -> (Command -> IO ()) -> IO t) -> IO t
	    doOnTables may f = maybe
		(f (readIORef text) (\x -> writeIORef text x >> execOnChange) (\x -> writeIORef text x >> execOnChange) performCommand)
		(\(n, col, row) -> f (do
				textVal <- readIORef text
				let Right (Left tbl) = obj (fst (toView textVal !! n))
				return $ snd (contents tbl !! col) !! row)
			(\newText -> do
				modifyIORef text $ alter n (\(Right (Left tbl)) -> Right $ Left $ Table $ changeAt col (second $ changeAt row $ const newText) (contents tbl))
				execOnChange)
			(\newText -> do
				modifyIORef text $ alter n (\(Right (Left tbl)) -> Right $ Left $ Table $ changeAt col (second $ changeAt row $ const newText) (contents tbl)) . clearSelection
				execOnChange)
			(\cmd -> performCommand (InTable n col row cmd)))
		may
	let mousemove (x, y) pr ob = do
		textVal <- readIORef text
		sel <- readIORef select
		case sel of
			Sel may m -> do
				(may2, xPos, yPos, idx) <- getCell (x, y) pr ob
				when (may == may2) $ doOnTables may $ \get _ putClearingSelection performCommand -> do
					textVal <- get
					let n = idx + if x < xPos + width (fst (toView textVal !! idx)) && y < yPos + height (fst (toView textVal !! idx)) then 0 else 1
					if m == n then
							putClearingSelection (setCaret ((idx - 1) `max` 0) textVal)
						else unless (idx == 0 || m == 0) $ do
							putClearingSelection ((if n < m then
									setSelection n m
								else
									setSelection m n)
								textVal)
			Drag n col interval -> do
				writeIORef text $ fromView textVal $ changeAt n (first $ \ob -> ob { obj = let Right (Left (Table contents)) = obj ob in Right $ Left $ Table $ changeAt col (first $ const $ interval + x) contents }) (toView textVal)
				execOnChange
			None -> return ()
	let mousedown pr pr2 ob = do
		textVal <- readIORef text
		case getCellEdge pr pr2 ob of
			Just i -> let Right (Left (Table contents)) = obj ob in
				writeIORef select $ Drag (position ob) i (fst (contents !! i) - fst pr)
			Nothing -> do
				(may, _, _, pos) <- getCell pr pr2 ob
				writeIORef select $ Sel may pos
		mousemove pr pr2 ob
	let mouseup = writeIORef select None
	let initialParagraph selection = [(L, [(Object 0 selection (Left $ Word "Times New Roman" 12 0 False False False "") mousedown mousemove mouseup, Inline)])]
	let newTable = do
		textVal <- readIORef text
		let (may, _, m) = fromJust $ getSelection $ toView textVal
		maybe
			(do
				let ob = Object 0 Unselected (Right $ Left $ Table [(100, [initialParagraph Unselected])]) mousedown mousemove mouseup
				performCommand $ Insert (m + 1) [(L, [(ob, Inline)])])
			(const (return ()))
			may
	let newCol = do
		textVal <- readIORef text
		let (may, _, _) = fromJust $ getSelection $ toView textVal
		maybe
			newTable
			(\(n, col, _) -> performCommand $ NewCol n col (100, repeat (initialParagraph Unselected)))
			may
	let newRow = do
		textVal <- readIORef text
		let (may, _, _) = fromJust $ getSelection $ toView textVal
		maybe
			newTable
			(\(n, _, row) -> performCommand $ NewRow n row (repeat (initialParagraph Unselected)))
			may
	let delCol = do
		textVal <- readIORef text
		let (Just (n, col, _), _, _) = fromJust $ getSelection $ toView textVal
		if oneCellTable (fst (toView textVal !! n)) then
				performCommand $ Delete n (n + 1)
			else
				performCommand $ DelCol n col
	let delRow = do
		textVal <- readIORef text
		let (Just (n, _, row), _, _) = fromJust $ getSelection $ toView textVal
		if oneCellTable (fst (toView textVal !! n)) then do
				performCommand $ Delete n (n + 1)
			else
				performCommand $ DelRow n row
	let doSave wnd = fileSave wnd filt "hos" >>= maybe
		(return False)
		(\path -> do
			textVal <- readIORef text
			undoVal <- readIORef undo
			encodeFile path (textVal, undoVal)
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
			writeIORef text $ setCaret 0 $ renumber 0 $ fromView textVal $ map (first $ \x -> x { mousedown = mousedown, mousemove = mousemove, mouseup = mouseup }) $ toView textVal
			writeIORef undo undoVal
			writeIORef changed False
			setWindowText wnd $ "Hoss - " ++ path
			execOnChange)
	let newFile wnd = promptForSave wnd $ do
		writeIORef text (initialParagraph Caret)
		writeIORef changed False
		execOnChange
	let copy = do
		textVal <- readIORef text
		let (may, n, m) = fromJust $ getSelection $ toView textVal
		doOnTables may $ \get _ _ _ -> do
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
		let (may, n, m) = fromJust $ getSelection $ toView textVal
		doOnTables may $ \_ _ _ performCommand -> do
			copy
			performCommand (if m < n then Delete m n else Delete n m)
	let paste = do
		textVal <- readIORef text
		let (may, _, n) = fromJust $ getSelection $ toView textVal
		doOnTables may $ \get _ _ performCommand -> do
			textVal <- get
			insetWnd <- readIORef inset
			openClipboard insetWnd
			catch (finally (do
				hdl <- getClipboardData format
				p <- globalLock hdl
				len <- peekByteOff p 0
				bytestring <- unsafePackCStringLen (p `plusPtr` 4, len)
				let ls = decode $ LB.fromChunks [bytestring]
				performCommand $ Insert (n + 1) $ fromView ls $ map (first $ \x -> x { mousedown = mousedown, mousemove = mousemove, mouseup = mouseup }) $ toView ls
				globalUnlock' hdl
				return ())
				closeClipboard)
				(\(_ :: SomeException) -> return ())
	let setJustification just = do
		textVal <- readIORef text
		let (may, n, m) = fromJust $ getSelection $ toView textVal
		doOnTables may $ \get put _ _ -> do
			textVal <- get
			put $ setJustif just n m textVal
	let setFloated flt' = do
		textVal <- readIORef text
		let (may, n, m) = fromJust $ getSelection $ toView textVal
		doOnTables may $ \get put _ _ -> do
			textVal <- get
			put $ fromView textVal $ map (\(x, flt) -> (x, if not (isLeft (obj x)) && selection x == Selected then flt' else flt)) (toView textVal)
	let printing = do
		textVal <- readIORef text
		printer $ \printerDC -> untilM (\textVal -> return $ null (tail textVal) && null (snd (head textVal)))
			(\textVal -> do
				let lay = layout 2250 ((0, 0), (2250, 0), 0) textVal
				let cutoff = maybe lay (\n -> take (n `max` 1) lay) (findIndex (\(_, y, (el, _)) -> y + height el > 2700) lay)
				startPage printerDC
				mapM_ (\(x, y, (el, _)) -> draw printerDC (x + 300, y + 300) el) cutoff
				endPage printerDC
				let (_, _, (el, _)) = last cutoff
				return $ delete 0 (position el + 1) textVal)
			textVal
	frameWindow "Hoss" Nothing Nothing $ \dialogs wnd msg wParam lParam -> if msg == wM_CREATE then do
			hdl <- getModuleHandle Nothing
 			initControls wnd hdl fontRef sizeRef clrRef clrRef2 undoRef redoRef delColRef delRowRef setJustification setFloated execOnChange mousedown mousemove mouseup undoCommand redoCommand doSave doOpen newFile cut copy paste newCol newRow delCol delRow printing text undo
			let name = mkClassName "Frame"
			insetWnd <- createWindow name "" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) Nothing Nothing Nothing Nothing (Just wnd) Nothing hdl (\wnd msg wParam lParam -> do
				textVal <- readIORef text
				let (may, n, m) = fromJust $ getSelection $ toView textVal
				doOnTables may (insetProc format fontRef sizeRef clrRef mousedown mousemove mouseup wnd msg wParam lParam n m))
			writeIORef inset insetWnd
			proc <- attachLayout text insetWnd
			writeIORef onChange proc
			newFile wnd
			modifyIORef dialogs (wnd:)
			sendMessage wnd wM_SIZE 0 0
			return 0
		else if msg == wM_COMMAND then do
			focus <- getFocus
			insetWnd <- readIORef inset
			textVal <- readIORef text
			let (may, _, n) = fromJust $ getSelection $ toView textVal
			when (loWord wParam == iDOK) $ doOnTables may $ \get put _ performCommand -> do
				textVal <- get
				if focus == Just insetWnd then
						performCommand (enterKey (n + 1) textVal)
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

-- Tests and debugging stuff

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
	shrink _ = []

conformToInvariant textVal = fromView generated $ case getSelection (toView generated) of
		Just (_, n, m) -> take (if n == m then m + 1 else m) (toView generated) ++ map (first $ \x -> x { selection = Unselected }) (drop m (toView generated))
		Nothing -> first (\x -> x { selection = Caret }) (head (toView generated)) : tail (toView generated)
	where generated = renumber 0 $ map (\(just, ls) -> (just, (makeObject Unselected "", Inline) : map (first $ \(Object a b (Left wrd) _ _ _) -> Object a b (Left (wrd { string = ' ' : string wrd })) undefined undefined undefined) ls)) textVal

laxInvariant ls = not (null ls) && isJust (getSelection (toView ls)) && isNothing (getSelection (drop (case fromJust $ getSelection (toView ls) of
	(Nothing, n, m) -> if n == m then m + 1 else m
	(Just (x, _, _), _, _) -> x + 1) (toView ls))) && all (\(_, ls) -> all (\(ob, _) -> case obj ob of
		Left wrd -> not (null (string wrd)) && head (string wrd) == ' '
		Right _ -> True) (tail ls)) ls

invariant ls = laxInvariant ls && all (\(_, ls) -> not (null ls) && case obj (fst (head ls)) of
	Left wrd -> null (string wrd)
	Right _ -> False)
	ls

validCommand (Insert n ls) (textVal :: [Paragraph Object]) = n >= 1 && not (null ls) && n + length ls <= position (fst (last (toView textVal))) + 1 && if null (tail ls) then
		laxInvariant ls
	else
		invariant (tail (init ls)) && laxInvariant [head ls] && laxInvariant [last ls]
validCommand (Delete n m) textVal = n >= 1 && n <= m && m <= position (fst (last (toView textVal))) + 1
validCommand (Alter n s) textVal = n >= 1 && n <= position (fst (last (toView textVal))) && not (null s) && head s == ' '
validCommand (InTable n col row cmd) textVal = n < position (fst (last (toView textVal))) && case obj (fst (toView textVal !! n)) of
	Right (Left (Table contents)) -> length contents > col && length (snd (contents !! col)) > row && validCommand cmd (snd (contents !! col) !! row)
	_ -> False
validCommand (DelCol n m) textVal = n < position (fst (last (toView textVal))) && case obj (fst (toView textVal !! n)) of
	Right (Left (Table contents)) -> length contents > m
	_ -> False
validCommand (DelRow n m) textVal = n < position (fst (last (toView textVal))) && case obj (fst (toView textVal !! n)) of
	Right (Left (Table contents)) -> length (snd (head contents)) > m
	_ -> False
validCommand (NewCol n m _) textVal = n < position (fst (last (toView textVal))) && case obj (fst (toView textVal !! n)) of
	Right (Left (Table contents)) -> length contents > m
	_ -> False
validCommand (NewRow n m _) textVal = n < position (fst (last (toView textVal))) && case obj (fst (toView textVal !! n)) of
	Right (Left (Table contents)) -> length (snd (head contents)) > m
	_ -> False

invariantPreserving cmd textVal = not (null textVal) ==> validCommand cmd (conformToInvariant textVal) ==> invariant (perform cmd (conformToInvariant textVal))

inverseValid cmd textVal = not (null textVal) ==> validCommand cmd (conformToInvariant textVal) ==> validCommand (invert cmd (conformToInvariant textVal)) (renumber 0 (perform cmd (conformToInvariant textVal)))

theForwards cmd textVal = renumber 0 (perform cmd (conformToInvariant textVal))

theInverse cmd textVal = renumber 0 (perform (invert cmd (conformToInvariant textVal)) (theForwards cmd textVal))

inverse cmd textVal = not (null textVal) ==> validCommand cmd (conformToInvariant textVal) ==> theInverse cmd textVal == conformToInvariant textVal

inverse2 cmd textVal = not (null textVal) ==> validCommand cmd (conformToInvariant textVal) ==> invert (invert cmd (conformToInvariant textVal)) (theForwards cmd textVal) == cmd

overlapping (x1, y1, x2, y2) (x3, y3, x4, y4) = (x1 <= x3 && x3 < x2 || x1 < x4 && x4 <= x2) && (y1 <= y3 && y3 < y2 || y1 < y4 && y4 <= y2)

toRect (x, y, (el, _)) = (x, y, x + width el, y + height el)

overlap :: [Paragraph Object] -> Bool
overlap ls = all (\(n, x) -> all (\(m, y) -> n == m || not (overlapping (toRect x) (toRect y))) (zip [0..] lay)) (zip [0..] lay) where
	lay = layout 200 ((0, 0), (200, 0), 0) ls