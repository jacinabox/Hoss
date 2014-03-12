{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import Graphics.Layout
import Graphics.Win32
import System.Win32.DLL
import System.IO.Unsafe
import System.Exit
import Control.Arrow
import Data.IORef
import Data.Char
import Data.List (find)
import Data.Int
import Data.Bits
import Data.Array (Ix(..))
import Data.Maybe
import Control.Monad
import Graphics.Layout
import Graphics.Displayable hiding (Selection, selection)
import Graphics.FrameWindow
import Graphics.Win32Extras
import Unsafe.Coerce
import Control.Exception
import Codec.BMP
import Data.Binary hiding (Word)

import Test.QuickCheck
import Test.QuickCheck.Gen
import System.Random

-- Invariants: Each paragraph begins with a word containing the empty string.
-- Every other word starts with a space.

data Selection = Unselected | Selected | Caret deriving Eq

data Table = Table {
	wnd :: HWND,
	reference :: IORef [Paragraph Object],
	onChg :: IO ()
	contents :: [Paragraph Object] }

data Word = Word {
	font :: String,
	size :: Int32,
	color :: COLORREF,
	bold :: Bool,
	italic :: Bool,
	underline :: Bool,
	string :: String } deriving (Eq, Show)

data Object = Object {
	position :: Int,
	selection :: Selection,
	obj :: Either Word (Either Table ()),
	mousedown :: (Int32, Int32) -> (Int32, Int32) -> Int -> IO (),
	mousemove :: (Int32, Int32) -> (Int32, Int32) -> Int -> IO (),
	mouseup :: IO () }

data Command = Insert Int [[(Object, Floated)]] | InsertEnter Int Just | Delete Int Int | DeleteEnter Int | Alter Int String | InTable Int Int Int Command deriving (Eq, Show)

instance Binary Table where
	put (Table _ contents) = put contents
	get = do
		ls <- get
		return (Table undefined undefined undefined ls)

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
	put (InsertEnter n jst) = do
		put (1 :: Word8)
		put n
		put jst
	put (Delete n m) = do
		put (2 :: Word8)
		put n
		put m
	put (DeleteEnter n) = do
		put (3 :: Word8)
		put n
	put (Alter n str) = do
		put (4 :: Word8)
		put n
		put str
	put (InTable n col row cmd) = do
		put (5 :: Word8)
		put n
		put col
		put row
		put cmd
	get = do
		(i :: Word8) <- get
		case i of
			0 -> liftM2 Insert get get
			1 -> liftM2 InsertEnter get get
			2 -> liftM2 Delete get get
			3 -> liftM DeleteEnter get
			4 -> liftM2 Alter get get
			5 -> liftM4 InTable get get get get

invertDelete n m ((just, ls):xs) = if null xs || n <= position (fst (head (snd (head xs)))) then
		Insert n $ takeWhile ((<m) . position . fst) (dropWhile ((<n) . position . fst) (tail ls)) : inv xs
	else
		invertDelete n m xs where
	inv ((_, ls):xs) = if position (fst (head ls)) >= m then
			[]
		else
			takeWhile ((<m) . position . fst) (tail ls) : inv xs
	inv [] = []

getJustification n ((just, _):xs) = if null xs || n < position (fst (head (snd (head xs)))) then
		just
	else
		getJustification n xs

changeAt n f ls = take n ls ++ f (ls !! n) : drop (n + 1) ls

invert (Insert n ls) _ = Delete n (n + length (head ls) + sum (map ((+1) . length) (tail ls)))
invert (InsertEnter n _) _ = DeleteEnter n
invert (Delete n m) textVal = invertDelete n m textVal
invert (DeleteEnter n) textVal = InsertEnter n (getJustification n textVal)
invert (Alter n _) textVal = Alter n (let Left wrd = obj (fst (toView textVal !! n)) in string wrd)
invert (InTable n col row cmd) textVal = InTable n row col $ invert cmd $ snd $ snd (contents (let Right (Left tbl) = obj (fst (toView textVal !! n)) in tbl) !! col) !! row

perform (Insert n ls) textVal = setCaret n $ foldr (uncurry insert) textVal (zip [n..] ls)
perform (InsertEnter n just) textVal = setCaret n $ enterKey just n textVal
perform (Delete n m) textVal = setCaret ((n - 1) `max` 0) $ deleteMany $ setSelection n m textVal
perform (DeleteEnter n) textVal = deleteEnter n textVal
perform (Alter n s) textVal = alter n (\(Left x) -> Left $ x { string = s }) textVal
perform (InTable n col row cmd) textVal = alter n (\(Right (Left tbl)) -> Right $ Left $ tbl { contents = changeAt col (second $ changeAt row $ second $ perform cmd) (contents tbl) }) textVal

createAFont dc font size bold italic underline = do
	logy <- getDeviceCaps dc lOGPIXELSY
	createFont (size * logy `div` 72) 0 0 0 (if bold then fW_BOLD else fW_NORMAL) italic underline False dEFAULT_CHARSET oUT_DEFAULT_PRECIS cLIP_DEFAULT_PRECIS dEFAULT_QUALITY fF_DONTCARE font

drawCaret dc (x, y) obj@(Object _ selected _ _ _ _) = when (selected == Caret) $ do
	let (wd, ht) = flowMeasure obj
	moveToEx dc (x + wd - 2) y
	lineTo dc (x + wd - 2) (y + ht)

instance Displayable Object where
	measure _ = (0, 0)
	flowMeasure (Object _ _ (Left (Word font size _ bold italic underline s)) _ _ _) = unsafePerformIO $ do
		dc <- getDC Nothing
		font <- createAFont dc font size bold italic underline
		oldFont <- selectFont dc font
		(x, y) <- getTextExtentPoint32 dc $ if null s then " " else s
		selectFont dc oldFont
		deleteFont font
		releaseDC Nothing dc
		return (x + 3, y)
	flowMeasure (Object _ _ (Right (Left (Table _ contents))) _ _ _) = (padding + sum (map ((+padding) . fst) contents),
		padding + sum (map (\(wid, ls) -> padding + maximum (map (measureCell wid) ls)) contents))
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
	draw dc (x, y) obj@(Object _ selected (Right (Left (Table wnd _ _ contents))) _ _ _) = do
		dc <- getDC (Just wnd)
		pen <- if selected == Selected then do
				black <- getStockBrush bLACK_BRUSH
				fillRect wnd (0, 0, 32767, 32767) black
				getStockPen wHITE_PEN
			else
				getStockPen bLACK_PEN
		oldPen <- selectPen dc pen
		withWindows obj $ \_ x y wid ht -> rectangle dc (x - 3) (y - 3) (x + wid + 3) (y + ht + 3)
		selectPen dc oldPen
		drawCaret dc (x, y) obj
		releaseDC (Just wnd) dc
	window (Object _ _ (Right (Left (Table wnd _))) _ _ _) = Just wnd
	window (Object _ _ _ _ _ _) = Nothing
	mouse MouseDown _ _ pr pr2 obj = mousedown obj pr pr2 (position obj)
	mouse MouseMove _ _ pr pr2 obj = mousemove obj pr pr2 (position obj)
	mouse MouseUp _ _ _ _ obj = mouseup obj

toView ls = concatMap snd ls 

fromView ((just, ls):xs) view = (just, take (length ls) view) : fromView xs (drop (length ls) view)
fromView [] _ = []

renumber n ((just, ls):xs) = (just, zipWith (\(x, f) i -> (x { position = i, obj = case obj x of
	Left _ -> obj x
	Right (Left (Table wnd contents)) -> Right $ Left $ Table wnd $ map (second (map (second (renumber 0)))) contents }, f)) ls [n..]) : renumber (n + length ls) xs
renumber _ [] = []

insert i ins ((just, ls):xs) = if null xs || i <= position (fst (head (snd (head xs)))) then
		(just, let j = i - position (fst (head ls)) in
			take j ls ++ ins ++ drop j ls) : xs
	else
		(just, ls) : insert i ins xs

delete i ((just, ls):xs) = if null xs || i <= position (fst (head (snd (head xs)))) then
	let j = i - position (fst (head ls)) in
		if j == 0 then
			Nothing
		else if j == length ls then
			Just (DeleteEnter i)
		else
			Just (Delete i (i + 1))
	else
		delete i xs

deleteMany textVal = map (\(just, ls) -> (just, head ls : filter ((/=Selected) . selection . fst) (tail ls))) textVal

deleteEnter i ((just, ls):xs) = if i <= position (fst (head (snd (head xs)))) then
		let (_, ls2) = head xs in
			(just, init ls ++ first (\x -> x { selection = Caret }) (last ls) : tail ls2) : tail xs
	else
		(just, ls) : deleteEnter i xs

alter i f ls = fromView ls (take i (toView ls) ++ first (\x -> x { obj = f (obj x) }) (toView ls !! i) : drop (i + 1) (toView ls))

findCaret ls = fmap (position . fst) $ find ((==Caret) . selection . fst) (toView ls)

clearSelection view = map (first (\x -> x { selection = Unselected })) view

enterKey just' i ((just, x):xs) = if null xs || i <= position (fst (head (snd (head xs)))) then
		let j = i - position (fst (head x)) in
			(just, take j x) : (just', (funOnWord (\x -> x { string = "" }) $ fst $ findWord (length x) x, Inline) : drop j x) : xs
	else
		(just, x) : enterKey just' i xs

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

setCaret location ls = fromView ls (take location (clearSelection (toView ls)) ++ first (\x -> x { selection = Caret }) (toView ls !! location) : drop (location + 1) (clearSelection (toView ls)))

setSelection n m ls = fromView ls (take n (clearSelection (toView ls)) ++ map (first (\x -> x { selection = Selected })) (take (m - n) (drop n (toView ls))) ++ drop m (clearSelection (toView ls)))

measureCell wid (_, cell) = maximum $ map (\(_, y, (el, _)) -> y + height el) $ layout wid ((0, 0), (wid, 0), 0) cell

toolbarHeight = 40

createAButton path x cmd wnd hdl = do
	Right bmp <- readBMP path
	ref <- newIORef bmp
	let name = mkClassName "Frame"
	wnd2 <- createWindow name "" (wS_VISIBLE .|. wS_CHILD) (Just x) (Just 4) (Just 32) (Just 32) (Just wnd) Nothing hdl $ \wnd msg wParam lParam -> if msg == wM_LBUTTONUP then do
			cmd
			return 0
		else
			defWindowProc (Just wnd) msg wParam lParam
	attachDisplay ref wnd2
	return wnd2

filt = "Hoss Files (*.hos)\0*.hos\0All Files\0*.*\0"

initControls wnd hdl fontRef sizeRef clrRef clrRef2 undoRef redoRef execOnChange mousedown mousemove mouseup undoCommand redoCommand doSave doOpen newFile tableCommand text undo = do
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
	createAButton "New.bmp" 340 (newFile wnd) wnd hdl
	createAButton "Open.bmp" (340 + 32) (doOpen wnd) wnd hdl
	createAButton "Save.bmp" (340 + 2 * 32) (doSave wnd) wnd hdl
	createAButton "Cut.bmp" (340 + 3 * 32) undefined wnd hdl
	createAButton "Copy.bmp" (340 + 4 * 32) undefined wnd hdl
	createAButton "Paste.bmp" (340 + 5 * 32) undefined wnd hdl
	undo <- createAButton "Undo.bmp" (340 + 6 * 32) undoCommand wnd hdl
	redo <- createAButton "Redo.bmp" (340 + 7 * 32) redoCommand wnd hdl
	createAButton "Table.bmp" (340 + 8 * 32) tableCommand wnd hdl
	writeIORef undoRef undo
	writeIORef redoRef redo

getIndex :: HWND -> IO Int
getIndex wnd = do
	parent <- getParent wnd
	liftM unsafeCoerce (getWindowLongPtr parent gWLP_USERDATA)

realizeTable text insetWnd ob inTableProc = case obj ob of
	Right (Left tbl) -> do
		hdl <- getModuleHandle Nothing
		let name = mkClassName "Frame"
		nested <- createWindow name "" (wS_VISIBLE .|. wS_CHILD) (Just 10) (Just 10) (Just 10) (Just 10) (Just insetWnd) Nothing hdl (defWindowProc . Just)
		c_SetWindowLongPtr outer gWLP_USERDATA (unsafeCoerce (position ob))
		ref <- newIORef (contents tbl)
		onChange <- attachLayout ref outer
		select <- newIORef (False, 0, 0)
		textVal <- readIORef text
		writeIORef text $ alter (position ob) (const $ Right (Left (Table nested ref onChange (contents tbl)))) textVal
		sizeTable ob
	_ -> return ()

insetProc get put performCommand select wnd msg wParam lParam = if msg == wM_GETDLGCODE then
		return (dLGC_WANTCHARS .|. dLGC_WANTARROWS .|. dLGC_DEFPUSHBUTTON)
	else if msg == wM_KEYDOWN then do
		textVal <- get wnd
		maybe
			(if wParam == vK_BACK || wParam == vK_DELETE then do
					(_, m, n) <- readIORef select
					performCommand wnd (if m < n then Delete m n else Delete n m)
				else
					return ())
			(\caret -> if wParam == vK_LEFT then
					put wnd $ setCaret ((caret - 1) `max` 0) textVal
				else if wParam == vK_RIGHT then
					put wnd $ setCaret ((caret + 1) `min` (length (toView textVal) - 1)) textVal
				else if wParam == vK_SPACE then
					performCommand wnd (Insert (caret + 1) [[first (funOnWord (\x -> x { string = " " })) (findWord (caret + 1) (toView textVal))]])
				else if wParam == vK_BACK then
					maybe
						(return ())
						(performCommand wnd)
						(delete caret textVal)
				else if wParam == vK_RETURN then
					maybe
						(return ())
						(\caret -> performCommand wnd (InsertEnter (caret + 1) (getJustification caret textVal)))
						(findCaret textVal)
				else
					return ())
			(findCaret textVal)
		return 0
	else if msg == wM_LBUTTONUP then do
		setFocus wnd
		return 0
	else if msg == wM_CHAR && wParam /= 8 && wParam /= 32 then do
		textVal <- get wnd
		maybe
			(return ())
			(\caret -> do
				caret' <- if onBoundary caret textVal then do
						performCommand wnd (Insert (caret + 1) [[first (funOnWord (\x -> x { string = " " })) (findWord (caret + 1) (toView textVal))]])
						return (caret + 1)
					else
						return caret
				textVal <- get wnd
				performCommand wnd (Alter caret' (let Left wrd = obj (fst (toView textVal !! caret')) in string wrd ++ [chr (fromIntegral wParam)])))
			(findCaret textVal)
		return 0
	else
		defWindowProc (Just wnd) msg wParam lParam

main = do
	text <- newIORef []
	undo <- newIORef ([], [])
	select <- newIORef (False, 0, 0)
	onChange <- newIORef undefined
	inset <- newIORef undefined
	fontRef <- newIORef undefined
	sizeRef <- newIORef undefined
	clrRef <- newIORef (rgb 0 0 0)
	clrRef2 <- newIORef undefined
	undoRef <- newIORef undefined
	redoRef <- newIORef undefined
	changed <- newIORef False
	let execOnChange = do
		readIORef onChange >>= id
		textVal <- readIORef text
		mapM_ (\(ob, _) -> case obj ob of
			Right (Left tbl) -> do
				mapM_ (\((_, ref, m), ls) -> writeIORef ref ls >> m) (concatMap snd (contents tbl))
				c_SetWindowLongPtr (wnd tbl) gWLP_USERDATA (unsafeCoerce (position ob))
				return ()
			_ -> return ()) (toView textVal)
		(bef, aft) <- readIORef undo
		undoCtrl <- readIORef undoRef
		redoCtrl <- readIORef redoRef
		showWindow undoCtrl (if null bef then sW_HIDE else sW_SHOW)
		showWindow redoCtrl (if null aft then sW_HIDE else sW_SHOW)
		maybe
			(return ())
			(\n -> let (x, _) = toView textVal !! n in
				case obj x of
					Left x -> do
						fontCtrl <- readIORef fontRef
						sizeCtrl <- readIORef sizeRef
						setWindowText fontCtrl (font x)
						setWindowText sizeCtrl (show (size x))
						writeIORef clrRef (color x)
						clrCtrl <- readIORef clrRef2
						invalidateRect (Just clrCtrl) Nothing True
					_ -> return ())
			(findCaret textVal)
	let mousemove wnd (x, y) (xPos, yPos) idx = do
		textVal <- readIORef text
		let n = idx + if x < xPos + width (fst (toView textVal !! idx)) && y < yPos + height (fst (toView textVal !! idx)) then 0 else 1
		(b, m, _) <- readIORef select
		when b $ do
			modifyIORef text (if n == m then
					setCaret ((n - 1) `max` 0)
				else if n < m then
					setSelection n m
				else do
					setSelection m n)
			writeIORef select (True, m, n)
			execOnChange
	let mousedown wnd pr pr2 n = do
		writeIORef select (True, n, n)
		mousemove wnd pr pr2 n
	let mouseup wnd = modifyIORef select (\(_, m, n) -> (False, m, n))
	let initialParagraph = [(L, [(Object 0 Caret (Left $ Word "Times New Roman" 12 0 False False False "") (mousedown wnd) (mousemove wnd) (mouseup wnd), Inline)])]
	let
		performCommand2 x textVal = do
			writeIORef text (renumber 0 (perform x textVal))
			case x of
				Insert n ls -> do
					insetWnd <- readIORef inset
					textVal <- readIORef text
					mapM_
						(\(ob, _) -> realizeTable text insetWnd ob inTableProc)
						(take (length (head ls) + sum (map ((+1) . length) (tail ls))) (drop n (toView textVal)))
				Delete n m -> mapM_ (\(el, _) -> maybe
					(return ())
					destroyWindow
					(window el)) (take (m - n) (drop n (toView textVal)))
				InTable n _ _ _ -> sizeTable (fst (toView textVal !! n))
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
		inTableProc col row = insetProc (\wnd -> do
				n <- getIndex wnd
				textVal <- readIORef text
				let Right (Left tbl) = obj (fst (toView textVal !! n))
				return $ snd $ snd (contents tbl !! col) !! row)
			(\wnd newText -> do
				n <- getIndex wnd
				modifyIORef text $ alter n (\(Right (Left tbl)) -> Right $ Left $ tbl { contents = changeAt col (second $ changeAt row $ second $ const newText) (contents tbl) })
				execOnChange)
			(\wnd cmd -> do
				n <- getIndex wnd
				performCommand (InTable n col row cmd))
	let tableCommand = do
		textVal <- readIORef text
		maybe
			(return ())
			(\caret -> do
				let ob = Object 0 Unselected (Right $ Left $ Table undefined [(200, [(undefined, initialParagraph)])]) (mousedown wnd) (mousemove wnd) (mouseup wnd)
				performCommand $ Insert (caret + 1) [[(ob, Inline)]])
			(findCaret textVal)
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
			writeIORef text $ renumber 0 $ fromView textVal $ map (first $ \x -> x { mousedown = mousedown wnd, mousemove = mousemove wnd, mouseup = mouseup wnd }) $ toView textVal
			insetWnd <- readIORef inset
			mapM_
				(\(ob, _) -> case obj ob of
					Right (Left tbl) -> realizeTable text insetWnd ob inTableProc
					_ -> return ())
				(toView textVal)
			writeIORef undo undoVal
			writeIORef changed False
			setWindowText wnd $ "Hoss - " ++ path
			execOnChange)
	let newFile wnd = promptForSave wnd $ do
		writeIORef text initialParagraph
		writeIORef changed False
		execOnChange
	frameWindow "Hoss" Nothing Nothing $ \dialogs wnd msg wParam lParam -> if msg == wM_CREATE then do
			hdl <- getModuleHandle Nothing
 			initControls wnd hdl fontRef sizeRef clrRef clrRef2 undoRef redoRef execOnChange mousedown mousemove mouseup undoCommand redoCommand doSave doOpen newFile tableCommand text undo
			let name = mkClassName "Frame"
			insetWnd <- createWindow name "" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) Nothing Nothing Nothing Nothing (Just wnd) Nothing hdl (insetProc (\_ -> readIORef text) (\_ x -> writeIORef text x >> execOnChange) (\_ -> performCommand) select)
			writeIORef inset insetWnd
			proc <- attachLayout text insetWnd
			writeIORef onChange proc
			newFile wnd
			modifyIORef dialogs (wnd:)
			sendMessage wnd wM_SIZE 0 0
			return 0
		else if msg == wM_COMMAND then do
			when (loWord wParam == iDOK) $ do
				textVal <- readIORef text
				fontCtrl <- readIORef fontRef
				sizeCtrl <- readIORef sizeRef
				clr <- readIORef clrRef
				fnt <- getWindowText fontCtrl
				sz <- getWindowText sizeCtrl
				catch
					(do
					n <- readIO sz
					writeIORef text $ fromView textVal $ map (\x -> if selection (fst x) /= Unselected then first (funOnWord (\y -> y { font = fnt, size = n, color = clr })) x else x) (toView textVal))
					(\(_ :: SomeException) -> return ())
				execOnChange
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

instance Eq Object where
	x == y = obj x == obj y

instance Show Object where
	show x = show (obj x)

compress x = map (second (map snd)) (contents x)

instance Eq Table where
	x == y = compress x == compress y

instance Show Table where
	show x = show (compress x)

makeWord s = Word "" 0 0 False False False s 

instance Arbitrary Word where
	arbitrary = MkGen $ \gen _ -> makeWord (show (fst (random gen) :: Int))
	shrink _ = []

instance Arbitrary Object where
	arbitrary = liftM (\x -> Object 0 Unselected (Left x) undefined undefined undefined) arbitrary

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
		x <- elements [0..5]
		case x of
			(0 :: Int) -> do
				y <- elements [0..5]
				z <- arbitrary
				return $ Insert y z
			1 -> do
				y <- elements [0..5]
				return $ InsertEnter y L
			2 -> do
				y <- elements [0..5]
				z <- elements [0..5]
				return $ Delete y (y + z)
			3 -> do
				y <- elements [0..5]
				return $ DeleteEnter y
			4 -> do
				y <- elements [0..5]
				z <- elements [0..1000]
				return $ Alter y (show z)
			5 -> do
				y <- elements [0..5]
				z <- elements [0..5]
				a <- elements [0..5]
				b <- arbitrary
				return $ InTable y z a b
	shrink _ = []

conformToInvariant textVal = renumber 0 $ map (\(just, ls) -> (just, (Object undefined Unselected (Left $ Word "" 0 0 False False False "") undefined undefined undefined, Inline) : map (first $ \(Object a b (Left wrd) _ _ _) -> Object a b (Left (wrd { string = ' ' : string wrd })) undefined undefined undefined) ls)) textVal

invariant ls = not (null ls) && all (\(_, ls) -> not (null ls) && (case obj (fst (head ls)) of
	Left wrd -> null (string wrd)
	Right _ -> False) && all (\(ob, _) -> case obj ob of
		Left wrd -> not (null (string wrd)) && head (string wrd) == ' '
		Right _ -> True) (tail ls)) ls

validCommand (Insert n ls) (textVal :: [Paragraph Object]) = n >= 1 && not (null ls) && n + length ls <= position (fst (last (toView textVal))) + 1
validCommand (InsertEnter n _) textVal = n >= 1 && n <= position (fst (last (toView textVal))) + 1
validCommand (Delete n m) textVal = n <= m && m <= position (fst (last (toView textVal))) + 1
validCommand (DeleteEnter n) textVal = n >= 1 && onBoundary n textVal
validCommand (Alter n s) textVal = n <= position (fst (last (toView textVal))) && not (null s) && head s == ' '
validCommand (InTable n col row cmd) textVal = n < position (fst (last (toView textVal))) && case obj (fst (toView textVal !! n)) of
	Left _ -> False
	Right (Left (Table _ contents)) -> length contents > col && length (snd (contents !! col)) > row && validCommand cmd (snd (snd (contents !! col) !! row))

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
