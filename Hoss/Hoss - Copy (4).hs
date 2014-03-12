{-# LANGUAGE ScopedTypeVariables #-}

module Graphics.Hoss where

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
import Control.Monad
import Graphics.Layout
import Graphics.Displayable hiding (Selection, selection)
import Graphics.FrameWindow
import Graphics.Win32Extras
import Unsafe.Coerce
import Control.Exception

data Selection = Unselected | Selected | Caret deriving Eq

data Word = Word {
	position :: Int,
	selection :: Selection,
	font :: String,
	size :: Int32,
	color :: COLORREF,
	bold :: Bool,
	italic :: Bool,
	underline :: Bool,
	string :: String,
	mousedown :: Int -> IO (),
	mousemove :: Int -> IO (),
	mouseup :: IO () }

data Command = Insert Int [Paragraph Word] | InsertEnter Int | Delete Int Int | DeleteEnter Int

invertDelete n m ((just, ls):xs) = if null (dropWhile ((<n) . position . fst) ls) then
		invertDelete n m xs
	else
		Insert n $ (just, dropWhile ((<n) . position . fst) ls) : inv m xs where
	inv ((just, ls):xs) = if null (takeWhile ((<m) . position . fst) ls) then
			[]
		else
			(just, takeWhile ((<m) . position . fst) ls) : inv xs

getJustification n ((just, ls):xs) = if null xs || n <= position (fst (head (snd xs))) then
		just
	else
		getJustification n xs

invert (Insert n ls) _ = Delete n (length (concat ls))
invert (InsertEnter n _) = DeleteEnter n
invert (Delete n m) textVal = invertDelete n m textVal
invert (DeleteEnter n) textVal = InsertEnter n (getJustification n textVal)

perform (Insert n ls) = setCaret (n + 1) . insert (caret + 1) ls
perform (InsertEnter n just) = setCaret (n + 1) . enterKey just (n + 1)
perform (Delete n m) = setCaret n . deleteMany . setSelection n m
perform (DeleteEnter n) = deleteEnter n

createAFont dc font size bold italic underline = do
	logy <- getDeviceCaps dc lOGPIXELSY
	createFont (size * logy `div` 72) 0 0 0 (if bold then fW_BOLD else fW_NORMAL) italic underline False dEFAULT_CHARSET oUT_DEFAULT_PRECIS cLIP_DEFAULT_PRECIS dEFAULT_QUALITY fF_DONTCARE font

instance Displayable Word where
	measure _ = (0, 0)
	flowMeasure (Word _ _ font size _ bold italic underline s _ _ _) = unsafePerformIO $ do
		dc <- getDC Nothing
		font <- createAFont dc font size bold italic underline
		oldFont <- selectFont dc font
		(x, y) <- getTextExtentPoint32 dc $ if null s then " " else s
		selectFont dc oldFont
		deleteFont font
		releaseDC Nothing dc
		return (x + 3, y)
	draw dc (x, y) wrd@(Word n selected font size clr bold italic underline s _ _ _) = do
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
		when (selected == Caret) $ do
			let (wd, ht) = flowMeasure wrd
			moveToEx dc (x + wd - 2) y
			lineTo dc (x + wd - 2) (y + ht)
		return ()
	mouse MouseDown _ _ _ _ wrd = mousedown wrd (position wrd)
	mouse MouseMove _ _ (x, y) (xPos, yPos) wrd = mousemove wrd (position wrd + if x < xPos + width wrd && y < yPos + height wrd then 0 else 1)
	mouse MouseUp _ _ _ _ wrd = mouseup wrd

toView ls = concatMap snd ls

fromView ((just, ls):xs) view = (just, take (length ls) view) : fromView xs (drop (length ls) view)
fromView [] _ = []

renumber n ((just, ls):xs) = (just, zipWith (\(x, f) i -> (x { position = i }, f)) ls [n..]) : renumber (n + length ls) xs
renumber _ [] = []

insert i ins ((just, ls):xs) = if null xs || i <= position (fst (head (snd (head xs)))) then
		(just, let j = i - position (fst (head ls)) in
			take j ls ++ ins ++ drop j ls) : xs
	else
		(just, ls) : insert i ins xs

doInsert caret textVal = setCaret (caret + 1) $ insert (caret + 1) [first (\x -> x { string = " " }) (toView textVal !! caret)] textVal

delete i ((just, ls):xs) = if null xs || i <= position (fst (head (snd (head xs)))) then
	let j = i - position (fst (head ls)) in
		if j == length ls then
			Just (DeleteEnter i)
		else if j == 0 then
			Nothing
		else
			Just (Delete j (j + 1))
	else
		delete i xs

deleteMany textVal = map (\(just, ls) -> (just, head ls : filter ((/=Selected) . selection . fst) (tail ls))) textVal

deleteEnter i ((_, ls):xs) = if null xs || i <= position (fst (head (snd (head xs)))) then
		let (_, ls2) = head xs in
			(just, init ls ++ first (\x -> x { selection = Caret }) (last ls) : tail ls2) : tail xs
	else
		(just, ls) : deleteEnter i xs

findCaret ls = fmap (position . fst) $ find ((==Caret) . selection . fst) (toView ls)

clearSelection view = map (first (\x -> x { selection = Unselected })) view

enterKey just' i ((just, x):xs) = if null xs || i <= position (fst (head (snd (head xs)))) then
		let j = i - position (fst (head x)) in
			(just, take j x) : (just', first (\x -> x { string = "" }) (last x) : drop j x) : xs
	else
		(just, x) : enterKey i xs

onBoundary 0 _ = True
onBoundary n ((_, ls):xs) = if n < length ls then
		False
	else
		onBoundary (n - length ls) xs

setCaret location ls = fromView ls (take location (clearSelection (toView ls)) ++ first (\x -> x { selection = Caret }) (toView ls !! location) : drop (location + 1) (clearSelection (toView ls)))

setSelection n m ls = fromView ls (take n (clearSelection (toView ls)) ++ map (first (\x -> x { selection = Selected })) (take (m - n) (drop n (toView ls))) ++ drop m (clearSelection (toView ls)))

toolbarHeight = 40

initControls wnd hdl fontRef sizeRef clrRef clrRef2 = do
	font <- createEditWindow "Times New Roman" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) 0 (Just 10) (Just 10) (Just 200) (Just 20) wnd Nothing hdl
	writeIORef fontRef font
	size <- createEditWindow "12" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) 0 (Just 220) (Just 10) (Just 20) (Just 20) wnd Nothing hdl
	writeIORef sizeRef size
	let name = mkClassName "Frame"
	clr <- createWindow name "" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) (Just 250) (Just 10) (Just 20) (Just 20) (Just wnd) Nothing hdl $ \wnd2 msg wParam lParam ->
		if msg == wM_LBUTTONUP then do
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

insetProc execOnChange performCommand wnd msg wParam lParam = if msg == wM_GETDLGCODE then
		return (dLGC_WANTCHARS .|. dLGC_WANTARROWS)
	else if msg == wM_KEYDOWN then do
		maybe
			(if wParam == vK_BACK || wParam == vK_DELETE then
					performCommand
				else
					textVal)
			(\caret -> if wParam == vK_LEFT then
					setCaret ((caret - 1) `max` 0) textVal
				else if wParam == vK_RIGHT then
					setCaret ((caret + 1) `min` (length (toView textVal) - 1)) textVal
				else if wParam == vK_SPACE then
					doInsert caret textVal
				else if wParam == vK_BACK then
					delete caret textVal
				else
					textVal)
				(findCaret textVal)
		execOnChange
		return 0
	else if msg == wM_CHAR && wParam /= 8 && wParam /= 32 then do
		textVal <- readIORef text
		maybe
			(return ())
			(\caret -> let (caret', ls) = if onBoundary caret textVal then
						(caret + 1, doInsert caret textVal)
					else
						(caret, textVal) in
				writeIORef text $ renumber 0 $ fromView ls (take caret' (toView ls) ++ first (\x -> x { string = string x ++ [chr (fromIntegral wParam)] }) (toView ls !! caret') : drop (caret' + 1) (toView ls)))
			(findCaret textVal)
		execOnChange
		return 0
	else
		defWindowProc (Just wnd) msg wParam lParam

main = do
	text <- newIORef []
	undo <- newIORef ([], [])
	select <- newIORef Nothing
	onChange <- newIORef undefined
	inset <- newIORef undefined
	fontRef <- newIORef undefined
	sizeRef <- newIORef undefined
	clrRef <- newIORef (rgb 0 0 0)
	clrRef2 <- newIORef undefined
	let execOnChange = do
		readIORef onChange >>= id
		textVal <- readIORef text
		let caret = findCaret textVal
		maybe
			(return ())
			(\n -> let (x, _) = toView textVal !! n in
				do
				fontCtrl <- readIORef fontRef
				sizeCtrl <- readIORef sizeRef
				setWindowText fontCtrl (font x)
				setWindowText sizeCtrl (show (size x))
				writeIORef clrRef (color x)
				clrCtrl <- readIORef clrRef2
				invalidateRect (Just clrCtrl) Nothing True)
			caret
	let mousemove wnd n = readIORef select >>= maybe
		(return ())
		(\(m, _) -> do
			modifyIORef text (if n == m then
					setCaret ((n - 1) `max` 0)
				else if n < m then do
					setSelection n m
				else do
					setSelection m n
			writeIORef select (Just (m, n))
			execOnChange)
	let mousedown wnd n = do
		writeIORef select (Just n)
		mousemove wnd n
	let mouseup wnd = writeIORef select Nothing
	let undoCommand = do
		(x:bef, aft) <- readIORef undo
		modifyIORef text (renumber 0 . perform x)
		writeIORef undo (bef, invert x : aft)
	let redoCommand = do
		(bef, x:aft) <- readIORef undo
		modifyIORef (renumber 0 . perform x)
		writeIORef undo (invert x : bef, aft)
	let performCommand x = do
		modifyIORef undo (second (x:))
		redoCommand
	frameWindow "Hoss" Nothing Nothing $ \dialogs wnd msg wParam lParam -> if msg == wM_CREATE then do
			hdl <- getModuleHandle Nothing
 			initControls wnd hdl fontRef sizeRef clrRef clrRef2
			let name = mkClassName "Frame"
			insetCtrl <- createWindow name "" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) Nothing Nothing Nothing Nothing (Just wnd) Nothing hdl (insetProc execOnChange performCommand)
			writeIORef inset insetCtrl
			proc <- attachLayout text insetCtrl
			writeIORef onChange proc
			writeIORef text [(L, [(Word 0 Caret "Times New Roman" 12 0 False False False "" (mousedown wnd) (mousemove wnd) (mouseup wnd), Inline)])]
			modifyIORef dialogs (wnd:)
			sendMessage wnd wM_SIZE 0 0
			return 0
		else if msg == wM_COMMAND then do
			when (loWord wParam == iDOK) $ do
				focus <- getFocus
				insetCtrl <- readIORef inset
				textVal <- readIORef text
				if focus == Just insetCtrl then
					maybe
						(return ())
						(\caret -> writeIORef text $ renumber 0 $ setCaret (caret + 1) $ enterKey (caret + 1) textVal)
						(findCaret textVal)
					else do
						fontCtrl <- readIORef fontRef
						sizeCtrl <- readIORef sizeRef
						clr <- readIORef clrRef
						fnt <- getWindowText fontCtrl
						sz <- getWindowText sizeCtrl
						catch
							(do
							n <- readIO sz
							writeIORef text $ fromView textVal $ map (\(x, f) -> (if selection x /= Unselected then x { font = fnt, size = n, color = clr } else x, f)) (toView textVal))
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
		else if msg == wM_CLOSE || msg == wM_ENDSESSION then
			exitSuccess
		else
			defWindowProc (Just wnd) msg wParam lParam
