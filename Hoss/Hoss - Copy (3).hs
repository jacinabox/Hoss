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

import Graphics.Subclass

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
			let (_, ls2) = head xs in
				(just, init ls ++ first (\x -> x { selection = Caret }) (last ls) : tail ls2) : tail xs
		else if j == 0 then
			(just, ls) : xs
		else
			(just, take (j - 1) ls ++ first (\x -> x { selection = Caret }) (ls !! (j - 1)) : drop (j + 1) ls) : xs
	else
		(just, ls) : delete i xs

findCaret ((_, ls):xs) = maybe (findCaret xs) (position . fst) (find ((==Caret) . selection . fst) ls)
findCaret [] = -1

clearSelection view = map (first (\x -> x { selection = Unselected })) view

enterKey i ((just, x):xs) = if null xs || i <= position (fst (head (snd (head xs)))) then
		let j = i - position (fst (head x)) in
			(just, take j x) : (just, first (\x -> x { string = "" }) (head x) : drop j x) : xs
	else
		(just, x) : enterKey i xs

onBoundary 0 _ = True
onBoundary n ((_, ls):xs) = if n < length ls then
		False
	else
		onBoundary (n - length ls) xs

setCaret location ls = fromView ls (take location (clearSelection (toView ls)) ++ first (\x -> x { selection = Caret }) (toView ls !! location) : drop (location + 1) (clearSelection (toView ls)))

setSelection n m ls = fromView ls (take n (clearSelection (toView ls)) ++ map (first (\x -> x { selection = Selected })) (take (m - n) (drop n (toView ls))) ++ drop m (clearSelection (toView ls)))

convert shift vk = if inRange (65, 90) vk then
		Just $ chr (vk + if shift then 0 else 32)
	else if inRange (48, 57) vk then
		Just $ if shift then convertNum vk else chr vk
	else
		Nothing where
	convertNum 48 = ')'
	convertNum 49 = '!'
	convertNum 50 = '@'
	convertNum 51 = '#'
	convertNum 52 = '$'
	convertNum 53 = '%'
	convertNum 54 = '^'
	convertNum 55 = '&'
	convertNum 56 = '*'
	convertNum 57 = '('

toolbarHeight = 40

initControls wnd hdl name = do
	dialogCtrl <- createWindow name "" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) Nothing Nothing Nothing Nothing (Just wnd) Nothing hdl $ \wnd msg wParam lParam -> if msg == wM_ERASEBKGND then do
			brush <- getSysColorBrush cOLOR_3DFACE
			fillRect (unsafeCoerce wParam) (0, 0, 32767, 32767) brush
			return 1
		else
			defWindowProc (Just wnd) msg wParam lParam
	createEditWindow "Times New Roman" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) 0 (Just 10) (Just 10) (Just 200) (Just 20) wnd Nothing dialogCtrl
	createEditWindow "12" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) 0 (Just 220) (Just 10) (Just 20) (Just 20) dialogCtrl Nothing hdl
	return dialogCtrl


main = do
	text <- newIORef []
	select <- newIORef Nothing
	inset <- newIORef undefined
	onChange <- newIORef undefined
	let execOnChange = readIORef onChange >>= id
	let mousemove wnd n = readIORef select >>= maybe
		(return ())
		(\m -> do
			modifyIORef text (if n == m then
					setCaret ((n - 1) `max` 0)
				else if n < m then
					setSelection n m
				else
					setSelection m n)
			execOnChange)
	let mousedown wnd n = do
		writeIORef select (Just n)
		mousemove wnd n
	let mouseup wnd = writeIORef select Nothing
	frameWindow "Hoss" Nothing Nothing $ \dialogs wnd msg wParam lParam -> if msg == wM_CREATE then do
			hdl <- getModuleHandle Nothing
			let name = mkClassName "Frame"
			dialogCtrl <- initControls wnd hdl name
			modifyIORef dialogs (dialogCtrl:)
			insetCtrl <- createWindow name "" (wS_VISIBLE .|. wS_CHILD .|. wS_TABSTOP) Nothing Nothing Nothing Nothing (Just wnd) Nothing hdl $ \wnd msg wParam lParam -> if msg == wM_KEYDOWN then do
					textVal <- readIORef text
					let caret = findCaret textVal
					writeIORef text $ renumber 0 $ if caret == -1 then
						if wParam == vK_BACK || wParam == vK_DELETE then
							map (\(just, ls) -> (just, head ls : filter ((/=Selected) . selection . fst) (tail ls))) textVal
						else
							textVal
					else
						if wParam == vK_LEFT then
							setCaret ((caret - 1) `max` 0) textVal
						else if wParam == vK_RIGHT then
							setCaret ((caret + 1) `min` (length (toView textVal) - 1)) textVal
						else if wParam == vK_SPACE then
							doInsert caret textVal
						else if wParam == vK_BACK then
							delete caret textVal
						else if wParam == vK_RETURN then
							setCaret (caret + 1) $ enterKey (caret + 1) textVal
						else
							textVal
					execOnChange
					return 0
				else if msg == wM_CHAR && wParam /= 8 then do
					textVal <- readIORef text
					let caret = findCaret textVal
					let (caret', ls) = if onBoundary caret textVal then
							(caret + 1, doInsert caret textVal)
						else
							(caret, textVal) 
					writeIORef text $ renumber 0 $ fromView ls (take caret' (toView ls) ++ first (\x -> x { string = string x ++ [chr (fromIntegral wParam)] }) (toView ls !! caret') : drop (caret' + 1) (toView ls))
					execOnChange
					return 0
				else
					defWindowProc (Just wnd) msg wParam lParam
			writeIORef inset insetCtrl
			proc <- attachLayout text insetCtrl
			writeIORef onChange proc
			writeIORef text [(L, [(Word 0 Caret "Times New Roman" 12 0 False False False "" (mousedown wnd) (mousemove wnd) (mouseup wnd), Inline)])]
			sendMessage wnd wM_SIZE 0 0
			return 0
		else if msg == wM_SIZE then do
			insetCtrl <- readIORef inset
			(_, _, wd, ht) <- getClientRect wnd
			moveWindow insetCtrl 0 toolbarHeight (fromIntegral wd) (fromIntegral ht - toolbarHeight) True
			[dialogCtrl] <- readIORef dialogs
			moveWindow dialogCtrl 0 0 (fromIntegral wd) toolbarHeight True
			return 0
		else if msg == wM_CLOSE || msg == wM_ENDSESSION then
			exitSuccess
		else
			defWindowProc (Just wnd) msg wParam lParam
