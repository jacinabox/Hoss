{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, ExistentialQuantification #-}

module Graphics.Displayable (MouseEvent(..), Displayable(..), Str(Str), Legend(Legend), Bars(..), Plot(Plot), Selection(..), Clear(Clear), Disp(Disp), HorizontalList(HorizontalList), attachDisplay, onChange, createNiceFont) where

import Graphics.Win32
import Data.IORef
import Control.Monad
import System.Win32.DLL
import System.IO.Unsafe
import Unsafe.Coerce
import Graphics.Win32Extras
import Graphics.Subclass
import Graphics.Scroll
import Data.Int
import Data.Bits
import Data.Fixed
import Codec.BMP
import Data.ByteString.Unsafe

data MouseEvent = MouseDown | MouseUp | MouseMove deriving Eq

-- | The type class of things that can be displayed.
--
-- For the click function, the first point is the location of the click,
-- and the second point is the upper-left corner of the thing being clicked.
--
-- The measure function gives a fixed dimension for all values of a type,
-- appropriate for table formatting. The flowMeasure function gives a
-- specific measurement for each value, appropriate for a flow layout.
class Displayable t where
	measure :: t -> (Int32, Int32)
	flowMeasure :: t -> (Int32, Int32)
	draw :: HDC -> (Int32, Int32) -> t -> IO ()
	mouse :: MouseEvent -> HWND -> IORef [HWND] -> (Int32, Int32) -> (Int32, Int32) -> t -> IO ()
	flowMeasure = measure
	mouse _ _ _ _ _ _ = return ()

newtype Str = Str String deriving (Eq, Ord, Read, Show)

instance Displayable Str where
	measure _ = (200, 20)
	flowMeasure (Str s) = unsafePerformIO $ do
		dc <- getDC Nothing
		font <- createNiceFont
		oldFont <- selectFont dc font
		(x, y) <- getTextExtentPoint32 dc s
		selectFont dc oldFont
		deleteFont font
		releaseDC Nothing dc
		return (x + 3, y)
	draw dc (x, y) (Str s) = do
		drawText dc s (x + 4, y, x + xExt, y + yExt) dT_WORD_ELLIPSIS
		return () where
		(xExt, yExt) = measure (Str s)

instance Displayable Int where
	measure _ = (90, 20)
	draw dc (x, y) n = textOut dc (x + 4) y (show n)

instance Displayable Double where
	measure _ = (200, 20)
	draw dc (x, y) n = textOut dc (x + 4) y (show n)

withPen dc pen m = do
	oldPen <- selectPen dc pen
	m
	selectPen dc oldPen
	deletePen pen

-- | A legend for a graph.
newtype Legend = Legend [String] deriving (Eq, Read, Show)

colours = [rgb 0 0 192, rgb 0 192 0, rgb 192 0 192, rgb 0 192 192, rgb 192 0 0, rgb 0 92 192, rgb 0 192 92, rgb 92 192 0, rgb 192 0 92, rgb 92 0 192, rgb 192 92 0, rgb 192 192 0, rgb 0 0 0]

instance Displayable Legend where
	measure (Legend ls) = (200, 2 + 18 * fromIntegral (length ls))
	draw dc (x, y) (Legend ls) = mapM_ (\(el, y, clr) -> do
			brush <- createSolidBrush clr
			fillRect dc (x, y, x + 18, y + 18) brush
			deleteBrush brush
			textOut dc (x + 20) y el)
		(zip3 ls [y,y+18..] (cycle colours))

-- | A set of bars that compare related data points side by side. A list of these is a bar chart.
data Bars = Bars { values :: ![Double], maxValue :: !Double } deriving (Eq, Read, Show)

instance Displayable Bars where
	measure (Bars ls _) = (200, 2 + 18 * fromIntegral (length ls))
	draw dc (x, y) (Bars ls mx) = do
		bkclr <- getBkColor dc
		setTextColor dc (rgb 255 255 255)
		mapM_ (\(el, y, clr) -> do
			brush <- createSolidBrush clr
			setBkColor dc clr
			textOut dc x y (show el)
			(x2, _) <- getTextExtentPoint32 dc (show el)
			let xRight = round $ 200 * el / mx
			when (x2 < xRight) (fillRect dc (x + x2, y, x + xRight, y + 18) brush)
			deleteBrush brush)
			(zip3 ls [y,y+18..] (cycle colours))
		setTextColor dc (rgb 0 0 0)
		setBkColor dc bkclr
		return ()

-- | A scatter plot. The outer list elements are for different datasets that are drawn with different colours.
newtype Plot = Plot [[(Double, Double)]] deriving (Eq, Read, Show)

maxOfRange :: [Double] -> (Int32, Fixed E6)
maxOfRange ls = (ceiling (maximum ls / 10 ^^ n), 10 ^^ n)
	where n = floor (log (maximum ls) / log 10)

instance Displayable Plot where
	measure _ = (360, 225)
	draw dc (x, y) (Plot ls) = do
		mapM_ (\n -> do
			let x2 = x + 60 + 300 * n `div` (mxX + 1)
			textOut dc (x2 - 5) (y + 205) $ showFixed True $ fromIntegral n * incrementX
			moveToEx dc x2 (y + 200)
			lineTo dc x2 (y + 205)) [0..mxX]
		mapM_ (\n -> do
			let y2 = y + 200 * (mxY + 1 - n) `div` (mxY + 1)
			drawText dc (showFixed True $ fromIntegral n * incrementY) (x, y2 - 9, x + 54, y2 + 11) dT_RIGHT
			moveToEx dc (x + 55) y2
			lineTo dc (x + 60) y2) [0..mxY]
		moveToEx dc (x + 60) y
		lineTo dc (x + 60) (y + 200)
		lineTo dc (x + 360) (y + 200)
		pen <- getStockPen nULL_PEN
		oldPen <- selectPen dc pen
		mapM_ (\(ls, clr) -> do
			brush <- createSolidBrush clr
			oldBrush <- selectBrush dc brush
			mapM_ (\(x2, y2) -> let
					x3 = x + 60 + round (x2 * 300 / fromIntegral (mxX + 1) / fromRational (toRational incrementX))
					y3 = y + 200 - round (y2 * 200 / fromIntegral (mxY + 1) / fromRational (toRational incrementY)) in
				ellipse dc (x3 - 5) (y3 - 5) (x3 + 6) (y3 + 6))
				ls
			selectBrush dc oldBrush
			deleteBrush brush)
			(zip ls (cycle colours))
		selectPen dc oldPen
		return ()
		where
		(mxX, incrementX) = maxOfRange (map fst (concat ls))
		(mxY, incrementY) = maxOfRange (map snd (concat ls))

-- Displays a check box the user can use to switch the value of 
-- the boolean reference.
instance Displayable (IORef Bool) where
	measure _ = (15, 19)
	draw dc (x, y) ref = do
		rectangle dc x (y + 2) (x + 15) (y + 17)
		b <- readIORef ref
		when b $ do
			-- Displays a check mark
			moveToEx dc (x + 2) (y + 8)
			lineTo dc (x + 6) (y + 12)
			lineTo dc (x + 14) (y + 4)
			moveToEx dc (x + 2) (y + 9)
			lineTo dc (x + 6) (y + 13)
			lineTo dc (x + 14) (y + 5)
	mouse ev wnd _ _ (xPos, yPos) ref = when (ev == MouseUp) $ do
		modifyIORef ref not
		let (xExt, yExt) = measure ref
		withRECT (xPos, yPos, xPos + xExt, yPos + yExt) $ \p -> invalidateRect (Just wnd) (Just p) True

-- This instance uses a string reference and creates a string the user
-- can click on to pop up an edit control. The edit control writes its value
-- back to the corresponding reference when it loses focus. So be sure to
-- remove the focus from the edit control before saving user data.
instance Displayable (IORef String) where
	measure _ = (200, 20)
	draw dc pt ref = do
		s <- readIORef ref
		draw dc pt (Str s)
	mouse ev wnd wnds (x, y) (xPos, yPos) ref = when (ev == MouseUp && x < xPos + wd && y < yPos + ht) $ do
		inst <- getModuleHandle Nothing
		edit <- createEditWindow "" (wS_CHILD .|. wS_VISIBLE) eS_AUTOHSCROLL (Just (fromIntegral xPos)) (Just (fromIntegral yPos)) (Just (fromIntegral wd)) (Just (fromIntegral ht)) wnd Nothing inst
		modifyIORef wnds (edit:)
		font <- createNiceFont
		sendMessage edit wM_SETFONT (unsafeCoerce font) 0
		s <- readIORef ref
		setWindowText edit s
		setFocus edit
		subclassProc edit $ \proc wnd msg wParam lParam -> do
			if msg == wM_KILLFOCUS then do
					destroyWindow wnd
				else if msg == wM_DESTROY then do
					s <- getWindowText wnd
					writeIORef ref s
					deleteFont font
					modifyIORef wnds (filter (/= wnd))
				else
					return ()
			proc wnd msg wParam lParam where
		(wd, ht) = measure ref

instance Displayable BMP where
	measure _ = (400, 300)
	flowMeasure bmp = (fromIntegral wd, fromIntegral ht) where
		(wd, ht) = bmpDimensions bmp
	draw dc (x, y) bmp = unsafeUseAsCString (bmpRawImageData bmp) $ \pBits ->
			withBITMAP (bmpBitmapInfo bmp) $ \pBmp -> do
				dc' <- createCompatibleDC (Just dc)
				bmp <- createCompatibleBitmap dc (fromIntegral wd) (fromIntegral ht)
				oldBmp <- selectBitmap dc' bmp
				setDIBitsToDevice dc' 0 0 (fromIntegral wd) (fromIntegral ht) 0 0 0 (fromIntegral ht) pBits pBmp dIB_RGB_COLORS
				bitBlt dc x y (fromIntegral wd) (fromIntegral ht) dc' 0 0 sRCCOPY
				selectBitmap dc' oldBmp
				deleteBitmap bmp
				deleteDC dc' where
		(wd, ht) = bmpDimensions bmp

-- | A fixed list of values the user can select from with a popup menu.
data Selection = Selection { selection :: !(IORef Int32), choices :: ![String] }

instance Displayable Selection where
	measure _ = (200, 20)
	draw dc pt (Selection ref choices) = do
		i <- readIORef ref
		draw dc pt (Str (choices !! fromIntegral i))
	mouse ev wnd wnds _ (xPos, yPos) sel@(Selection ref choices) = when (ev == MouseUp) $ do
		menu <- createPopupMenu
		i <- readIORef ref
		mapM_
			(\(j, s) -> insertMenuItem' menu (fromIntegral j) True (MenuItemInfo mFT_STRING 0 (fromIntegral (j + 1)) nullPtr nullPtr nullPtr 0 s))
			(zip [0..] choices)
		(x, y) <- clientToScreen wnd (xPos, yPos)
		choice <- trackPopupMenu' menu tPM_RETURNCMD (fromIntegral x) (fromIntegral y) 0 wnd nullPtr
		when (choice /= 0) $ writeIORef ref (choice - 1)
		let (wd, ht) = measure sel
		withRECT (xPos, yPos, xPos + wd, yPos + ht) $ \p -> invalidateRect (Just wnd) (Just p) True
		destroyMenu menu

-- | When used in a flow layout, moves subsequent text below all floated elements.
data Clear = Clear

instance Displayable Clear where
	measure _ = (32767, 0)
	draw _ _ _ = return ()

-- | A type box that forgets everything about a value except the fact
--   that it is displayable.
data Disp = forall t. (Displayable t) => Disp t

instance Displayable Disp where
	measure (Disp x) = measure x
	flowMeasure (Disp x) = flowMeasure x
	draw dc pt (Disp x) = draw dc pt x
	mouse ev wnd wnds pt pt2 (Disp x) = mouse ev wnd wnds pt pt2 x

instance (Displayable t) => Displayable [t] where
	measure ls = (maximum (map fst ms), sum (map snd ms) + 3)
		where ms = map measure ls
	draw dc (x, y) (z:zs) = do
		draw dc (x, y) z
		let (_, y2) = measure z
		draw dc (x, y + y2) zs
	draw dc (x, y) [] = do
		pen <- createPen pS_SOLID 0 (rgb 180 180 180)
		withPen dc pen $ do
			moveToEx dc (x + 1) (y + 1)
			lineTo dc (x + 100) (y + 1)
	mouse ev wnd wnds (x, y) (xPos, yPos) (z:zs) = let (_, y2) = measure z in
		if y < yPos + y2 then
			mouse ev wnd wnds (x, y) (xPos, yPos) z
		else
			mouse ev wnd wnds (x, y) (xPos, yPos + y2) zs
	mouse _ _ _ _ _ [] = return ()

instance (Displayable t, Displayable u) => Displayable (t, u) where
	measure (a, b) = (x1 + x2 + 3, y1 `max` y2) where
		(x1, y1) = measure a
		(x2, y2) = measure b
	draw dc (x, y) (a, b) = do
		let y2 = snd (measure a) `max` snd (measure b)
		draw dc (x, y) a
		let (x2, _) = measure a
		pen <- createPen pS_SOLID 0 (rgb 180 180 180)
		withPen dc pen $ do
			moveToEx dc (x + x2 + 1) (y + 1)
			lineTo dc (x + x2 + 1) (y + y2 - 1)
		draw dc (x + x2 + 3, y) b
	mouse ev wnd wnds (x, y) (xPos, yPos) (a, b) = let (x2, _) = measure a in
		if x < xPos + x2 then
			mouse ev wnd wnds (x, y) (xPos, yPos) a
		else
			mouse ev wnd wnds (x, y) (xPos + x2 + 3, yPos) b

instance Displayable () where
	measure _ = (0, 0)
	draw _ _ _ = return ()

instance (Displayable t, Displayable u, Displayable v) => Displayable (t, u, v) where
	measure (a, b, c) = measure (a, (b, c))
	draw dc pt (a, b, c) = draw dc pt (a, (b, c))
	mouse ev wnd wnds pt pt2 (a, b, c) = mouse ev wnd wnds pt pt2 (a, (b, c))

instance (Displayable t, Displayable u, Displayable v, Displayable w) => Displayable (t, u, v, w) where
	measure (a, b, c, d) = measure (a, (b, c, d))
	draw dc pt (a, b, c, d) = draw dc pt (a, (b, c, d))
	mouse ev wnd wnds pt pt2 (a, b, c, d) = mouse ev wnd wnds pt pt2 (a, (b, c, d))

instance (Displayable t, Displayable u, Displayable v, Displayable w, Displayable x) => Displayable (t, u, v, w, x) where
	measure (a, b, c, d, e) = measure (a, (b, c, d, e))
	draw dc pt (a, b, c, d, e) = draw dc pt (a, (b, c, d, e))
	mouse ev wnd wnds pt pt2 (a, b, c, d, e) = mouse ev wnd wnds pt pt2 (a, (b, c, d, e))

instance (Displayable t, Displayable u, Displayable v, Displayable w, Displayable x, Displayable y) => Displayable (t, u, v, w, x, y) where
	measure (a, b, c, d, e, f) = measure (a, (b, c, d, e, f))
	draw dc pt (a, b, c, d, e, f) = draw dc pt (a, (b, c, d, e, f))
	mouse ev wnd wnds pt pt2 (a, b, c, d, e, f) = mouse ev wnd wnds pt pt2 (a, (b, c, d, e, f))

instance (Displayable t, Displayable u, Displayable v, Displayable w, Displayable x, Displayable y, Displayable z) => Displayable (t, u, v, w, x, y, z) where
	measure (a, b, c, d, e, f, g) = measure (a, (b, c, d, e, f, g))
	draw dc pt (a, b, c, d, e, f, g) = draw dc pt (a, (b, c, d, e, f, g))
	mouse ev wnd wnds pt pt2 (a, b, c, d, e, f, g) = mouse ev wnd wnds pt pt2 (a, (b, c, d, e, f, g))

-- | A list that displays horizontally instead of vertically.
newtype HorizontalList t = HorizontalList [t] deriving (Eq, Ord, Read, Show)

instance (Displayable t) => Displayable (HorizontalList t) where
	measure (HorizontalList (x:xs)) = measure (x, HorizontalList xs)
	measure (HorizontalList []) = (0, 0)
	draw dc pt (HorizontalList (x:xs)) = draw dc pt (x, HorizontalList xs)
	draw _ _ (HorizontalList []) = return ()
	mouse ev wnd wnds pt pt2 (HorizontalList (x:xs)) = mouse ev wnd wnds pt pt2 (x, HorizontalList xs)
	mouse ev _ _ _ _ (HorizontalList []) = return ()

instance (Displayable t, Displayable u) => Displayable (Either t u) where
	measure _ = (max x1 x2, max y1 y2) where
		(x1, y1) = measure (undefined :: t)
		(x2, y2) = measure (undefined :: u)
	flowMeasure = either flowMeasure flowMeasure
	draw dc pt = either (draw dc pt) (draw dc pt)
	mouse ev wnd wnds pt pt2 = either (mouse ev wnd wnds pt pt2) (mouse ev wnd wnds pt pt2)

createNiceFont = createFont 18 0 0 0 fW_NORMAL False False False dEFAULT_CHARSET oUT_DEFAULT_PRECIS cLIP_DEFAULT_PRECIS dEFAULT_QUALITY fF_DONTCARE "Tahoma"

-- | Subclasses the window in order to display the value in the reference.
attachDisplay ref wnd = do
	wnds <- newIORef []
	subclassProc wnd $ \proc wnd msg wParam lParam -> do
		if msg == wM_PAINT then
				allocaPAINTSTRUCT $ \ps -> do
					dc <- beginPaint wnd ps
					val <- readIORef ref
					font <- createNiceFont
					oldFont <- selectFont dc font
					pos <- liftM nPos (getScrollInfo wnd sB_VERT)
					draw dc (0, -pos) val
					selectFont dc oldFont
					deleteFont font
					endPaint wnd ps
			else if msg == wM_LBUTTONUP || msg == wM_LBUTTONDOWN || msg == wM_MOUSEMOVE then do
				val <- readIORef ref
				pos <- liftM nPos (getScrollInfo wnd sB_VERT)
				mouse (if msg == wM_LBUTTONUP then MouseUp else
					if msg == wM_LBUTTONDOWN then MouseDown else
					MouseMove) wnd wnds (loWord lParam, hiWord lParam) (0, -pos) val
			else if msg == wM_VSCROLL then do
				wndList <- readIORef wnds
				mapM_ destroyWindow wndList
				sendMessage wnd wM_PAINT 0 0
				return ()
			else
				return ()
		vScroll wnd msg wParam lParam
		proc wnd msg wParam lParam
	onChange ref wnd

-- | Call this when the reference changes.
onChange ref wnd = do
	val <- readIORef ref
	si <- getScrollInfo wnd sB_VERT
	setScrollInfo wnd sB_VERT (si { nMax = snd (measure val) })
	invalidateRect (Just wnd) Nothing True

