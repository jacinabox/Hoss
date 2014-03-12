module Graphics.Layout (Just(..), Floated(..), Paragraph, Zipper, width, height, layout, eraseTuples, hitTest, attachLayout) where

import Graphics.Displayable
import Graphics.Scroll
import Graphics.Subclass
import Graphics.Buffered
import Graphics.Win32Extras
import Graphics.Win32
import Data.Int
import Data.List.Extras.Argmax
import Data.IORef
import Control.Monad
import Unsafe.Coerce

data Just = L | Center | R | Justified deriving (Eq, Show)

data Floated = Inline | FloatLeft | FloatRight deriving (Eq, Show)

type Paragraph t = (Just, [(t, Floated)])

type Zipper t = (Int, [Paragraph t], Just, [(t, Floated)], [(t, Floated)], [Paragraph t])

data Pending = None | Sizing | Update deriving Eq

width x = fst (flowMeasure x)

height x = snd (flowMeasure x)

lineWidth st@(lft, rgt, x) ((z, float):zs) wdt n = case float of
	Inline -> if x + width z <= rgt then
			lineWidth (lft, rgt, x + width z) zs (wdt + width z) (n + 1)
		else
			(wdt, n)
	_ -> lineWidth (lft, rgt, x) zs wdt n
lineWidth _ [] wdt n = (wdt, n)

layoutLine (wdt, n) just (lft, rgt, y) = doLayout (lft, rgt, case just of
		Center -> lft + (rgt - lft - wdt) `div` 2
		R -> rgt - wdt
		_ -> lft, 0) where
	doLayout (lft, rgt, x, err) ((z, float):zs) = case float of
		Inline -> if x + width z > rgt then 
				[]
			else let err' = err + (rgt - lft - wdt) `mod` (n - 1) in
				(x, y, (z, Inline)) : doLayout (lft, rgt, case just of
					-- It uses error terms to distribute the space evenly between justified elements.
					Justified -> if n <= 1 then x + width z else x + (rgt - lft - wdt) `div` (n - 1) + (if err' > n - 1 then 1 else 0) + width z
					_ -> x + width z, if err' > n - 1 then err' - (n - 1) else err') zs
		-- Can't compute position of floated elements here. It is done in layoutFloated*.
		_ -> (0, 0, (z, float)) : doLayout (lft, rgt, x, err) zs
	doLayout _ [] = []

layoutFloatedLeft (flt, fltY) ((_, _, (x, float)):xs) acc = layoutFloatedLeft (max flt (width x), fltY + height x) xs ((0, fltY, (x, float)):acc)
layoutFloatedLeft pr [] acc = (pr, acc)

-- The if test is to ensure that left- and right-floated elements don't overlap.
layoutFloatedRight wdt (lft, lftY) (rgt, rgtY) ((_, _, (x, float)):xs) acc = if lft > wdt - width x then
		layoutFloatedRight wdt (lft, lftY) (wdt - width x, lftY + height x) xs ((wdt - width x, lftY, (x, float)):acc)
	else
		layoutFloatedRight wdt (lft, lftY) (min rgt (wdt - width x), rgtY + height x) xs ((wdt - width x, rgtY, (x, float)):acc)
layoutFloatedRight _ _ pr [] acc = (pr, acc)

layoutParagraph _ _ tuple [] acc = (tuple, acc)
layoutParagraph wdt just (lftPr, rgtPr, y) ls acc = layoutParagraph
		wdt
		just
		((if lftY <= y' then 0 else lft, lftY), (if rgtY <= y' then wdt else rgt, rgtY), y')
		(drop (length (inlines' ++ outLfts ++ outRgts)) ls)
		(inlines' ++ outLfts ++ outRgts ++ acc) where
	lineLayout = layoutLine (lineWidth (fst lftPr, fst rgtPr, fst lftPr) ls 0 0) just (fst lftPr, fst rgtPr, y) ls
	inlines = filter (\(_, _, (_, flt)) -> flt == Inline) lineLayout
	-- If there isn't enough space, can still position one element below all other elements.
	inlines' = if null inlines && y >= snd lftPr && y >= snd rgtPr && let (_, float) = head ls in float == Inline then [(0, y, head ls)] else inlines
	floatLefts = filter (\(_, _, (_, flt)) -> flt == FloatLeft) lineLayout
	floatRights = filter (\(_, _, (_, flt)) -> flt == FloatRight) lineLayout
	((lft, lftY), outLfts) = layoutFloatedLeft (fst lftPr, max y' (snd lftPr)) floatLefts []
	((rgt, rgtY), outRgts) = layoutFloatedRight wdt (lft, lftY) (fst rgtPr, max y' (snd rgtPr)) floatRights []
	y' = maximum (y + 1 : map (\(_, y, (z, _)) -> y + height z) inlines')

layout :: (Displayable t) => Int32 -> ((Int32, Int32), (Int32, Int32), Int32) -> [Paragraph t] -> [(((Int32, Int32), (Int32, Int32), Int32), [(Int32, Int32, (t, Floated))])]
layout wdt tuple ((just, paragraph):xs) = (tuple, out) : layout wdt tuple' xs where
	(tuple', out) = layoutParagraph wdt just tuple paragraph []
layout _ _ [] = []

eraseTuples ls = concatMap snd ls

hitTest _ [] = Nothing
hitTest (x, y) ls = if x >= x2 && y >= y2 then Just res else Nothing where
	res@(x2, y2, _) = argmin (\(x2, y2, _) -> if x >= x2 && y >= y2 then x - x2 + 32767 * (y - y2) else maxBound) ls

paint layoutData wnd dc = do
	font <- createNiceFont
	oldFont <- selectFont dc font
	pos <- liftM nPos (getScrollInfo wnd)
	lay <- readIORef layoutData
	mapM_ (\(x, y, (z, _)) -> draw dc (x, y - pos) z) (eraseTuples lay)
	selectFont dc oldFont
	deleteFont font

locateBreak n ((tuple, ls):xs) acc = if n <= length ls then
		(tuple, reverse acc)
	else
		locateBreak (n - length ls) xs ((tuple, ls) : acc)

-- | Call this to attach flow layout to the given window. Returns a procedure
--   that should be called when the reference changes. All changes must be
--   to the paragraph pointed to by the zipper or the paragraph before it.
attachLayout :: (Displayable t) => IORef (Zipper t) -> HWND -> IO (IO ())
attachLayout ref wnd = do
	wnds <- newIORef []
	layoutData <- newIORef [(((0, 0), (100, 0), 0), [])]
	pending <- newIORef None
	let onChange = do
		modifyIORef pending (\x -> if x == Sizing then Sizing else Update)
		invalidateRect (Just wnd) Nothing True
	subclassProc wnd $ \proc wnd msg wParam lParam -> do
		if msg == wM_SIZE then do
				writeIORef pending Sizing
				invalidateRect (Just wnd) Nothing True
			else if msg == wM_LBUTTONUP || msg == wM_LBUTTONDOWN || msg == wM_MOUSEMOVE then do
				lay <- readIORef layoutData
				let pt = (loWord lParam, hiWord lParam)
				si <- getScrollInfo wnd
				maybe
					(return ())
					(\(x, y, (z, _)) -> mouse (if msg == wM_LBUTTONUP then MouseUp else
						if msg == wM_LBUTTONDOWN then MouseDown else
						MouseMove) wnd wnds pt (x, y) z)
					(hitTest pt (map (\(x, y, (z, flt)) -> (x, y - nPos si, (z, flt))) (eraseTuples lay)))
			else
				return ()
		buffered wnd msg (\dc _ -> do
			pend <- readIORef pending
			when (pend /= None) $ do
				(count, befBig, just, bef, aft, aftBig) <- readIORef ref
				let (count', befBig', aftBig') = if not (null befBig) then
						(count - length (snd (head befBig)), tail befBig, head befBig : (just, reverse bef ++ aft) : aftBig)
					else
						(count, befBig, (just, reverse bef ++ aft) : aftBig)
				lay0 <- readIORef layoutData
				(_, _, wdt, _) <- getClientRect wnd
				let lay = if pend == Sizing then
						layout wdt ((0, 0), (wdt, 0), 0) (reverse befBig' ++ aftBig')
					else let (tuple, existing) = locateBreak count' lay0 [] in
						existing ++ layout wdt tuple aftBig'
				writeIORef layoutData lay
				si <- getScrollInfo wnd
				setScrollInfo wnd (si { nMax = maximum (0 : map (\(_, y, (z, _)) -> y + height z) (eraseTuples lay)) })
				writeIORef pending None
			paint layoutData wnd dc)
		vScroll wnd msg wParam lParam
		proc wnd msg wParam lParam
	onChange
	return onChange

