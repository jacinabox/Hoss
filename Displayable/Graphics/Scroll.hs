module Graphics.Scroll (vScroll) where

import Graphics.Win32
import Graphics.Win32Extras
import Control.Monad

doScroll wnd off = do
	dc <- getDC (Just wnd)
	(_, _, x, y) <- getClientRect wnd
	bitBlt dc 0 0 x y dc 0 off sRCCOPY
	let redrawRt = if off < 0 then
			(0, 0, x, -off)
		else
			(0, y - off, x, y)
	withRECT redrawRt $ \p -> invalidateRect (Just wnd) (Just p) True
	sendMessage wnd wM_PAINT 0 0
	releaseDC (Just wnd) dc

-- | Call this from your window procedure to get automatic scrolling
-- using the window's standard scroll bar.
vScroll :: HWND -> WindowMessage -> WPARAM -> LPARAM -> IO ()
vScroll wnd msg wParam lParam = if msg == wM_VSCROLL then do
		si <- getScrollInfo wnd sB_VERT
		let newY = if loWord wParam == sB_LINEDOWN then
				nPos si + 10
			else if loWord wParam == sB_LINEUP then
				nPos si - 10
			else if loWord wParam == sB_PAGEDOWN then
				nPos si + fromIntegral (nPage si)
			else if loWord wParam == sB_PAGEUP then
				nPos si - fromIntegral (nPage si)
			else if loWord wParam == sB_THUMBPOSITION || loWord wParam == sB_THUMBTRACK then
				fromIntegral (hiWord wParam)
			else
				nPos si
		let clampedY = max 0 (min newY (nMax si - fromIntegral (nPage si)))
		setScrollInfo wnd sB_VERT (si { nPos = clampedY }) 
		doScroll wnd (clampedY - nPos si)
	else if msg == wM_SIZE then do
		si <- getScrollInfo wnd sB_VERT
		(_, _, _, height) <- getClientRect wnd
		setScrollInfo wnd sB_VERT (si { nPage = fromIntegral height })
		si2 <- getScrollInfo wnd sB_VERT
		doScroll wnd (nPos si2 - nPos si)
	else
		return ()
