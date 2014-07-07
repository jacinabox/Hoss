module Graphics.Buffered where

import Graphics.Win32
import Control.Monad
import Foreign.Ptr

bufferedDraw wnd dc f = do
	rt@(_, _, wd, ht) <- getClientRect wnd
	dc' <- createCompatibleDC (Just dc)
	bmp <- createCompatibleBitmap dc wd ht
	oldBmp <- selectBitmap dc' bmp
	f dc' rt
	bitBlt dc 0 0 wd ht dc' 0 0 sRCCOPY
	selectBitmap dc' oldBmp
	deleteBitmap bmp
	deleteDC dc'

-- | Call this from your window procedure to do the given drawing
--   code, double-buffered.
buffered wnd msg f = when (msg == wM_PAINT) $ allocaPAINTSTRUCT $ \ps -> do
	dc <- beginPaint wnd ps
	bufferedDraw wnd dc f
	endPaint wnd ps

