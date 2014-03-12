module Graphics.Subclass (subclassProc) where

import Unsafe.Coerce
import Data.IORef
import Foreign.Ptr
import Control.Monad
import Graphics.Win32
import Graphics.Win32Extras

-- | This function subclasses a window and takes care of freeing
-- the function pointer when the window closes. The parameter function
-- is passed a function that invokes the default behaviour of the
-- window.
subclassProc :: HWND -> (WindowClosure -> WindowClosure) -> IO ()
subclassProc wnd proc = do
	procVar <- newIORef Nothing
	let closure wnd msg wParam lParam = do
		may <- readIORef procVar
		case may of
			Just (funPtr, oldProc) -> do
				when (msg == wM_NCDESTROY) $ do
					c_SetWindowLongPtr wnd gWLP_WNDPROC oldProc
					freeHaskellFunPtr funPtr
				proc (callWindowProc (unsafeCoerce oldProc)) wnd msg wParam lParam
			Nothing -> proc (\_ _ _ _ -> return 0) wnd msg wParam lParam
	funPtr <- mkWindowClosure closure
	oldProc <- c_SetWindowLongPtr wnd gWLP_WNDPROC (unsafeCoerce funPtr)
	writeIORef procVar (Just (funPtr, oldProc))
