{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import Graphics.Layout
import Graphics.Displayable
import Graphics.FrameWindow
import Graphics.Win32Extras
import Graphics.Print
import System.Exit
import Graphics.Win32
import Data.Bits
import Data.Int
import Data.IORef
import System.Win32.DLL
import Control.Monad

wndProc _ wnd msg wParam lParam = if msg == wM_CREATE then do
-- 	f <- attachLayout wnd
--	Example 1
--	f [(L, [((Legend ["Thing1", "Thing2"], Bars [1,2,4] 5), Inline)])]
--
--	Example 2
--	ref <- newIORef 0
--	ref2 <- newIORef 0
--	f [(L, [(Selection ref ["Thing1", "Thing2"], Inline), (Selection ref2 ["Thing1", "Thing2"], Inline)])]
--
--	Example 3
--	ref <- newIORef [(Justified, (Str "Thing", FloatRight) : map (\s -> (Str (s ++ " "), Inline)) (words lorem)), (R, [(Str "Thing2", Inline)])]
--
--	Example 4
--	f [(L, [(Right (Plot [[(2,1),(1,2)]]), FloatRight), (Right (Plot [[(1,1),(2,2)]]), FloatLeft), (Right (Plot [[(1,1),(2,2)]]), FloatLeft), (Right (Plot [[(3,3),(4,4)]]), Inline), (Right (Plot [[(3,3),(4,4)]]), Inline)] ++ map (\s -> (Left (Str (s ++ " ")), Inline)) (words lorem))]
--
--	Example 5
--	f [(L, [(Right (Str "Hello"), FloatRight), (Left Clear, Inline), (Right (Str "Hello"), Inline)])]
	printer wnd $ \dc -> startPage dc >> getStockPen bLACK_PEN >>= \pen -> selectPen dc pen >> rectangle dc 0 0 10000 10000 >> endPage dc
	return 0
	else if msg == wM_CLOSE then
	exitSuccess
	else
	defWindowProc (Just wnd) msg wParam lParam

lorem = "Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nunc consectetur euismod leo a convallis. Mauris hendrerit volutpat enim sit amet porttitor. Vivamus eleifend dui fringilla tincidunt consectetur. Maecenas vehicula pharetra libero, sed condimentum lorem. Nullam sed tellus sit amet erat convallis malesuada quis nec nisi. Aenean rhoncus nulla nec enim imperdiet, id tristique tortor dictum. Etiam sit amet ultricies metus. Sed mattis magna dolor, sagittis condimentum eros adipiscing sit amet. Aenean pretium feugiat sapien. Sed rutrum dignissim urna, nec mollis ipsum mattis ut. Fusce in mauris velit. Pellentesque at metus nisi. Nullam non massa id lorem auctor interdum."

main = do
	frameWindow "Test" Nothing Nothing wndProc
	return 0

