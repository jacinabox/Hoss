module Graphics.Print where

import Graphics.Win32
import Graphics.Win32Extras
import Control.Monad
import Data.Int
import Data.Word
import Foreign.ForeignPtr
import Foreign.Ptr
import Foreign.Storable
import Foreign.Marshal.Utils

-- Sets up printing. The f function just has to call startPage and endPage, doing the drawing.
-- For some reason, I can only get this to work with XPS Document Writer.
printer f = with nullPtr $ \phdl ->
	withTString "Microsoft XPS Document Writer" $ \nm -> do
	openPrinter nm phdl nullPtr
	hdl <- peek phdl
	size <- documentProperties nullPtr hdl nm nullPtr nullPtr 0
	fp <- mallocForeignPtrBytes (fromIntegral size)
	withForeignPtr fp $ \p -> do
		res <- documentProperties nullPtr hdl nm p nullPtr dM_OUT_BUFFER
		withTString "WINSPOOL" $ \dctype -> do
			printerDC <- createDC dctype (castPtr p) nullPtr p
			fp2 <- mallocForeignPtrBytes 20
			withForeignPtr fp2 $ \p2 -> do
				pokeByteOff p2 0 (20 :: Int32)
				pokeByteOff p2 4 nullPtr
				pokeByteOff p2 8 nullPtr
				pokeByteOff p2 12 nullPtr
				pokeByteOff p2 16 (0 :: Word32)
				startDoc printerDC p2
				f printerDC
				endDoc printerDC
				deleteDC printerDC
				closePrinter hdl
				return ()
