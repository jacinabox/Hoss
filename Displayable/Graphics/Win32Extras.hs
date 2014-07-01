{-# LANGUAGE ForeignFunctionInterface #-}
module Graphics.Win32Extras where

import Graphics.Win32
import System.Win32.DLL
import Data.Int
import Data.Word
import Data.Bits
import Foreign.ForeignPtr
import Foreign.Ptr
import Foreign.Storable
import Foreign.C.Types
import Codec.BMP
import System.IO.Unsafe
import Control.Monad

foreign import stdcall "windows.h GetWindowTextW" c_GetWindowText :: HWND -> LPTSTR -> Int32 -> IO LRESULT

getWindowText wnd = do
	ptr <- mallocForeignPtrBytes 1000
	withForeignPtr ptr $ \p -> do
		c_GetWindowText wnd p 1000
		peekTString p

foreign import stdcall "windows.h SetFocus" setFocus :: HWND -> IO HWND

dT_WORD_ELLIPSIS :: Word32
dT_WORD_ELLIPSIS = 262144

dT_RIGHT :: Word32
dT_RIGHT = 2

foreign import stdcall "windows.h DrawTextW" c_DrawText :: HDC -> LPTSTR -> Int32 -> LPRECT -> UINT -> IO Int32

drawText dc s rt format = withTString s $ \ps ->
	withRECT rt $ \pr ->
		c_DrawText dc ps (-1) pr format

foreign import stdcall "windows.h SetScrollInfo" c_SetScrollInfo :: HWND -> Int32 -> Ptr SCROLLINFO -> BOOL -> IO BOOL

foreign import stdcall "windows.h GetScrollInfo" c_GetScrollInfo :: HWND -> Int32 -> Ptr SCROLLINFO -> IO Int32

setScrollInfo wnd bar si = withSCROLLINFO si $ \p -> c_SetScrollInfo wnd bar p True

getScrollInfo wnd bar = withSCROLLINFO (SCROLLINFO sIF_ALL 0 0 0 0 0) $ \p -> do
	c_GetScrollInfo wnd bar p
	readSCROLLINFO p

data SCROLLINFO = SCROLLINFO { fMask :: Word32, nMin :: Int32, nMax :: Int32, nPage :: Word32, nPos :: Int32, nTrackPos :: Int32 } deriving Show

withSCROLLINFO :: SCROLLINFO -> (Ptr SCROLLINFO -> IO t) -> IO t
withSCROLLINFO si f = do
	fp <- mallocForeignPtrBytes 28
	withForeignPtr fp $ \p -> do 
		pokeByteOff p 0 (28 :: Word32)
		pokeByteOff p 4 (fMask si)
		pokeByteOff p 8 (nMin si)
		pokeByteOff p 12 (nMax si)
		pokeByteOff p 16 (nPage si)
		pokeByteOff p 20 (nPos si)
		pokeByteOff p 24 (nTrackPos si)
		f p

readSCROLLINFO :: Ptr SCROLLINFO -> IO SCROLLINFO
readSCROLLINFO p = do
	fMask <- peekByteOff p 4
	nMin <- peekByteOff p 8
	nMax <- peekByteOff p 12
	nPage <- peekByteOff p 16
	nPos <- peekByteOff p 20
	nTrackPos <- peekByteOff p 24
	return (SCROLLINFO fMask nMin nMax nPage nPos nTrackPos)

sB_HORZ :: Int32
sB_HORZ = 0

sB_VERT :: Int32
sB_VERT = 1

sB_CTL :: Word32
sB_CTL = 2

sIF_ALL :: Word32
sIF_ALL = 31

sB_PAGEDOWN :: Word32
sB_PAGEDOWN = 3

sB_PAGEUP :: Word32 
sB_PAGEUP = 2

sB_LINEUP :: Word32
sB_LINEUP = 0

sB_LINEDOWN :: Word32
sB_LINEDOWN = 1

sB_BOTTOM :: Word32
sB_BOTTOM = 7

sB_TOP :: Word32
sB_TOP = 6

sB_THUMBPOSITION :: Word32
sB_THUMBPOSITION = 4

sB_THUMBTRACK :: Word32
sB_THUMBTRACK = 5

loWord x = x .&. 32767

hiWord x = shiftR x 16

foreign import stdcall "windows.h CallWindowProcW" callWindowProc :: FunPtr WindowClosure -> HWND -> UINT -> WPARAM -> LPARAM -> IO LRESULT

gWLP_WNDPROC :: Int32
gWLP_WNDPROC = -4

gWLP_ID :: Int32
gWLP_ID = -12

gWLP_USERDATA :: Int32
gWLP_USERDATA = -21

cB_ADDSTRING :: Word32
cB_ADDSTRING = 323

cB_GETCURSEL :: Word32
cB_GETCURSEL = 327

cB_SETCURSEL :: Word32
cB_SETCURSEL = 334

foreign import stdcall "windows.h TrackPopupMenu"
	trackPopupMenu' :: HMENU -> TrackMenuFlag -> Int -> Int -> Int -> HWND -> LPRECT -> IO Int32

allocaMenuItemInfo' :: (Ptr MenuItemInfo -> IO a) -> IO a
allocaMenuItemInfo' f = do
  let size = 48
  fp <- mallocForeignPtrBytes size
  withForeignPtr fp $ \ p -> do
	pokeByteOff p 0 (fromIntegral size::DWORD)
	f p

withMenuItemInfo' :: MenuItemInfo -> (Ptr MenuItemInfo -> IO a) -> IO a
withMenuItemInfo' info f =
  allocaMenuItemInfo' $ \ p ->
  withTString (menuItemTypeData info) $ \ c_str -> do
  pokeByteOff p 8 (menuItemType info)
  pokeByteOff p 12 (menuItemState info)
  pokeByteOff p 16 (menuItemID info)
  pokeByteOff p 20 (menuItemSubMenu info)
  pokeByteOff p 24 (menuItemBitmapChecked info)
  pokeByteOff p 28 (menuItemBitmapUnchecked info)
  pokeByteOff p 36 c_str
  f p

insertMenuItem' :: HMENU -> MenuItem -> Bool -> MenuItemInfo -> IO ()
insertMenuItem' menu item bypos info =
  withMenuItemInfo' info $ \ p_info -> do
    pokeFMask p_info (mIIM_ID .|. mIIM_TYPE)
    failIfFalse_ "InsertMenuItem" $ c_InsertMenuItem menu item bypos p_info
    return ()

foreign import stdcall "windows.h SetDIBitsToDevice"
	setDIBitsToDevice :: HDC -> Int32 -> Int32 -> Word32 -> Word32 -> Int32 -> Int32 -> Word32 -> Word32 -> Ptr CChar -> LPBITMAPINFO -> Word32 -> IO Int32

withBITMAP :: BitmapInfo -> (Ptr () -> IO a) -> IO a
withBITMAP (InfoV3 bi) f = do
	fp <- mallocForeignPtrBytes 24
	withForeignPtr fp $ \p -> do
		pokeByteOff p 0 (dib3Size bi)
		pokeByteOff p 4 (dib3Width bi)
		pokeByteOff p 8 (dib3Height bi)
		pokeByteOff p 12 (dib3Planes bi)
		pokeByteOff p 14 (dib3BitCount bi)
		pokeByteOff p 16 bI_RGB
		pokeByteOff p 20 (dib3ImageSize bi)
		pokeByteOff p 24 (dib3PelsPerMeterX bi)
		pokeByteOff p 28 (dib3PelsPerMeterY bi)
		pokeByteOff p 32 (dib3ColorsUsed bi)
		pokeByteOff p 36 (dib3ColorsImportant bi)
		f p

foreign import stdcall "windows.h GetSysColorBrush" getSysColorBrush :: Int32 -> IO HBRUSH

foreign import stdcall "windows.h GetSysColor" getSysColor :: Int32 -> IO Word32

cOLOR_3DFACE :: Int32
cOLOR_3DFACE = 15

cOLOR_WINDOWTEXT :: Int32
cOLOR_WINDOWTEXT = 8

{-type LOGFONT = ()

type TEXTMETRIC = ()

type FamiliesProc = Ptr LOGFONT -> Ptr TEXTMETRIC -> Word32 -> LPARAM -> IO Int32
foreign import ccall "wrapper"
   mkFamiliesProc :: FamiliesProc -> IO (FunPtr FamiliesProc)

foreign import stdcall "windows.h EnumFontFamiliesExW" c_EnumFontFamiliesEx :: HDC -> Ptr LOGFONT -> FunPtr FamiliesProc -> LPARAM -> Word32 -> IO Int32

withLOGFONT f = do
	fp <- mallocForeignPtrBytes 30
	withForeignPtr fp $ \p -> do
		pokeByteOff p 23 dEFAULT_CHARSET
		pokeByteOff p 27 (0 :: Word8)
		pokeByteOff p 28 (0 :: Word16)
		f p

enumFontFamiliesEx f = withLOGFONT $ \p -> do
	dc <- getDC Nothing
	funptr <- mkFamiliesProc f
	c_EnumFontFamiliesEx dc p funptr 0 0
	freeHaskellFunPtr funptr
	releaseDC Nothing dc

fontName p = p `plusPtr` 28-}

foreign import stdcall "windows.h GetDeviceCaps" getDeviceCaps :: HDC -> Int32 -> IO Int32

lOGPIXELSX :: Int32
lOGPIXELSX = 88

lOGPIXELSY :: Int32
lOGPIXELSY = 90

dLGC_WANTCHARS :: Int32
dLGC_WANTCHARS = 128

dLGC_WANTARROWS :: Int32
dLGC_WANTARROWS = 1

dLGC_DEFPUSHBUTTON :: Int32
dLGC_DEFPUSHBUTTON = 16

wM_CTLCOLORSTATIC :: Word32
wM_CTLCOLORSTATIC = 312

foreign import stdcall "windows.h ChooseColorW" c_ChooseColor :: Ptr () -> IO Bool

cC_RGBINIT :: Word32
cC_RGBINIT = 1

customcolors = unsafePerformIO $ mallocForeignPtrBytes 64
{-# NOINLINE customcolors #-}

chooseColor :: HWND -> COLORREF -> IO (Maybe COLORREF)
chooseColor wnd clr = do
	hdl <- getModuleHandle Nothing
	fp <- mallocForeignPtrBytes 36
	withForeignPtr fp $ \p ->
		withForeignPtr customcolors $ \p2 -> do
		pokeByteOff p 0 (36 :: Word32)
		pokeByteOff p 4 wnd
		pokeByteOff p 8 hdl
		pokeByteOff p 12 clr
		pokeByteOff p 16 p2
		pokeByteOff p 20 cC_RGBINIT
		pokeByteOff p 24 (0 :: Word32)
		pokeByteOff p 28 (0 :: Word32)
		pokeByteOff p 32 (0 :: Word32)
		b <- c_ChooseColor p
		if b then do
				clr <- peekByteOff p 12
				return (Just clr)
			else
				return Nothing

type OPENFILENAME = ()

foreign import stdcall "windows.h GetOpenFileNameW" getOpenFileName :: Ptr OPENFILENAME -> IO Bool

foreign import stdcall "windows.h GetSaveFileNameW" getSaveFileName :: Ptr OPENFILENAME -> IO Bool

oFN_EXPLORER :: Word32
oFN_EXPLORER = 524288

oFN_FILEMUSTEXIST :: Word32
oFN_FILEMUSTEXIST = 4096

oFN_OVERWRITEPROMPT :: Word32
oFN_OVERWRITEPROMPT = 2

data Action = Open | Save deriving Eq

fileOpenOrSave :: Action -> HWND -> String -> String -> IO (Maybe String)
fileOpenOrSave action wnd filter extension = do
	hdl <- getModuleHandle Nothing
	fp <- mallocForeignPtrBytes 76
	fp2 <- mallocForeignPtrBytes 1000
	withForeignPtr fp $ \p ->
		withForeignPtr fp2 $ \p2 ->
		withTString filter $ \flt ->
		withTString extension $ \ext -> do
		pokeByteOff p2 0 (0 :: Word16)
		pokeByteOff p 0 (76 :: Word32)
		pokeByteOff p 4 wnd
		pokeByteOff p 8 hdl
		pokeByteOff p 12 flt
		pokeByteOff p 16 nullPtr
		pokeByteOff p 24 (1 :: Word32)
		pokeByteOff p 28 p2
		pokeByteOff p 32 (1000 :: Word32)
		pokeByteOff p 36 nullPtr
		pokeByteOff p 44 nullPtr
		pokeByteOff p 48 nullPtr
		pokeByteOff p 52 (oFN_EXPLORER .|. if action == Open then oFN_FILEMUSTEXIST else oFN_OVERWRITEPROMPT)
		pokeByteOff p 60 ext
		b <- (if action == Open then getOpenFileName else getSaveFileName) p
		if b then do
				liftM Just (peekTString p2)
			else
				return Nothing

fileOpen = fileOpenOrSave Open

fileSave = fileOpenOrSave Save

messageBox' :: HWND -> String -> String -> MBStyle -> IO MBStatus
messageBox' wnd text caption style =
  withTString text $ \ c_text ->
  withTString caption $ \ c_caption ->
  failIfZero "MessageBox" $ c_MessageBox' wnd c_text c_caption style
foreign import stdcall safe "windows.h MessageBoxW"
  c_MessageBox' :: HWND -> LPCTSTR -> LPCTSTR -> MBStyle -> IO MBStatus

foreign import stdcall "windows.h GlobalUnlock" globalUnlock' :: HANDLE -> IO Bool

foreign import stdcall "windows.h OpenPrinterW" openPrinter :: LPTSTR -> Ptr HANDLE -> Ptr () -> IO Bool

foreign import stdcall "windows.h DocumentPropertiesW" documentProperties :: HWND -> HANDLE -> LPTSTR -> Ptr () -> Ptr () -> Word32 -> IO LONG

foreign import stdcall "windows.h CreateDCW" createDC :: LPCTSTR -> LPCTSTR -> LPCSTR -> Ptr () -> IO HDC

foreign import stdcall "windows.h StartDocW" startDoc :: HDC -> Ptr () -> IO Int32

foreign import stdcall "windows.h EndDoc" endDoc :: HDC -> IO Int32

foreign import stdcall "windows.h StartPage" startPage :: HDC -> IO Int32

foreign import stdcall "windows.h EndPage" endPage :: HDC -> IO Int32

foreign import stdcall "windows.h ClosePrinter" closePrinter :: HANDLE -> IO Bool

foreign import stdcall "windows.h GetDefaultPrinterW" getDefaultPrinter :: LPTSTR -> Ptr DWORD -> IO Bool

dM_OUT_BUFFER :: Word32
dM_OUT_BUFFER = 2

dM_IN_PROMPT :: Word32
dM_IN_PROMPT = 4

type XFORM = Ptr ()

foreign import stdcall "windows.h SetWorldTransform" setWorldTransform :: HDC -> XFORM -> IO Bool

withXFORM :: (Float, Float, Float, Float, Float, Float) -> (XFORM -> IO t) -> IO t
withXFORM (eM11, eM12, eM21, eM22, eDx, eDy) f = do
	fp <- mallocForeignPtrBytes 24
	withForeignPtr fp $ \p -> do
		pokeByteOff p 0 eM11
		pokeByteOff p 4 eM12
		pokeByteOff p 8 eM21
		pokeByteOff p 12 eM22
		pokeByteOff p 16 eDx
		pokeByteOff p 20 eDy
		f p

foreign import stdcall "windows.h PostMessageW" postMessage :: HWND -> WindowMessage -> WPARAM -> LPARAM -> IO Bool

eN_UPDATE :: Word32
eN_UPDATE = 1024

cBN_EDITUPDATE :: Word32
cBN_EDITUPDATE = 6

cBN_SELENDOK :: Word32
cBN_SELENDOK = 9

lBN_SELCHANGE :: Word32
lBN_SELCHANGE = 1

bN_PUSHED :: Word32
bN_PUSHED = 0

hTBOTTOM :: Word32
hTBOTTOM = 15

hTBOTTOMLEFT :: Word32
hTBOTTOMLEFT = 16

hTBOTTOMRIGHT :: Word32
hTBOTTOMRIGHT = 17

hTCAPTION :: Word32
hTCAPTION = 2

hTLEFT :: Word32
hTLEFT = 10

hTRIGHT :: Word32
hTRIGHT = 11

hTTOP :: Word32
hTTOP = 12

hTTOPLEFT :: Word32
hTTOPLEFT = 13

hTTOPRIGHT :: Word32
hTTOPRIGHT = 14

hTCLOSE :: Word32
hTCLOSE = 20

hTMAXBUTTON :: Word32
hTMAXBUTTON = 9

hTMINBUTTON :: Word32
hTMINBUTTON = 8

foreign import stdcall "windows.h SetCapture" setCapture :: HWND -> IO HWND

foreign import stdcall "windows.h ReleaseCapture" releaseCapture :: IO Bool

sS_OWNERDRAW :: Word32
sS_OWNERDRAW = 13

foreign import stdcall "windows.h EnableWindow"
  enableWindow' :: HWND -> Bool -> IO Bool

wC_LISTVIEW = "SysListView32"

lVS_REPORT :: Word32
lVS_REPORT = 1

lVS_SINGLESEL :: Word32
lVS_SINGLESEL = 4

wC_TREEVIEW = "SysTreeView32"

lVM_FIRST :: Word32
lVM_FIRST = 4096

lVM_GETITEMCOUNT = lVM_FIRST + 4

lVM_DELETEITEM = lVM_FIRST + 8

lVM_INSERTITEM = lVM_FIRST + 77

lVM_GETITEMSTATE = lVM_FIRST + 44

lVM_SETITEMTEXT = lVM_FIRST + 116

lVM_GETCOLUMN = lVM_FIRST + 95

lVM_DELETECOLUMN = lVM_FIRST + 28

lVM_INSERTCOLUMN = lVM_FIRST + 97

lVM_SETCOLUMN = lVM_FIRST + 26

lVIF_STATE :: Word32
lVIF_STATE = 8

lVIF_TEXT :: Word32
lVIF_TEXT = 1

lVCF_TEXT :: Word32
lVCF_TEXT = 4

lVCF_WIDTH :: Word32
lVCF_WIDTH = 2

lVIS_SELECTED :: Word32
lVIS_SELECTED = 2

tVM_FIRST :: Word32
tVM_FIRST = 4352

tVM_INSERTITEM = tVM_FIRST

tVM_DELETEITEM = tVM_FIRST + 1

tVM_GETNEXTITEM = tVM_FIRST + 10

tVM_GETITEM = tVM_FIRST + 12

tVM_SETITEM = tVM_FIRST + 13

tVGN_NEXT :: Word32
tVGN_NEXT = 1

tVGN_CHILD :: Word32
tVGN_CHILD = 4

tVIF_TEXT :: Word32
tVIF_TEXT = 1

tVIF_HANDLE :: Word32
tVIF_HANDLE = 16

tVS_HASLINES :: Word32
tVS_HASLINES = 2

foreign import stdcall "windows.h InitCommonControls" initCommonControls :: IO ()

