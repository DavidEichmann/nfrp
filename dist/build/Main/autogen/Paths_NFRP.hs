{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_NFRP (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/david/.cabal/bin"
libdir     = "/home/david/.cabal/lib/x86_64-linux-ghc-8.4.2/NFRP-0.1.0.0-DnomXDMCBT4HqifWWZOoKH-Main"
dynlibdir  = "/home/david/.cabal/lib/x86_64-linux-ghc-8.4.2"
datadir    = "/home/david/.cabal/share/x86_64-linux-ghc-8.4.2/NFRP-0.1.0.0"
libexecdir = "/home/david/.cabal/libexec/x86_64-linux-ghc-8.4.2/NFRP-0.1.0.0"
sysconfdir = "/home/david/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "NFRP_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "NFRP_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "NFRP_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "NFRP_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "NFRP_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "NFRP_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
