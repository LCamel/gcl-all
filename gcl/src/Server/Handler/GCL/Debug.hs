{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Server.Handler.GCL.Debug where

import Control.Monad.IO.Class (liftIO)
import qualified Data.Aeson as JSON
import qualified Data.Text as Text
import qualified Data.Text.Lazy as TextLazy
import qualified Data.Text.Lazy.Encoding as TextLazy
import GHC.Generics (Generic)
import Server.Monad (ServerM, getFileState, logTextLn, readSource)
import qualified Server.ToClient as ToClient
import System.Directory (findExecutable)
import System.Environment (lookupEnv)

data DebugParams = DebugParams {filePath :: FilePath}
  deriving (Eq, Show, Generic)

instance JSON.FromJSON DebugParams

instance JSON.ToJSON DebugParams

handler :: DebugParams -> ServerM ()
handler DebugParams {filePath} = do
  -- Show the PATH this server process actually received (set by the VS Code
  -- extension, which prepends the bundled bin/ dir) and whether `z3` resolves
  -- on it. findExecutable does the same PATH search sbv uses to locate z3.
  logTextLn ">>>> gcl.debug: PATH / z3"
  mPath <- liftIO (lookupEnv "PATH")
  logTextLn $ Text.pack $ "PATH=" ++ maybe "(unset)" id mPath
  mZ3 <- liftIO (findExecutable "z3")
  logTextLn $ Text.pack $ "findExecutable z3 => " ++ maybe "NOT FOUND" id mZ3
  logTextLn "<<<< gcl.debug: PATH / z3"

  logTextLn ">>>> gcl.debug: FileState"
  maybeFs <- getFileState filePath
  case maybeFs of
    Nothing -> logTextLn "  FileState not found"
    Just fs -> do
      let json = ToClient.toClientFileStateJSON filePath fs
      logTextLn . TextLazy.toStrict . TextLazy.decodeUtf8 . JSON.encode $ json
  logTextLn "<<<< gcl.debug: FileState"

  logTextLn ">>>> gcl.debug: source"
  maybeSource <- readSource filePath
  case maybeSource of
    Nothing -> do
      logTextLn $ Text.pack $ "source not found for filePath: " ++ filePath
    Just source -> do
      logTextLn source
  logTextLn "<<< gcl.debug: source"
