// This module handles connections:

import * as vscode from "vscode";
import * as fs from "fs";
import * as path from "path";
import {
  LanguageClient,
  LanguageClientOptions,
  ProtocolNotificationType,
  ServerOptions,
  TransportKind,
} from "vscode-languageclient/node";
import { FileStateNotification } from "./data/ClientState";

let client: LanguageClient | undefined;

export async function stop() {
  if (client) {
    try {
      await client.stop();
    } finally {
      client = undefined;
    }
  }
}

export async function sendRequest<R>(method: string, param: any): Promise<R> {
  if (!client) throw new Error("Language client is not running");
  return client.sendRequest(method, param);
}

/**
 * Resolves the path to the `gcl` LSP executable:
 *   1. An explicit `gcl-vscode.gclPath` setting wins (power users / dev builds).
 *   2. Otherwise the binary bundled in the platform-specific VSIX (bin/gcl).
 *   3. Otherwise fall back to `gcl` on PATH.
 */
function resolveGclPath(context: vscode.ExtensionContext): string {
  const configured = vscode.workspace
    .getConfiguration("gcl-vscode")
    .get<string>("gclPath")
    ?.trim();
  if (configured) return configured;

  const bundled = path.join(
    context.extensionPath,
    "bin",
    process.platform === "win32" ? "gcl.exe" : "gcl",
  );
  if (fs.existsSync(bundled)) {
    // Packaging into a VSIX can drop the executable bit; restore it.
    if (process.platform !== "win32") {
      try {
        fs.chmodSync(bundled, 0o755);
      } catch {
        // best-effort: a spawn error later will surface the real problem
      }
    }
    return bundled;
  }

  return "gcl";
}

export async function start(context: vscode.ExtensionContext) {
  const gclPath = resolveGclPath(context);

  const serverOptions: ServerOptions = {
    // TODO: Temporarily enable logging in both run and debug modes
    run: {
      command: gclPath,
      args: [`--out=./gcl_server.log`],
      transport: TransportKind.stdio,
    },
    debug: {
      command: gclPath,
      args: [`--out=./gcl_server.log`],
      transport: TransportKind.stdio,
    },
  };

  // Options to control the language client
  const clientOptions: LanguageClientOptions = {
    // Register the server for `.gcl` documents
    documentSelector: [{ scheme: "file", language: "gcl" }],
    synchronize: {
      // Notify the server about file changes to '.gcl' files contained in the workspace
      fileEvents: vscode.workspace.createFileSystemWatcher("**/.gcl"),
    },
  };

  // Use "gcl-vscode" as the client ID (matches extension ID for consistency, though not required).
  // This enables automatic trace configuration: vscode-languageclient will automatically read
  // the "gcl-vscode.trace.server" setting without requiring manual setTrace() calls.
  client = new LanguageClient(
    "gcl-vscode",
    "GCL LSP Server",
    serverOptions,
    clientOptions,
  );
  await client.start();
}

export function onFileStateNotification(
  handler: (fileStateNotification: FileStateNotification) => void,
) {
  if (!client) throw new Error("Language client is not running");
  return client.onNotification(
    new ProtocolNotificationType<FileStateNotification, any>("gcl/update"),
    handler,
  );
}
