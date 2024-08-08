// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Logging configuration and functions.
module Log

/// Internal lock, in case multiple threads perform logging at the same time.
let internal lockObject = obj()


/// Log levels.  Higher value means "more serious".
type LogLevel =
   // fsharplint:disable enumCaseNames
   | debug = -2
   | info = -1
   | warning = 0 // IMPORTANT: the default value must be 0
   | error = 1


/// Log level threshold: only messages of equal or higher level are reported.
let mutable internal logLevelTH: LogLevel = LogLevel.warning


/// Set the log level of the compiler.
let setLogLevel (level: LogLevel): unit =
    logLevelTH <- level


// Internal, thread-safe generic logging function.
let internal log color prefix msg: Unit =
    lock lockObject (fun _ ->
        eprintf "hyggec: "
        System.Console.ForegroundColor <- color
        eprintf $"%s{prefix}:"
        System.Console.ResetColor()
        eprintfn $" %s{msg}")


/// Print a debug messages (only shown if the log level is Debug).
let debug (msg: string): unit =
    if logLevelTH <= LogLevel.debug then
        log System.ConsoleColor.Cyan "debug" msg


/// Print an info message (only shown if the log level is Info or below).
let info (msg: string): unit =
    if logLevelTH <= LogLevel.info then
        log System.ConsoleColor.Green "info" msg


/// Print a warning message (only shown if the log level is Warning or below).
let warning (msg: string): unit =
    if logLevelTH <= LogLevel.warning then
        log System.ConsoleColor.Yellow "warning" msg


/// Print an error message (only shown if the log level is Error or below).
let error (msg: string): unit =
    if logLevelTH <= LogLevel.error then
        log System.ConsoleColor.Red "error" msg
