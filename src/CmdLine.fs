// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Configuration of the compiler's command line arguments, and functions to
/// parse it.
module CmdLine
// fsharplint:disable MaxCharactersOnLine

open CommandLine // See https://github.com/commandlineparser/commandline


/// Command line options for tokenization.
[<Verb("tokenize", HelpText="Tokenize the given input source file.")>]
type TokenizerOptions = {
    [<Value(0, Required=true, MetaName="input file", HelpText="Source code file to be tokenized.")>]
    File: string;

    [<Option('l', "log-level", HelpText="Set the log level. Valid values: debug, info, warning, error. (Default: warning)")>]
    LogLevel: Log.LogLevel;

    [<Option('v', "verbose", HelpText="Enable verbose output. (Same effect of using option '--log-level debug')")>]
    Verbose: bool;
}


/// Command line options for parsing.
[<Verb("parse", HelpText="Parse the given input source file.")>]
type ParserOptions = {
    [<Value(0, Required=true, MetaName="input file", HelpText="Source code file to be parsed.")>]
    File: string;

    [<Option('l', "log-level", HelpText="Set the log level. Valid values: debug, info, warning, error. (Default: warning)")>]
    LogLevel: Log.LogLevel;

    [<Option('v', "verbose", HelpText="Enable verbose output. (Same effect of using option '--log-level debug')")>]
    Verbose: bool;

    [<Option('a', "anf", HelpText="Transform the AST into Administrative Normal Form (ANF) after parsing")>]
    ANF: bool;
}


/// Command line options for type-checking.
[<Verb("typecheck", HelpText="Typecheck the given input source file.")>]
type TypecheckerOptions = {
    [<Value(0, Required=true, MetaName="input file", HelpText="Source code file to be typechecked.")>]
    File: string;

    [<Option('l', "log-level", HelpText="Set the log level. Valid values: debug, info, warning, error. (Default: warning)")>]
    LogLevel: Log.LogLevel;

    [<Option('v', "verbose", HelpText="Enable verbose output. (Same effect of using option '--log-level debug')")>]
    Verbose: bool;
}


/// Command line options for the interpreter.
[<Verb("interpret", HelpText="Interpret the given input source file.")>]
type InterpreterOptions = {
    [<Option('t', "typecheck", HelpText="Typecheck the source file before running the interpreter. (Default: false)")>]
    Typecheck: bool;

    [<Value(0, Required=true, MetaName="input file", HelpText="Source code file to be interpreted.")>]
    File: string;

    [<Option('l', "log-level", HelpText="Set the log level. Valid values: debug, info, warning, error (default: warning).")>]
    LogLevel: Log.LogLevel;

    [<Option('v', "verbose", HelpText="Enable verbose output. (Same effect of using option '--log-level debug')")>]
    Verbose: bool;

    [<Option('a', "anf", HelpText="Transform the AST into Administrative Normal Form (ANF) before interpreting")>]
    ANF: bool;
}


/// Command line options for compilation.
[<Verb("compile", isDefault=false, HelpText="Compile the given input source file.")>]
type CompilerOptions = {
    [<Value(0, Required=true, MetaName="input file", HelpText="Source code file to be compiled.")>]
    File: string;

    [<Option('o', "output-file", HelpText="Save the generated assembly code on the given file. (Default: don't save, print on the terminal)")>]
    OutFile: Option<string>;

    [<Option('l', "log-level", HelpText="Set the log level. Valid values: debug, info, warning, error. (Default: warning)")>]
    LogLevel: Log.LogLevel;

    [<Option('v', "verbose", HelpText="Enable verbose output. (Same effect of using option '--log-level debug')")>]
    Verbose: bool;

    [<Option('a', "anf", HelpText="Transform the AST into Administrative Normal Form (ANF) before compiling")>]
    ANF: bool;

    [<Option('r', "registers", HelpText="Number of registers to use for ANF-based code generation (min 3, max 18; default: 18)")>]
    Registers: uint;

    [<Option('O', "optimize", HelpText="Optimization level (default: 0, i.e. no optimizations)")>]
    Optimize: uint
}


/// Command line options for launching RARS with the generated RISC-V assembly.
[<Verb("rars", HelpText="Compile the given input source file and run the generated RISC-V assembly code with RARS.")>]
type RARSLaunchOptions = {
    [<Value(0, Required=true, MetaName="input file", HelpText="Source code file to be compiled.")>]
    File: string;

    [<Option('l', "log-level", HelpText="Set the log level. Valid values: debug, info, warning, error. (Default: warning)")>]
    LogLevel: Log.LogLevel;

    [<Option('v', "verbose", HelpText="Enable verbose output. (Same effect of using option '--log-level debug')")>]
    Verbose: bool;

    [<Option('a', "anf", HelpText="Transform the AST into Administrative Normal Form (ANF) before compiling")>]
    ANF: bool;

    [<Option('r', "registers", HelpText="Number of registers to use for ANF-based code generation (min 3, max 18; default: 18)")>]
    Registers: uint;

    [<Option('O', "optimize", HelpText="Optimization level (default: 0, i.e. no optimizations)")>]
    Optimize: uint
}


/// Command line options for testing.
[<Verb("test", HelpText="Run the test suite.")>]
type TestOptions = {
    [<Option('f', "filter", HelpText="Only execute the tests whose names matches the given string. Examples: \"parser\" for running all parser tests; \"typechecker.fail\" for running the type checking tests that are expected to fail. To see the test names, use the '--debug' option.")>]
    Filter: string;

    [<Option('v', "verbose", HelpText="Enable verbose output (including the test names, usable with the '--filter' option).")>]
    Verbose: bool
}


/// Possible result of command line parsing.
[<RequireQualifiedAccess>]
type ParseResult =
    | Error of int
    | Tokenize of TokenizerOptions
    | Parse of ParserOptions
    | Typecheck of TypecheckerOptions
    | Compile of CompilerOptions
    | RARSLaunch of RARSLaunchOptions
    | Interpret of InterpreterOptions
    | Test of TestOptions


/// Parse the command line.  If successful, return the parsed options; otherwise,
/// return a non-zero integer usable as exit code.
let parse (args: string[]): ParseResult =
    let res = CommandLine.Parser.Default.ParseArguments<TokenizerOptions,
                                                        ParserOptions,
                                                        TypecheckerOptions,
                                                        CompilerOptions,
                                                        InterpreterOptions,
                                                        RARSLaunchOptions,
                                                        TestOptions>(args);

    match res with
    | :? NotParsed<obj> ->
        ParseResult.Error(1) // Non-zero exit code
    | :? Parsed<obj> as parsed ->
        match parsed.Value with
        | :? TokenizerOptions as opt -> ParseResult.Tokenize(opt)
        | :? ParserOptions as opt -> ParseResult.Parse(opt)
        | :? TypecheckerOptions as opt -> ParseResult.Typecheck(opt)
        | :? CompilerOptions as opt -> ParseResult.Compile(opt)
        | :? InterpreterOptions as opt -> ParseResult.Interpret(opt)
        | :? RARSLaunchOptions as opt -> ParseResult.RARSLaunch(opt)
        | :? TestOptions as opt -> ParseResult.Test(opt)
        | x -> failwith $"BUG: unexpected command line parsed value: %O{x}"
    | x -> failwith $"BUG: unexpected command line parsing result: %O{x}"
