module Util

/// Return the newline representation (may be e.g. "\n" on Linux and MacOS,
/// "\r\n" on Windows).
let nl = System.Environment.NewLine


/// Return the list of tokens in the given file
let lexFile (fileName: string): Result<list<Parser.token>, string> =
    try
        use textReader = new System.IO.StreamReader(fileName)
        let lexbuf = (Lexer.LexBuffer<char>.FromTextReader textReader)
        lexbuf.EndPos <- { pos_fname = fileName
                           pos_lnum = 0
                           pos_orig_lnum = 0
                           pos_bol = 0
                           pos_cnum = 0
                         }

        // Recursively accumulate tokens in a list, until EOF is reached.
        let rec lexTokens (toks: list<Parser.token>): list<Parser.token> =
            let token = Lexer.tokenize lexbuf
            if token <> Parser.token.EOF then
                // Note that newest tokens are prepended (for performance)
                lexTokens (token :: toks)
            else
                // Reverse the list of tokens, so newest tokens come last
                List.fold (fun acc elem -> elem :: acc) [] (token :: toks)

        try
            Ok(lexTokens [])
        with e ->
            let pos = lexbuf.EndPos
            let line = pos.Line
            let column = pos.Column
            let message = e.Message
            let _lastToken = System.String(lexbuf.Lexeme)
            // Note: internal line & column numbers start from 0
            Error $"%s{fileName}:%d{line+1}:%d{column}: %s{message}"

    with // Top-level exception, possibly thrown by StreamReader creation
    | e -> Error e.Message


/// Parse the given file.
let parseFile (fileName: string): Result<AST.UntypedAST, string> =
    try
        use textReader = new System.IO.StreamReader(fileName)
        let lexbuf = (Lexer.LexBuffer<char>.FromTextReader textReader)
        lexbuf.EndPos <- { pos_fname = fileName
                           pos_lnum = 0
                           pos_orig_lnum = 0
                           pos_bol = 0
                           pos_cnum = 0
                         }

        try
            Ok (Parser.program Lexer.tokenize lexbuf)
        with e ->
            let pos = lexbuf.EndPos
            let line = pos.Line
            let column = pos.Column
            let message = e.Message
            let lastToken = System.String(lexbuf.Lexeme)
            // Note: internal line & column numbers start from 0
            Error $"%s{fileName}:%d{line+1}:%d{column}: %s{message} (last-seen token: '%s{lastToken}')"

    with // Top-level exception, possibly thrown by StreamReader creation
    | e -> Error e.Message


/// Format a message (e.g. an error message) with a position in the given file.
let formatMsg (pos: AST.Position, msg: string): string =
    $"%s{pos.FileName}%s{pos.Format}: %s{msg}"


/// Format the contents of the given sequence as an easy-to-read string.
let formatSeq (s: seq<'A>): string =
    System.String.Join(", ", Seq.map (fun x -> x.ToString()) s)


/// Format the contents of the given sequence as an easy-to-read string looking
/// like a set (with curly brackets around the elements).
let formatAsSet (s: seq<'A>): string =
    "{" + (formatSeq s) + "}"


/// Return a string with a compact representation of the given map, whose
/// keys are assumed to be strings.
let internal formatMap (m: Map<string, 'T>): string =
    let entries = Map.fold (fun s k v -> $"%O{k}: %O{v}" :: s) [] m
    "{" + (String.concat ", " entries) + "}"


/// Given two maps 'm1' and 'm2', return a new map by adding all entries of 'm2'
/// to 'm1'. If a key appears in both maps, the value of 'm2' is used.
let addMaps (m1: Map<'K,'V>) (m2: Map<'K,'V>): Map<'K,'V> =
    let mapFolder (m: Map<'K,'V>) k v = m.Add(k, v)
    Map.fold mapFolder m1 m2


/// Find duplicate entries in a list.
let duplicates<'T when 'T: equality> (lst: List<'T>): List<'T> =
    let grouped = List.map snd (List.groupBy id lst)
    List.choose (fun (g: List<'T>) -> if g.Length > 1 then Some(g.[0]) else None)
                grouped


/// Random number generator for temp directory creation.  NOTE: this object must
/// be locked to be used correctly by multiple threads!
let internal random =  System.Random()


/// Create a temporary directory with a random name, using the given prefix.
let rec mkTempDir (prefix: string): string =
    // Try creating a random directory until we find a non-existent name
    let rnd = lock random (fun _ -> random.Next())
    let dirName = System.IO.Path.Combine(System.IO.Path.GetTempPath(), $"%s{prefix}%d{rnd}")
    // FIXME: .NET does not seem to have any sane way to atomically create a new
    // unique directory, like Unix mktemp...
    if System.IO.Directory.Exists(dirName) || System.IO.File.Exists(dirName) then
        mkTempDir prefix // Let's try again with a different random name
    else
        System.IO.Directory.CreateDirectory(dirName).FullName


/// Set of known uniquely-generated symbols.  It must be locked before being
/// used, to avoid errors if multiple threads attempt to generate unique symbols
/// at the same time.
let mutable internal knownSyms = System.Collections.Generic.HashSet<string>()


/// Internal counter used to generate suffixes for unique symbols.  This counter
/// should only be used after locking 'knownSyms' above.
let mutable internal nextSymSuffix: uint = 0u


/// Generate a unique symbol, e.g. usable as a label or a variable.  The given
/// 'prefix' is used directly as a symbol if it has not been used before;
/// otherwise, it is tweaked to become unique, so this function always returns a
/// different result.
let genSymbol (prefix: string): string =
    lock knownSyms (fun _ ->
        if knownSyms.Add(prefix) then prefix
        else
            let sym = $"%s{prefix}_%d{nextSymSuffix}"
            nextSymSuffix <- nextSymSuffix + 1u
            knownSyms.Add(sym) |> ignore
            sym
    )


/// List of known symbols used to generate unique ids.  It must be locked before
/// being used, to avoid errors if multiple threads attempt to generate unique
/// ids at the same time.
let mutable internal knownSymsWithIds = System.Collections.Generic.List<string>()


/// Generate a numerical id that is unique for the given symbol, e.g. usable to
/// tag the type of an object in memory.  This function returns different ids
/// when invoked with different arguments; if it is called twice with the same
/// argument, it returns the same id.
let genSymbolId (symbol: string): int =
    lock knownSymsWithIds (fun _ ->
        let id = knownSymsWithIds.IndexOf(symbol)
        if (id = -1) then
            knownSymsWithIds.Add(symbol)
            knownSymsWithIds.Count
        else
            // We return the symbol position in 'knownSymsWithIds' as unique id
            id + 1
    )
