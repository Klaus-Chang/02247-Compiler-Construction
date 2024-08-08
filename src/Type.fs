// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Definition of a type in the hyggec compiler.
module Type


/// Representation of a type.  This is essentially the abstract syntax tree of a
/// type as it appears in a Hygge program (not to be confused with the
/// 'TypedAST' of a whole Hygge program).  The type argument I determines how
/// type identifiers are represented inside the type tree.
type Type =
    /// Boolean type.
    | TBool
    /// Integer type.
    | TInt
    /// Floating-point type (single-precision).
    | TFloat
    /// String type.
    | TString
    /// Unit type.
    | TUnit
    /// Type variable.
    | TVar of name: string
    /// A function type, with argument types and return type.
    | TFun of args: List<Type> * ret: Type
    /// A struct type with ordered fields, each having a unique name and a type.
    | TStruct of fields: List<string * Type>
    /// Discriminated union type.  Each case consists of a label and a type.
    | TUnion of cases: List<string * Type>

    /// Returns a human-readable string describing the type.
    override this.ToString(): string =
        match this with
        | TBool -> "bool"
        | TInt -> "int"
        | TFloat -> "float"
        | TString -> "string"
        | TUnit -> "unit"
        | TVar(name) -> name
        | TFun(args, ret) ->
            let fmtArg (t: Type) = $"%O{t}"
            let argsStr = List.map fmtArg args
            "(" + System.String.Join(", ", argsStr) + $") -> %O{ret}"
        | TStruct(fields) ->
            let fmtEntry (f: string, t: Type) = $"%s{f}: %O{t}"
            let entriesStr = Seq.map fmtEntry fields
            "struct {" + System.String.Join("; ", entriesStr) + "}"
        | TUnion(cases) ->
            let fmtCase (f: string, t: Type) = $"%s{f}: %O{t}"
            let casesStr = Seq.map fmtCase cases
            "union {" + System.String.Join("; ", casesStr) + "}"

/// List of basic types known by the compiler.  NOTE: this list must be kept in
/// sync with the definition of 'Type'.
let basicTypes = [TBool; TInt; TFloat; TString; TUnit]


/// Set of free type variables in a type.
let rec freeTypeVars (t: Type): Set<string> =
    match t with
    | TBool
    | TInt
    | TFloat
    | TString
    | TUnit -> Set[]
    | TVar(name) -> Set[name]
    | TFun(args, ret) ->
        Set.union (collectFreeTypeVars args) (freeTypeVars ret)
    | TStruct(fields) ->
        let (_, fieldTypes) = List.unzip fields
        collectFreeTypeVars fieldTypes
    | TUnion(cases) ->
        let (_, caseTypes) = List.unzip cases
        collectFreeTypeVars caseTypes

/// Collect all free type variables in the given list of types.
and collectFreeTypeVars (ts: List<Type>): Set<string> =
    /// Folder to collect the union of free variables in a list of types.
    let folder (fvs: Set<string>) (t: Type) = Set.union (freeTypeVars t) fvs
    List.fold folder (Set[]) ts
