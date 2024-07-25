// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Type definitions and functions for type-checking an untyped Hygge AST, and
/// translating it into a typed AST.
module Typechecker

open AST
open Type


/// Representation of typing errors
type TypeErrors = list<Position * string>


/// A typing environment, with information used for typing a program expression.
type TypingEnv = {
    /// Mapping from the variables names in the current scope to their type.
    Vars: Map<string, Type>
    /// Mapping from type aliases in the current scope to their definition.
    TypeVars: Map<string, Type>
    /// Mutable variables in the current scope.
    Mutables: Set<string>
} with
    /// Return a compact and readable representation of the typing environment.
    override this.ToString(): string =
                 "{" + $"vars: %s{Util.formatMap this.Vars}; "
                     + $"types: %s{Util.formatMap this.TypeVars}"
                     + $"mutable vars: %s{Util.formatAsSet this.Mutables}"
                     + "}"


/// A type alias for a typed AST, where there is a typing environment and typing
/// information in each node.
type TypedAST = AST.Node<TypingEnv, Type>


/// A type alias for a typed expression within a typed AST, where there is a
/// typing environment and typing information in each node.
type TypedExpr = AST.Expr<TypingEnv, Type>


/// Result of a typing computation: a typed AST, or a list of errors with
/// positions.
type TypingResult = Result<TypedAST, TypeErrors>


/// Auxiliary function that takes 2 Results, combines their Error contents into
/// a single Error instance, and returns it.  This function expects that at
/// least one of the two Results is an Error.
let internal mergeErrors (r1: Result<'A, TypeErrors>, r2: Result<'A, TypeErrors>): Result<'B, TypeErrors> =
    match (r1, r2) with
    | (Ok(_), Error(es)) -> Error(es)
    | (Error(es), Ok(_)) -> Error(es)
    | (Error(es1), Error(es2)) -> Error(es1 @ es2)
    | (ok1, ok2) -> failwith $"BUG: expecting at least one Error, got %O{ok1}, %O{ok2}"


/// Retrieve a list of all errors from a list of results.
let internal collectErrors (rs: List<Result<'R, List<'E>>>): List<'E> =
    let getError (x: Result<'R, List<'E>>): List<'E> = match x with
                                                       | Ok(_) -> []
                                                       | Error(es) -> es
    List.collect id (List.map getError rs)


/// Get an Ok value from a Result, and fail immediately if it is an Error.
let internal getOkValue (x: Result<'R,'E>): 'R =
    match x with
    | Ok(t) -> t
    | Error(es) -> failwith $"BUG: unexpected error: %O{es}"


/// Transform the given pretype into a full-fledget type, if possible, using the
/// given environment.  Return the resulting Type, or errors.
let rec internal resolvePretype (env: TypingEnv) (pt: AST.PretypeNode): Result<Type, TypeErrors> =
    match pt.Pretype with
    | Pretype.TId(name) ->
        match (lookupTypeVar env name) with
        | Some(t) -> Ok(t)
        | None -> Error([(pt.Pos, $"reference to undefined type: %s{name}")])
    | Pretype.TFun(argPretypes, retPretype) ->
        /// Lambda argument types (possibly with errors)
        let argTypes = List.map (fun a -> resolvePretype env a) argPretypes
        /// Lambda return type, or error
        let returnType = resolvePretype env retPretype
        /// Errors occurred while resolving 'argPretypes' or 'retPretypes'
        let errors = collectErrors (argTypes @ [returnType])
        if not errors.IsEmpty then Error(errors)
        else
            let argTypes = List.map getOkValue argTypes
            let returnType = getOkValue returnType
            Ok(TFun(argTypes, returnType))
    | Pretype.TStruct(fields) ->
        /// Struct field names and pretypes
        let (fieldNames, fieldPretypes) = List.unzip fields
        /// List of duplicate field names
        let dups = Util.duplicates fieldNames
        if not dups.IsEmpty then
            Error([(pt.Pos, $"duplicate field names in struct type: %s{Util.formatSeq dups}")])
        else
            /// List of field types (possibly with errors)
            let fieldTypes = List.map (fun a -> resolvePretype env a) fieldPretypes
            /// Errors occurred while resolving 'fieldPretypes'
            let errors = collectErrors fieldTypes
            if not errors.IsEmpty then Error(errors)
            else
                /// Type of each struct field
                let fieldTypes = List.map getOkValue fieldTypes
                Ok(TStruct(List.zip fieldNames fieldTypes))
    | Pretype.TUnion(cases) ->
        /// Union type labels and pretypes
        let (caseLabels, casePretypes) = List.unzip cases
        /// List of duplicate label names
        let dups = Util.duplicates caseLabels
        if not dups.IsEmpty then
            Error([(pt.Pos, $"duplicate label names in union type: %s{Util.formatSeq dups}")])
        else
            /// List of case types (possibly with errors)
            let caseTypes = List.map (fun a -> resolvePretype env a) casePretypes
            /// Errors occurred while resolving 'caseTypes'
            let errors = collectErrors caseTypes
            if not errors.IsEmpty then Error(errors)
            else
                /// Type of each union case
                let caseTypes = List.map getOkValue caseTypes
                Ok(TUnion(List.zip caseLabels caseTypes))

/// Resolve a type variable using the given typing environment: optionally
/// return the Type corresponding to variable 'name', or None if 'name' is not
/// defined in the given environment.
and internal lookupTypeVar (env: TypingEnv) (name: string): Option<Type> =
    // Mapping between type names and known basic types
    let btmap = Map (List.map (fun t -> (t.ToString(), t)) Type.basicTypes)
    match (btmap.TryFind name) with
    | Some(t) -> Some(t)
    | None ->
        // Let's check whether we are dealing with a type alias.  Note that we
        // do *not* recursively resolve the type alias with its definition
        match (env.TypeVars.TryFind(name)) with
        | Some(_) -> Some(TVar(name))
        | None -> None


/// Expand the given type 't' according to the given typing 'env'ironment.  If
/// the given type is a type variable, perform a recursive look-up in the
/// environment, until its actual type definition (i.e. a type that is not just
/// a type variable) is reached and returned.  If the given type is not a type
/// variable, it is just returned immediately.
let rec expandType (env: TypingEnv) (t: Type): Type =
    match t with
    | TVar(name) ->
        // Recursive look-up. Crash immediately if 'name' is not in 'env'
        expandType  env (env.TypeVars.[name])
    | other -> other


/// Check whether 't1' is subtype of 't2' in the typing environment 'env'.
let rec isSubtypeOf (env: TypingEnv) (t1: Type) (t2: Type): bool =
    match (t1, t2) with
    | (t1, t2) when t1 = t2
        -> true // Straightforward equality between types
    | (TVar(name), t2) ->
        // Expand the type variable; crash immediately if 'name' is not in 'env'
        isSubtypeOf env (env.TypeVars.[name]) t2
    | (t1, TVar(name)) ->
        // Expand the type variable; crash immediately if 'name' is not in 'env'
        isSubtypeOf env t1 (env.TypeVars.[name])
    | (TStruct(fields1), TStruct(fields2)) ->
        // A subtype struct must have at least the same fields of the supertype
        if fields1.Length < fields2.Length then false
        else
            /// First n fields of the subtype struct, where n is the number of
            /// fields of the supertype struct: we only check whether these
            /// fields are compatible (the subtype can have more fields)
            let fields1' = fields1[0..(fields2.Length-1)]
            let (fieldNames1, fieldTypes1) = List.unzip fields1'
            let (fieldNames2, fieldTypes2) = List.unzip fields2
            if (fieldNames1 <> fieldNames2) then false
            else
                List.forall2 (fun t1 t2 -> isSubtypeOf env t1 t2)
                             fieldTypes1 fieldTypes2
    | (TUnion(cases1), TUnion(cases2)) ->
        /// Labels of the subtype union
        let (labels1, _) = List.unzip cases1
        /// Labels of the supertype union
        let (labels2, _) = List.unzip cases2
        // A subtype union must have a subset of the labels of the supertype
        if not (Set.isSubset (Set(labels1)) (Set(labels2))) then false
        else
            // A label that appears in both the subtype and supertype unions
            // must have a subtyped argument in the subtype union
            let map1 = Map.ofList cases1
            let map2 = Map.ofList cases2
            List.forall (fun l -> isSubtypeOf env map1.[l] map2.[l]) labels1
    | (_, _) -> false


/// Perform type checking on an untyped AST, using the given typing environment.
/// Return a well-typed AST in case of success, or a sequence of error messages
/// in case of failure.
let rec internal typer (env: TypingEnv) (node: UntypedAST): TypingResult =
    match node.Expr with
    | UnitVal ->
        Ok { Pos = node.Pos; Env = env; Type = TUnit; Expr = UnitVal }
    | BoolVal(v) ->
        Ok { Pos = node.Pos; Env = env; Type = TBool; Expr = BoolVal(v) }
    | IntVal(v) ->
        Ok { Pos = node.Pos; Env = env; Type = TInt; Expr = IntVal(v) }
    | FloatVal(v) ->
        Ok { Pos = node.Pos; Env = env; Type = TFloat; Expr = FloatVal(v) }
    | StringVal(v) ->
        Ok { Pos = node.Pos; Env = env; Type = TString; Expr = StringVal(v) }

    | Var(name) ->
        match (env.Vars.TryFind name) with
        | Some(tpe) ->
            Ok { Pos = node.Pos; Env = env; Type = tpe; Expr = Var(name) }
        | None ->
            Error([(node.Pos, $"undefined variable: %s{name}")])


    | Sub(lhs, rhs) ->
        match (binaryNumericalOpTyper "subtraction" node.Pos env lhs rhs) with
        | Ok(tpe, tlhs, trhs) ->
            Ok { Pos = node.Pos; Env = env; Type = tpe; Expr = Sub(tlhs, trhs) }
        | Error(es) -> Error(es)

    | Div(lhs, rhs) ->
        match (binaryNumericalOpTyper "division" node.Pos env lhs rhs) with
        | Ok(tpe, tlhs, trhs) ->
            Ok { Pos = node.Pos; Env = env; Type = tpe; Expr = Div(tlhs, trhs) }
        | Error(es) -> Error(es)

    | Rem(lhs, rhs) ->
        match (binaryNumericalOpTyper "remainder" node.Pos env lhs rhs) with
        | Ok(tpe, tlhs, trhs) ->
            Ok { Pos = node.Pos; Env = env; Type = TInt; Expr = Rem(tlhs, trhs) }
        | Error(es) -> Error(es)

    | Sqrt(arg) ->
        match (typer env arg) with
        | Ok(targ) when (isSubtypeOf env targ.Type TFloat) ->
            Ok { Pos = node.Pos; Env = env; Type = TFloat; Expr = Sqrt(targ) }
        | Error(es) -> Error(es)

    | Add(lhs, rhs) ->
        match (binaryNumericalOpTyper "addition" node.Pos env lhs rhs) with
        | Ok(tpe, tlhs, trhs) ->
            Ok { Pos = node.Pos; Env = env; Type = tpe; Expr = Add(tlhs, trhs) }
        | Error(es) -> Error(es)

    | Mult(lhs, rhs) ->
        match (binaryNumericalOpTyper "multiplication" node.Pos env lhs rhs) with
        | Ok(tpe, tlhs, trhs) ->
            Ok { Pos = node.Pos; Env = env; Type = tpe; Expr = Mult(tlhs, trhs) }
        | Error(es) -> Error(es)

    | And(lhs, rhs) ->
        match (binaryBooleanOpTyper "and" node.Pos env lhs rhs) with
        | Ok(tlhs, trhs) ->
            Ok { Pos = node.Pos; Env = env; Type = TBool; Expr = And(tlhs, trhs) }
        | Error(es) -> Error(es)

    | Or(lhs, rhs) ->
        match (binaryBooleanOpTyper "or" node.Pos env lhs rhs) with
        | Ok(tlhs, trhs) ->
            Ok { Pos = node.Pos; Env = env; Type = TBool; Expr = Or(tlhs, trhs) }
        | Error(es) -> Error(es)

    | Not(arg) ->
        match (typer env arg) with
        | Ok(targ) when (isSubtypeOf env targ.Type TBool) ->
            Ok { Pos = node.Pos; Env = env; Type = TBool; Expr = Not(targ) }
        | Ok(targ) ->
            Error([(node.Pos, $"logical 'not': expected argument of type %O{TBool}, "
                              + $"found %O{targ.Type}")])
        | Error(es) -> Error(es)

    | Eq(lhs, rhs) ->
        match (numericalRelationTyper "equal to" node.Pos env lhs rhs) with
        | Ok(tlhs, trhs) ->
            Ok { Pos = node.Pos; Env = env; Type = TBool; Expr = Eq(tlhs, trhs) }
        | Error(es) -> Error(es)

    | Less(lhs, rhs) ->
        match (numericalRelationTyper "less than" node.Pos env lhs rhs) with
        | Ok(tlhs, trhs) ->
            Ok { Pos = node.Pos; Env = env; Type = TBool; Expr = Less(tlhs, trhs) }
        | Error(es) -> Error(es)

    | ReadInt ->
        Ok {Pos = node.Pos; Env = env; Type = TInt; Expr = ReadInt}

    | ReadFloat ->
        Ok {Pos = node.Pos; Env = env; Type = TFloat; Expr = ReadFloat}

    | Print(arg) ->
        match (printArgTyper "print" node.Pos env arg) with
        | Ok(targ) -> Ok {Pos = node.Pos; Env = env; Type = TUnit; Expr = Print(targ)}
        | Error(es) -> Error(es)

    | PrintLn(arg) ->
        match (printArgTyper "println" node.Pos env arg) with
        | Ok(targ) -> Ok {Pos = node.Pos; Env = env; Type = TUnit; Expr = PrintLn(targ)}
        | Error(es) -> Error(es)

    | If(cond, ifT, ifF) ->
        match (typer env cond) with
        | Ok(tcond) when (isSubtypeOf env tcond.Type TBool) ->
            match ((typer env ifT), (typer env ifF)) with
            | (Ok(tifT), Ok(tifF)) when (isSubtypeOf env tifT.Type tifF.Type) ->
                Ok { Pos = node.Pos; Env = env; Type = tifT.Type;
                     Expr = If(tcond, tifT, tifF) }
            | (Ok(tifT), Ok(tifF)) when (isSubtypeOf env tifF.Type tifT.Type) ->
                Ok { Pos = node.Pos; Env = env; Type = tifF.Type;
                     Expr = If(tcond, tifT, tifF) }
            | (Ok(tifT), Ok(tifF)) ->
                Error([(node.Pos, $"mismatching 'then' and 'else' types: "
                               + $"%O{tifT.Type} and %O{tifF.Type}")])
            | otherwise -> mergeErrors otherwise
        | Ok(tcond) ->
            Error([(cond.Pos, $"'if' condition: expected type %O{TBool}, "
                              + $"found %O{tcond.Type}")])
        | Error(es) -> Error(es)

    | Seq(nodes) ->
        // We type-check all nodes, then see whether there is any error
        let typingResults = List.map (fun n -> typer env n) nodes
        let errors = collectErrors typingResults
        if errors.IsEmpty then
            let typedNodes = List.map getOkValue typingResults
            let typing = match (List.tryLast typedNodes) with
                         | Some(n) -> n.Type // Take the typing of last node
                         | None -> TUnit // Empty sequence
            Ok {Pos = node.Pos; Env = env; Type = typing; Expr = Seq(typedNodes)}
        else Error(errors)

    | Type(name, def, scope) ->
        // List of known basic type identifiers
        let basicTypeNames = List.map (fun t -> t.ToString()) Type.basicTypes
        if List.contains name basicTypeNames then
            Error([(node.Pos, $"cannot redefine basic type '%s{name}'")])
        else
            match def.Pretype with
            | Pretype.TId(tname) when tname = name ->
                // The type definition is something like:  type T = T
                Error([(node.Pos, $"invalid recursive definition for type %s{name}")])
            | _ ->
                // We disallow the redefinition of type aliases.  This avoids
                // tricky corner cases and simplifies the handling of typing
                // environments.
                match (lookupTypeVar env name) with
                | Some(_) ->
                    Error([(node.Pos, $"type '%s{name}' is already defined")])
                | None ->
                    /// Extended typing environment where the type variable
                    /// being defined maps to 'unit' (although any other type
                    /// would work).  This allows for recursive type definitions
                    let env2 = {env with TypeVars = env.TypeVars.Add(name, TUnit)}
                    match (resolvePretype env2 def) with
                    | Ok(resDef) ->
                        /// Environment to type-check the 'scope' of the type
                        /// variable.  We add the new type variable to this
                        /// environment, mapped to the resolved type definition.
                        let scopeEnv =
                            {env with TypeVars = env.TypeVars.Add(name, resDef)}
                        match (typer scopeEnv scope) with
                        | Ok(tscope) ->
                            // We now need to check that the return type of the
                            // 'scope' of this type definition is also valid
                            // _outside_ the type definition, i.e. the return
                            // type does not capture the type variable being
                            // defined.  To this end, we expand the return type,
                            // and check whether the type variable being defined
                            // still occurs in it.

                            /// Expanded return type of the 'scope' expression.
                            let scopeType = expandType scopeEnv tscope.Type
                            /// Set of free type variables in the 'scope' type.
                            let scopeTypeFV = freeTypeVars scopeType
                            if (scopeTypeFV.Contains name) then
                                Error([(scope.Pos,
                                        $"type variable '%s{name} exits its scope")])
                            else
                               Ok {Pos = node.Pos; Env = env; Type = scopeType;
                                   Expr = Type(name, def, tscope)}
                        | Error(es) -> Error(es)
                    | Error(es) -> Error(es)

    | Ascription(ascr, expr) ->
        let tascr = resolvePretype env ascr
        let texpr = typer env expr
        match (tascr, texpr) with
        | (Ok(tascr), Ok(texpr)) when (isSubtypeOf env (texpr.Type) tascr) ->
            Ok { Pos = node.Pos; Env = env; Type = tascr; Expr = Ascription(ascr, texpr) }
        | (Ok(tascr), Ok(texpr)) ->
            Error([(node.Pos, $"expression type %O{texpr.Type} does not match "
                              + $"ascription type %O{tascr}")])
        | (Ok(_), Error(es)) -> Error(es)
        | (Error(es), tn) ->
            let terrs = match tn with
                        | Ok(_) -> es
                        | Error(es2) -> es @ es2
            Error(terrs)

    | Assertion(arg) ->
        match (typer env arg) with
        | Ok(targ) when (isSubtypeOf env targ.Type TBool) ->
            Ok { Pos = node.Pos; Env = env; Type = TUnit; Expr = Assertion(targ) }
        | Ok(targ) ->
            Error([(node.Pos, $"assertion: expected argument of type %O{TBool}, "
                              + $"found %O{targ.Type}")])
        | Error(es) -> Error(es)

    | Let(name, init, scope) ->
        letTyper node.Pos env name init scope false

    | LetT(name, tpe, init, scope) ->
        letTypeAnnotTyper node.Pos env name tpe init scope

    | LetMut(name, init, scope) ->
        letTyper node.Pos env name init scope true

    | Assign(target, expr) ->
        match ((typer env target), (typer env expr)) with
        | (Ok(ttarget), Ok(texpr)) when (isSubtypeOf env texpr.Type ttarget.Type) ->
            match ttarget.Expr with
            | Var(name) ->
                if (env.Mutables.Contains name) then
                    Ok { Pos = node.Pos; Env = env; Type = ttarget.Type;
                         Expr = Assign(ttarget, texpr) }
                else
                    Error([(node.Pos,
                            $"assignment to non-mutable variable %s{name}")])
            | FieldSelect(_, _) ->
                Ok { Pos = node.Pos; Env = env; Type = ttarget.Type;
                     Expr = Assign(ttarget, texpr) }
            | _ -> Error([(node.Pos, "invalid assignment target")])
        | (Ok(ttarget), Ok(texpr)) ->
            Error([(texpr.Pos,
                    $"expected an expression of type %O{ttarget.Type}, "
                    + $" found %O{texpr.Type}")])
        | (Error(es), Ok(_)) -> Error(es)
        | (Ok(_), Error(es)) -> Error(es)
        | (Error(es1), Error(es2)) -> Error(es1 @ es2)

    | While(cond, body) ->
        match ((typer env cond), (typer env body)) with
        | (Ok(tcond), Ok(tbody)) when (isSubtypeOf env tcond.Type TBool) ->
            Ok { Pos = node.Pos; Env = env; Type = TUnit; Expr = While(tcond, tbody)}
        | (Ok(tcond), Ok(_)) ->
            Error([(tcond.Pos, $"'while' condition: expected type %O{TBool}, "
                               + $"found %O{tcond.Type}")])
        | Ok(tcond), Error(es) ->
            Error((tcond.Pos, $"'while' condition: expected type %O{TBool}, "
                              + $"found %O{tcond.Type}") :: es)
        | Error(es), Ok(_) -> Error(es)
        | Error(esCond), Error(esBody) -> Error(esCond @ esBody)

    | Lambda(args, body) ->
        let (argNames, argPretypes) = List.unzip args
        /// Duplicate names in 'lambda' arguments
        let dups = Util.duplicates argNames
        if not (dups.IsEmpty) then
            Error([(node.Pos, $"duplicate argument names: %s{Util.formatSeq dups}")])
        else
            /// Tentatively-resolved types of all 'lambda' arguments
            let tryResArgTypes = List.map (fun t -> resolvePretype env t) argPretypes
            /// Errors (if any) which occurred during argument type resolution
            let argTypeErrors = collectErrors tryResArgTypes
            if not (argTypeErrors.IsEmpty) then Error(argTypeErrors)
            else
                /// List of resolved argument types
                let resArgTypes = List.map getOkValue tryResArgTypes
                /// Mapping from 'lambda' argument names to their resolved types
                let funArgsTypes = Map(List.zip argNames resArgTypes)
                /// Environment to type-check the function body, including the
                /// argument names and types
                let bodyEnv = {env with Vars = Util.addMaps env.Vars funArgsTypes}
                match (typer bodyEnv body) with
                | Ok(tbody) ->
                    Ok { Pos = node.Pos; Env = env;
                         Type = TFun(resArgTypes, tbody.Type);
                         Expr = Lambda(args, tbody) }
                | Error(es) -> Error(es)

    | Application(expr, args) ->
        match (typer env expr) with
        | Ok(texpr) ->
            match (expandType env texpr.Type) with
            | TFun(funArgTypes, funRetType) ->
                if funArgTypes.Length <> args.Length then
                    Error([(node.Pos, $"applying function to %d{args.Length} arguments, "
                                      + $"while it expects %d{funArgTypes.Length}")])
                else
                    /// Tentatively type-checked function call arguments
                    let argTypings = List.map (fun n -> typer env n) args
                    /// List of errors (if any) in argument typings
                    let errs = collectErrors argTypings
                    if not errs.IsEmpty then Error(errs)
                    else
                        /// List of well-typed function call arguments
                        let targs = List.map getOkValue argTypings
                        /// Does the given 'arg'ument have the given 't'ype?
                        let isArgBadlyTyped (arg: TypedAST, t: Type) =
                            not (isSubtypeOf arg.Env arg.Type t)
                        /// Application arguments whose types doesn't match the
                        /// corresponding type in 'funArgTypes'
                        let badArgs = List.filter isArgBadlyTyped
                                                   (List.zip targs funArgTypes)
                        if not badArgs.IsEmpty then
                            let errFormat (node: TypedAST, t: Type) =
                                (node.Pos, $"expected argument of type %O{t}, found %O{node.Type}")
                            let errors = List.map errFormat badArgs
                            Error(errors)
                        else
                            Ok { Pos = node.Pos; Env = env; Type = funRetType;
                                 Expr = Application(texpr, targs) }
            | t ->
                Error([(expr.Pos, $"cannot apply an expression of type %O{t} as a function")])
        | Error(es) -> Error(es)

    | StructCons(fields) ->
        let (fieldNames, fieldNodes) = List.unzip fields
        let dups = Util.duplicates fieldNames
        if not (dups.IsEmpty) then
            Error([(node.Pos, $"duplicate structure field names: %s{Util.formatSeq dups}")])
        else
            /// Typings (possibly with errors) of init expressions of all fields
            let initTypings = List.map (fun n -> typer env n) fieldNodes
            let errs = collectErrors initTypings
            if not errs.IsEmpty then Error(errs)
            else
                /// Typed AST nodes of init expressions, for all struct fields
                let typedInits = List.map getOkValue initTypings
                /// Types of each struct field (derived from their init expr)
                let fieldTypes = List.map (fun (t: TypedAST) -> t.Type) typedInits
                /// Pairs of field names and their respective type
                let fieldNamesTypes = List.zip fieldNames fieldTypes
                /// Pairs of field names and typed AST node of init expression
                let fieldsTypedInits = List.zip fieldNames typedInits
                Ok { Pos = node.Pos; Env = env; Type = TStruct(fieldNamesTypes);
                     Expr = Expr.StructCons(fieldsTypedInits)}

    | FieldSelect(target, field) ->
        match (typer env target) with
        | Ok(texpr) ->
            match (expandType env texpr.Type) with
            | TStruct(fields) ->
                let (fieldNames, fieldTypes) = List.unzip fields
                if not (List.contains field fieldNames) then
                    Error([(node.Pos, $"struct has no field called '%s{field}'")])
                else
                    let idx = List.findIndex (fun f -> f = field) fieldNames
                    Ok { Pos = node.Pos; Env = env; Type = fieldTypes.[idx];
                         Expr = FieldSelect(texpr, field)}
            | _ -> Error([(node.Pos, $"cannot access field '%s{field}' "
                                     + $"on expression of type %O{texpr.Type}")])
        | Error(es) -> Error(es)

    | Pointer(_) ->
        Error([(node.Pos, "pointers cannot be type-checked (by design!)")])

    | UnionCons(label, expr) ->
        match (typer env expr) with
        | Ok(texpr) ->
            // We type the union instance with the most precise labelled union
            // type that contains it
            Ok { Pos = node.Pos; Env = env; Type = TUnion([label, texpr.Type]);
                 Expr = UnionCons(label, texpr) }
        | Error(es) -> Error(es)

    | Match(expr, cases) ->
        /// Duplicate labels in the pattern matching cases
        let dups = Util.duplicates ((List.map (fun (label,_,_) -> label)) cases)
        if not dups.IsEmpty then
            Error([(expr.Pos, $"duplicate case labels in pattern matching: %s{Util.formatSeq dups}")])
        else
            match (typer env expr) with
            | Ok(texpr) ->
                match (expandType env texpr.Type) with
                | TUnion(unionCases) ->
                    let (unionLabels, unionTypes) = List.unzip unionCases
                    /// The function 'caseTyper' is mapped over all
                    /// 'unionCases': it looks for the matched label in
                    /// 'unionLabels', extracts the corresponding type from
                    /// 'unionTypes', and type-checks the match continuation by
                    /// introducing the matched variable and type in the
                    /// environment.
                    let caseTyper (label, v, cont: UntypedAST): TypingResult =
                        match (List.tryFindIndex (fun l -> l = label) unionLabels) with
                        | Some(i) ->
                            /// Updated environment for type-checking the union
                            /// case continuation
                            let env2 = {env with Vars = env.Vars.Add(v, unionTypes.[i])}
                            typer env2 cont
                        | None -> Error([(cont.Pos, $"invalid match case: %s{label}")])
                    /// Typed continuations (possibly with errors)
                    let tconts = List.map caseTyper cases
                    /// Typing errors in continuations
                    let errors = collectErrors tconts
                    if errors.IsEmpty then
                        /// Typed continuations, without errors
                        let typedConts = List.map getOkValue tconts
                        /// Desired type for all union cases (taken from the
                        /// first union case)
                        let matchType = typedConts.[0].Type
                        /// Has the given AST node a "bad" type that is not a
                        /// subtype of 'matchType'?
                        let hasBadType (c: TypedAST) =
                            not (isSubtypeOf env c.Type matchType)
                        /// List of match continuation types that are not compatible
                        /// with 'matchType'
                        let badTypes = List.filter hasBadType typedConts.[1..]
                        if badTypes.IsEmpty then
                            /// Match case labels and variables
                            let (caseLabels, caseVars, _) = List.unzip3 cases
                            /// Typed match cases
                            let tcases = List.zip3 caseLabels caseVars typedConts
                            Ok { Pos = node.Pos; Env = env; Type = matchType;
                                 Expr = Match(texpr, tcases)}
                        else
                            let errFmt (c: TypedAST) =
                                (c.Pos, $"pattern match result type mismatch: "
                                        + $"expected %O{matchType}, found %O{c.Type}")
                            Error(List.map errFmt badTypes)
                    else Error(errors)
                | _ ->
                    Error([(expr.Pos, $"cannot match on expression of type %O{texpr.Type}")])
            | Error(es) -> Error(es)

/// Compute the typing of a binary numerical operation, by computing and
/// combining the typings of the 'lhs' and 'rhs'.  The argument 'descr' (used in
/// error messages) specifies which expression is being typed, while 'pos'
/// specifies its position.  In case the 'lhs' and 'rhs' have the same
/// (numerical) type, return a tuple containing the type of the resulting
/// numerical expression, and the typed ASTs of the 'lhs' and 'rhs'.  Otherwise,
/// return type errors.
and internal binaryNumericalOpTyper descr pos (env: TypingEnv)
                                    (lhs: UntypedAST)
                                    (rhs: UntypedAST): Result<Type * TypedAST * TypedAST, TypeErrors> =
    let tlhs = typer env lhs
    let trhs = typer env rhs
    match (tlhs, trhs) with
    | (Ok(ln), Ok(rn)) when (isSubtypeOf env ln.Type TInt)
                            && (isSubtypeOf env rn.Type TInt) ->
        Ok(TInt, ln, rn)
    | (Ok(ln), Ok(rn)) when (isSubtypeOf env ln.Type TFloat)
                            && (isSubtypeOf env rn.Type TFloat) ->
        Ok(TFloat, ln, rn)
    | (Ok(t1), Ok(t2)) ->
        Error([(pos, $"%s{descr}: expected arguments of a same type "
                     + $"between %O{TInt} or %O{TFloat}, "
                     + $"found %O{t1.Type} and %O{t2.Type}")])
    | otherwise -> mergeErrors otherwise

/// Perform the typing of a binary logical operation, by computing the typings
/// of the 'lhs' and 'rhs'.  The argument 'descr' (used in error messages)
/// specifies which expression is being typed, while 'pos' specifies its
/// position.  In case the 'lhs' and 'rhs' have type Bool, return a tuple
/// containing the typed ASTs of the 'lhs' and 'rhs'. Otherwise, return type
/// errors.
and internal binaryBooleanOpTyper descr pos (env: TypingEnv)
                                  (lhs: UntypedAST)
                                  (rhs: UntypedAST): Result<TypedAST * TypedAST, TypeErrors> =
    let tlhs = typer env lhs
    let trhs = typer env rhs
    match (tlhs, trhs) with
    | (Ok(ln), Ok(rn)) when (isSubtypeOf env ln.Type TBool)
                            && (isSubtypeOf env rn.Type TBool) ->
        Ok(ln, rn)
    | (Ok(t1), Ok(t2)) ->
        Error([(pos, $"logical '%s{descr}': expected arguments of type %O{TBool}, "
                     + $"found %O{t1.Type} and %O{t2.Type}")])
    | otherwise -> mergeErrors otherwise

/// Perform the typing of a relation between numerical values, by computing the
/// typings of the 'lhs' and 'rhs'.  The argument 'descr' (used in error
/// messages) specifies which expression is being typed, while 'pos' specifies
/// its position.  In case the 'lhs' and 'rhs' have the same (numerical) type,
/// return a tuple containing the typed ASTs of the 'lhs' and 'rhs'. Otherwise,
/// return type errors.
and internal numericalRelationTyper descr pos (env: TypingEnv)
                                    (lhs: UntypedAST)
                                    (rhs: UntypedAST): Result<TypedAST * TypedAST, TypeErrors> =
    let tlhs = typer env lhs
    let trhs = typer env rhs
    match (tlhs, trhs) with
    | (Ok(ln), Ok(rn)) when (isSubtypeOf env ln.Type TInt)
                            && (isSubtypeOf env rn.Type TInt) ->
        Ok(ln, rn)
    | (Ok(ln), Ok(rn)) when (isSubtypeOf env ln.Type TFloat)
                            && (isSubtypeOf env rn.Type TFloat) ->
        Ok(ln, rn)
    | (Ok(t1), Ok(t2)) ->
        Error([(pos, $"relation '%s{descr}': expected arguments of a same type "
                     + $"between %O{TInt} or %O{TFloat}, "
                     + $"found %O{t1.Type} and %O{t2.Type}")])
    | otherwise -> mergeErrors otherwise

/// Perform the typing of the argument of a 'print' or 'println' expression at
/// the given 'pos'ition, using the given 'env'ironment.  The argument 'descr'
/// (used in error messages) specifies which expression is being typed, while
/// 'pos' specifies its position.  Return a typed argument in case of success.
/// Otherwise, return type errors.
and internal printArgTyper descr pos (env: TypingEnv) (arg: UntypedAST): Result<TypedAST, TypeErrors> =
    /// Types of values that can be printed.
    let printables = [TBool; TInt; TFloat; TString]
    match (typer env arg) with
    | Ok(targ) when List.exists (isSubtypeOf env targ.Type) printables ->
        Ok(targ)
    | Ok(targ)->
        Error([(pos, $"%s{descr}: expected argument of a type among "
                        + $"%s{Util.formatAsSet printables}, found %O{targ}")])
    | Error(es) -> Error(es)

/// Perform the typing of a 'let...' binding (without type annotations).  The
/// arguments are: the 'pos'ition of the "let..." expression, the typing
/// 'env'ironment, the 'name' of the declared variable, the 'init'ialisation AST
/// node, and the 'scope' expression of the 'let...' binder.
and internal letTyper pos (env: TypingEnv) (name: string) (init: UntypedAST)
                      (scope: UntypedAST) (isMutable: bool): TypingResult =
    match (typer env init) with
    | Ok(tinit) ->
        /// Variables and types to type-check the 'let...' scope: we add the
        /// newly-declared variable and its type (obtained fron the 'init'
        /// sub-expression) to the typing environment
        let envVars2 = env.Vars.Add(name, tinit.Type)
        /// Mutable variables in the 'let...' scope: if we are declaring an
        /// immutable variable, we remove it from the known mutables
        /// variables (if present); otherwise, if we are declaring a mutable
        /// variable, we add it to the known mutable variables.
        let envMutVars2 = if isMutable then env.Mutables.Add(name)
                                       else env.Mutables.Remove(name)
        /// Environment for type-checking the 'let...' scope
        let env2 = {env with Vars = envVars2
                             Mutables = envMutVars2}
        match (typer env2 scope) with // Recursively type the scope
        | Ok(tscope) ->
            /// Typed "let" expression to be returned
            let tLetExpr = if isMutable then LetMut(name, tinit, tscope)
                                        else Let(name, tinit, tscope)
            Ok { Pos = pos; Env = env; Type = tscope.Type;
                 Expr = tLetExpr }
        | Error(es) -> Error(es)
    | Error(es) -> Error(es)

/// Perform the typing of a 'let...' binding with a type annotation.  The
/// arguments are: the 'pos'ition of the "let..." expression, the typing
/// 'env'ironment, the 'name' of the declared variable, its pretype annotation
/// ('tannot'), the 'init'ialisation AST node, and the 'scope' of the 'let...'
/// binder.
and internal letTypeAnnotTyper pos (env: TypingEnv) (name: string)
                               (tannot: PretypeNode) (init: UntypedAST)
                               (scope: UntypedAST): TypingResult =
    match (resolvePretype env tannot) with
    | Ok(letVariableType) ->
        match (typer env init) with
        | Ok(tinit) ->
            if not (isSubtypeOf env tinit.Type letVariableType)
                then Error [(pos, $"variable '%s{name}' of type %O{letVariableType} "
                                  + $"initialized with expression of incompatible type %O{tinit.Type}")]
                else
                    /// Variables and types to type-check the 'let...' scope: we
                    /// add the newly-declared variable and its type (obtained
                    /// fron the resolved type annotation) to the typing
                    /// environment
                    let envVars2 = env.Vars.Add(name, letVariableType)
                    /// Mutable variables in the 'let...' scope: since we are
                    /// declaring an immutable variable, we remove it from the
                    /// known mutables variables (if present).
                    let envMutVars2 = env.Mutables.Remove(name)
                    /// Environment for type-checking the 'let...' scope
                    let env2 = { env with Vars = envVars2
                                          Mutables = envMutVars2 }
                    match (typer env2 scope) with // Recursively type the scope
                    | Ok(tscope) ->
                        /// Typed "let" expression to be returned
                        let tLetExpr = LetT(name, tannot, tinit, tscope)
                        Ok { Pos = pos; Env = env; Type = tscope.Type;
                             Expr = tLetExpr }
                    | Error(es) -> Error(es)
        | Error(es) -> Error(es)
    | Error(es) -> Error(es)


/// Perform type checking of the given untyped AST.  Return a well-typed AST in
/// case of success, or a sequence of error messages in case of failure.
let typecheck (node: UntypedAST): TypingResult =
    typer { Vars = Map[]; TypeVars = Map[]; Mutables = Set[] } node
