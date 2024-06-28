(*    
    Copyright (C) 2023-2024 Raven Beutner

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

module HySO.CommandLineParser

open System

type ExecutionMode = | ExplicitSystem

type CommandLineArguments =
    {
        ExecutionMode : ExecutionMode
        LogPrintouts : bool
        PrintWitness : bool
        RaiseExceptions : bool

        InputFiles : option<list<string>>
    }

    static member Default =
        {
            ExecutionMode = ExplicitSystem
            LogPrintouts = false
            PrintWitness = false
            RaiseExceptions = false

            InputFiles = None
        }

let rec private splitByPredicate (f : 'T -> bool) (xs : list<'T>) =
    match xs with
    | [] -> [], []
    | x :: xs ->
        if f x then
            [], x :: xs
        else
            let r1, r2 = splitByPredicate f xs
            x :: r1, r2

let parseCommandLineArguments (args : list<String>) =
    let rec parseArgumentsRec (args : list<String>) (opt : CommandLineArguments) =

        match args with
        | [] -> Result.Ok opt
        | x :: xs ->
            match x with
            | "--log" -> parseArgumentsRec xs { opt with LogPrintouts = true }
            | "--witness" -> parseArgumentsRec xs { opt with PrintWitness = true }
            | "--debug" -> parseArgumentsRec xs { opt with RaiseExceptions = true }
            | s when s <> "" && s.Trim().StartsWith "-" -> Result.Error("Option " + s + " is not supported")
            | x ->
                // When no option is given, we assume that this is the input
                if opt.InputFiles.IsSome then
                    Result.Error "Input files cannot be given more than once"
                else
                    let files, ys = splitByPredicate (fun (y : string) -> y.[0] = '-') (x :: xs)

                    if List.length args < 1 then
                        Result.Error "The input must consist of at least one arguments"
                    else
                        parseArgumentsRec
                            ys
                            { opt with
                                InputFiles = files |> Some
                            }
        
    parseArgumentsRec args CommandLineArguments.Default
