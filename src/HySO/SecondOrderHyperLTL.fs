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

module HySO.SecondOrderHyperLTL

open FsOmegaLib.LTL

type TraceVariable = string
type SetVariable = string


type FixpointConstraint<'L when 'L : comparison> =
    {
        QuantifierPrefix : Map<TraceVariable, SetVariable>
        StepFormula : LTL<'L * TraceVariable>
        TargetTraceVariable : TraceVariable
    }

module FixpointConstraint =
    let usedSetVariables (c : FixpointConstraint<'L>) = c.QuantifierPrefix |> Map.values |> set


type FirstOrderQuantifierType =
    | FORALL
    | EXISTS

type Quantifier<'L when 'L : comparison> =
    | FirstOrderQuantifier of FirstOrderQuantifierType * TraceVariable * SetVariable
    | FixpointQuantifier of list<FixpointConstraint<'L>> * SetVariable


module Quantifier =

    let setVariablesNeededFor (x : SetVariable) (q : Quantifier<'L>) =
        match q with
        | FixpointQuantifier(c, y) when y = x -> c |> List.map FixpointConstraint.usedSetVariables |> Set.unionMany
        | _ -> Set.empty


    let usedSetVariables (q : Quantifier<'L>) =
        match q with
        | FirstOrderQuantifier(_, _, x) -> Set.singleton x
        | FixpointQuantifier _ -> Set.empty


type SOHyperLTL<'L when 'L : comparison> =
    {
        QuantifierPrefix : list<Quantifier<'L>>
        LTLMatrix : LTL<'L * TraceVariable>
    }

module SOHyperLTL =

    let firstOrderPrefix (formula : SOHyperLTL<'L>) =
        formula.QuantifierPrefix
        |> List.choose (
            function
            | FirstOrderQuantifier(f, x, s) -> Some(f, x, s)
            | _ -> None
        )

    let fixpointConstraintsMap (formula : SOHyperLTL<'L>) =
        formula.QuantifierPrefix
        |> List.choose (
            function
            | FixpointQuantifier(constraints, y) -> (y, constraints) |> Some
            | FirstOrderQuantifier _ -> None
        )
        |> Map.ofList


    exception private FoundError of string

    let findError (formula : SOHyperLTL<'L>) =
        try
            let traceVariables = firstOrderPrefix formula |> List.map (fun (_, pi, _) -> pi)

            traceVariables
            |> List.groupBy id
            |> List.iter (fun (pi, l) ->
                if List.length l > 1 then
                    raise <| FoundError $"Trace variable '{pi}' is quantified more than once"
            )

            LTL.allAtoms formula.LTLMatrix
            |> Set.iter (fun (_, pi) ->
                if List.contains pi traceVariables |> not then
                    raise
                    <| FoundError $"Trace variable '{pi}' is used but not defined in the prefix"
            )

            fixpointConstraintsMap formula
            |> Map.iter (fun x l -> 
                l 
                |> List.iter (fun c -> 
                    if Map.containsKey c.TargetTraceVariable c.QuantifierPrefix |> not then 
                        raise
                        <| FoundError $"A fixpoint constraint for '{x}' adds trace variables '{c.TargetTraceVariable}', but may only add trace variables quantified in the prefix"
                    )
                )
                
            None

        with FoundError msg ->
            Some msg

module Parser =
    open FParsec

    let private commentParser = (skipString "--" .>> restOfLine false)

    let private ws = spaces .>> sepEndBy commentParser spaces

    let private traceVarParser = many1Chars (letter <|> digit)

    let private setVarParser = many1Chars (letter <|> digit)



    let private prefixParser indexedAtomParser =
        let forallParser =
            pipe2
                (skipString "forall" >>. ws >>. traceVarParser)
                (ws >>. skipChar ':' >>. ws >>. setVarParser .>> ws .>> skipChar '.')
                (fun x y -> (FORALL, x, y) |> FirstOrderQuantifier)

        let existsParser =
            pipe2
                (skipString "exists" >>. ws >>. traceVarParser)
                (ws >>. skipChar ':' >>. ws >>. setVarParser .>> ws .>> skipChar '.')
                (fun x y -> (EXISTS, x, y) |> FirstOrderQuantifier)

        let fixpointParser indexedAtomParser =
            let fixpointConstraintParser =
                let fixpointQuantifierPrefixParser =
                    between
                        (skipChar '[' .>> ws)
                        (skipChar ']')
                        (many (
                            tuple2
                                (traceVarParser .>> ws .>> skipChar ':' .>> ws)
                                (setVarParser .>> ws .>> skipChar '.')
                            .>> ws
                        ))

                pipe3
                    (fixpointQuantifierPrefixParser .>> ws)
                    (skipChar '{' >>. ws >>. FsOmegaLib.LTL.Parser.ltlParser indexedAtomParser
                     .>> ws
                     .>> skipChar '}'
                     .>> ws
                     .>> skipString "=>"
                     .>> ws)
                    (traceVarParser)
                    (fun qf f pi ->
                        {
                            FixpointConstraint.QuantifierPrefix = Map.ofList qf
                            StepFormula = f
                            TargetTraceVariable = pi
                        }
                    )

            pipe2
                (skipString "fix" >>. ws >>. skipChar '(' >>. ws >>. setVarParser
                 .>> ws
                 .>> skipChar '$'
                 .>> ws)
                (sepBy (fixpointConstraintParser .>> ws) (skipChar '$' .>> ws)
                 .>> ws
                 .>> skipChar ')'
                 .>> ws
                 .>> skipChar '.')
                (fun f c -> FixpointQuantifier(c, f))

        many1 ((forallParser <|> existsParser <|> fixpointParser indexedAtomParser) .>> ws)


    let private secondOrderHyperLTLParser (atomParser : Parser<'T, unit>) =
        let ap : Parser<'T * string, unit> =
            atomParser .>> pchar '_' .>>. (many1Chars letter)

        pipe2
            (ws >>. prefixParser ap .>> ws)
            (FsOmegaLib.LTL.Parser.ltlParser ap)
            (fun x y ->
                {
                    SOHyperLTL.QuantifierPrefix = x
                    LTLMatrix = y
                }
            )

    let parseSecondOrderHyperLTL (atomParser : Parser<'T, unit>) s =
        let full = secondOrderHyperLTLParser atomParser .>> ws .>> eof
        let res = run full s

        match res with
        | Success(res, _, _) -> Result.Ok res
        | Failure(err, _, _) -> Result.Error err
