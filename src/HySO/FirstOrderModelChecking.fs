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

module HySO.FirstOrderModelChecking

open System

open FsOmegaLib.SAT
open FsOmegaLib.GNBA
open FsOmegaLib.NBA
open FsOmegaLib.Operations

open Util
open Configuration
open ProductConstruction
open SecondOrderHyperLTL


type SetAssignment<'L when 'L : comparison> =
    // Gives an under and an over approximation
    | Range of GNBA<int, FunctionLabel<'L>> * GNBA<int, FunctionLabel<'L>>
    // Gives the fixed system
    | Fixed of GNBA<int, FunctionLabel<'L>>

    member this.Under =
        match this with
        | Range(a, _) -> a
        | Fixed a -> a

    member this.Over =
        match this with
        | Range(_, b) -> b
        | Fixed a -> a

type FirstOrderCheckingResult =
    | FO_SAT
    | FO_UNSAT

let rec private outsideInModelChecking
    (config : Configuration)
    (soAssignment : Map<SetVariable, SetAssignment<'L>>)
    (quantifierPrefix : list<FirstOrderQuantifierType * TraceVariable * SetVariable>)
    (aut : GNBA<int, 'L * string>, isNegated : bool)
    =

    if quantifierPrefix.IsEmpty then
        assert (aut.APs.Length = 0)

        let isEmpty =
            FsOmegaLib.Operations.AutomataChecks.isEmpty
                config.RaiseExceptions
                config.SolverConfig.MainPath
                config.SolverConfig.AutfiltPath
                aut
            |> AutomataOperationResult.defaultWith (fun err -> raise <| HySOException err.Info)

        if (isEmpty && not isNegated) || (not isEmpty && isNegated) then
            // The property does not hold
            FO_UNSAT
        else
            FO_SAT
        
    else
        let lastQuantifier = List.last quantifierPrefix
        let remainingPrefix = quantifierPrefix[.. quantifierPrefix.Length - 2]

        match lastQuantifier with
        | (EXISTS, pi, x) ->
            // config.Logger.LogN $"Start checking of exists %s{pi} : %s{x}..."
            // Make sure that the automaton is positive
            let positiveAut =
                if isNegated then
                    // config.Logger.LogN $"Start automaton complementation..."

                    FsOmegaLib.Operations.AutomataOperations.complementToGNBA
                        config.RaiseExceptions
                        config.SolverConfig.MainPath
                        config.SolverConfig.AutfiltPath
                        Effort.HIGH
                        aut
                    |> AutomataOperationResult.defaultWith (fun err -> raise <| HySOException err.Info)
                else
                    aut

            // Construct the product with the under-approximation
            let nextAut =
                ProductConstruction.constructExistentialProductWithFunction positiveAut soAssignment.[x].Under pi true

            outsideInModelChecking config soAssignment remainingPrefix (nextAut, false)

        | (FORALL, pi, x) ->
            // config.Logger.LogN $"Start checking of forall %s{pi} : %s{x}..."
            // Make sure the automaton is negated
            let negativeAut =
                if not isNegated then
                    // config.Logger.LogN $"Start automaton complementation..."

                    FsOmegaLib.Operations.AutomataOperations.complementToGNBA
                        config.RaiseExceptions
                        config.SolverConfig.MainPath
                        config.SolverConfig.AutfiltPath
                        Effort.HIGH
                        aut
                    |> AutomataOperationResult.defaultWith (fun err -> raise <| HySOException err.Info)
                else
                    aut

            // Construct the product with the overapproximation
            let nextAut =
                ProductConstruction.constructExistentialProductWithFunction negativeAut soAssignment.[x].Over pi true

            outsideInModelChecking config soAssignment remainingPrefix (nextAut, true)


type VerificationResult =
    | SAT
    | UNSAT
    | UNKNOWN

let checkFirstOrderPrefix
    (config : Configuration)
    (soAssignment : Map<SetVariable, SetAssignment<'L>>)
    (quantifierPrefix : list<FirstOrderQuantifierType * TraceVariable * SetVariable>)
    (aut : GNBA<int, 'L * string>, negAut : GNBA<int, 'L * string>)
    =

    // We first check if the formula holds
    config.Logger.LogN $"Start SAT Check"

    let posRes =
        match List.last quantifierPrefix with
        | (EXISTS, _, _) -> outsideInModelChecking config soAssignment quantifierPrefix (aut, false)
        | (FORALL, _, _) -> outsideInModelChecking config soAssignment quantifierPrefix (negAut, true)

    // config.Logger.LogN $"---------- SAT Check - END ----------"

    match posRes with
    | FO_SAT ->
        // The formula holds!
        SAT
    | FO_UNSAT ->
        // UNSAT, we check if we get a decisive result by checking the negation
        let flippedPrefix =
            quantifierPrefix
            |> List.map (fun q ->
                match q with
                | (FORALL, x, y) -> (EXISTS, x, y)
                | (EXISTS, x, y) -> (FORALL, x, y)
            )

        config.Logger.LogN $"Start UNSAT Check"
        // We check the negated formula, i.e., flip the prefix and use the negated body
        let negRes =
            match List.last flippedPrefix with
            | (EXISTS, _, _) -> outsideInModelChecking config soAssignment flippedPrefix (negAut, false)
            | (FORALL, _, _) -> outsideInModelChecking config soAssignment flippedPrefix (aut, true)

        // config.Logger.LogN $"---------- UNSAT Check - END ----------"

        match negRes with
        | FO_SAT ->
            // The negation holds, so the orginal formula does not
            UNSAT
        | FO_UNSAT ->
            // No statement is possible
            UNKNOWN
