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

module HySO.BidirectionalModelChecking

open System

open FsOmegaLib.LTL
open FsOmegaLib.GNBA
open FsOmegaLib.Operations

open Util
open Configuration
open TransitionSystem
open ProductConstruction
open FirstOrderModelChecking
open SecondOrderHyperLTL
open Iteration

let private relevantSetVariables
    (prefix : list<FirstOrderQuantifierType * TraceVariable * SetVariable>)
    (fixpointDefinitions : Map<SetVariable, list<FixpointConstraint<_>>>)
    : Set<SetVariable> =
    let rec addDependentSetVariables currentVars =
        let a =
            currentVars
            |> Seq.map (fun x ->
                match Map.tryFind x fixpointDefinitions with
                | None -> Set.empty
                | Some c ->
                    c
                    |> List.map (fun y -> y.QuantifierPrefix |> Map.values |> set)
                    |> Set.unionMany
            )
            |> Set.unionMany
            |> Set.union currentVars
        
        if a = currentVars then a else addDependentSetVariables a

    let firstOrderNeed = prefix |> List.map (fun (_, _, x) -> x) |> set


    addDependentSetVariables firstOrderNeed

let modelChecking (config : Configuration) (tslist : list<TransitionSystem<'T, 'L>>) (property : SOHyperLTL<'L>) =

    let firstOrderPrefix =
        property.QuantifierPrefix
        |> List.choose (
            function
            | FirstOrderQuantifier(f, x, s) -> Some(f, x, s)
            | _ -> None
        )

    let fixpointConstraintsMap =
        property.QuantifierPrefix
        |> List.choose (
            function
            | FixpointQuantifier(constraints, y) -> (y, constraints) |> Some
            | FirstOrderQuantifier _ -> None
        )
        |> Map.ofList

    let fixedSetVariables, flexibleSetVariables =
        relevantSetVariables firstOrderPrefix fixpointConstraintsMap
        |> Set.partition (fun x -> x = "all" || x.StartsWith "sys")

    // This is the assignment for all setvaraibles that will never change, i.e., the system and the set of all traces
    let fixedAssignment =
        fixedSetVariables
        |> Set.toList
        |> List.map (fun x ->
            let m =
                if x = "all" then
                    // Get the automaton that returns all traces
                    GNBA.trueAutomaton ()
                else
                    // Get the automat
                    assert (x.StartsWith "sys")
                    let tsIndex = x.[3..] |> int

                    let aut =
                        tslist.[tsIndex]
                        |> ProductConstruction.convertSystemToGNBA tslist.[tsIndex].APs
                        |> GNBA.mapAPs (fun x -> Res x)
                        |> GNBA.convertStatesToInt

                    aut

            x, m
        )
        |> Map.ofList

    

    // For all needed but non-fixed set varaibles, we create a refiner object
    let refinerList =
        flexibleSetVariables
        |> Set.toList
        // Sort these in decreasing order
        |> List.sortBy (fun x ->
            property.QuantifierPrefix
            |> List.findIndex (fun q ->
                match q with
                | FixpointQuantifier(_, z) -> x = z
                | FirstOrderQuantifier _ -> false
            )
        )
        // Map each of these variables to a Refiner pair
        |> List.map (fun x ->
            let iterator =
                let fixpointConstraintAutomata =
                    fixpointConstraintsMap.[x]
                    |> List.map (fun c ->
                        let stepAutomaton =
                            FsOmegaLib.Operations.LTLConversion.convertLTLtoGNBA
                                config.RaiseExceptions
                                config.SolverConfig.MainPath
                                config.SolverConfig.Ltl2tgbaPath
                                c.StepFormula
                            |> AutomataOperationResult.defaultWith (fun err ->
                                config.Logger.LogN err.DebugInfo
                                raise <| HySOException err.Info
                            )

                        {
                            FixpointConstraintAutomaton.QuantifierPrefix = c.QuantifierPrefix
                            StepAutomaton = stepAutomaton
                            TargetTraceVariable = c.TargetTraceVariable
                        }
                    )

                Iteration.IterationUnderapproximation(config, fixedAssignment, x, fixpointConstraintAutomata)

            x, iterator
        )

    let matrixAut =
        FsOmegaLib.Operations.LTLConversion.convertLTLtoGNBA
            config.RaiseExceptions
            config.SolverConfig.MainPath
            config.SolverConfig.Ltl2tgbaPath
            property.LTLMatrix
        |> AutomataOperationResult.defaultWith (fun err -> raise <| HySOException err.Info)

    let negMatrixAut =
        FsOmegaLib.Operations.LTLConversion.convertLTLtoGNBA
            config.RaiseExceptions
            config.SolverConfig.MainPath
            config.SolverConfig.Ltl2tgbaPath
            (LTL.Not property.LTLMatrix)
        |> AutomataOperationResult.defaultWith (fun err -> raise <| HySOException err.Info)


    let rec iterativeChecking step stepBound =
        config.Logger.LogN $"============= Bidirectional Checking - Iteration %i{step} ============="

        // Get the assignment by querying each iterator for its current model
        let currentAssignment =
            refinerList
            |> Map.ofList
            |> Map.map (fun x iterator ->
                let u: GNBA<int,FunctionLabel<'L>> = iterator.GetCurrentModel()

                if config.PrintWitness then 
                    let a = (u :> FsOmegaLib.AbstractAutomaton.AbstractAutomaton<_, _>).ToHoaString string (FunctionLabel.print string)
                    printfn $"{x}:"
                    printfn $"{a}"

                if iterator.ModelIsPrecise() then
                    SetAssignment.Fixed u
                else
                    SetAssignment.Range(u, GNBA.trueAutomaton ())
            )
            |> Util.joinMaps (Map.map (fun _ x -> Fixed x) fixedAssignment)

        let r =
            FirstOrderModelChecking.checkFirstOrderPrefix
                config
                currentAssignment
                firstOrderPrefix
                (matrixAut, negMatrixAut)

        match r with
        | SAT ->
            SAT, step
        | UNSAT ->
            UNSAT, step
        | UNKNOWN when step > stepBound ->
            // exeeced the bound
            UNKNOWN, step
        | UNKNOWN ->
            // Need to refine the second-order assignment

            refinerList
            |> List.iter (fun (x, iterator) ->
                let a = iterator.Step()

                if a then
                    // The model for x has changed, forward this to all other iterators
                    let newRange = Range(iterator.GetCurrentModel(), GNBA.trueAutomaton ())

                    refinerList
                    |> List.iter (fun (y, i) ->
                        if y <> x then
                            i.Update(y, newRange)
                    )
            )

            iterativeChecking (step + 1) stepBound

    let result = iterativeChecking 0 200

    result
