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

module HySO.Iteration

open System

open FsOmegaLib.SAT
open FsOmegaLib.AutomatonSkeleton
open FsOmegaLib.GNBA
open FsOmegaLib.Operations

open Util
open Configuration
open SecondOrderHyperLTL
open ProductConstruction
open FirstOrderModelChecking


type FixpointConstraintAutomaton<'T, 'L when 'L : comparison and 'T : comparison> =
    {
        QuantifierPrefix : Map<TraceVariable, SetVariable>
        StepAutomaton : GNBA<'T, 'L * TraceVariable>
        TargetTraceVariable : TraceVariable
    }

type private IntermediateFunctionLabel<'L> =
    // Takes the same role as an Arg
    | IntermediateArg of 'L * TraceVariable
    // Record the intermediate output of some automaton used in the iteration
    | IntermediateRes of 'L * string


// let private constructIdentifyFunction (aps : list<'L>) (pi : TraceVariable) = 
    
//     let equivGuard : DNF<int>  = 
//         Util.computeBooleanPowerSet (aps.Length)
//         |> Seq.map (fun b -> 
//             [0..aps.Length - 1]
//             |> List.map (fun i -> 
//                 if b[i] then
//                     [PL i; PL (i + aps.Length)]
//                 else 
//                     [NL i; NL (i + aps.Length)]
//                 )
//             |> List.concat
//             )
//         |> Seq.toList

//     {
//         GNBA.Skeleton =
//             {
//                 AutomatonSkeleton.States = Set.singleton 0
//                 APs =
//                     (aps |> List.map (fun x -> Arg (x, pi)))
//                     @
//                     (aps |> List.map Res)
//                 Edges = 
//                     [0, [equivGuard, 0]]
//                     |> Map.ofList
//             }
//         InitialStates = Set.singleton 0
//         NumberOfAcceptingSets = 0
//         AcceptanceSets = [0, Set.empty] |> Map.ofList
//     }
//     |> GNBA.convertStatesToInt


let computeProjectionAutomaton
    (soAssignment : Map<SetVariable, GNBA<int, FunctionLabel<'L>>>)
    (fixAut : FixpointConstraintAutomaton<int, 'L>)
    (includeInRange : 'L -> bool)
    : GNBA<int, FunctionLabel<'L>> =

    let distinctTransducerIndices =
        fixAut.StepAutomaton.APs
        |> List.map snd
        // We only consider those trace varaibles that are resolved on an automaton and thus not part of the function arguments
        |> List.filter (fun pi -> Map.containsKey pi fixAut.QuantifierPrefix)
        |> List.distinct

    // For each index we generate a unique name. This is used to later compose with the transducer automaton in the correct positions
    let indexToNameMap =
        distinctTransducerIndices
        |> List.mapi (fun i pi -> pi, "_index" + string (i))
        |> Map.ofList

    // We create one GNBA copy for each index we need. The result of each such function GNBA is mapped to the proposition
    let modelList =
        distinctTransducerIndices
        |> List.map (fun pi ->
            soAssignment.[fixAut.QuantifierPrefix.[pi]]
            |> GNBA.mapAPs (
                function
                | Arg(y, ind) -> IntermediateArg(y, ind)
                | Res y -> IntermediateRes(y, indexToNameMap.[pi])
            )
        )

    let transducerAutomaton =
        fixAut.StepAutomaton
        |> GNBA.mapAPs (fun (x, pi) ->
            if Map.containsKey pi fixAut.QuantifierPrefix then
                // This variable is reolved on a given automataon. Rename the AP to match the output of that automataon
                IntermediateRes(x, indexToNameMap.[pi])
            else
                // This trace is not resolved on a given set and thus part of the function
                IntermediateArg(x, pi)
        )

    let auts = transducerAutomaton :: modelList

    let resGNBA = auts |> AutomataUtil.constructConjunctionOfGNBAs

    let newAPs =
        resGNBA.APs
        |> List.filter (
            function
            | IntermediateArg _ -> true
            | IntermediateRes(x, pi) ->
                // Only keep those result APs that match the target && are in the fixed APs that we care about
                pi = indexToNameMap.[fixAut.TargetTraceVariable] && (includeInRange x)
        )

    let resGNBA = resGNBA |> GNBA.projectToTargetAPs newAPs

    {
        GNBA.Skeleton =
            {
                AutomatonSkeleton.States = resGNBA.States
                APs =
                    resGNBA.APs
                    |> List.map (
                        function
                        | IntermediateArg(y, pi) -> Arg(y, pi)
                        | IntermediateRes(y, _) -> Res y
                    )
                Edges = resGNBA.Edges
            }
        InitialStates = resGNBA.InitialStates
        NumberOfAcceptingSets = resGNBA.NumberOfAcceptingSets
        AcceptanceSets = resGNBA.AcceptanceSets
    }
    |> GNBA.convertStatesToInt



// A Refiner that maintains an underapproximation by iterating a transducer
type IterationUnderapproximation<'L when 'L : comparison>
    (
        config : Configuration,
        fixedAssignments : Map<SetVariable, GNBA<int, FunctionLabel<'L>>>,
        name : SetVariable,
        fixpointConstraints : list<FixpointConstraintAutomaton<int, 'L>>
    ) =

    let mutable env : Map<SetVariable, SetAssignment<'L>> = Map.empty
    let mutable envHasChanged = true
    let mutable hasConverged = false

    // We initialize the current model with the empty set
    let mutable currentModel = GNBA.falseAutomaton ()

    let relevantSetVariables =
        fixpointConstraints
        |> List.map (fun c ->
            c.StepAutomaton.APs
            |> List.map snd
            |> List.choose (fun pi -> Map.tryFind pi c.QuantifierPrefix)
        )
        |> List.concat
        |> List.filter (fun x -> x <> name)
        |> List.distinct

    do
        // All variable sets are initialized to the range of all sets
        relevantSetVariables
        |> List.iter (fun x -> env <- Map.add x (Range(GNBA.falseAutomaton (), GNBA.trueAutomaton ())) env)

        // We fix the model for all fixed sets
        fixedAssignments |> Map.iter (fun k v -> env <- Map.add k (Fixed v) env)

    member this.GetCurrentModel() : GNBA<int, FunctionLabel<'L>> = currentModel

    member this.ModelIsPrecise() = hasConverged && not envHasChanged

    member this.Step() =
        if hasConverged && not envHasChanged then
            // Nothing to do. The model did not change
            false
        else
            // As we are computing an under-approximation, we are only interested in the under-approximation of the other models
            // For the current name, we simply take the current model
            let under =
                relevantSetVariables
                |> List.map (fun x -> x, env.[x].Under)
                |> Map.ofList
                |> Map.add name currentModel


            let iterResultsPerConstraint =
                fixpointConstraints
                |> List.map (fun c -> computeProjectionAutomaton under c (fun _ -> true))

            let union = 
                AutomataUtil.constructUnionOfGNBAs (currentModel :: iterResultsPerConstraint)
                |> AutomataUtil.removeEmptyStates
  
            // Simplify the automaton using spot
            let union = 
                FsOmegaLib.Operations.AutomatonConversions.convertToGNBA 
                    config.RaiseExceptions
                    config.SolverConfig.MainPath
                    config.SolverConfig.AutfiltPath
                    Effort.HIGH
                    union
                |> AutomataOperationResult.defaultWith (fun err -> raise <| HySOException err.Info)

            // We check if we have converged to the iteration fixpoint
            let hasReachedFixpoint =
                FsOmegaLib.Operations.AutomataChecks.isEquivalent
                    config.RaiseExceptions
                    config.SolverConfig.MainPath
                    config.SolverConfig.AutfiltPath
                    union
                    currentModel
                |> AutomataOperationResult.defaultWith (fun err -> raise <| HySOException err.Info)

            // We have done one iteration with the new env, so we can set this to false
            envHasChanged <- false

            if hasReachedFixpoint then
                // The last iteration did not change the model
                config.Logger.LogN "## Iteration has converged ##"
                hasConverged <- true
                false
            else
                currentModel <- union
                hasConverged <- false
                true

    member this.Update(x, sol) =
        if List.contains x relevantSetVariables && x <> name then
            // We update the env and set the flag that this has been updated
            // Note that we assume that model changes are monotone (i.e., only improve in precision), so we do not need to restart the computation
            env <- Map.add x sol env
            envHasChanged <- true

            
