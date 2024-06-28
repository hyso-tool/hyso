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

module HySO.ProductConstruction

open System.Collections.Generic

open TransitionSystem
open FsOmegaLib.SAT
open FsOmegaLib.AutomatonSkeleton
open FsOmegaLib.GNBA

open SecondOrderHyperLTL

type FunctionLabel<'L> =
    | Arg of 'L * TraceVariable
    | Res of 'L


module FunctionLabel = 

    let print (varStringer : 'L -> string) (l : FunctionLabel<'L>) = 
        match l with 
        | Arg (x, pi) -> "arg@" + varStringer x + "_" + pi
        | Res (x) -> "res@" + varStringer x



let constructExistentialProductWithFunction
    (aut : GNBA<int, 'L * TraceVariable>)
    (func : GNBA<int, FunctionLabel<'L>>) // The system is given a function (represented as an automaton)
    (index : TraceVariable)
    (project : bool)
    =

    // The results of the function automaton is resolved on the 'index' trace
    let transformedFunc =
        func
        |> GNBA.mapAPs (fun x ->
            match x with
            | Arg(y, pi) -> (y, pi)
            | Res y -> y, index
        )

    let resGNBA = [ aut; transformedFunc ] |> AutomataUtil.constructConjunctionOfGNBAs

    if project then
        // Compute the APs that will be used in the final automaton.
        // These are all propositions except those indexed by 'index'
        let newAPs = resGNBA.APs |> List.filter (fun (_, i) -> i <> index)

        GNBA.projectToTargetAPs newAPs resGNBA
    else
        resGNBA


/// Given a system and a matching list of relevant propositions, construct an NBA that accepts the traces of the system system (projected on the relevant propositions)
let convertSystemToGNBA (relevantAps : list<'L>) (ts : TransitionSystem<'T, 'L>) =
    // Assert that all interesting aps are also aps in the transition system
    assert (ts.APs |> List.forall (fun x -> List.contains x relevantAps))

    let apMapping =
        relevantAps
        |> List.mapi (fun i a -> i, ts.APs |> List.findIndex ((=) a))
        |> Map.ofList

    let queue = new Queue<_>(ts.InitialStates)
    let edgesDict = new Dictionary<_, _>()
    let allStates = new HashSet<_>(ts.InitialStates)

    while queue.Count <> 0 do
        let tstate = queue.Dequeue()

        let sucs, apEval = ts.Step.[tstate]

        // This is simply a conjunction of literals that hold in the given state and are put on all outgoing transitions
        let guardDNF : DNF<int> =
            [ 0 .. relevantAps.Length - 1 ]
            |> List.map (fun i ->
                let b = apEval.[apMapping.[i]]
                if b then Literal.PL i else Literal.NL i
            )
            |> List.singleton

        let outgoingEdges = sucs |> Seq.toList |> List.map (fun x -> guardDNF, x)

        edgesDict.Add(tstate, outgoingEdges)

        for tstate' in sucs do
            if allStates.Contains tstate' |> not then
                allStates.Add tstate' |> ignore
                queue.Enqueue tstate'


    {
        GNBA.Skeleton =
            {
                AutomatonSkeleton.States = allStates |> set
                Edges = Util.dictToMap edgesDict
                APs = relevantAps
            }
        InitialStates = ts.InitialStates |> set
        NumberOfAcceptingSets = 0
        AcceptanceSets = allStates |> Seq.map (fun x -> x, Set.empty) |> Map.ofSeq
    }
