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

module internal HySO.AutomataUtil

open System.Collections.Generic

open FsOmegaLib.SAT
open FsOmegaLib.AutomatonSkeleton
open FsOmegaLib.GNBA

/// Intersect a list of GNBAs
let constructConjunctionOfGNBAs (autList : list<GNBA<int, 'L>>) =
    let autList = GNBA.bringToSameAPs autList

    let sumOfAccSets =
        (0, autList) ||> List.mapFold (fun s x -> s, s + x.NumberOfAcceptingSets) |> fst

    let initStates =
        autList
        |> List.map (fun x -> x.InitialStates |> seq)
        |> Util.cartesianProduct
        |> set

    let queue = new Queue<_>(initStates)

    let allStates = new HashSet<_>(initStates)
    let newEdgesDict = new Dictionary<_, _>()
    let newAccSetsDict = new Dictionary<_, _>()

    while queue.Count <> 0 do
        let n = queue.Dequeue()

        let edges =
            n
            |> List.mapi (fun i state -> autList.[i].Edges.[state] |> seq)
            |> Util.cartesianProduct
            |> Seq.choose (fun x ->
                let guards, sucs = List.unzip x

                let combinedGuard = DNF.constructConjunction guards

                if DNF.isSat combinedGuard then
                    if allStates.Contains sucs |> not then
                        allStates.Add sucs |> ignore
                        queue.Enqueue sucs

                    Some(combinedGuard, sucs)
                else
                    None
            )
            |> Seq.toList

        // Ensure disjoint acceptance sets
        let accSets =
            n
            |> List.mapi (fun i state -> autList.[i].AcceptanceSets.[state])
            |> List.mapi (fun i accSet -> accSet |> Set.map (fun y -> y + sumOfAccSets.[i]))
            |> Set.unionMany

        newEdgesDict.Add(n, edges)
        newAccSetsDict.Add(n, accSets)

    {
        GNBA.Skeleton =
            {
                AutomatonSkeleton.States = set allStates
                APs = autList.[0].APs
                Edges = Util.dictToMap newEdgesDict
            }
        InitialStates = initStates
        AcceptanceSets = Util.dictToMap newAccSetsDict
        NumberOfAcceptingSets = autList |> List.map (fun x -> x.NumberOfAcceptingSets) |> List.sum
    }
    |> GNBA.convertStatesToInt


let constructUnionOfGNBAs (autList : list<GNBA<int, 'L>>) =
    let autList = GNBA.bringToSameAPs autList

    let maxAccSet = autList |> List.map (fun x -> x.NumberOfAcceptingSets) |> List.max

    {
        GNBA.Skeleton =
            {
                AutomatonSkeleton.States =
                    autList
                    |> List.mapi (fun i aut -> aut.States |> Set.map (fun y -> i, y))
                    |> Set.unionMany
                APs = autList.[0].APs
                Edges =
                    autList
                    |> List.mapi (fun i aut ->
                        aut.Edges
                        |> Map.toSeq
                        |> Seq.map (fun (s, l) -> (i, s), l |> List.map (fun (g, t) -> g, (i, t)))
                    )
                    |> Seq.concat
                    |> Map.ofSeq
            }
        InitialStates =
            autList
            |> List.mapi (fun i x -> x.InitialStates |> Set.map (fun y -> i, y))
            |> Set.unionMany
        AcceptanceSets =
            autList
            |> List.mapi (fun i aut ->
                aut.AcceptanceSets
                |> Map.toSeq
                |> Seq.map (fun (s, acc) ->
                    let newAcc = Set.union acc (set [ aut.NumberOfAcceptingSets .. maxAccSet - 1 ])

                    (i, s), newAcc
                )
            )
            |> Seq.concat
            |> Map.ofSeq

        NumberOfAcceptingSets = maxAccSet
    }
    |> GNBA.convertStatesToInt

// Needed to avoid a bug in spot 2.12
let removeEmptyStates (aut : GNBA<int, 'L>) = 
    let rec removeEmptyStates (aut : GNBA<int, 'L>) = 
        let emptyStates = 
            aut.States
            |> Set.filter (fun s -> List.isEmpty aut.Edges.[s])

        if Set.isEmpty emptyStates then 
            aut 
        else 
            let reducedAut = 
                {
                    GNBA.Skeleton =
                        {
                            AutomatonSkeleton.States =
                                Set.difference aut.States emptyStates
                            APs = aut.APs
                            Edges =
                                aut.Edges
                                |> Map.filter (fun s _ -> Set.contains s emptyStates |> not)
                                |> Map.map (fun _ l -> 
                                    l 
                                    |> List.filter (fun (_, t) -> Set.contains t emptyStates |> not)
                                    )
                        }
                    InitialStates =
                        Set.difference aut.InitialStates emptyStates
                    AcceptanceSets =
                        aut.AcceptanceSets
                        |> Map.filter (fun s _ -> Set.contains s emptyStates |> not)
                    NumberOfAcceptingSets = aut.NumberOfAcceptingSets
                }

            removeEmptyStates reducedAut

    removeEmptyStates aut
    |> GNBA.convertStatesToInt