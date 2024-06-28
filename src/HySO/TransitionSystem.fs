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

module HySO.TransitionSystem

open System.Collections.Generic

/// A transition systems consists of a set of initial states, a set of APs
/// and a step function that maps each state to a set of successors and the evaluation of the APs.
/// Successors and AP-Evaluation are saved in the same Dictionary to save space.
type TransitionSystem<'T, 'L when 'T : comparison and 'L : comparison> =
    {
        InitialStates : HashSet<'T>
        APs : list<'L>
        Step : Dictionary<'T, HashSet<'T> * list<bool>>
    }

    /// Check if this system is consistent, i.e., all states are contained in step and the length of the AP eval matches
    member this.IsConsistent() =
        (this.InitialStates |> Seq.forall (fun x -> this.Step.ContainsKey x))
        && (this.Step.Values
            |> Seq.forall (fun (x, y) ->
                x |> Seq.forall (fun z -> this.Step.ContainsKey z)
                && List.length y = List.length this.APs
            ))

module Parser =
    open FParsec

    let private apsatParser =
        let trueParser = charReturn 't' true
        let falseParser = charReturn 'f' false

        skipChar '[' >>. spaces >>. many ((trueParser <|> falseParser) .>> spaces)
        .>> spaces
        .>> skipChar ']'

    let private stateParser =
        pstring "State:"
        >>. pipe3
            (spaces >>. pint32)
            (spaces >>. apsatParser)
            (spaces >>. many (pint32 .>> spaces))
            (fun id ap sucs -> (id, (new HashSet<_>(sucs), ap)))

    let private bodyParser =
        spaces >>. many (stateParser .>> spaces)
        |>> (fun x ->
            let d = new Dictionary<_, _>()
            x |> Seq.iter (fun (k, v) -> d.Add(k, v))
            d
        )

    let private tsParser =
        pipe3
            (spaces
             >>. skipString "aps"
             >>. spaces
             >>. many1 (Util.ParserUtil.escapedStringParser .>> spaces))
            (spaces >>. skipString "init" >>. spaces >>. many1 (pint32 .>> spaces))
            (spaces >>. skipString "--BODY--" >>. bodyParser)
            (fun aps init st ->
                {
                    TransitionSystem.InitialStates = new HashSet<_>(init)
                    APs = aps
                    Step = st
                }
            )

    /// Given a string s, parse s into a transition system
    /// If parsing fails, returns the message returned by FParsec
    let parseTS (s : string) =
        let full = tsParser .>> spaces .>> eof
        let res = run full s

        match res with
        | Success(res, _, _) -> Result.Ok res
        | Failure(err, _, _) -> Result.Error("Transition System could not be parsed: " + err)
