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

module HySO.Util

open System.Collections.Generic

exception HySOException of string

/// Given a number n, computes all lists of booleans of length n
let rec computeBooleanPowerSet n =
    if n = 0 then
        Seq.singleton []
    else
        let r = computeBooleanPowerSet (n - 1)
        Seq.append (Seq.map (fun x -> true :: x) r) (Seq.map (fun x -> false :: x) r)

/// Compute the cartesian product of a list of sets
let rec cartesianProduct (LL : list<seq<'a>>) =
    match LL with
    | [] -> Seq.singleton []
    | L :: Ls ->
        seq {
            for x in L do
                for xs in cartesianProduct Ls -> x :: xs
        }

let dictToMap (d : Dictionary<'A, 'B>) =
    d |> Seq.map (fun x -> x.Key, x.Value) |> Map.ofSeq

let joinMaps (map1 : Map<'A, 'B>) (map2 : Map<'A, 'B>) =
    let l1 = Map.toList map1
    let l2 = Map.toList map2

    let m = l1 @ l2 |> Map.ofList

    if m.Count <> map1.Count + map2.Count then
        failwith "Could not merge maps"
    else
        m


/// Parser for variables used in HyperLTL specifications
module ParserUtil =
    open FParsec

    let escapedStringParser : Parser<string, unit> =
        let escapedCharParser : Parser<string, unit> =
            anyOf "\"\\/bfnrt"
            |>> fun x ->
                match x with
                | 'b' -> "\b"
                | 'f' -> "\u000C"
                | 'n' -> "\n"
                | 'r' -> "\r"
                | 't' -> "\t"
                | c -> string c

        between
            (pchar '"')
            (pchar '"')
            (stringsSepBy (manySatisfy (fun c -> c <> '"' && c <> '\\')) (pstring "\\" >>. escapedCharParser))

    let pipe6 a b c d e f fu =
        pipe5 (a .>>. b) c d e f (fun (a, b) c d e f -> fu a b c d e f)
