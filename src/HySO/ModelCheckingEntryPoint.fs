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

module HySO.ModelCheckingEntryPoint

open System.IO

open Util
open Configuration

let explictSystemVerification (config : Configuration) systemPaths propPath =
    let sw = System.Diagnostics.Stopwatch()
    sw.Start()

    let propertyContent =
        try
            File.ReadAllText propPath
        with _ ->
            raise <| HySOException $"Could not open/read file %s{propPath}"

    let tscontent =
        systemPaths
        |> List.map (fun x ->
            try
                File.ReadAllText x
            with _ ->
                raise <| HySOException $"Could not open/read file %s{x}"
        )

    config.Logger.LogN $"Read Input in: %i{sw.ElapsedMilliseconds}ms"

    sw.Restart()

    let property =
        match
            SecondOrderHyperLTL.Parser.parseSecondOrderHyperLTL Util.ParserUtil.escapedStringParser propertyContent
        with
        | Result.Ok x -> x
        | Result.Error err -> raise <| HySOException $"The formula could not be parsed: %s{err}"


    let tslist =
        tscontent
        |> List.map (fun x ->
            match TransitionSystem.Parser.parseTS x with
            | Result.Ok y -> y
            | Result.Error err -> raise <| HySOException $"The system could not be parsed: %s{err}"
        )

    config.Logger.LogN $"Parsed Input in: %i{sw.ElapsedMilliseconds}ms"

    tslist
    |> List.iteri (fun i x ->
        if x.IsConsistent() |> not then
            raise <| HySOException $"The %i{i}th transition system is inconsistent"
    )

    tslist, property

