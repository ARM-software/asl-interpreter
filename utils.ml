(****************************************************************
 * Generic utility functions
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

(** Generic utility functions *)

(****************************************************************
 * Pretty-printer related
 ****************************************************************)

let to_string (d: PPrintEngine.document): string =
    let buf = Buffer.create 100 in
    PPrintEngine.ToBuffer.compact buf d;
    Buffer.contents buf


(****************************************************************
 * List related
 ****************************************************************)

let nub (xs: 'a list): 'a list =
    let rec nub_aux seen xs = (match xs with
        | [] -> seen
        | (y::ys) -> if List.mem y seen then nub_aux seen ys else nub_aux (y::seen) ys
    ) in
    nub_aux [] xs

let zip_list (xs: 'a list) (ys: 'b list): ('a * 'b) list =
    List.map2 (fun x y -> (x, y)) xs ys

let zipWithIndex (f: 'a -> int -> 'b) (xs: 'a list): 'b list =
    let rec aux i xs = (match xs with
        | [] -> []
        | (y::ys) -> f y i :: aux (i+1) ys
    ) in
    aux 0 xs

(****************************************************************
 * Option related
 ****************************************************************)

let isNone (ox : 'a option): bool =
    (match ox with
    | None   -> true
    | Some _ -> false
    )

let map_option (f: 'a -> 'b) (ox: 'a option): 'b option =
    (match ox with
    | None -> None
    | Some x -> Some (f x)
    )

let get_option (ox: 'a option): 'a =
    (match ox with
    | None -> raise Not_found
    | Some x -> x
    )

let from_option (ox: 'a option) (d: unit -> 'a): 'a =
    (match ox with
    | None -> d()
    | Some x -> x
    )

let bind_option (ox: 'a option) (f: 'a -> 'b option): 'b option =
    (match ox with
    | None   -> None
    | Some x -> f x
    )

let orelse_option (ox: 'a option) (f: unit -> 'a option): 'a option =
    (match ox with
    | None -> f()
    | Some x -> ox
    )

let rec concat_option (oss: (('a list) option) list): ('a list) option =
    (match oss with
    | [] -> Some []
    | None::_ -> None
    | (Some xs)::xss -> map_option (List.append xs) (concat_option xss)
    )

(* extract all non-None elements from a list *)
let flatten_option (os: ('a option) list): 'a list =
    let rec aux r os = (match os with
    | [] -> List.rev r
    | Some o :: os' -> aux (o::r) os'
    | None   :: os' -> aux r      os'
    )
    in
    aux [] os

(* extract all non-None elements from a list *)
let flatmap_option (f: 'a -> 'b option) (xs: 'a list): 'b list =
    let rec aux r xs = (match xs with
    | [] -> List.rev r
    | x :: xs' ->
            (match f x with
            | Some b -> aux (b::r) xs'
            | None   -> aux r      xs'
            )
    )
    in
    aux [] xs

(* todo: give this a better name *)
let flatten_map_option (f: 'a -> 'b option) (xs: 'a list): 'b list option =
    let rec aux r xs = (match xs with
    | [] -> Some (List.rev r)
    | x :: xs' ->
            (match f x with
            | Some b -> aux (b::r) xs'
            | None   -> None
            )
    )
    in
    aux [] xs

(* find first non-None result from function 'f' on list 'xs' *)
let rec first_option (f: 'a -> 'b option) (xs: 'a list): 'b option =
    (match xs with
    | [] -> None
    | x :: xs' ->
            (match f x with
            | Some b -> Some b
            | None   -> first_option f xs'
            )
    )


(****************************************************************
 * String related
 ****************************************************************)

(** Test whether 'x' starts with (is prefixed by) 'y' *)
let startswith (x: string) (y: string): bool =
    let lx = String.length x in
    let ly = String.length y in
    if lx < ly then begin
        false
    end else begin
        let head = String.sub x 0 ly in
        String.equal head y
    end

(** Test whether 'x' ends with (is suffixed by) 'y' *)
let endswith (x: string) (y: string): bool =
    let lx = String.length x in
    let ly = String.length y in
    if lx < ly then begin
        false
    end else begin
        let tail = String.sub x (lx - ly) ly in
        String.equal tail y
    end

(** Drop first n characters from string *)
let stringDrop (n: int) (s: string): string =
    let l = String.length s in
    if n > l then begin
        ""
    end else begin
        String.sub s n (l-n)
    end

(****************************************************************
 * End
 ****************************************************************)
