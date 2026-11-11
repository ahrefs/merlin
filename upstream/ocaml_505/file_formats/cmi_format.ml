(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Fabrice Le Fessant, INRIA Saclay                     *)
(*                                                                        *)
(*   Copyright 2012 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Misc

type pers_flags =
  | Rectypes
  | Alerts of alerts
  | Opaque

type error =
  | Not_an_interface of filepath
  | Wrong_version_interface of filepath * string
  | Corrupted_interface of filepath

exception Error of error

(* A .cmi file has the following layout:

   - magic number
   - length of the data block, as a 64-bit integer
   - data block
   - header: unit name and offset of the top-level signature in the data block
   - crcs
   - flags

   The data block contains marshalled pieces of the signature: each
   signature (the top-level one and the ones of nested modules and module
   types) and the type of each value are marshalled separately, and refer to
   their nested pieces by their offset in the block. When reading a .cmi
   file, the whole data block is read into memory, but a piece is only
   unmarshalled when the corresponding part of the signature is needed. *)

open Types

type serialized_signature = serialized_item list

and serialized_item =
  | Ser_value of
      Ident.t * int * value_kind * Location.t * Parsetree.attributes * Uid.t
      * visibility
      (* the int is the offset of the value type *)
  | Ser_module of
      Ident.t * module_presence * serialized_module_decl * rec_status
      * visibility
  | Ser_modtype of Ident.t * serialized_modtype_decl * visibility
  | Ser_item of signature_item
      (* types, extension constructors, classes and class types *)

and serialized_module_decl =
  { smd_type: serialized_modtype;
    smd_attributes: Parsetree.attributes;
    smd_loc: Location.t;
    smd_uid: Uid.t }

and serialized_modtype =
  | SMty_ident of Path.t
  | SMty_signature of int (* offset of a [serialized_signature] *)
  | SMty_functor of serialized_functor_parameter * serialized_modtype
  | SMty_alias of Path.t

and serialized_functor_parameter =
  | SUnit
  | SNamed of Ident.t option * serialized_modtype

and serialized_modtype_decl =
  { smtd_type: serialized_modtype option;
    smtd_attributes: Parsetree.attributes;
    smtd_loc: Location.t;
    smtd_uid: Uid.t }

(* these type abbreviations are not exported;
   they are used to provide consistency across
   input_value and output_value usage. *)
type flags = pers_flags list
type header = modname * int

type 'sg cmi_infos_generic = {
    cmi_name : modname;
    cmi_sign : 'sg;
    cmi_crcs : crcs;
    cmi_flags : flags;
}

type cmi_infos = Types.signature cmi_infos_generic
type cmi_infos_lazy = Subst.Lazy.signature cmi_infos_generic

let serialize oc ~base sg =
  let marshal x =
    let pos = pos_out oc in
    Compression.output_value oc x;
    pos - base
  in
  let rec signature sg = marshal (List.map signature_item sg : serialized_signature)
  and signature_item = function
    | Sig_value (id, vd, vis) ->
        Ser_value (id, marshal (vd.val_type : type_expr), vd.val_kind,
                   vd.val_loc, vd.val_attributes, vd.val_uid, vis)
    | Sig_module (id, pres, md, rs, vis) ->
        Ser_module (id, pres, module_decl md, rs, vis)
    | Sig_modtype (id, mtd, vis) -> Ser_modtype (id, modtype_decl mtd, vis)
    | Sig_type _ | Sig_typext _ | Sig_class _ | Sig_class_type _ as item ->
        Ser_item item
  and module_decl md =
    { smd_type = modtype md.md_type;
      smd_attributes = md.md_attributes;
      smd_loc = md.md_loc;
      smd_uid = md.md_uid }
  and modtype_decl mtd =
    { smtd_type = Option.map modtype mtd.mtd_type;
      smtd_attributes = mtd.mtd_attributes;
      smtd_loc = mtd.mtd_loc;
      smtd_uid = mtd.mtd_uid }
  and modtype = function
    | Mty_ident p -> SMty_ident p
    | Mty_signature sg -> SMty_signature (signature sg)
    | Mty_functor (param, res) -> SMty_functor (functor_param param, modtype res)
    | Mty_alias p -> SMty_alias p
  and functor_param = function
    | Unit -> SUnit
    | Named (id, mty) -> SNamed (id, modtype mty)
  in
  signature sg

let deserialize data offset =
  let open Subst.Lazy in
  let unmarshal offset = Marshal.from_bytes data offset in
  let rec signature offset =
    of_deferred_signature_items
      (lazy (List.map signature_item (unmarshal offset : serialized_signature)))
  and signature_item = function
    | Ser_value (id, ty, kind, loc, attrs, uid, vis) ->
        let vdl_type =
          of_deferred_type_expr (lazy (unmarshal ty : type_expr))
        in
        SigL_value (id, { vdl_type; vdl_kind = kind; vdl_loc = loc;
                          vdl_attributes = attrs; vdl_uid = uid }, vis)
    | Ser_module (id, pres, md, rs, vis) ->
        SigL_module (id, pres, module_decl md, rs, vis)
    | Ser_modtype (id, mtd, vis) -> SigL_modtype (id, modtype_decl mtd, vis)
    | Ser_item item -> of_signature_item item
  and module_decl md =
    { mdl_type = modtype md.smd_type;
      mdl_attributes = md.smd_attributes;
      mdl_loc = md.smd_loc;
      mdl_uid = md.smd_uid }
  and modtype_decl mtd =
    { mtdl_type = Option.map modtype mtd.smtd_type;
      mtdl_attributes = mtd.smtd_attributes;
      mtdl_loc = mtd.smtd_loc;
      mtdl_uid = mtd.smtd_uid }
  and modtype = function
    | SMty_ident p -> MtyL_ident p
    | SMty_signature offset -> MtyL_signature (signature offset)
    | SMty_functor (param, res) ->
        MtyL_functor (functor_param param, modtype res)
    | SMty_alias p -> MtyL_alias p
  and functor_param = function
    | SUnit -> (Unit : functor_parameter)
    | SNamed (id, mty) -> Named (id, modtype mty)
  in
  signature offset

let input_cmi_lazy ic =
  let really_input_bytes n = Bytes.unsafe_of_string (really_input_string ic n) in
  let data_len = Int64.to_int (Bytes.get_int64_le (really_input_bytes 8) 0) in
  let data = really_input_bytes data_len in
  let (name, offset) = (input_value ic : header) in
  let crcs = (input_value ic : crcs) in
  let flags = (input_value ic : flags) in
  {
      cmi_name = name;
      cmi_sign = deserialize data offset;
      cmi_crcs = crcs;
      cmi_flags = flags;
    }

let force_cmi_infos cmi =
  { cmi with cmi_sign = Subst.Lazy.force_signature cmi.cmi_sign }

let read_cmi_lazy filename =
  let ic = open_in_bin filename in
  try
    let buffer =
      really_input_string ic (String.length Config.cmi_magic_number)
    in
    if buffer <> Config.cmi_magic_number then begin
      close_in ic;
      let pre_len = String.length Config.cmi_magic_number - 3 in
      if String.sub buffer 0 pre_len
          = String.sub Config.cmi_magic_number 0 pre_len then
      begin
        let msg =
          if buffer < Config.cmi_magic_number then "an older" else "a newer" in
        raise (Error (Wrong_version_interface (filename, msg)))
      end else begin
        raise(Error(Not_an_interface filename))
      end
    end;
    let cmi = input_cmi_lazy ic in
    close_in ic;
    cmi
  with End_of_file | Failure _ ->
      close_in ic;
      raise(Error(Corrupted_interface(filename)))
    | Error e ->
      close_in ic;
      raise (Error e)

let input_cmi ic = force_cmi_infos (input_cmi_lazy ic)

let read_cmi filename = force_cmi_infos (read_cmi_lazy filename)

let output_cmi filename oc cmi =
(* beware: the provided signature must have been substituted for saving *)
  output_string oc Config.cmi_magic_number;
  let output_int64 n =
    let buf = Bytes.create 8 in
    Bytes.set_int64_le buf 0 (Int64.of_int n);
    output_bytes oc buf
  in
  (* Reserve room for the length of the data block, write the block, then
     go back and write its length. *)
  let len_pos = pos_out oc in
  output_int64 0;
  let base = pos_out oc in
  let offset = serialize oc ~base cmi.cmi_sign in
  let header_pos = pos_out oc in
  seek_out oc len_pos;
  output_int64 (header_pos - base);
  seek_out oc header_pos;
  output_value oc ((cmi.cmi_name, offset) : header);
  flush oc;
  let crc = Digest.BLAKE128.file filename in
  let crcs = (cmi.cmi_name, Some crc) :: cmi.cmi_crcs in
  output_value oc (crcs : crcs);
  output_value oc (cmi.cmi_flags : flags);
  crc

(* Error report *)

open Format_doc

let report_error_doc ppf = function
  | Not_an_interface filename ->
      fprintf ppf "%a@ is not a compiled interface"
        Location.Doc.quoted_filename filename
  | Wrong_version_interface (filename, older_newer) ->
      fprintf ppf
        "%a@ is not a compiled interface for this version of OCaml.@.\
         It seems to be for %s version of OCaml."
        Location.Doc.quoted_filename filename older_newer
  | Corrupted_interface filename ->
      fprintf ppf "Corrupted compiled interface@ %a"
        Location.Doc.quoted_filename filename

let () =
  Location.register_error_of_exn
    (function
      | Error err -> Some (Location.error_of_printer_file report_error_doc err)
      | _ -> None
    )

let report_error = Format_doc.compat report_error_doc
