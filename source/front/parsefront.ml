(****************************************************************************
*Copyright 2008
*  Andrew Gacek, Steven Holte, Gopalan Nadathur, Xiaochu Qi, Zach Snow
****************************************************************************)
(****************************************************************************
* This file is part of Teyjus.
*
* Teyjus is free software: you can redistribute it and/or modify
* it under the terms of the GNU General Public License as published by
* the Free Software Foundation, either version 3 of the License, or
* (at your option) any later version.
*
* Teyjus is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
* GNU General Public License for more details.
*
* You should have received a copy of the GNU General Public License
* along with Teyjus.  If not, see <http://www.gnu.org/licenses/>.
****************************************************************************)
open Parseargs
open Absyn

let linearize = ref false
let explicify = ref false
                  
let addedTypes = ref []

(**********************************************************************
* Writing Functions
**********************************************************************)
let writeLine oc s = output_string oc (s ^ "\n")

let writeConst oc inSig isLocal c =
  let name = getConstantName c in
  let ty = string_of_skeleton (getConstantSkeletonValue c) in
  
  let hasFixity = (getConstantFixity c) <> NoFixity in
  let fixity = string_of_fixity (getConstantFixity c) in
  let prec = string_of_int (getConstantPrec c) in
  
  let local = "local" in
  let isUseonly = getConstantUseOnly c in
  let useonly = "useonly" in
  let isExportDef = getConstantExportDef c in
  let exportdef = "exportdef" in
  let isClosed = getConstantClosed c in
  let closed = "closed" in
  
  let aspects =
    [ (false, isLocal, local);
      (true, isUseonly, useonly);
      (true, isExportDef, exportdef);
      (false, isClosed, closed)] in

  writeLine oc ("type " ^ name ^ " " ^ ty ^ ".");
  if hasFixity then writeLine oc (fixity ^ " " ^ name ^ " " ^ prec ^ ".");
  List.iter
    (fun (inSig', isIt, it) ->
      if isIt && (inSig && inSig') then
        writeLine oc ("  " ^ it ^ " " ^ name ^ "."))
    aspects;
  ()

let writeKind oc isLocal k =
  let rec create e i = if i = 0 then [] else e :: (create e (i - 1)) in
  let name = getKindName k in
  let arity = getKindArity k in
  let ty = String.concat " -> " (create "type" (arity + 1)) in
  writeLine oc ("kind " ^ name ^ " " ^ ty ^ ".");
  if isLocal then writeLine oc ("localkind " ^ name ^ ".");
  ()

let writeModule m clauses newclauses oc =  
  let writeImp oc (ImportedModule(name,_)) =
    writeLine oc ("import " ^ name ^ ".")
  in
  let writeAcc oc (AccumulatedModule(name,_)) =
    writeLine oc ("accumulate " ^ name ^ ".")
  in
  
  let writeClause oc lastHead t =
    let isConstant test t =
      match t with
          ConstantTerm(c, _, _) -> test c
        | _ -> false
    in
    let isUniversal v = match v with
        ImplicitVar(_) -> true
      | AnonymousImplicitVar(_) -> true
      | BoundVar(sym,_,_,_) ->
          let name = Symbol.name sym in
          name.[0] = '_' || name = (String.capitalize name)
    in
      
    let rec getActualClause t =
      match t with
          ApplicationTerm(
            FirstOrderApplication(h,[AbstractionTerm(_) as abs],_),
            _)
            when isConstant Pervasive.isallConstant h
            ->  let vs = getTermAllAbstractionVars abs in
                if List.for_all isUniversal vs then
                  getActualClause (getTermAbstractionBody abs)
                else
                  t
        | _ ->  t
    in
    
    let reverse t =
      match t with
          ApplicationTerm(FirstOrderApplication(h, [l;r], i), p)
            when isConstant Pervasive.isimplConstant h
            ->  ApplicationTerm(
                  FirstOrderApplication(
                    ConstantTerm(Pervasive.colondashConstant, [], p),
                    [r;l],
                    i),
                  p)
        | _ ->  t
    in
    let getHead t =
      let get t =
        let head = getTermApplicationHead t in
        if isTermConstant head then
          let name = getConstantPrintName (getTermConstant head) in
          Some (name)
        else
          None
      in
      match t with
          ApplicationTerm(FirstOrderApplication(h, [l;_], _), _)
            when isConstant Pervasive.iscolondashConstant h
            -> get l
        | _ -> get t
    in
    let stringOfType ty = 
      (* the string_of_type functionfrom absyn.ml is here sligthly modified.
       * I am not sure if this could be merged in absyn.ml so keep it here *)
      let aux str needsParens ty bindings = 
        let parens s =
          if needsParens then
            "(" ^ s ^ ")"
          else
            s
        in
        let stringOfVar  = 
          let character i =
            if i>= 26 then
              (string_of_int i)
            else
              (String.make 1 (Char.chr ((Char.code 'A') + i)))
          in
            (try
               let i = List.assq t !bindings in
                 character i
             with
                 Not_found ->
                   let i = List.length !bindings in
                   let _ = bindings := (t, i)::!bindings in
                     character i) 
        in
        let ty' = dereferenceType ty in
          match ty' with
            | TypeVarType(_) -> stringOfVar 
            | ApplicationType(kind, tlist) ->
                if (List.length tlist) > 0 then
                  let args = String.concat " " (List.map (fun x -> str true x bindings) tlist) in
                  let s = (string_of_kind kind) ^ " " ^ args in
                    parens s
                    else
                      string_of_kind kind

            | _ -> string_of_type ty
      in
        aux false ty (ref [])
    in


    let rec renameAndWriteGeneratedSymbols t =
      match t with
        | ConstantTerm(
              Constant(sym, fix, prec, expdef, use, nodefs, closed, tpres, red, 
                     skel, tenvSize, skelNeed, need, cinfo, ct, index, p) as const, 
              atypList,
              constPos)  -> 
              (* Write missing type *)
              if not (List.mem const (getModuleGlobalConstantsList m) ||
                      Pervasive.isPerv const ||
                      List.mem const !addedTypes )
               then
                let name = getConstantPrintName const in
                let skValue = getConstantSkeletonValue const in
                let ty = getSkeletonType skValue in
                let tyStr = stringOfType ty (ref []) in
                  let newSym = 
                    (* Prefix with g since anonymous constants start with a _
                     * which is not allowed by the grammar *)
                    ((addedTypes := const::!addedTypes ;
                      writeLine oc ("type " ^  "g" ^ name ^ " " ^ tyStr ^ "."));
                     Symbol.symbol ("g" ^ name))
                in
                 ConstantTerm(
                   Constant(newSym, fix, prec, expdef, use, nodefs, closed, tpres, red, 
                            skel, tenvSize, skelNeed, need, cinfo, ct, index, p), 
                   atypList, constPos)
              else
                   t
        | ApplicationTerm(FirstOrderApplication(head, args, nbArgs), pos) ->
            let head' = renameAndWriteGeneratedSymbols head in
            let args' = List.map renameAndWriteGeneratedSymbols args in
              ApplicationTerm(FirstOrderApplication(head', args', nbArgs), pos) 
        | _ -> t
    in

(*    let writeTypeNewClauses t = *)
(*      Printf.printf "term = %s\n" (string_of_term t);*)
(*      match t with*)
(*        | ApplicationTerm(FirstOrderApplication(h, [_;r], _), _) when *)
(*            isConstant Pervasive.isimplConstant h &&*)
(*            isTermConstant r -> *)
(*            let const = getTermConstant r in*)
(*              if not (List.mem const (getModuleGlobalConstantsList m) ||*)
(*                      List.mem const !addedTypes) then*)
(*                  let constName = getConstantPrintName const in*)
(*                    (if String.sub constName 0 1 = "_" then*)
(*                      (addedTypes := const::!addedTypes ;*)
(*                       writeLine oc ("type " ^  "g" ^ constName ^ " o."))*)
(*                    else*)
(*                      failwith "Unsupported generated symbol")*)
(*        | _ -> ()*)

(*    in*)

(*    writeTypeNewClauses  t;*)
    let t' = reverse (getActualClause t) in
    let t'' = renameAndWriteGeneratedSymbols t' in
    let head = getHead t'' in
    if Option.isNone head || (head <> lastHead) then 
      writeLine oc ""; writeLine oc (string_of_term t'' ^ "."); head
  in
  
  match m with
    | Module(name, implist, acclist, _, _, _, _, _, 
             lkinds, _, lconsts, _, _, _, ci) ->
        writeLine oc ("module " ^ name ^ ".");
        List.iter (writeImp oc)  implist;
        List.iter (writeAcc oc) acclist;
        writeLine oc "";
        List.iter (writeKind oc true) lkinds;
        writeLine oc "";
        List.iter (writeConst oc false true) lconsts;
        ignore (List.fold_left (writeClause oc) None (List.rev clauses));
        ignore (List.fold_left (writeClause oc) None (List.rev newclauses));
        ()
    | _ -> Errormsg.impossible Errormsg.none "Absyn.writeModule: invalid module"
    
let writeModuleSignature s oc =
  match s with
    | Module(name, _, _, _, _, _, _, gkinds, _, gconsts, _, _, _, _, _) ->
        writeLine oc ("sig " ^ name ^ ".");
        writeLine oc "";
        List.iter (writeKind oc false) (List.rev gkinds);
        writeLine oc "";
        List.iter (writeConst oc true false) (List.rev gconsts);
        ()
    | _ -> Errormsg.impossible Errormsg.none 
             "Absyn.writeModuleSignature: invalid signature"

(**********************************************************************
* Program
**********************************************************************)
let abortOnError () =
  if !Errormsg.anyErrors then
    exit 1

let compile basename outbasename =
  (* Parse the input module and signature and generate preabsyn. *)
  let modresult = Compile.compileModule basename in
  let _ = abortOnError () in
    
  let sigresult = Compile.compileSignature basename in
  let _ = abortOnError () in

  (* Construct an absyn module.  At this point only the module's *)
  (* constant, kind, and type abbrev information is valid.       *)
  let (absyn, _) = Translate.translate modresult sigresult in
  let _ = abortOnError () in


  (* Get the list of clauses and new clauses. *)
  let (absyn, clauses, newclauses, _) =
    Clauses.translateClauses modresult absyn
  in
  let _ = abortOnError () in

  let (clauses', newclauses', absyn') =
    if !explicify then
      let () = Errormsg.log Errormsg.none "explicifying..." in
      (List.map (fun x -> Explicify.explicify_term x false true) clauses,
      List.map (fun x-> Explicify.explicify_term x false true) newclauses,
      Explicify.add_constants absyn)
    else
     (clauses, newclauses, absyn)
  in
  let _ = abortOnError () in

  (*  Linearize heads if requested. *)
  let (clauses'', newclauses'') =
    if !linearize then
      let () = Errormsg.log Errormsg.none "linearizing..." in
      (List.map Clauses.linearizeClause clauses',
      List.map Clauses.linearizeClause newclauses')
    else
     (clauses', newclauses')
  in
  let _ = abortOnError () in

  let modout = Compile.openFile (outbasename ^ ".mod") open_out in
  let sigout = Compile.openFile (outbasename ^ ".sig") open_out in
  let absyn'' = Absyn.setModuleName absyn' outbasename in
  writeModule absyn'' clauses'' newclauses'' modout;
  writeModuleSignature absyn'' sigout;
  
  close_out modout;
  close_out sigout;
  
  exit 0
  
let outputName = ref ""

let specList = (dualArgs
  [("-o", "--output", Arg.Set_string outputName,
    " Specifies the name of the output module (default is input module name)") ;
   versionspec]) @
  ["--linearize", Arg.Set linearize, " linearize clause heads"] @
  ["--explicify", Arg.Set explicify, " explicify clauses"]

let usageMsg = 
  "Usage: tjparse [options] <module-file>\n" ^
  "options are:"

let _ =    
  Arg.parse (Arg.align specList) (setInputName ~filter:getModName) usageMsg ;
  ensureInputName () ;

  if !outputName = "" then
    outputName := !inputName;
  
  compile !inputName !outputName
