(* 1. 타입 정의 *)
type reg = RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15;;
type scale = S1 | S2 | S4 | S8;;

type operand =
  | Reg of reg
  | Imm64 of int64
  | Mem of { base: reg option; index: (reg * scale) option; disp: int32 };;

type instr =
  | Mov of operand * operand
  | Add of operand * operand
  | Sub of operand * operand
  | Mul of operand
  | Div of operand
  | And of operand * operand
  | Or of operand * operand
  | Xor of operand * operand
  | Push of operand
  | Pop of operand
  | Call of string
  | CallReg of reg
  | Shl of operand * operand
  | Shr of operand * operand
  | Cmp of operand * operand
  | Je of string
  | Jne of string
  | Label of string
  | Jmp of string
  | Syscall | Ret;;

(* 2. 유틸리티 함수 *)
let reg_info = function
  | RAX -> (0, 0) | RCX -> (1, 0) | RDX -> (2, 0) | RBX -> (3, 0)
  | RSP -> (4, 0) | RBP -> (5, 0) | RSI -> (6, 0) | RDI -> (7, 0)
  | R8  -> (0, 1) | R9  -> (1, 1) | R10 -> (2, 1) | R11 -> (3, 1)
  | R12 -> (4, 1) | R13 -> (5, 1) | R14 -> (6, 1) | R15 -> (7, 1);;

let scale_to_bits = function S1 -> 0 | S2 -> 1 | S4 -> 2 | S8 -> 3;;

let int32_to_bytes n =
  let b i = Int32.to_int (Int32.shift_right n (i * 8)) land 0xFF in
  [b 0; b 1; b 2; b 3];;

let int64_to_bytes n =
  let rec loop i acc =
    if i = 8 then List.rev acc
    else
      let byte = Int64.to_int (Int64.logand (Int64.shift_right n (i * 8)) 0xFFL) in
      loop (i + 1) (byte :: acc)
  in loop 0 [];;
(* 즉시값이 8비트(signed) 범위인지 확인 *)
let is_int8 v =
  let v32 = Int64.to_int32 v in
  v32 >= -128l && v32 <= 127l

(* 8비트면 0x83, 아니면 0x81을 사용하여 인코딩하는 공통 로직 *)
let encode_imm_op d_c d_b op_type v =
  let rex = 0x48 lor d_b in
  if is_int8 v then
    (* 0x83 사용: [REX, 0x83, ModRM(with op_type), imm8] *)
    [rex; 0x83; op_type lor d_c; Int64.to_int v land 0xFF]
  else
    (* 0x81 사용: [REX, 0x81, ModRM(with op_type), imm32] *)
    [rex; 0x81; op_type lor d_c] @ int32_to_bytes (Int64.to_int32 v)
(* 3. 메모리 주소 인코딩 (ModR/M & SIB) *)
(* 인라인 레코드 탈출 문제를 피하기 위해 필드를 개별 인자로 받음 *)
let encode_mem_access base index disp reg_val_code =
  let (base_code, b_ext, index_code, i_ext, use_sib) = 
    match (base, index) with
    | (Some b, Some (i, _)) -> 
        let (bc, be) = reg_info b in let (ic, ie) = reg_info i in (bc, be, ic, ie, true)
    | (Some b, None) when b = RSP || b = R12 ->
        let (bc, be) = reg_info b in (bc, be, 0b100, 0, true)
    | (Some b, None) ->
        let (bc, be) = reg_info b in (bc, be, 0, 0, false)
    | (None, Some (i, _)) ->
        let (ic, ie) = reg_info i in (0b101, 0, ic, ie, true)
    | (None, None) -> failwith "Absolute address not implemented"
  in
  let (mod_bits, disp_bytes) = 
    if disp = 0l && (base <> Some RBP && base <> Some R13) then (0b00, [])
    else if disp >= -128l && disp <= 127l then (0b01, [Int32.to_int disp land 0xFF])
    else (0b10, int32_to_bytes disp)
  in
  let modrm = (mod_bits lsl 6) lor (reg_val_code lsl 3) lor (if use_sib then 0x04 else base_code) in
  let sib = if use_sib then 
              let s_bits = match index with Some(_, s) -> scale_to_bits s | _ -> 0 in
              Some ((s_bits lsl 6) lor (index_code lsl 3) lor base_code)
            else None in
  (modrm, sib, disp_bytes, b_ext, i_ext);;

(* 4. 명령어 개별 조립 *)
module StringMap = Map.Make(String);;

let assemble_instr labels offset = function
  | Mov (Reg d, Reg s) ->
      let (d_c, d_b) = reg_info d in let (s_c, s_r) = reg_info s in
      [0x48 lor (s_r lsl 2) lor d_b; 0x89; 0xC0 lor (s_c lsl 3) lor d_c]
  | Mov (Reg d, Imm64 v) ->
      let (d_c, d_b) = reg_info d in
      [0x48 lor d_b; 0xB8 + d_c] @ int64_to_bytes v
  | Mov (Reg d, Mem {base; index; disp}) ->
      let (d_c, d_r) = reg_info d in
      let (modrm, sib, disp_b, b_b, i_x) = encode_mem_access base index disp d_c in
      let rex = 0x48 lor (d_r lsl 2) lor (i_x lsl 1) lor b_b in
      [rex; 0x8B; modrm] @ (match sib with Some s -> [s] | _ -> []) @ disp_b
  | Mov (Mem {base; index; disp}, Reg s) ->
      let (s_c, s_r) = reg_info s in
      let (modrm, sib, disp_b, b_b, i_x) = encode_mem_access base index disp s_c in
      let rex = 0x48 lor (s_r lsl 2) lor (i_x lsl 1) lor b_b in
      [rex; 0x89; modrm] @ (match sib with Some s -> [s] | _ -> []) @ disp_b
  | Add (Reg d, Reg s) ->
      let (d_c, d_b) = reg_info d in let (s_c, s_r) = reg_info s in
      [0x48 lor (s_r lsl 2) lor d_b; 0x01; 0xC0 lor (s_c lsl 3) lor d_c]
      
  | Add (Reg d, Mem {base; index; disp}) ->
      let (d_c, d_r) = reg_info d in
      let (modrm, sib, disp_b, b_b, i_x) = encode_mem_access base index disp d_c in
      let rex = 0x48 lor (d_r lsl 2) lor (i_x lsl 1) lor b_b in
      [rex; 0x03; modrm] @ (match sib with Some s -> [s] | _ -> []) @ disp_b
  | Add (Reg d, Imm64 v) ->
      let (d_c, d_b) = reg_info d in
      encode_imm_op d_c d_b 0xC0 v
  | Sub (Reg d, Reg s) ->
      let (d_c, d_b) = reg_info d in let (s_c, s_r) = reg_info s in
      [0x48 lor (s_r lsl 2) lor d_b; 0x29; 0xC0 lor (s_c lsl 3) lor d_c]

  | Sub (Reg d, Mem {base; index; disp}) ->
      let (d_c, d_r) = reg_info d in
      let (modrm, sib, disp_b, b_b, i_x) = encode_mem_access base index disp d_c in
      let rex = 0x48 lor (d_r lsl 2) lor (i_x lsl 1) lor b_b in
      [rex; 0x2B; modrm] @ (match sib with Some s -> [s] | _ -> []) @ disp_b
  | Sub (Reg d, Imm64 v) ->
      let (d_c, d_b) = reg_info d in
      encode_imm_op d_c d_b 0xE8 v
  | Mul (Reg r) ->
      let (r_c, r_b) = reg_info r in
      (* 0xF7 /4: MUL r/m64 *)
      [0x48 lor r_b; 0xF7; 0xE0 lor r_c]

  | Mul (Mem {base; index; disp}) ->
      let (modrm, sib, disp_b, b_b, i_x) = encode_mem_access base index disp 4 in (* reg=4 *)
      let rex = 0x48 lor (i_x lsl 1) lor b_b in
      [rex; 0xF7; modrm] @ (match sib with Some s -> [s] | _ -> []) @ disp_b

  | Div (Reg r) ->
      let (r_c, r_b) = reg_info r in
      (* 0xF7 /6: DIV r/m64 *)
      [0x48 lor r_b; 0xF7; 0xF0 lor r_c]

  | Div (Mem {base; index; disp}) ->
      let (modrm, sib, disp_b, b_b, i_x) = encode_mem_access base index disp 6 in (* reg=6 *)
      let rex = 0x48 lor (i_x lsl 1) lor b_b in
      [rex; 0xF7; modrm] @ (match sib with Some s -> [s] | _ -> []) @ disp_b
  | And (Reg d, Reg s) ->
      let (d_c, d_b) = reg_info d in let (s_c, s_r) = reg_info s in
      [0x48 lor (s_r lsl 2) lor d_b; 0x21; 0xC0 lor (s_c lsl 3) lor d_c]
  | And (Reg d, Imm64 v) ->
      let (d_c, d_b) = reg_info d in
      encode_imm_op d_c d_b 0xE0 v
  (* OR 연산 *)
  | Or (Reg d, Reg s) ->
      let (d_c, d_b) = reg_info d in let (s_c, s_r) = reg_info s in
      [0x48 lor (s_r lsl 2) lor d_b; 0x09; 0xC0 lor (s_c lsl 3) lor d_c]
  | Or (Reg d, Imm64 v) ->
      let (d_c, d_b) = reg_info d in
      encode_imm_op d_c d_b 0xC8 v 
  | Xor (Reg d, Reg s) ->
      let (d_c, d_b) = reg_info d in let (s_c, s_r) = reg_info s in
      (* 0x31: XOR r/m64, r64 *)
      [0x48 lor (s_r lsl 2) lor d_b; 0x31; 0xC0 lor (s_c lsl 3) lor d_c]
      
  | Xor (Reg d, Imm64 v) ->
      let (d_c, d_b) = reg_info d in
      encode_imm_op d_c d_b 0xF0 v
  | Push (Reg r) ->
      let (r_c, r_b) = reg_info r in
      if r_b = 0 then [0x50 + r_c] (* RAX~RDI: 50~57 *)
      else [0x41; 0x50 + r_c]     (* R8~R15: REX.B + 50~57 *)

  (* PUSH 메모리 *)
  | Push (Mem {base; index; disp}) ->
      let (modrm, sib, disp_b, b_b, i_x) = encode_mem_access base index disp 6 in (* /6 *)
      let rex = (if b_b = 1 || i_x = 1 then [0x40 lor (i_x lsl 1) lor b_b] else []) in
      rex @ [0xFF; modrm] @ (match sib with Some s -> [s] | _ -> []) @ disp_b

  (* POP 레지스터 *)
  | Pop (Reg r) ->
      let (r_c, r_b) = reg_info r in
      if r_b = 0 then [0x58 + r_c] (* RAX~RDI: 58~5F *)
      else [0x41; 0x58 + r_c]     (* R8~R15: REX.B + 58~5F *)

  (* POP 메모리 *)
  | Pop (Mem {base; index; disp}) ->
      let (modrm, sib, disp_b, b_b, i_x) = encode_mem_access base index disp 0 in (* /0 *)
      let rex = (if b_b = 1 || i_x = 1 then [0x40 lor (i_x lsl 1) lor b_b] else []) in
      rex @ [0x8F; modrm] @ (match sib with Some s -> [s] | _ -> []) @ disp_b
  | Call target ->
      (match StringMap.find_opt target labels with
       | Some addr -> 
           (* JMP와 마찬가지로 (타겟 주소 - 다음 명령어 주소) 계산 *)
           let rel = Int32.of_int (addr - (offset + 5)) in 
           [0xE8] @ int32_to_bytes rel
       | None -> [0xE8; 0; 0; 0; 0])

  (* CALL 레지스터 (간접 호출) *)
  | CallReg r ->
      let (r_c, r_b) = reg_info r in
      (* 0xFF /2: CALL r/m64 *)
      let rex = (if r_b = 1 then [0x41] else []) in
      rex @ [0xFF; 0xD0 lor r_c]
  (* SHL Reg, Imm8 *)
  | Shl (Reg d, Imm64 v) ->
      let (d_c, d_b) = reg_info d in
      let rex = 0x48 lor d_b in
      (* 0xC1 /4: SHL r/m64, imm8 *)
      [rex; 0xC1; 0xE0 lor d_c; Int64.to_int v land 0xFF]

  (* SHR Reg, Imm8 *)
  | Shr (Reg d, Imm64 v) ->
      let (d_c, d_b) = reg_info d in
      let rex = 0x48 lor d_b in
      (* 0xC1 /5: SHR r/m64, imm8 *)
      [rex; 0xC1; 0xE8 lor d_c; Int64.to_int v land 0xFF]
  | Cmp (Reg d, Reg s) ->
      let (d_c, d_b) = reg_info d in let (s_c, s_r) = reg_info s in
      [0x48 lor (s_r lsl 2) lor d_b; 0x39; 0xC0 lor (s_c lsl 3) lor d_c]

  (* CMP 즉시값 (최적화 적용) *)
  | Cmp (Reg d, Imm64 v) ->
      let (d_c, d_b) = reg_info d in
      encode_imm_op d_c d_b 0xF8 v  (* /7: CMP r/m64, imm *)

  (* 조건부 점프 (Near relative) *)
  | Je target ->
      (match StringMap.find_opt target labels with
       | Some addr -> 
           let rel = Int32.of_int (addr - (offset + 6)) in 
           [0x0F; 0x84] @ int32_to_bytes rel
       | None -> [0x0F; 0x84; 0; 0; 0; 0])

  | Jne target ->
      (match StringMap.find_opt target labels with
       | Some addr -> 
           let rel = Int32.of_int (addr - (offset + 6)) in 
           [0x0F; 0x85] @ int32_to_bytes rel
       | None -> [0x0F; 0x85; 0; 0; 0; 0])
  | Label _ -> []
  | Jmp target ->
      (match StringMap.find_opt target labels with
       | Some addr -> 
           let rel = Int32.of_int (addr - (offset + 5)) in 
           [0xE9] @ int32_to_bytes rel
       | None -> [0xE9; 0; 0; 0; 0])
  | Syscall -> [0x0F; 0x05]
  | Ret -> [0xC3]
  | _ -> failwith "Other instructions not yet implemented";;

(* 5. 2-Pass 어셈블 프로세스 *)
let assemble program =
  let rec pass1 off acc = function
    | [] -> acc
    | Label n :: t -> pass1 off (StringMap.add n off acc) t
    | i :: t -> pass1 (off + List.length (assemble_instr StringMap.empty off i)) acc t
  in
  let labels = pass1 0 StringMap.empty program in
  let rec pass2 off = function
    | [] -> []
    | Label _ :: t -> pass2 off t
    | i :: t -> 
        let b = assemble_instr labels off i in
        b @ pass2 (off + List.length b) t
  in
  pass2 0 program;;
