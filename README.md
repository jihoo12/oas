## OCaml x86-64 Instruction Assembler
A lightweight, functional assembler written in OCaml. This engine translates a subset of the x86-64 instruction set into raw machine code bytes, handling register encoding, REX prefixes, ModR/M, SIB bytes, and label resolution.
<br>
## Features
- x86-64 Support: Implements 64-bit operand sizes and extended registers (R8–R15).

- Two-Pass Assembly: Automatically calculates jump offsets and call targets by scanning labels first.

- Complex Addressing: Supports the ModR/M and SIB (Scale-Index-Base) encoding for memory access.

- Immediate Optimization: Dynamically chooses between 8-bit (imm8) and 32-bit (imm32) encodings for arithmetic operations to save space.

## Instruction Set Support
The assembler currently supports the following instructions:
- Data Movement: MOV, PUSH, POP

- Arithmetic: ADD, SUB, MUL, DIV

- Logic: AND, OR, XOR, SHL, SHR

- Control Flow: CMP, JE (Jump If Equal), JNE (Jump If Not Equal), JMP, CALL, RET

- System: SYSCALL

## Architecture Overview

1. Type Definitions
<br>
The system uses strongly typed variants for registers, scales, operands, and instructions, ensuring that only valid assembly structures can be constructed.

2. Operand Encoding
- Registers: Encoded using reg_info which maps OCaml variants to hardware register codes and REX bit extensions.

- Memory Access: The encode_mem_access function handles complex logic like:

    - Base and Index register presence.

    - Displacement (0, 8-bit, or 32-bit).

    - The special case of RSP and R12 requiring SIB bytes.

3. Assembly Process
The assemble function performs two passes over the instruction list:
    - Pass 1: Calculates the memory offset for every instruction and maps Label names to specific addresses.

    - Pass 2: Generates the final byte stream, calculating relative offsets for jumps (JMP, JE, JNE) and calls based on the label map.

## Usage Example
```OCaml
(* Define a simple program: RAX = 10; RAX += 20; RET *)
let program = [
  Mov (Reg RAX, Imm64 10L);
  Add (Reg RAX, Imm64 20L);
  Ret
];;

(* Assemble to bytes *)
let machine_code = assemble program;;
```