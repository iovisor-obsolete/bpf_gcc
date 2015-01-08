/* Definitions of target machine for GCC for BPF.
   Copyright (C) 2013-2015 PLUMgrid Inc

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

Under Section 7 of GPL version 3, you are granted additional
permissions described in the GCC Runtime Library Exception, version
3.1, as published by the Free Software Foundation.

You should have received a copy of the GNU General Public License and
a copy of the GCC Runtime Library Exception along with this program;
see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
<http://www.gnu.org/licenses/>.  */

#ifndef __BPF_H
#define __BPF_H

typedef enum __bpf_cc_opcode_type{
    CC_EQ,
    CC_NE,
    CC_GT,
    CC_GTU,
    CC_LT,
    CC_LTU,
    CC_GE,
    CC_GEU,
    CC_LE,
    CC_LEU,
    CC_REVERSE,
    CC_NORMAL
} bpf_cc_opcode_type;

/* Macros used in the machine description to test the flags.  */
#undef  TARGET_CPU_CPP_BUILTINS
#define TARGET_CPU_CPP_BUILTINS()		\
  do						\
    {						\
      builtin_define ("__BPF__");		\
    }						\
  while (0)


/* Define this if most significant bit is lowest numbered
   in instructions that operate on numbered bit-fields. */
#define BITS_BIG_ENDIAN 0

/* Define this if most significant byte of a word is the lowest numbered.  */
#define BYTES_BIG_ENDIAN 0

/* Define this if most significant word of a multiword number is the lowest
   numbered.  */
#define WORDS_BIG_ENDIAN 0

/* Width in bits of a "word", which is the contents of a machine register.
   Note that this is not necessarily the width of data type `int';
   if using 16-bit ints on a 68000, this would still be 32.
   But on a machine with 16-bit registers, this would be 16.  */
#define BITS_PER_WORD 64

/* Width of a word, in units (bytes).  */
#define UNITS_PER_WORD 8

#define SHORT_TYPE_SIZE		16
#define INT_TYPE_SIZE		32
#define LONG_TYPE_SIZE		64
#define LONG_LONG_TYPE_SIZE	64
#define FLOAT_TYPE_SIZE		32
#define DOUBLE_TYPE_SIZE	64
#define LONG_DOUBLE_TYPE_SIZE   128

#define WIDEST_HARDWARE_FP_SIZE 64

#define WCHAR_TYPE "long int"
#define WCHAR_TYPE_SIZE 32

#define WINT_TYPE "long int"
#define WINT_TYPE_SIZE BITS_PER_WORD

#define PTRDIFF_TYPE "int"
#define SIZE_TYPE "unsigned int"

/* Width in bits of a pointer. See also the macro `Pmode' defined below.  */
#define POINTER_SIZE 64

/* Allocation boundary (in *bits*) for storing arguments in argument list.  */
#define PARM_BOUNDARY 64

/* Largest alignment for stack parameters (if greater than PARM_BOUNDARY).  */
#define MAX_PARM_BOUNDARY 64

/* Allocation boundary (in *bits*) for the code of a function.  */
#define FUNCTION_BOUNDARY 128

/* Alignment of field after `int : 0' in a structure.  */
#define EMPTY_FIELD_BOUNDARY 32

/* Every structure's size must be a multiple of this.  */
#define STRUCTURE_SIZE_BOUNDARY 8

/* A bitfield declared as `int' forces `int' alignment for the struct.  */
#define PCC_BITFIELD_TYPE_MATTERS 1

/* No data type wants to be aligned rounder than this.  */
/* even int128 should be 64-bit aligned to avoid allocate_stack for them */
#define BIGGEST_ALIGNMENT 64

/* No structure field wants to be aligned rounder than this.  */
/*#define BIGGEST_FIELD_ALIGNMENT 64*/

#define FASTEST_ALIGNMENT 64

/*  Make strcpy of constants fast. */
#define CONSTANT_ALIGNMENT(CODE, TYPEALIGN) \
  ((TYPEALIGN) < 32 ? 32 : (TYPEALIGN))

/* Make arrays of chars word-aligned for the same reasons.  */
#define DATA_ALIGNMENT(TYPE, ALIGN)		\
  (TREE_CODE (TYPE) == ARRAY_TYPE		\
   && TYPE_MODE (TREE_TYPE (TYPE)) == QImode	\
   && (ALIGN) < BITS_PER_WORD ? BITS_PER_WORD : (ALIGN))

/* Set this nonzero if move instructions will actually fail to work
   when given unaligned data.  */
#define STRICT_ALIGNMENT 1

/* Let's keep the stack somewhat aligned.  */
#define STACK_BOUNDARY 64

/* Define this macro if it is advisable to hold scalars in registers
   in a wider mode than that declared by the program.  In such cases,
   the value is constrained to be within the bounds of the declared
   type, but kept valid in the wider mode.  The signedness of the
   extension may differ from that of the type.
*/
#define PROMOTE_MODE(MODE, UNSIGNEDP, TYPE)	\
  if (GET_MODE_CLASS (MODE) == MODE_INT		\
      && GET_MODE_SIZE (MODE) < 8)		\
    {						\
      MODE = DImode;			\
    }


/* Standard register usage.  */

/* Number of actual hardware registers.
   The hardware registers are assigned numbers for the compiler
   from 0 to just below FIRST_PSEUDO_REGISTER.
   All registers that the compiler knows about must be given numbers,
   even those that are not normally considered general registers.  */
#define FIRST_PSEUDO_REGISTER 32

/* 1 for registers that have pervasive standard uses
   and are not available for the register allocator. */
#define FIXED_REGISTERS \
{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, \
 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1}


/* 1 for registers not available across function calls.
   These must include the FIXED_REGISTERS and also any
   registers that can be used without being saved.
   The latter must include the registers where values are returned
   and the register where structure-value addresses are passed.
   Aside from that, you can include as many other registers as you like.  */
#define CALL_USED_REGISTERS \
{1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, \
 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1}

/* Return number of consecutive hard regs needed starting at reg REGNO
   to hold something of mode MODE.
   This is ordinarily the length in words of a value of mode MODE
   but can be less for certain modes in special long registers. */
#define HARD_REGNO_NREGS(REGNO, MODE)   \
        ((GET_MODE_SIZE (MODE) + UNITS_PER_WORD - 1) / UNITS_PER_WORD)

#define HARD_REGNO_MODE_OK(REGNO, MODE) \
  ( (MODE) == SImode || (MODE) == DImode || (MODE) == HImode || (MODE) == QImode || (MODE) == TImode )

/* Value is 1 if it is a good idea to tie two pseudo registers
   when one has mode MODE1 and one has mode MODE2.
   If HARD_REGNO_MODE_OK could produce different values for MODE1 and MODE2,
   for any hard reg, then this must be 0 for correct output.  */

#define MODES_TIEABLE_P(MODE1, MODE2) \
  ((MODE1) == (MODE2)						\
   || (GET_MODE_CLASS (MODE1) == GET_MODE_CLASS (MODE2)))

/* Specify the registers used for certain standard purposes.
   The values of these macros are register numbers.  */

/* Register to use for pushing function arguments.  */
#define STACK_POINTER_REGNUM 31

/* Base register for access to local variables of the function.  */
#define FRAME_POINTER_REGNUM 30

#define ACCUMULATE_OUTGOING_ARGS 1

/* If defined, a C expression whose value is nonzero when we want to use PUSH
   instructions to pass outgoing arguments.  */
#define PUSH_ARGS 0

/* We want the stack and args grow in opposite directions, even if
   PUSH_ARGS is 0.  */
#define PUSH_ARGS_REVERSED 1

/* Base register for access to arguments of the function.  */
#define ARG_POINTER_REGNUM 29

/* Register in which static-chain is passed to a function.  */
#define STATIC_CHAIN_REGNUM 28

/* Define the classes of registers for register constraints in the
   machine description.  Also define ranges of constants.

   One of the classes must always be named ALL_REGS and include all hard regs.
   If there is more than one class, another class must be named NO_REGS
   and contain no registers.

   The name GENERAL_REGS must be the name of a class (or an alias for
   another name such as ALL_REGS).  This is the class of registers
   that is allowed by "g" or "r" in a register constraint.
   Also, registers outside this class are allocated only when
   instructions express preferences for them.

   The classes must be numbered in nondecreasing order; that is,
   a larger-numbered class must never be contained completely
   in a smaller-numbered class.

   For any two classes, it is very desirable that there be another
   class that represents their union.  */

enum reg_class { NO_REGS, GENERAL_REGS, ALL_REGS, LIM_REG_CLASSES};

#define N_REG_CLASSES (int) LIM_REG_CLASSES

/* Give names of register classes as strings for dump file.   */

#define REG_CLASS_NAMES \
 {"NO_REGS", "GENERAL_REGS", "ALL_REGS" }

/* Define which registers fit in which classes.
   This is an initializer for a vector of HARD_REG_SET
   of length N_REG_CLASSES.  */

#define REG_CLASS_CONTENTS \
 { {0},   /* NO_REGS */       \
   {~0}, /* GENERAL_REGS */  \
   {~0} /* ALL_REGS */ }

   /* The same information, inverted:
   Return the class number of the smallest class containing
   reg number REGNO.  This could be a conditional expression
   or could index an array.  */

#define REGNO_REG_CLASS(REGNO) GENERAL_REGS

/* This is the order in which to allocate registers normally.  */

#define REG_ALLOC_ORDER \
  { 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31}

/* The class value for index registers, and the one for base regs.  */

#define INDEX_REG_CLASS GENERAL_REGS
#define BASE_REG_CLASS GENERAL_REGS


/* Given an rtx X being reloaded into a reg required to be
   in class CLASS, return the class of reg to actually use.
   In general this is just CLASS; but on some machines
   in some cases it is preferable to use a more restrictive class.  */
#define PREFERRED_RELOAD_CLASS(X,CLASS)  (CLASS)

/* Return the maximum number of consecutive registers
   needed to represent mode MODE in a register of class CLASS.  */
#define CLASS_MAX_NREGS(CLASS, MODE) \
    ( ((GET_MODE_SIZE (MODE) + UNITS_PER_WORD - 1) / UNITS_PER_WORD))

/* Stack layout; function entry, exit and calling.  */

/* Define this if pushing a word on the stack
   makes the stack pointer a smaller address.  */
#define STACK_GROWS_DOWNWARD

/* Define this to nonzero if the nominal address of the stack frame
   is at the high-address end of the local variables;
   that is, each additional local variable allocated
   goes at a more negative offset in the frame.  */
#define FRAME_GROWS_DOWNWARD 1

/* Offset within stack frame to start allocating local variables at.
   If FRAME_GROWS_DOWNWARD, this is the offset to the END of the
   first local allocated.  Otherwise, it is the offset to the BEGINNING
   of the first local allocated.  */
#define STARTING_FRAME_OFFSET 0

/* Given an rtx for the address of a frame,
   return an rtx for the address of the word in the frame
   that holds the dynamic chain--the previous frame's address.  */
#define DYNAMIC_CHAIN_ADDRESS(frame) (frame)

/* If we generate an insn to push BYTES bytes,
   this says how many the stack pointer really advances by. */
#define PUSH_ROUNDING(BYTES) ((BYTES + 7) & ~7)

/* Offset of first parameter from the argument pointer register value. */
#define FIRST_PARM_OFFSET(FNDECL) 0

#define RETURN_IN_MEMORY(TYPE) \
  (TYPE_MODE (TYPE) == BLKmode || COMPLEX_MODE_P (TYPE_MODE (TYPE)) )

/* Define how to find the value returned by a function.
   VALTYPE is the data type of the value (as a tree).
   If the precise function being called is known, FUNC is its FUNCTION_DECL;
   otherwise, FUNC is 0.  */
#define FUNCTION_VALUE(VALTYPE, FUNC) bpf_function_value(VALTYPE, FUNC)

/* Define how to find the value returned by a library function
   assuming the value has mode MODE.  */
#define LIBCALL_VALUE(MODE)  \
  gen_rtx_REG ((MODE), 0)

/* 1 if N is a possible register number for a function value
   as seen by the caller.  */
#define FUNCTION_VALUE_REGNO_P(N) ((N) == 0 || (N) == 3)

/* 1 if N is a possible register number for function argument passing.  */
#define FUNCTION_ARG_REGNO_P(N) ((N) >= 1 && (N) <= 5)

#define DEFAULT_PCC_STRUCT_RETURN 1

#define STRUCT_VALUE 0

#define CUMULATIVE_ARGS int
#define INIT_CUMULATIVE_ARGS(CUM,FNTYPE,LIBNAME,FNDECL,N_NAMED_ARGS) {*(int*)&CUM = 1;}

/* Output assembler code to FILE to increment profiler label # LABELNO
   for profiling a function entry.  */

#define FUNCTION_PROFILER(FILE, LABELNO) \
  fatal_error("function profiler is not supported");

/* EXIT_IGNORE_STACK should be nonzero if, when returning from a function,
   the stack pointer does not matter.  The value is tested only in
   functions that have frame pointers.
   No definition is equivalent to always zero.  */
/*#define EXIT_IGNORE_STACK 1*/

/* Store in the variable DEPTH the initial difference between the
   frame pointer reg contents and the stack pointer reg contents,
   as of the start of the function body.  This depends on the layout
   of the fixed parts of the stack frame and on how registers are saved. */
#define INITIAL_FRAME_POINTER_OFFSET(DEPTH) \
  DEPTH = 0

/* Macros to check register numbers against specific register classes.  */

/* These assume that REGNO is a hard or pseudo reg number.
   They give nonzero only if REGNO is a hard reg of the suitable class
   or a pseudo reg currently allocated to a suitable hard reg.
   Since they use reg_renumber, they are safe only once reg_renumber
   has been allocated, which happens in local-alloc.c.  */

#define REGNO_OK_FOR_INDEX_P(regno)  \
        ((regno) < 32 || (unsigned)reg_renumber[regno] < 32)

#define REGNO_OK_FOR_BASE_P(regno) REGNO_OK_FOR_INDEX_P(regno)

/* Maximum number of registers that can appear in a valid memory address.  */

#define MAX_REGS_PER_ADDRESS 1

/* 1 if X is an rtx for a constant that is a valid address.  */

#define CONSTANT_ADDRESS_P(X)   \
  (GET_CODE (X) == LABEL_REF || GET_CODE (X) == SYMBOL_REF		\
   || GET_CODE (X) == CONST_INT || GET_CODE (X) == CONST)

/* The macros REG_OK_FOR..._P assume that the arg is a REG rtx
   and check its validity for a certain class.
   We have two alternate definitions for each of them.
   The usual definition accepts all pseudo regs; the other rejects
   them unless they have been allocated suitable hard regs.
   The symbol REG_OK_STRICT causes the latter definition to be used.

   Most source files want to accept pseudo regs in the hope that
   they will get allocated to the class that the insn wants them to be in.
   Source files for reload pass need to be strict.
   After reload, it makes no difference, since pseudo regs have
   been eliminated by then.  */

#ifndef REG_OK_STRICT

/* Nonzero if X is a hard reg that can be used as an index
   or if it is a pseudo reg.  */
#define REG_OK_FOR_INDEX_P(X) \
  ((REGNO (X) < 32 || REGNO(X) >= FIRST_PSEUDO_REGISTER))

/* Nonzero if X is a hard reg that can be used as a base reg
   or if it is a pseudo reg.  */
#define REG_OK_FOR_BASE_P(X) \
 ((REGNO (X) < 32 || REGNO(X) >= FIRST_PSEUDO_REGISTER))

#else

/* Nonzero if X is a hard reg that can be used as an index.  */
#define REG_OK_FOR_INDEX_P(X) (REGNO(X) < 32)

/* Nonzero if X is a hard reg that can be used as a base reg.  */
#define REG_OK_FOR_BASE_P(X) (REGNO (X) < 32)

#endif


/* GO_IF_LEGITIMATE_ADDRESS recognizes an RTL expression
   that is a valid memory address for an instruction.
   The MODE argument is the machine mode for the MEM expression
   that wants to use this address.

   The other macros defined here are used only in GO_IF_LEGITIMATE_ADDRESS,
   except for CONSTANT_ADDRESS_P which is actually machine-independent.  */

/* Non-zero if X is an address which can be indirected. */

#define CONSTANT_ADDRESS_P_2(X)   \
  (GET_CODE (X) == LABEL_REF || GET_CODE (X) == SYMBOL_REF		\
   || GET_CODE (X) == CONST)

#define INDIRECTABLE_CONSTANT_ADDRESS_P(X) 0

#define INDIRECTABLE_ADDRESS_P(X)  \
  (GET_CODE (X) == REG && REG_OK_FOR_BASE_P (X))

#define INDIRECTABLE_INDEX_P(X)  \
  (GET_CODE (X) == REG && REG_OK_FOR_INDEX_P (X))

/* Go to ADDR if X is a valid address not using indexing.
   (This much is the easy part.)  */

#define GO_IF_NONINDEXED_ADDRESS(X, ADDR)	\
{ if (CONSTANT_ADDRESS_P (X)) goto ADDR;	\
  if (INDIRECTABLE_ADDRESS_P (X)) goto ADDR; }


#define GO_IF_LEGITIMATE_ADDRESS(MODE, X, ADDR) \
{ register rtx xfoo = (X);			\
  GO_IF_NONINDEXED_ADDRESS (xfoo, ADDR);	\
  if (GET_CODE (xfoo) == PLUS)			\
    { register rtx xfoo0, xfoo1;		\
      xfoo0 = XEXP (xfoo, 0);			\
      xfoo1 = XEXP (xfoo, 1);			\
          if (INDIRECTABLE_ADDRESS_P (xfoo0) && GET_CODE (xfoo1) == CONST_INT)	\
            goto ADDR;							\
          if (INDIRECTABLE_ADDRESS_P (xfoo1) && GET_CODE (xfoo0) == CONST_INT)	\
            goto ADDR;  \
          if (INDIRECTABLE_INDEX_P (xfoo0) && CONSTANT_ADDRESS_P_2 (xfoo1))	\
            goto ADDR;							\
          if (INDIRECTABLE_INDEX_P (xfoo1) && CONSTANT_ADDRESS_P_2 (xfoo0))	\
            goto ADDR;  \
          if (INDIRECTABLE_ADDRESS_P (xfoo0) && INDIRECTABLE_INDEX_P (xfoo1)) \
            goto ADDR; \
          if (INDIRECTABLE_ADDRESS_P (xfoo1) && INDIRECTABLE_INDEX_P (xfoo0)) \
            goto ADDR; \
    }}


/* Try machine-dependent ways of modifying an illegitimate address
   to be legitimate.  If we find one, return the new, valid address.
   This macro is used in only one place: `memory_address' in explow.c.

   OLDX is the address as it was before break_out_memory_refs was called.
   In some cases it is useful to look at this to decide what needs to be done.

   MODE and WIN are passed so that this macro can use
   GO_IF_LEGITIMATE_ADDRESS.

   It is always safe for this macro to do nothing.  It exists to recognize
   opportunities to optimize the output. */

#define LEGITIMIZE_RELOAD_ADDRESS(X,MODE,OPNUM,TYPE,IND_LEVELS,WIN)     {}

/* Specify the machine mode that this machine uses
   for the index in the tablejump instruction.  */
#define CASE_VECTOR_MODE DImode

/* Define this if the case instruction drops through after the table
   when the index is out of range.  Don't define it if the case insn
   jumps to the default label instead.  */
/* #define CASE_DROPS_THROUGH */

/* Define if operations between registers always perform the operation
   on the full register even if a narrower mode is specified.  */
#define WORD_REGISTER_OPERATIONS

/* Define if loading in MODE, an integral mode narrower than BITS_PER_WORD
   will either zero-extend or sign-extend.  The value of this macro should
   be the code that says which one of the two operations is implicitly
   done, NIL if none.  */
#define LOAD_EXTEND_OP(MODE) ZERO_EXTEND

/* Define this as 1 if `char' should by default be signed; else as 0.  */
#define DEFAULT_SIGNED_CHAR 1

/* Max number of bytes we can move from memory to memory
   in one reasonably fast instruction.  */
#define MOVE_MAX 8

/* always use loops instead of function calls */
#define MOVE_RATIO(speed) 128
#define CLEAR_RATIO(speed) 128
#define SET_RATIO(speed) 128

/* Nonzero if access to memory by bytes is slow and undesirable.  */
#define SLOW_BYTE_ACCESS 1

/* Define if shifts truncate the shift count
   which implies one can omit a sign-extension or zero-extension
   of a shift count.  */
/* #define SHIFT_COUNT_TRUNCATED */

/* Value is 1 if truncating an integer of INPREC bits to OUTPREC bits
   is done just by pretending it is already truncated.  */

#define TRULY_NOOP_TRUNCATION(OUTPREC, INPREC) 1

/* Specify the machine mode that pointers have.
   After generation of rtl, the compiler makes no further distinction
   between pointers and any other objects of this machine mode.  */
#define Pmode DImode

#define POINTERS_EXTEND_UNSIGNED 1

#define STACK_SIZE_MODE Pmode

/* A function address in a call instruction
   is a byte address (for indexing purposes)
   so give the MEM rtx a byte's mode.  */
#define FUNCTION_MODE Pmode

/* It is as good or better to call a constant function address than to
   call an address kept in a register.  */
#define NO_FUNCTION_CSE 1

/* #define TARGET_FLOAT_FORMAT IEEE_FLOAT_FORMAT */

/* Specify the cost of a branch insn; roughly the number of extra insns that
   should be added to avoid a branch */

#define BRANCH_COST(speed_p, predictable_p) 1

#define MEMORY_MOVE_COST(M,C,I) 4

#define REGISTER_MOVE_COST(MODE,CLASS1,CLASS2) 2

#define ISSUE_RATE  4

/* Output at beginning of assembler file.  */
#define TARGET_ASM_FILE_START bpf_asm_file_start
#define TARGET_ASM_FILE_END bpf_asm_file_end

/* Output to assembler file text saying following lines
   may contain character constants, extra white space, comments, etc.  */
#define ASM_APP_ON "asm(\""

/* Output to assembler file text saying following lines
   no longer contain unusual constructs.  */
#define ASM_APP_OFF "\");\n"

/* Output before read-only data.  */
#define TEXT_SECTION_ASM_OP "/*.text*/"

/* Output before writable data.  */
#define DATA_SECTION_ASM_OP "/*.data*/"

/* How to refer to registers in assembler output.
   This sequence is indexed by compiler's hard-register-number (see above).  */
#define REGISTER_NAMES \
{"R0", "R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", \
 "R9", "R10", "R11", "R12", "R13", "R14", "R15", "R16", \
 "R17", "R18", "R19", "R20", "R21", "R22", "R23", "R24", \
 "R25", "R26", "R27", "__chain__", "__arg__", "__fp__", "__sp__"}

/* How to renumber registers for dbx and gdb. */
#define DBX_REGISTER_NUMBER(REGNO) (REGNO)

/* This is how to output the definition of a user-level label named NAME,
   such as the label on a static function or variable NAME.  */

#define ASM_OUTPUT_LABEL(FILE,NAME) bpf_output_label(FILE,NAME)

#define ASM_OUTPUT_POOL_PROLOGUE(FILE, NAME, DECL, SIZE)        \
  { \
    bpf_output_vars_end (FILE);   \
    if (SIZE) fprintf(FILE, "/* start local variables for function '%s' size=%d*/\n", \
            ((NAME) + ((NAME)[0]=='*')), SIZE); \
  }
#define ASM_OUTPUT_POOL_EPILOGUE(FILE, NAME, DECL, SIZE)  \
  { \
    bpf_output_vars_end (FILE);   \
    if (SIZE) fprintf(FILE,"/* end local variables for function '%s' */\n", \
            ((NAME) + ((NAME)[0]=='*'))); \
  }
  /* This is how to output an assembler line defining an `int' constant.  */

#define ASM_OUTPUT_LABELREF(FILE,NAME)  bpf_output_labelref(FILE,NAME)

#define ASM_OUTPUT_LABEL_REF(FILE,NAME)  bpf_output_label_ref(FILE,NAME)

#define ASM_OUTPUT_SYMBOL_REF(FILE,ADDR) bpf_output_symbol_ref(FILE,ADDR)

#define ASM_OUTPUT_ALIGN(FILE,LOG) bpf_output_align(FILE,LOG)

#define ASM_OUTPUT_ASCII(FILE,PTR,LEN) bpf_output_ascii(FILE,PTR,LEN)

/* This is how to output an insn to push a register on the stack.
   It need not be very fast code.  */

#define ASM_OUTPUT_REG_PUSH(FILE,REGNO)  \
  fprintf (FILE, "// unsupported reg_push %s;\n", reg_names[REGNO])

/* This is how to output an insn to pop a register from the stack.
   It need not be very fast code.  */

#define ASM_OUTPUT_REG_POP(FILE,REGNO)  \
  fprintf (FILE, "// unsupported reg_pop %s\n", reg_names[REGNO])

/* This is how to output an element of a case-vector that is absolute */
#define ASM_OUTPUT_ADDR_VEC_ELT(FILE, VALUE) \
  fprintf(FILE, "unsupported addr_vec_elt\n");

/* This is how to output an element of a case-vector that is relative.  */
#define ASM_OUTPUT_ADDR_DIFF_ELT(FILE, BODY, VALUE, REL) \
  fprintf(FILE, "unsupported addr_diff_elt\n");

#define ASM_OUTPUT_CASE_LABEL(FILE, PREFIX, NUM, TABLE) \
  fprintf(FILE, "unsupported case_label\n");

#define ASM_OUTPUT_CASE_END(FILE, NUM, TABLE) \
  fprintf(FILE, "unsupported case_end\n");

/* This is how to output an assembler line
   that says to advance the location counter by SIZE bytes.  */
#define ASM_OUTPUT_SKIP(FILE,SIZE)  bpf_output_skip(FILE,SIZE)

#define ASM_OUTPUT_ALIGNED_LOCAL(FILE,NAME,SIZE,ALIGN) bpf_output_local(FILE, NAME, SIZE, ALIGN)
#define ASM_OUTPUT_ALIGNED_BSS(FILE, DECL, NAME, SIZE, ALIGN)	\
  do {								\
    ASM_OUTPUT_ALIGNED_LOCAL (FILE, NAME, SIZE, ALIGN);		\
  } while (0)

/* Store in OUTPUT a string (made with alloca) containing
   an assembler-name for a local static variable named NAME.
   LABELNO is an integer which is different for each call.  */

#define ASM_FORMAT_PRIVATE_NAME(OUTPUT, NAME, LABELNO)	\
        ( (OUTPUT) = (char *) alloca (strlen ((NAME)) + 25),	\
          sprintf ((OUTPUT), "%s__PrivateName__%u", (NAME), (LABELNO)))

/* Print an instruction operand X on file FILE. */

#define PRINT_OPERAND(FILE, X, CODE) bpf_print_operand(FILE, X, CODE)

/* Print a memory operand whose address is X, on file FILE. */

#define PRINT_OPERAND_ADDRESS(FILE, ADDR)  \
  print_operand_address (FILE, ADDR)

#define NO_DOT_IN_LABEL
#define NO_DOLLAR_IN_LABEL

#define DONT_USE_BUILTIN_SETJMP
#define JMP_BUF_SIZE 64

/* not an ELF file format  */
/* #define OBJECT_FORMAT_ELF */

#define ASM_WEAKEN_LABEL(FILE,NAME) \
  do { const char * __name = (NAME) + ((NAME)[0]=='*'); \
       fprintf ((FILE), "//weak %s\n", __name); } while (0)

#define ASM_OUTPUT_DEF(FILE,LABEL1,LABEL2) \
 do {if (LABEL2) fprintf ((FILE), "unsupported\n"); \
     else ASM_WEAKEN_LABEL(FILE,LABEL1); \
    } while (0)

/* builtin_return_addr is unsupported */
#define RETURN_ADDR_RTX(count, frame) const0_rtx

/* Length in units of the trampoline for entering a nested function.  */
/* trampolines are not supported, but this macro has to be defined */
#define TRAMPOLINE_SIZE 32

#ifdef IN_LIBGCC2
#define NO_ASM
#endif /* IN_LIBGCC2 */

/* default value for assembler */
#ifndef DEFAULT_ASSEMBLER
#define DEFAULT_ASSEMBLER "/usr/bin/gcc"
#endif

/* default value for linker */
#ifndef DEFAULT_LINKER
#define DEFAULT_LINKER "/usr/bin/gcc"
#endif

#undef ASM_OUTPUT_INTERNAL_LABEL
#define ASM_OUTPUT_INTERNAL_LABEL(FILE,PREFIX) \
    bpf_output_internal_label(FILE,PREFIX)

#undef ASM_OUTPUT_SOURCE_FILENAME
#define ASM_OUTPUT_SOURCE_FILENAME(FILE, NA) bpf_output_source_filename(FILE, NA)

#undef ASM_OUTPUT_ALIGNED_COMMON
#define ASM_OUTPUT_ALIGNED_COMMON(FILE, NAME, SIZE, ALIGN)  \
  bpf_output_common(FILE, NAME, SIZE, ALIGN)

#define ASM_COMMENT_START "//"

#undef BSS_SECTION_ASM_OP
#define BSS_SECTION_ASM_OP  "/*.bss*/"

#undef INIT_SECTION_ASM_OP
#define INIT_SECTION_ASM_OP "/*.init*/"

#undef FINI_SECTION_ASM_OP
#define FINI_SECTION_ASM_OP "/*.fini*/"

#endif

