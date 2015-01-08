;; GCC machine description for BPF
;; Copyright (C) 2013-2015, PLUMgrid Inc
;;
;; This file is part of GCC.
;;
;; GCC is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; GCC is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GCC; see the file COPYING3.  If not see
;; <http://www.gnu.org/licenses/>
;;
;;- See file "rtl.def" for documentation on define_insn, match_*, et. al.

(define_attr "type" "load,store,argload,argstore,arith,arithfp,compare,branch,call"
 (const_string "arith"))

;(define_register_constraint "b" "GENERAL_REGS" "The @code{b} register.")
;(define_register_constraint "a" "GENERAL_REGS" "The @code{a} register.")

;; Integer constant constraints.
(define_constraint "I"
  "Integer constant in the range 0 @dots{} 31, for 32-bit shifts."
  (and (match_code "const_int")
       (match_test "IN_RANGE (ival, 0, 31)")))

(define_constraint "S"
  "symbol_ref"
  (match_code "symbol_ref"))

(define_constraint "K"
  "Signed 32-bit integer constant."
  (and (match_code "const_int")
       (match_test "IN_RANGE (ival, -1 - 0x7fffFFFF, 0x7fffFFFF)")))

(define_predicate "int_reg_operand"
  (match_code "reg, subreg")
{
  return register_operand (op, mode);
})

(define_predicate "symbolic_operand"
  (match_code "symbol_ref,label_ref,const")
{
  enum machine_mode omode = GET_MODE (op);

  if (omode != mode && omode != VOIDmode && mode != VOIDmode)
    return 0;

  switch (GET_CODE (op))
    {
    case CONST_INT:
    case SYMBOL_REF:
      return 1;

    case CONST:
      op = XEXP (op, 0);
      return ((GET_CODE (XEXP (op, 0)) == SYMBOL_REF
               || GET_CODE (XEXP (op, 0)) == LABEL_REF)
	      && GET_CODE (XEXP (op, 1)) == CONST_INT);

    default:
      return 0;
    }
})

(define_predicate "call_operand"
  (match_code "mem")
{
  if (GET_CODE (op) != MEM)
    return 0;

  op = XEXP (op, 0);

  if (symbolic_operand (op, mode) || GET_CODE (op) == REG)
    return 1;

  return 0;
})

(define_predicate "simm32_operand"
  (match_code "const_int")
{
  return CONST_INT_P (op) && IN_RANGE (INTVAL (op), -1 - 0x7fffFFFF, 0x7fffFFFF);
})

(define_predicate "int_reg_or_const_operand"
  (match_code "reg, subreg, const, const_int, symbol_ref")
{
  return int_reg_operand (op, mode) || immediate_operand (op, mode);
})

(define_predicate "int_reg_or_const_or_mem_operand"
  (match_code "reg, subreg, const, const_int, symbol_ref, mem")
{
  return int_reg_operand (op, mode) || immediate_operand (op, mode)
      || memory_operand (op, mode);
})

(define_predicate "int_reg_or_mem_operand"
  (match_code "reg, subreg, mem")
{
  return int_reg_operand (op, mode) || memory_operand (op, mode);
})

(define_predicate "register_compare_operator"
  (match_code "eq,ne,geu,gtu,ge,gt"))

;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CMPs

(define_expand "cbranchdi4"
  [(set (pc)
	(if_then_else (match_operator 0 "comparison_operator"
			[(match_operand:DI 1 "int_reg_operand" "r")
			 (match_operand:DI 2 "int_reg_or_const_operand" "rK")])
		      (label_ref (match_operand 3 "" ""))
		      (pc)))]
  ""
  "
{
  if (register_compare_operator(operands[0], VOIDmode))
    /* have matching BPF insn */;
  else
    {
      rtx_code code = GET_CODE(operands[0]);
      rtx tmp = operands[1];
      operands[2] = force_reg (DImode, operands[2]);
      switch (code)
        {
	case LTU: code = GTU; break;
	case LEU: code = GEU; break;
	case LT: code = GT; break;
	case LE: code = GE; break;
	default: FAIL;
	}
      PUT_CODE (operands[0], code);
      operands[1] = operands[2];
      operands[2] = tmp;
    }
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; movDI
(define_expand "movdi"
  [(set (match_operand:DI 0 "general_operand" "")
	(match_operand:DI 1 "general_operand" ""))]
  ""
  "
{
  if (CONST_INT_P(operands[1]))
    {
      if (!simm32_operand(operands[1], DImode))
        {
          HOST_WIDE_INT val = INTVAL(operands[1]);
          if (memory_operand(operands[0], DImode))
            {
              rtx low = GEN_INT ((HOST_WIDE_INT)(int)val);
              rtx high = GEN_INT (val >> 32);
              rtx low_dest = change_address (operands[0], SImode, NULL_RTX);
              rtx high_dest = change_address (operands[0], SImode,
                                              plus_constant (DImode, XEXP (low_dest, 0), 4));
              emit_insn (gen_movsi (low_dest, low));
              emit_insn (gen_movsi (high_dest, high));
              DONE;
            }
          else
            {
              operands[0] = force_reg (DImode, operands[0]);
              if ( !(val & 0xffffFFFF)) // lower bits are zero
                {
                  emit_insn (gen_movdi (operands[0], GEN_INT (val >> 32)));
                  emit_insn (gen_ashldi3 (operands[0], operands[0], GEN_INT (32)));
                  DONE;
                }
              else if (val == 0xffffFFFF) // special case
                {
                  emit_insn (gen_movdi (operands[0], GEN_INT (-1)));
                  emit_insn (gen_lshrdi3 (operands[0], operands[0], GEN_INT (32)));
                  DONE;
                }
              else // bad case
                {
                  // 0x11223344 55667788 ->
                  // reg = 0x11223344
                  // reg <<= 32
                  // reg += 0x55667788
                  //
                  // 0x11223344 FF667788 ->
                  // reg = 0x11223345
                  // reg <<= 32
                  // reg += (long long)(int)0xFF667788

                  HOST_WIDE_INT low = (HOST_WIDE_INT)(int)val;
                  emit_insn (gen_movdi (operands[0], GEN_INT ((val - low) >> 32)));
                  emit_insn (gen_ashldi3 (operands[0], operands[0], GEN_INT (32)));
                  emit_insn (gen_adddi3 (operands[0], operands[0], GEN_INT (low)));
                  DONE;
                }
            }
        }
    }

  if( !int_reg_operand(operands[0], DImode) && !int_reg_operand(operands[1], DImode))
    {
      operands[1] = force_reg (DImode, operands[1]);
    }
}")

(define_insn "movdi_2reg"
  [(set (match_operand:DI 0 "register_operand"         "=r, r, r")
	(match_operand:DI 1 "int_reg_or_const_operand" " r, K, S"))]
  ""
  "@
   BPF_INSN_ALU(BPF_MOV, %0, %1), // %0 = %1
   BPF_INSN_ALU_IMM(BPF_MOV, %0, %1), // %0 = %1
   BPF_INSN_ALU_IMM(BPF_MOV, %0, encode_symbol(%1)), // %0 = %1"
[(set_attr "type" "arith,arith,arith")])

(define_split
  [(set (match_operand:TI 0 "register_operand" "")
	(match_operand:TI 1 "memory_operand"  ""))]
  "GET_CODE (operands[0]) == REG"
  [(clobber (const_int 0))]
  "
{
  rtx word0 = change_address (operands[1], DImode, NULL_RTX);
  rtx word1 = change_address (operands[1], DImode,
			      plus_constant (DImode, XEXP (word0, 0), 4));
  rtx high_part = gen_highpart (DImode, operands[0]);
  rtx low_part = gen_lowpart (DImode, operands[0]);

  if (reg_overlap_mentioned_p (high_part, word1))
    {
      emit_insn (gen_movdi (low_part, word1));
      emit_insn (gen_movdi (high_part, word0));
    }
  else
    {
      emit_insn (gen_movdi (high_part, word0));
      emit_insn (gen_movdi (low_part, word1));
    }
  DONE;
}")

(define_split
  [(set (match_operand:TI 0 "memory_operand" "")
	(match_operand:TI 1 "register_operand"  ""))]
  "GET_CODE (operands[1]) == REG"
;  ""
  [(clobber (const_int 0))]
  "
{
  rtx word0 = change_address (operands[0], DImode, NULL_RTX);
  rtx word1 = change_address (operands[0], DImode,
			      plus_constant (DImode, XEXP (word0, 0), 4));
  rtx high_part = gen_highpart (DImode, operands[1]);
  rtx low_part = gen_lowpart (DImode, operands[1]);

  if (reg_overlap_mentioned_p (high_part, word1))
    {
      emit_insn (gen_movdi (word1, low_part));
      emit_insn (gen_movdi (word0, high_part));
    }
  else
    {
      emit_insn (gen_movdi (word0, high_part));
      emit_insn (gen_movdi (word1, low_part));
    }
  DONE;
}")


(define_insn "movdi_mem2reg"
  [(set (match_operand:DI 0 "int_reg_operand" "=r")
	(match_operand:DI 1 "memory_operand"  "m"))]
  ""
  "BPF_INSN_LD(BPF_DW, %0, %1), // %0=*(uint64*)(%1)"
[(set_attr "type" "load")])

(define_insn "movdi_2mem"
  [(set (match_operand:DI 0 "memory_operand" "=m,m")
	(match_operand:DI 1 "int_reg_or_const_operand" "r,K"))]
  ""
  "@
   BPF_INSN_ST(BPF_DW, %0, %1), // *(uint64*)(%0)=%1
   BPF_INSN_ST_IMM(BPF_DW, %0, %1), // *(uint64*)(%0)=%1"
[(set_attr "type" "store, store")])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; movSI

(define_expand "movsi"
  [(set (match_operand:SI 0 "general_operand" "")
	(match_operand:SI 1 "general_operand" ""))]
  ""
  "
{
  if( !int_reg_operand(operands[0], SImode) && !int_reg_operand(operands[1], SImode) )
    {
      operands[1] = force_reg (SImode, operands[1]);
    }
}")

;; ----------------------------------------------------------------------

(define_insn "movsi_mem2reg"
  [(set (match_operand:SI 0 "int_reg_operand" "=r")
	(match_operand:SI 1 "memory_operand" "m"))]
  ""
  "BPF_INSN_LD(BPF_W, %0, %1), // %0=*(uint32*)(%1)"
[(set_attr "type" "load")])

(define_insn "movsi_2reg"
  [(set (match_operand:SI 0 "register_operand"   "=r,r")
	(match_operand:SI 1 "int_reg_or_const_operand"  "r,K"))]
  ""
  "@
   BPF_INSN_ALU(BPF_MOV, %0, %1), // %0 = %1
   BPF_INSN_ALU_IMM(BPF_MOV, %0, %1), // %0 = %1"
[(set_attr "type" "arith,arith")])

(define_insn "movsi_2mem"
  [(set (match_operand:SI 0 "memory_operand" "=m, m")
	(match_operand:SI 1 "int_reg_or_const_operand" "r, K"))]
  ""
  "@
   BPF_INSN_ST(BPF_W, %0, %1), // *(uint32*)(%0)=%1
   BPF_INSN_ST_IMM(BPF_W, %0, %1), // *(uint32*)(%0)=%1"
[(set_attr "type" "store, store")])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; movHI
;;
;; movhi
;;

(define_expand "movhi"
  [(set (match_operand:HI 0 "general_operand" "")
	(match_operand:HI 1 "general_operand" ""))]
  ""
  "
{
  if( !int_reg_operand(operands[0], HImode) && !int_reg_operand(operands[1], HImode))
    {
      operands[1] = force_reg (HImode, operands[1]);
    }
}")

;; Extension and truncation insns.

(define_insn "zero_extendhidi2"
  [(set (match_operand:DI 0 "int_reg_operand" "=r,r")
	(zero_extend:DI (match_operand:HI 1 "int_reg_or_mem_operand" "0,m")))]
  ""
  "@
   BPF_INSN_ALU_IMM(BPF_AND, %0, 0xffff), // %0 &= 0xffff; %0 = (uint64)(uint16)%0
   BPF_INSN_LD(BPF_H, %0, %1), // %0=(uint64)*(uint16*)(%1)"
[(set_attr "type" "arith,load")])


(define_insn "movhi_2reg"
  [(set (match_operand:HI 0 "register_operand"   "=r,r")
	(match_operand:HI 1 "int_reg_or_const_operand"  "r,K"))]
  ""
  "@
   BPF_INSN_ALU(BPF_MOV, %0, %1), // %0 = %1
   BPF_INSN_ALU_IMM(BPF_MOV, %0, %1), // %0 = %1"
[(set_attr "type" "arith,arith")])

(define_insn "movhi_mem2reg"
  [(set (match_operand:HI 0 "int_reg_operand" "=r")
	(match_operand:HI 1 "memory_operand"  "m"))]
  ""
  "BPF_INSN_LD(BPF_H, %0, %1), // %0=*(uint16*)(%1)"
[(set_attr "type" "load")])

(define_insn "movhi_2mem"
  [(set (match_operand:HI 0 "memory_operand" "=m,m")
	(match_operand:HI 1 "int_reg_or_const_operand" "r,K"))]
  ""
  "@
   BPF_INSN_ST(BPF_H, %0, %1), // *(uint16*)(%0) = %1
   BPF_INSN_ST_IMM(BPF_H, %0, %1), // *(uint16*)(%0) = %1"
[(set_attr "type" "store,store")])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; movQI
;;
;; movqi
;;

(define_expand "movqi"
  [(set (match_operand:QI 0 "general_operand" "")
	(match_operand:QI 1 "general_operand" ""))]
  ""
  "
{
  if( !int_reg_operand(operands[0], QImode) && !int_reg_operand(operands[1], QImode))
    {
      operands[1] = force_reg (QImode, operands[1]);
    }
}")

(define_insn "movqi_mem2reg"
  [(set (match_operand:QI 0 "int_reg_operand" "=r")
	(match_operand:QI 1 "memory_operand" "m"))]
  ""
  "BPF_INSN_LD(BPF_B, %0, %1), // %0=*(uint8*)(%1)"
[(set_attr "type" "load")])

(define_insn "movqi_2reg"
  [(set (match_operand:QI 0 "register_operand"   "=r,r")
	(match_operand:QI 1 "int_reg_or_const_operand"  "r,K"))]
  ""
  "@
   BPF_INSN_ALU(BPF_MOV, %0, %1), // %0 = %1
   BPF_INSN_ALU_IMM(BPF_MOV, %0, %1), // %0 = %1"
[(set_attr "type" "arith,arith")])

(define_insn "movqi_2mem"
  [(set (match_operand:QI 0 "memory_operand" "=m,m")
	(match_operand:QI 1 "int_reg_or_const_operand" "r,K"))]
  ""
  "@
   BPF_INSN_ST(BPF_B, %0, %1), // *(uint8*)(%0) = %1
   BPF_INSN_ST_IMM(BPF_B, %0, %1), // *(uint8*)(%0) = %1"
[(set_attr "type" "store,store")])

(define_insn "zero_extendqidi2"
  [(set (match_operand:DI 0 "int_reg_operand" "=r,r")
	(zero_extend:DI (match_operand:QI 1 "int_reg_or_mem_operand" "0,m")))]
  ""
  "@
   BPF_INSN_ALU_IMM(BPF_AND, %0, 0xff), // %0 &= 0xff; %0 = (uint64)(uint8)%0
   BPF_INSN_LD(BPF_B, %0, %1), // %0=(uint64)*(uint8*)(%1)"
[(set_attr "type" "arith,load")])

(define_expand "zero_extendsidi2"
  [(set (match_operand:DI 0 "int_reg_operand" "")
	(zero_extend:DI (match_operand:SI 1 "int_reg_or_mem_operand" "")))]
  ""
  "
{
  if (int_reg_operand(operands[1], SImode))
    {
      operands[1] = gen_lowpart (DImode, operands[1]);
      emit_insn (gen_ashldi3 (operands[0], operands[1], GEN_INT (32)));
      emit_insn (gen_lshrdi3 (operands[0], operands[0], GEN_INT (32)));
      DONE;
    }
}")

(define_insn "*zero_extendsidi2"
  [(set (match_operand:DI 0 "int_reg_operand" "=r")
	(zero_extend:DI (match_operand:SI 1 "memory_operand" "m")))]
  ""
  "BPF_INSN_LD(BPF_W, %0, %1), // %0=(uint64)*(uint32*)(%1)"
[(set_attr "type" "load")])

(define_insn "adddi3"
  [(set (match_operand:DI 0 "int_reg_operand" "=r, r")
	(plus:DI (match_operand:DI 1 "int_reg_operand" "0, 0")
		 (match_operand:DI 2 "int_reg_or_const_operand" "r, K")))]
  ""
  "@
   BPF_INSN_ALU(BPF_ADD, %0, %2), // %0 += %2
   BPF_INSN_ALU_IMM(BPF_ADD, %0, %2), // %0 += %2"
[(set_attr "type" "arith,arith") ])

(define_insn "subdi3"
  [(set (match_operand:DI 0 "int_reg_operand" "=r, r")
	(minus:DI (match_operand:DI 1 "int_reg_operand" "0, 0")
		  (match_operand:DI 2 "int_reg_or_const_operand" "r, K")))]
  ""
  "@
   BPF_INSN_ALU(BPF_SUB, %0, %2), // %0 -= %2
   BPF_INSN_ALU_IMM(BPF_SUB, %0, %2), // %0 -= %2"
[(set_attr "type" "arith, arith") ])


(define_insn "muldi3"
  [(set (match_operand:DI 0 "int_reg_operand" "=r,r")
	(mult:DI (match_operand:DI 1 "int_reg_operand" "0,0")
	         (match_operand:DI 2 "int_reg_or_const_operand" "r,K")))]
  ""
  "@
   BPF_INSN_ALU(BPF_MUL, %0, %2), // %0 *= %2
   BPF_INSN_ALU_IMM(BPF_MUL, %0, %2), // %0 *= %2"
[(set_attr "type" "arith, arith") ])

;;- Divide and mod instructions.

(define_insn "divdi3"
  [(set (match_operand:DI 0 "int_reg_operand" "=r,r")
	(div:DI (match_operand:DI 1 "int_reg_operand" "0,0")
		(match_operand:DI 2 "int_reg_or_const_operand" "r,K")))]
  ""
  "@
   BPF_INSN_ALU(BPF_DIV, %0, %2), // %0=((int64)%1)/((int64)%2)
   BPF_INSN_ALU_IMM(BPF_DIV, %0, %2), // %0=((int64)%1)/((int64)%2)"
[(set_attr "type" "arith, arith") ])

(define_insn "udivdi3"
  [(set (match_operand:DI 0 "int_reg_operand" "=r,r")
	(udiv:DI (match_operand:DI 1 "int_reg_operand" "0,0")
		(match_operand:DI 2 "int_reg_or_const_operand" "r,K")))]
  ""
  "@
   BPF_INSN_ALU(BPF_DIV, %0, %2), // %0=((uint64)%1)/((uint64)%2)
   BPF_INSN_ALU_IMM(BPF_DIV, %0, %2), // %0=((uint64)%1)/((uint64)%2)"
[(set_attr "type" "arith, arith") ])

(define_insn "moddi3"
  [(set (match_operand:DI 0 "int_reg_operand" "=r")
	(mod:DI (match_operand:DI 1 "int_reg_operand" "r")
		(match_operand:DI 2 "int_reg_or_const_operand" "rK")))]
  ""
  "%0=((long long)%1)%%((long long)%2)"
[(set_attr "type" "arith")])

(define_insn "umoddi3"
  [(set (match_operand:DI 0 "int_reg_operand" "=r,r")
	(umod:DI (match_operand:DI 1 "int_reg_operand" "0,0")
		(match_operand:DI 2 "int_reg_or_const_operand" "r,K")))]
  ""
  "@
   BPF_INSN_ALU(BPF_MOD, %0, %2), // %0=((uint64)%1)%%((uint64)%2)
   BPF_INSN_ALU_IMM(BPF_MOD, %0, %2), // %0=((uint64)%1)%%((uint64)%2)"
[(set_attr "type" "arith")])

;;
;; bit and/or instructions
;;

(define_insn "anddi3"
  [(set (match_operand:DI 0 "int_reg_operand" "=r,r")
        (and:DI (match_operand:DI 1 "int_reg_operand" "%0,0")
		(match_operand:DI 2 "int_reg_or_const_operand" "r,K")))]
  ""
  "@
   BPF_INSN_ALU(BPF_AND, %0, %2), // %0 &= %2
   BPF_INSN_ALU_IMM(BPF_AND, %0, %2), // %0 &= %2"
[(set_attr "type" "arith, arith")])

(define_insn "iordi3"
  [(set (match_operand:DI 0 "int_reg_operand" "=r,r")
	(ior:DI (match_operand:DI 1 "int_reg_operand" "%0,0")
	        (match_operand:DI 2 "int_reg_or_const_operand" "r,K")))]
  ""
  "@
   BPF_INSN_ALU(BPF_OR, %0, %2), // %0 |= %2
   BPF_INSN_ALU_IMM(BPF_OR, %0, %2), // %0 |= %2"
[(set_attr "type" "arith, arith")])

(define_insn "xordi3"
  [(set (match_operand:DI 0 "int_reg_operand" "=r,r")
	(xor:DI (match_operand:DI 1 "int_reg_operand" "%0,0")
		(match_operand:DI 2 "int_reg_or_const_operand" "r,K")))]
  ""
  "@
   BPF_INSN_ALU(BPF_XOR, %0, %2), // %0 ^= %2
   BPF_INSN_ALU_IMM(BPF_XOR, %0, %2), // %0 ^= %2"
[(set_attr "type" "arith, arith")])

(define_insn "negdi2"
  [(set (match_operand:DI 0 "int_reg_operand" "=r")
	(neg:DI (match_operand:DI 1 "int_reg_operand" "0")))]
  ""
  "BPF_INSN_ALU(BPF_NEG, %0, 0/*ignored*/), // %0= - %1"
[(set_attr "type" "arith")])

;(define_insn "one_cmpldi2"
;  [(set (match_operand:DI 0 "int_reg_operand" "=r")
;	(not:DI (match_operand:DI 1 "int_reg_operand" "r")))]
;  ""
;  "TODO /*one_cmpldi2*/"
;[(set_attr "type" "arith")])


(define_insn "ashrdi3"
  [(set (match_operand:DI 0 "int_reg_operand" "=r,r")
	(ashiftrt:DI (match_operand:DI 1 "int_reg_operand" "0,0")
		     (match_operand:SI 2 "int_reg_or_const_operand" "r,K")))]
  ""
  "@
   BPF_INSN_ALU(BPF_ARSH, %0, %2), // %0=((int64)%0)>>%2
   BPF_INSN_ALU_IMM(BPF_ARSH, %0, %2), // %0=((int64)%0)>>%2"
[(set_attr "type" "arith,arith")])

;;
;; left shift
;;

(define_insn "ashldi3"
  [(set (match_operand:DI 0 "int_reg_operand" "=r,r")
	(ashift:DI (match_operand:DI 1 "int_reg_operand" "0,0")
		   (match_operand:SI 2 "int_reg_or_const_operand" "r,K")))]
  ""
  "@
   BPF_INSN_ALU(BPF_LSH, %0, %2), // %0 <<= %2
   BPF_INSN_ALU_IMM(BPF_LSH, %0, %2), // %0 <<= %2"
[(set_attr "type" "arith,arith")])


;;
;; logical shift
;;


(define_insn "lshrdi3"
  [(set (match_operand:DI 0 "int_reg_operand" "=r,r")
	(lshiftrt:DI (match_operand:DI 1 "int_reg_operand" "0,0")
		     (match_operand:SI 2 "int_reg_or_const_operand" "r,K")))]
  ""
  "@
   BPF_INSN_ALU(BPF_RSH, %0, %2), // %0=((uint64)%0)>>%2
   BPF_INSN_ALU_IMM(BPF_RSH, %0, %2), // %0=((uint64)%0)>>%2"
[(set_attr "type" "arith,arith")])

;;
;; jump and branch insns
;;
(define_insn "jump"
  [(set (pc)
	(label_ref (match_operand 0 "" "")))]
  ""
  "* return bpf_output_jump (operands[0], insn);"
[(set_attr "type" "branch")])

(define_insn "tablejump"
  [(set (pc) (match_operand:SI 0 "int_reg_operand" "r"))
   (use (label_ref (match_operand 1 "" "")))]
  ""
  "// TODO tablejump %0"
[(set_attr "type" "branch")])

;-----------------------------------------------------------------
;  branches
;;;;;;;;;;;;;;;;;

(define_insn "br_di"
  [(set (pc)
	(if_then_else (match_operator 3 "register_compare_operator"
			 [(match_operand:DI 0 "int_reg_operand" "r")
			  (match_operand:DI 1 "int_reg_or_const_operand" "rK")])
		      (label_ref (match_operand 2 "" ""))
		      (pc)))]
  ""
  "* return bpf_output_compare (operands, insn, CC_NORMAL);"
[(set_attr "type" "branch")])

;(define_insn "br_di_reverse"
;  [(set (pc)
;	(if_then_else (match_operator 3 "register_compare_operator"
;			 [(match_operand:DI 0 "int_reg_operand" "r")
;			  (match_operand:DI 1 "int_reg_or_const_operand" "rK")])
;                      (pc)
;		      (label_ref (match_operand 2 "" ""))))]
;  ""
;  "* return bpf_output_compare (operands, insn, CC_REVERSE);"
;[(set_attr "type" "branch")])

;
;;-----------------------------------------------------------------
;
;;
;; call instructions
;;

(define_expand "call"
  [(call (match_operand:DI 0 "call_operand" "m")
	 (match_operand:SI 1 "general_operand" ""))
	 (match_operand 3 "" "i") ]
  ""
  "
{
  emit_call_insn (gen_rtx_PARALLEL (VOIDmode, gen_rtvec (2,
                  gen_rtx_CALL (VOIDmode, operands[0], operands[1]), operands[3])));
  /* emit_call_insn (gen_rtx_CALL (VOIDmode, operands[0], operands[1])); */
  DONE;
}")

(define_insn "call_insn"
  [(call (match_operand:DI 0 "call_operand" "m")
	 (match_operand:SI 1 "general_operand" ""))
	 (match_operand 2 "" "i") ]
  ""
  "*
{
  output_call_value (operands, 0, 0);
  return \"\";
}"
[(set_attr "type" "call")])

(define_insn "call_value"
  [(set (match_operand 0 "register_operand" "")
	(call (match_operand:DI 1 "call_operand" "m")
	      (match_operand:SI 2 "general_operand" "")))]
  ""
  "*
{
  output_call_value (operands, 1, 0);
  return \"\";
}"
[(set_attr "type" "call")])


;; UNSPEC_VOLATILE is considered to use and clobber all hard registers and
;; all of memory.  This blocks insns from being moved across this point.

(define_insn "blockage"
  [(unspec_volatile [(const_int 0)] 0)]
  ""
  "")

(define_insn "indirect_jump"
  [(set (pc) (match_operand:SI 0 "int_reg_operand" "r"))]
  ""
  "// TODO indirect jump %0"
[(set_attr "type" "branch")])


(define_insn "nop"
  [(const_int 0)]
  ""
  "NOP insn is unsupported, recompile with -O2"
[(set_attr "type" "arith") ])


(define_insn "allocate_stack"
  [(set (match_operand:DI 0 "int_reg_operand" "=r")
        (minus:DI (reg:DI 31) (match_operand:DI 1 "int_reg_operand" "r")))
   (set (reg:DI 31) (minus:DI (reg:DI 31) (match_dup 1)))
; have to clobber to prevent unused op0 to be optimized to SP=SP-const_int
   (clobber (match_dup 1))]
  ""
  "*
  {
    return \"allocate_stack not supported\";
  }"
[(set_attr "type" "call")])


(define_expand "save_stack_nonlocal"
  [(use (match_operand:DI 0 "memory_operand" ""))
   (use (match_operand:DI 1 "register_operand" ""))]
  ""
  "
{
  FAIL;
}")

(define_expand "nonlocal_goto"
  [(use (match_operand 0 "general_operand" ""))
   (use (match_operand 1 "general_operand" ""))
   (use (match_operand 2 "general_operand" ""))
   (use (match_operand 3 "general_operand" ""))]
  ""
  "
{
  FAIL;
}")


(define_expand "nonlocal_goto_receiver"
  [(unspec_volatile [(const_int 0)] 1)]
  ""
  "
{
  FAIL;
}")


(define_expand "save_stack_function"
  [(match_operand 0 "general_operand" "")
   (match_operand 1 "register_operand" "")]
  ""
  "DONE;")

(define_expand "save_stack_block"
  [(match_operand 0 "general_operand" "")
   (match_operand 1 "register_operand" "")]
  ""
  "DONE;")

(define_expand "restore_stack_function"
  [(match_operand 0 "register_operand" "")
   (match_operand 1 "general_operand" "")]
  ""
  "DONE;")

(define_expand "restore_stack_block"
  [(match_operand 0 "register_operand" "")
   (match_operand 1 "general_operand" "")]
  ""
  "DONE;")

(define_expand "atomic_fetch_adddi"
  [(match_operand:DI 0 "register_operand")
   (match_operand:DI 1 "memory_operand")
   (match_operand:DI 2 "register_operand")
   (match_operand:SI 3 "const_int_operand")]
  ""
{
  emit_insn (gen_atomic_fetch_adddi_1 (operands[0], operands[1], operands[2]));
  DONE;
})

(define_expand "atomic_fetch_addsi"
  [(match_operand:SI 0 "register_operand")
   (match_operand:SI 1 "memory_operand")
   (match_operand:SI 2 "register_operand")
   (match_operand:SI 3 "const_int_operand")]
  ""
{
  emit_insn (gen_atomic_fetch_addsi_1 (operands[0], operands[1], operands[2]));
  DONE;
})

(define_insn "atomic_fetch_adddi_1"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(unspec_volatile:DI [(match_operand:DI 1 "memory_operand" "")]
	 0))
   (set (match_dup 1)
	(unspec_volatile:DI
	 [(plus:DI (match_dup 1)
		    (match_operand:DI 2 "register_operand" "r"))]
	 0))]
  ""
  "BPF_INSN_XADD(BPF_DW, %1, %0), // atomic (*(uint64*)%1) += %0"
  [(set_attr "type" "load")])

(define_insn "atomic_fetch_addsi_1"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec_volatile:SI [(match_operand:SI 1 "memory_operand" "")]
	 0))
   (set (match_dup 1)
	(unspec_volatile:SI
	 [(plus:SI (match_dup 1)
		    (match_operand:SI 2 "register_operand" "r"))]
	 0))]
  ""
  "BPF_INSN_XADD(BPF_W, %1, %0), // atomic (*(uint32*)%1) += %0"
  [(set_attr "type" "load")])

(define_expand "bswapdi2"
  [(set (match_operand:DI 0 "register_operand")
	(bswap:DI (match_operand:DI 1 "nonimmediate_operand")))]
  ""
{
  operands[1] = force_reg (DImode, operands[1]);
})

(define_expand "bswapsi2"
  [(set (match_operand:SI 0 "register_operand")
	(bswap:SI (match_operand:SI 1 "nonimmediate_operand")))]
  ""
{
  operands[1] = force_reg (SImode, operands[1]);
})

; experimental bswap16
;(define_expand "bswaphi2"
;  [(set (match_operand:HI 0 "register_operand")
;	(bswap:HI (match_operand:HI 1 "nonimmediate_operand")))]
;  ""
;{
;  operands[1] = copy_to_mode_reg (HImode, operands[1]);
;})

(define_insn "*bswapdi2"
  [(set (match_operand:DI 0 "register_operand" "=r")
	(bswap:DI (match_operand:DI 1 "register_operand" "0")))]
  ""
  "BPF_INSN_ALU(BPF_BSWAP64, %0, 0/*ignored*/), // bswap64 %0"
  [(set_attr "type" "arith")])

(define_insn "*bswapsi2"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(bswap:SI (match_operand:SI 1 "register_operand" "0")))]
  ""
  "BPF_INSN_ALU(BPF_BSWAP32, %0, 0/*ignored*/), // bswap32 %0"
  [(set_attr "type" "arith")])

;(define_insn "*bswaphi2"
;  [(set (match_operand:HI 0 "register_operand" "=r")
;	(bswap:HI (match_operand:HI 1 "register_operand" "0")))]
;  ""
;  "BPF_INSN_ALU(BPF_BSWAP16, %0, 0/*ignored*/), // bswap16 %0"
;  [(set_attr "type" "arith")])

