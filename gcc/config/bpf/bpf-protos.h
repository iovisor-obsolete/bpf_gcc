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

#ifndef __BPF_PROTOS_H__
#define __BPF_PROTOS_H__

#ifdef RTX_CODE
extern void output_call_value (struct rtx_def** op,int is_value, int cheat_num);
extern char * bpf_output_compare (rtx * operands, rtx_insn *insn,
				  bpf_cc_opcode_type opcode);
extern char * bpf_output_jump (rtx code_label, rtx_insn *insn);
extern void bpf_print_operand (FILE *f, struct rtx_def* X, char code);
extern void print_operand_address (FILE * file, struct rtx_def* addr);

extern void bpf_output_symbol_ref (FILE * file, struct rtx_def * addr);

#ifdef TREE_CODE
extern rtx bpf_function_value (const_tree, const_tree);
extern void bpf_output_section_name (FILE * file, tree decl, const char * name, int reloc);
#endif

#endif

extern void bpf_output_vars_end (FILE* f);
extern void bpf_output_vars_start (FILE* f);
extern void bpf_output_source_filename (FILE*, const char*);
extern void bpf_output_internal_label (FILE*, const char*);
extern void bpf_asm_file_start (FILE * f);
extern void bpf_asm_file_end (FILE * f);
extern void bpf_output_common (FILE * f, const char * , int , int );
extern void bpf_output_local (FILE * f, const char * , int , int );
extern void bpf_output_skip (FILE*, int size);
extern void bpf_output_align (FILE*, int align);
extern void bpf_output_label (FILE*, const char*);
extern void bpf_output_labelref (FILE*, const char*);
extern void bpf_output_label_ref (FILE*, const char*);
extern void bpf_output_ascii (FILE*,const char *,int);

#endif /* __BPF_PROTOS_H__ */

