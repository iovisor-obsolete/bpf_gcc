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
#include "bpf.h"
#endif

#undef CPP_SUBTARGET_SPEC
#define CPP_SUBTARGET_SPEC ""

#define CPP_SPEC ""

#undef ASM_SPEC
#define ASM_SPEC ""

#undef ASM_CPU_DEFAULT_SPEC
#define ASM_CPU_DEFAULT_SPEC ""

#undef ASM_CPU_SPEC
#define ASM_CPU_SPEC ""

#undef STARTFILE_SPEC
#define STARTFILE_SPEC  ""

#undef LIB_SPEC
#define LIB_SPEC ""

#undef  ENDFILE_SPEC
#define ENDFILE_SPEC ""

#undef LINK_SPEC
#define LINK_SPEC ""

#undef HAVE_ATEXIT
#define HAVE_ATEXIT

#undef USER_LABEL_PREFIX
#define USER_LABEL_PREFIX ""

#undef LOCAL_LABEL_PREFIX
#define LOCAL_LABEL_PREFIX "Label"

#undef ASM_GENERATE_INTERNAL_LABEL
#define ASM_GENERATE_INTERNAL_LABEL(STRING, PREFIX, NUM) \
    sprintf ((STRING), "%s%s%d", LOCAL_LABEL_PREFIX, (PREFIX), (NUM))

