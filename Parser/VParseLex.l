%option align interactive
%option stack
%option noc++
%option prefix="VParseLex"
%{
/* $Id$
 ******************************************************************************
 * DESCRIPTION: Verilog Parser Lexer
 * 
 * This file is part of Verilog-Perl.  
 * 
 * Author: Wilson Snyder <wsnyder@wsnyder.org>
 * 
 * Code available from: http://www.veripool.com/systemperl
 * 
 ******************************************************************************
 * 
 * Copyright 2000-2007 by Wilson Snyder.  This program is free software;
 * you can redistribute it and/or modify it under the terms of either the GNU
 * General Public License or the Perl Artistic License.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 *****************************************************************************
 * Do not use Flex in C++ mode.  It has bugs with yyunput() which result in
 * lost characters.
 *****************************************************************************/

#include "VParseLex.h"
#include <stdio.h>
#include <iostream>
#include <stdarg.h>

#include "VParseGrammar.h"
#include "VParseBison.h"

#define YY_SKIP_YYWRAP

VParseLex* VParseLex::s_currentLexp = NULL;	// Current lexing point
VParseBisonYYSType* VParseLex::s_yylvalp = NULL;		// LValue for current bison object

#define LEXP (VParseLex::s_currentLexp)
#define PARSEP (LEXP->m_parsep)

#define NEXTLINE()  { PARSEP->inFilelineInc(); }

#define FL { VParseLex::s_yylvalp->fl = PARSEP->inFilelinep(); }

// lval.fileline not used yet; here for Verilator parser compatibility
#define VALTEXTL(text,leng) VParseLex::s_yylvalp->str = string((text),(leng))
#define VALTEXT   VALTEXTL(yytext,yyleng)
#define CALLBACKL(whichCb,text,leng) {PARSEP->whichCb(VParseLex::s_yylvalp->fl, string((text),(leng))); }
#define CALLBACK(whichCb) CALLBACKL(whichCb,yytext,yyleng)

#define YY_INPUT(buf,result,max_size) \
    result = PARSEP->inputToLex(buf,max_size);

int yywrap() { return PARSEP->eofToLex(); }

#define StashPrefix PARSEP->unreadbackCat(yytext,yyleng)

void yyerror(char* errmsg) {
    PARSEP->inFilelinep()->error(errmsg);
}

void yyerrorf(const char* format, ...) {
    char msg[1024];

    va_list ap;
    va_start(ap,format);
    vsprintf(msg,format,ap);
    va_end(ap);

    yyerror(msg);
}

/**********************************************************************/
%}

%s V95 V01 V05 S05
%s STRING CMTMODE PROTMODE ATTRMODE

ws	[ \t\f\r]+
	/* identifier */
id	[a-zA-Z_][a-zA-Z0-9_$]*
	/* escaped identifier */
escid	\\[^ \t\f\r\n]+

%%

<INITIAL>.|\n 		{BEGIN S05; yyless(0); }

  /* Verilog 1995 */
<V95,V01,V05,S05>{
  {ws}			{ StashPrefix; }	/* otherwise ignore white-space */
  \n			{ StashPrefix; NEXTLINE();}		/* Count line numbers */
  /*     Keywords */
  "always"		{ FL; VALTEXT; CALLBACK(keywordCb); return yALWAYS; }
  "and"			{ FL; VALTEXT; CALLBACK(keywordCb); return yAND; }
  "assign"		{ FL; VALTEXT; CALLBACK(keywordCb); return yASSIGN; }
  "begin"		{ FL; VALTEXT; CALLBACK(keywordCb); return yBEGIN; }
  "buf"			{ FL; VALTEXT; CALLBACK(keywordCb); return yBUF; }
  "case"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCASE; }
  "casex"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCASEX; }
  "casez"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCASEZ; }
  "deassign"		{ FL; VALTEXT; CALLBACK(keywordCb); return yDEASSIGN; }
  "default"		{ FL; VALTEXT; CALLBACK(keywordCb); return yDEFAULT; }
  "defparam"		{ FL; VALTEXT; CALLBACK(keywordCb); return yDEFPARAM; }
  "disable"		{ FL; VALTEXT; CALLBACK(keywordCb); return yDISABLE; }
  "edge"		{ FL; VALTEXT; CALLBACK(keywordCb); return yaTIMINGSPEC; }
  "else"		{ FL; VALTEXT; CALLBACK(keywordCb); return yELSE; }
  "end"			{ FL; VALTEXT; CALLBACK(keywordCb); return yEND; }
  "endcase"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDCASE; }
  "endfunction"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDFUNCTION; }
  "endmodule"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDMODULE; }
  "endprimitive"	{ FL; VALTEXT; CALLBACK(keywordCb); return yENDMODULE; }
  "endspecify"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDSPECIFY; }
  "endtable"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDTABLE; }
  "endtask"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDTASK; }
  "for"			{ FL; VALTEXT; CALLBACK(keywordCb); return yFOR; }
  "force"		{ FL; VALTEXT; CALLBACK(keywordCb); return yFORCE; }
  "forever"		{ FL; VALTEXT; CALLBACK(keywordCb); return yFOREVER; }
  "fork"		{ FL; VALTEXT; CALLBACK(keywordCb); return yFORK; }
  "function"		{ FL; VALTEXT; CALLBACK(keywordCb); return yFUNCTION; }
  "if"			{ FL; VALTEXT; CALLBACK(keywordCb); return yIF; }
  "initial"		{ FL; VALTEXT; CALLBACK(keywordCb); return yINITIAL; }
  "inout"		{ FL; VALTEXT; CALLBACK(keywordCb); return yINOUT; }
  "input"		{ FL; VALTEXT; CALLBACK(keywordCb); return yINPUT; }
  "integer"		{ FL; VALTEXT; CALLBACK(keywordCb); return yINTEGER; }
  "join"		{ FL; VALTEXT; CALLBACK(keywordCb); return yJOIN; }
  "macromodule"		{ FL; VALTEXT; CALLBACK(keywordCb); return yMODULE; }
  "module"		{ FL; VALTEXT; CALLBACK(keywordCb); return yMODULE; }
  "nand"		{ FL; VALTEXT; CALLBACK(keywordCb); return yNAND; }
  "negedge"		{ FL; VALTEXT; CALLBACK(keywordCb); return yNEGEDGE; }
  "nor"			{ FL; VALTEXT; CALLBACK(keywordCb); return yNOR; }
  "not"			{ FL; VALTEXT; CALLBACK(keywordCb); return yNOT; }
  "or"			{ FL; VALTEXT; CALLBACK(keywordCb); return yOR; }
  "output"		{ FL; VALTEXT; CALLBACK(keywordCb); return yOUTPUT; }
  "parameter"		{ FL; VALTEXT; CALLBACK(keywordCb); return yPARAMETER; }
  "posedge"		{ FL; VALTEXT; CALLBACK(keywordCb); return yPOSEDGE; }
  "primitive"		{ FL; VALTEXT; CALLBACK(keywordCb); return yMODULE; }
  "real"		{ FL; VALTEXT; CALLBACK(keywordCb); return yREAL; }
  "realtime"		{ FL; VALTEXT; CALLBACK(keywordCb); return yREALTIME; }
  "reg"			{ FL; VALTEXT; CALLBACK(keywordCb); return yREG; }
  "release"		{ FL; VALTEXT; CALLBACK(keywordCb); return yRELEASE; }
  "repeat"		{ FL; VALTEXT; CALLBACK(keywordCb); return yREPEAT; }
  "scalared"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySCALARED; }
  "specify"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySPECIFY; }
  "specparam"		{ FL; VALTEXT; CALLBACK(keywordCb); return yaTIMINGSPEC; }
  "supply0"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySUPPLY0; }
  "supply1"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySUPPLY1; }
  "table"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTABLE; }
  "task"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTASK; }
  "time"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTIME; }
  "tri"			{ FL; VALTEXT; CALLBACK(keywordCb); return yTRI; }
  "vectored"		{ FL; VALTEXT; CALLBACK(keywordCb); return yVECTORED; }
  "wait"		{ FL; VALTEXT; CALLBACK(keywordCb); return yWAIT; }
  "while"		{ FL; VALTEXT; CALLBACK(keywordCb); return yWHILE; }
  "wire"		{ FL; VALTEXT; CALLBACK(keywordCb); return yWIRE; }
  "xnor"		{ FL; VALTEXT; CALLBACK(keywordCb); return yXNOR; }
  "xor"			{ FL; VALTEXT; CALLBACK(keywordCb); return yXOR; }
  /*     Types Verilator doesn't support but we do generically here */
  "bufif0"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "bufif1"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "cmos"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "event"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenNETTYPE; }
  "highz0"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenSTRENGTH; }
  "highz1"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenSTRENGTH; }
  "large"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenSTRENGTH; }
  "medium"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenSTRENGTH; }
  "nmos"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "notif0"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "notif1"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "pmos"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "pull0"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenSTRENGTH; }
  "pull1"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenSTRENGTH; }
  "pulldown"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "pullup"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "rcmos"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "rnmos"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "rpmos"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "rtran"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "rtranif0"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "rtranif1"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "small"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenSTRENGTH; }
  "strong0"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenSTRENGTH; }
  "strong1"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenSTRENGTH; }
  "tran"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "tranif0"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "tranif1"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "tri0"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenNETTYPE; }
  "tri1"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenNETTYPE; }
  "triand"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenNETTYPE; }
  "trior"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenNETTYPE; }
  "trireg"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenNETTYPE; }
  "wand"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenNETTYPE; }
  "weak0"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenSTRENGTH; }
  "weak1"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenSTRENGTH; }
  "wor"			{ FL; VALTEXT; CALLBACK(keywordCb); return ygenNETTYPE; }
  /*     Generic unsupported warnings */
}

  /* Verilog 2001 */
<V01,V05,S05>{
  /*     Keywords*/
  "automatic"		{ FL; VALTEXT; CALLBACK(keywordCb); return yAUTOMATIC; }
  "endgenerate"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDGENERATE; }
  "generate"		{ FL; VALTEXT; CALLBACK(keywordCb); return yGENERATE; }
  "genvar"		{ FL; VALTEXT; CALLBACK(keywordCb); return yGENVAR; }
  "ifnone"		{ FL; VALTEXT; CALLBACK(keywordCb); return yaTIMINGSPEC; }
  "localparam"		{ FL; VALTEXT; CALLBACK(keywordCb); return yLOCALPARAM; }
  "noshowcancelled"	{ FL; VALTEXT; CALLBACK(keywordCb); return yaTIMINGSPEC; }
  "pulsestyle_ondetect"	{ FL; VALTEXT; CALLBACK(keywordCb); return yaTIMINGSPEC; }
  "pulsestyle_onevent"	{ FL; VALTEXT; CALLBACK(keywordCb); return yaTIMINGSPEC; }
  "showcancelled"	{ FL; VALTEXT; CALLBACK(keywordCb); return yaTIMINGSPEC; }
  "signed"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySIGNED; }
  "unsigned"		{ FL; VALTEXT; CALLBACK(keywordCb); return yUNSIGNED; }
  /*     Generic unsupported keywords */
  "cell"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; } // config
  "config"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; } // config
  "design"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; } // config
  "endconfig"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; } // config
  "incdir"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; } // config
  "include"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; } // config
  "instance"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; } // config
  "liblist"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; } // config
  "library"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; } // config
  "use"			{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; } // config
}

  /* System Verilog 2005 */
<S05>{
  /*     Keywords */
  "always_comb"		{ FL; VALTEXT; CALLBACK(keywordCb); return yALWAYS; }
  "always_ff"		{ FL; VALTEXT; CALLBACK(keywordCb); return yALWAYS; }
  "always_latch"	{ FL; VALTEXT; CALLBACK(keywordCb); return yALWAYS; }
  "assert"		{ FL; VALTEXT; CALLBACK(keywordCb); return yASSERT; }
  "do"			{ FL; VALTEXT; CALLBACK(keywordCb); return yDO; }
  "final"		{ FL; VALTEXT; CALLBACK(keywordCb); return yFINAL; }
  /*     Generic unsupported keywords */
  "alias"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "assume"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "before"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "bind"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "bins"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "binsof"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "bit"			{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "break"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "byte"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "chandle"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "class"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "clocking"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "const"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "constraint"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "context"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "continue"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "cover"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "covergroup"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "coverpoint"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "cross"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "dist"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "endcass"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "endclocking"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "endgroup"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "endinterface"	{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "endpackage"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "endprogram"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "endproperty"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "endsequence"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "enum"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "expect"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "export"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "extends"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "extern"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "first_match"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "foreach"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "forkjoin"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "iff"			{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "ignore_bins"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "illegal_bins"	{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "import"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "inside"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "int"			{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "interface"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "intersect"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "join_any"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "join_none"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "local"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "logic"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "longint"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "matches"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "modport"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "new"			{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "null"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "package"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "packed"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "priority"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "program"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "property"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "protected"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "pure"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "rand"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "randc"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "randcase"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "randsequence"	{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "ref"			{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "return"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "sequence"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "shortint"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "shortreal"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "solve"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "static"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "string"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "struct"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "super"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "tagged"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "this"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "throughout"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "timeprecision"	{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "timeunit"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "type"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "typedef"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "union"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "unique"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "var"			{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "virtual"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "void"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "wait_order"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "wildcard"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "with"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
  "within"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenKEYWORD; }
}

  /* Default PLI rule */
<V95,V01,V05,S05>{
    "$"[a-zA-Z_$][a-zA-Z0-9_$]*	{ FL; VALTEXT; CALLBACK(sysfuncCb); return ygenSYSCALL; }
}

  /************************************************************************/
  /* Single character operator thingies */
<V95,V01,V05,S05>{
  "!"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "#"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "$"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "%"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "&"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "("			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  ")"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "*"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "+"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  ","			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "-"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "."			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "/"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  ":"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  ";"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "<"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "="			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  ">"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "?"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "@"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "["			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "]"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "^"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "{"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "|"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "}"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "~"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
}

  /************************************************************************/
  /* Operators */
<V95,V01,V05,S05>{
  "&&"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_ANDAND; }
  "||"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_OROR; }
  "<="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_LTE; }
  ">="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_GTE; }
  "<<"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_SLEFT; }
  ">>"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_SRIGHT; }
  "=="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_EQUAL; }
  "!="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_NOTEQUAL; }
  "==="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_CASEEQUAL; }
  "!=="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_CASENOTEQUAL; }
  "^~"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_XNOR; }
  "~^"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_XNOR; }
  "~&"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_NAND; }
  "~|"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_NOR; }
}

  /* Verilog 2001 Operators */
<V01,V05,S05>{
  "<<<"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_SLEFT; }
  ">>>"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_SSRIGHT; }
  "**"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_POW; }
  "+:"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_PLUSCOLON; }
  "-:"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_MINUSCOLON; }
}

  /* Identifiers and numbers */
<V95,V01,V05,S05>{
  {escid}		{ if (VParseLex::symEscapeless(yytext+1,yyleng-1)) {
			      FL; CALLBACKL(symbolCb, yytext+1,yyleng-1); VALTEXTL(yytext+1,yyleng-1);
			  } else {
			      FL; CALLBACK(symbolCb); VALTEXT;
			      VParseLex::s_yylvalp->str += ' ';   /* SigParser users need to be sure to quote it */
			  }
			  return yaID; }
  {id}			{ FL; VALTEXT; CALLBACK(symbolCb); return yaID; }
  \"[^\"\\]*\"		{ FL; VALTEXT; CALLBACK(stringCb); return yaSTRING;
			}
  \" 			{ yy_push_state(STRING); yymore(); }

  [0-9]*?['']s?[bcodhBCODH][ \t]*[A-Fa-f0-9xXzZ_?]*	{
			  FL; VALTEXT; CALLBACK(numberCb); return yaINTNUM;
			}
  [0-9]*?['']s?[01xXzZ]	{	/* SystemVerilog */
			  FL; VALTEXT; CALLBACK(numberCb); return yaINTNUM;
			}
  [0-9][_0-9]*[ \t]*['']s?[bcodhBCODH]?[ \t]*[A-Fa-f0-9xXzZ_?]*	{
			  FL; VALTEXT; CALLBACK(numberCb); return yaINTNUM;
			}
  [0-9][_0-9]*		{ FL; VALTEXT; CALLBACK(numberCb); return yaINTNUM;
			}
  [0-9][_0-9]*(\.[_0-9]+)([eE][-+]?[_0-9]+)? {
                          FL; VALTEXT; CALLBACK(numberCb); return yaFLOATNUM;
			}
  [0-9][_0-9]*(\.[_0-9]+)?([eE][-+]?[_0-9]+) {
                          FL; VALTEXT; CALLBACK(numberCb); return yaFLOATNUM;
			}
}

  /************************************************************************/
  /* STRINGS */
<STRING>\n 		{ yyerror("Unterminated string\n"); }
<STRING>\r		;
<STRING>[^\"\\]* 	{ yymore(); }
<STRING>\\.	 	{ yymore(); }
<STRING>\" 		{ yy_pop_state();
			  FL; VALTEXT; CALLBACK(stringCb); return yaSTRING; }

  /************************************************************************/
  /* Multi-line COMMENTS */
<CMTMODE>"*"+[^*/\n]* 	{ yymore(); }
<CMTMODE>\n		{ yymore(); NEXTLINE(); }
<CMTMODE>"*"+"/"	{ FL; VALTEXT; CALLBACK(commentCb); yy_pop_state(); }
<CMTMODE>. 		{ yymore(); }
<CMTMODE><<EOF>>	{ yyerror("EOF in '/* ... */' block comment");
			  yyleng = 0; }

  /************************************************************************/
  /* Protected */
<PROTMODE>\n		{ yymore(); NEXTLINE(); }
<PROTMODE>"`endprotected"	{ FL; VALTEXT; CALLBACK(preprocCb); yy_pop_state(); } 
<PROTMODE>. 		{ yymore(); }
<PROTMODE><<EOF>>	{ yyerror("EOF in `protected");
			  yyleng = 0; }

  /************************************************************************/
  /* Attributes */
<ATTRMODE>\n		{ yymore(); NEXTLINE(); }
<ATTRMODE>"*)"		{ FL; VALTEXT; CALLBACK(attributeCb); yy_pop_state(); }
<ATTRMODE>. 		{ yymore(); }
<ATTRMODE><<EOF>>	{ yyerror("EOF in (*");
			  yyleng = 0; }

  /************************************************************************/
  /* Attributes */
<V95,V01,V05,S05>{
    "(*"/{ws}*[^)]	{ FL; yymore(); yy_push_state(ATTRMODE); }	// Doesn't match (*)
}

  /************************************************************************/
  /* Preprocssor */
<V95,V01,V05,S05>{
  "`celldefine"			{ FL; VALTEXT; CALLBACK(preprocCb); LEXP->m_inCellDefine=true; }
  "`endcelldefine"		{ FL; VALTEXT; CALLBACK(preprocCb); LEXP->m_inCellDefine=false; }
  "`endprotect"			{ FL; VALTEXT; CALLBACK(preprocCb); }
  "`inline"			{ FL; VALTEXT; CALLBACK(preprocCb); }
  "`line"{ws}+.*\n		{ PARSEP->inLineDirective(yytext);
			  	  FL; VALTEXT; CALLBACK(preprocCb); }
  "`portcoerce"			{ FL; VALTEXT; CALLBACK(preprocCb); }
  "`protect"			{ FL; VALTEXT; CALLBACK(preprocCb); }
  "`protected"			{ FL; VALTEXT; CALLBACK(preprocCb); yy_push_state(PROTMODE); }
  "`resetall"			{ FL; VALTEXT; CALLBACK(preprocCb); }
  "`timescale"{ws}+.*\n		{ FL; VALTEXT; CALLBACK(preprocCb); NEXTLINE(); }

  "`begin_keywords"[ \t]*\"1364-1995\"		{ yy_push_state(V95); CALLBACK(preprocCb); }
  "`begin_keywords"[ \t]*\"1364-2001\"		{ yy_push_state(V01); CALLBACK(preprocCb); }
  "`begin_keywords"[ \t]*\"1364-2001-noconfig\"	{ yy_push_state(V01); CALLBACK(preprocCb); }
  "`begin_keywords"[ \t]*\"1364-2005\"		{ yy_push_state(V05); CALLBACK(preprocCb); }
  "`begin_keywords"[ \t]*\"1800-2005\"		{ yy_push_state(S05); CALLBACK(preprocCb); }
  "`end_keywords"					{ yy_pop_state();     CALLBACK(preprocCb); }
}

  /************************************************************************/
  /* Default rules - leave last */

<V95,V01,V05,S05>{
  "`"[a-zA-Z_0-9]+	{ FL; VALTEXT;
			  if (PARSEP->sigParser()) { yyerrorf("Define or directive not defined: %s",yytext); }
			  else { CALLBACK(preprocCb); } }
  "//"[^\n]*		{ FL; VALTEXT; CALLBACK(commentCb); }
  "/*"		       	{ yy_push_state(CMTMODE); yymore(); }
  .			{ FL; VALTEXT; CALLBACK(operatorCb); return ygenOPERATOR; } /* return single char ops. */
}

  /* Catch all - absolutely last */
<*>.|\n     		{ yyerrorf("Missing VParseLex.l rule: Default rule invoked in state %d: %s", YY_START, yytext); }
%%

void VParseLex::unputString(const char* textp) {
    s_currentLexp = this;
    // Add characters to input stream in back-to-front order
    const char* cp;
    for (cp = textp; *cp; cp++);
    for (cp--; cp >= textp; cp--) {
	unput(*cp);
    }
}

void VParseLex::unused() {
    if (0) {
	// Prevent unused warnings
	yy_top_state();
    }
}

int VParseLex::lexToken(VParseBisonYYSType* yylvalp) {
    s_currentLexp = this;
    if (m_ahead) {
	// We prefetched a extra token, give it back
	m_ahead = false;
	*yylvalp = m_aheadVal;
	return m_aheadToken;
    }
    // Parse new token
    s_yylvalp = yylvalp;
    int token = yylex();
    // If a paren, read another
    if (token == '(') {
#ifdef FLEX_DEBUG
	if (yy_flex_debug) { cout<<"   lexToken: reading ahead to find possible strength"<<endl; }
#endif
	s_yylvalp = &m_aheadVal;
	int nexttok = yylex();
	m_ahead = true;
	m_aheadToken = nexttok;
	// Now potentially munge the current token
	if (token == '(' && (nexttok == ygenSTRENGTH
			     || nexttok == ySUPPLY0
			     || nexttok == ySUPPLY1)) {
	    token = yP_PARSTRENGTH;
	}
    }
    return token;
}

void VParseLex::debug(int level) {
#ifdef FLEX_DEBUG
    yy_flex_debug = level;
#endif
}

/*###################################################################
 * Local Variables:
 * mode: C++
 * End:
 */
