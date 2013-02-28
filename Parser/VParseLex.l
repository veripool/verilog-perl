%option align interactive
%option stack
%option noc++
%option prefix="VParseLex"
%{
/**************************************************************************
 * DESCRIPTION: Verilog Parser Lexer
 *
 * This file is part of Verilog-Perl.
 *
 * Author: Wilson Snyder <wsnyder@wsnyder.org>
 *
 * Code available from: http://www.veripool.org/systemperl
 *
 **************************************************************************
 *
 * Copyright 2000-2013 by Wilson Snyder.  This program is free software;
 * you can redistribute it and/or modify it under the terms of either the
 * GNU Lesser General Public License Version 3 or the Perl Artistic License
 * Version 2.0.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 **************************************************************************
 * Do not use Flex in C++ mode.  It has bugs with yyunput() which result in
 * lost characters.
 *************************************************************************/

#include "VParseLex.h"
#include <cstdio>
#include <iostream>
#include <cstdarg>
#include <cstring>

#include "VParseGrammar.h"
#include "VParseBison.h"

#define YY_SKIP_YYWRAP

#define STATE_VERILOG_RECENT  S12		// State name for most recent Verilog Version

// Flex 2.5.35 has compile warning in ECHO, so we'll default our own rule
#define ECHO yyerrorf("Missing VParseLex.l rule: ECHO rule invoked in state %d: %s", YY_START, yytext);

VParseLex* VParseLex::s_currentLexp = NULL;	// Current lexing point
VParseBisonYYSType* VParseLex::s_yylvalp = NULL;		// LValue for current bison object

#define LEXP (VParseLex::s_currentLexp)
#define LPARSEP (LEXP->m_parsep)

#define NEXTLINE()  { LPARSEP->inFilelineInc(); }
#define LINECHECK()  { const char* cp=yytext; for (int n=yyleng; n; --n) if (cp[n]=='\n') NEXTLINE(); }

#define FL { VParseLex::s_yylvalp->fl = LPARSEP->inFilelinep(); }

// lval.fileline not used yet; here for Verilator parser compatibility
#define VALTEXTS(strg) VParseLex::s_yylvalp->str = strg
#define VALTEXT   VALTEXTS(string(yytext,yyleng))
#define CALLBACKS(whichCb,strg) {LPARSEP->whichCb(VParseLex::s_yylvalp->fl, strg); }
#define CALLBACK(whichCb) CALLBACKS(whichCb,string(yytext,yyleng))

#define YY_INPUT(buf,result,max_size) \
    result = LPARSEP->inputToLex(buf,max_size);

int yywrap() { return LPARSEP->eofToLex(); }

#define StashPrefix LPARSEP->unreadbackCat(yytext,yyleng)

void yyerror(char* errmsg) {
    LPARSEP->inFilelinep()->error(errmsg);
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

%s V95 V01 V05 S05 S09 S12
%s STRING ATTRMODE
%s CMTMODE PROTMODE
%s DUMMY_TO_AVOID_WARNING

space	[ ]
ws	[ \t\f\r]+
crnl	[\r]*[\n]
	/* identifier */
id	[a-zA-Z_][a-zA-Z0-9_$]*
	/* escaped identifier */
escid	\\[^ \t\f\r\n]+
word	[a-zA-Z0-9_]+

%%

<INITIAL>.|\n 		{BEGIN STATE_VERILOG_RECENT; yyless(0); }

  /* Verilog 1995 */
<V95,V01,V05,S05,S09,S12>{
  {ws}			{ StashPrefix; }	/* otherwise ignore white-space */
  {crnl}		{ StashPrefix; NEXTLINE(); }		/* Count line numbers */
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
  "edge"		{ FL; VALTEXT; CALLBACK(keywordCb); return yEDGE; }
  "else"		{ FL; VALTEXT; CALLBACK(keywordCb); return yELSE; }
  "end"			{ FL; VALTEXT; CALLBACK(keywordCb); return yEND; }
  "endcase"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDCASE; }
  "endfunction"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDFUNCTION; }
  "endmodule"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDMODULE; }
  "endprimitive"	{ FL; VALTEXT; CALLBACK(keywordCb); return yENDMODULE; }
  "endspecify"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDSPECIFY; }
  "endtable"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDTABLE; }
  "endtask"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDTASK; }
  "event"		{ FL; VALTEXT; CALLBACK(keywordCb); return yEVENT; }
  "for"			{ FL; VALTEXT; CALLBACK(keywordCb); return yFOR; }
  "force"		{ FL; VALTEXT; CALLBACK(keywordCb); return yFORCE; }
  "forever"		{ FL; VALTEXT; CALLBACK(keywordCb); return yFOREVER; }
  "fork"		{ FL; VALTEXT; CALLBACK(keywordCb); return yFORK; }
  "function"		{ FL; VALTEXT; CALLBACK(keywordCb); return yFUNCTION__LEX; }
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
  "specparam"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySPECPARAM; }
  "supply0"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySUPPLY0; }
  "supply1"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySUPPLY1; }
  "table"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTABLE; }
  "task"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTASK__LEX; }
  "time"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTIME; }
  "tri"			{ FL; VALTEXT; CALLBACK(keywordCb); return yTRI; }
  "tri0"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTRI0; }
  "tri1"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTRI1; }
  "triand"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTRIAND; }
  "trior"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTRIOR; }
  "trireg"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTRIREG; }
  "vectored"		{ FL; VALTEXT; CALLBACK(keywordCb); return yVECTORED; }
  "wait"		{ FL; VALTEXT; CALLBACK(keywordCb); return yWAIT; }
  "wand"		{ FL; VALTEXT; CALLBACK(keywordCb); return yWAND; }
  "while"		{ FL; VALTEXT; CALLBACK(keywordCb); return yWHILE; }
  "wire"		{ FL; VALTEXT; CALLBACK(keywordCb); return yWIRE; }
  "wor"			{ FL; VALTEXT; CALLBACK(keywordCb); return yWOR; }
  "xnor"		{ FL; VALTEXT; CALLBACK(keywordCb); return yXNOR; }
  "xor"			{ FL; VALTEXT; CALLBACK(keywordCb); return yXOR; }
  /*     Types Verilator doesn't support but we do generically here */
  "bufif0"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "bufif1"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
  "cmos"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenGATE; }
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
  "weak0"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenSTRENGTH; }
  "weak1"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenSTRENGTH; }
  /*     Generic unsupported warnings */
}

  /* Verilog 2001 */
<V01,V05,S05,S09,S12>{
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
  "cell"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenCONFIGKEYWORD; }
  "config"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenCONFIGKEYWORD; }
  "design"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenCONFIGKEYWORD; }
  "endconfig"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenCONFIGKEYWORD; }
  "incdir"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenCONFIGKEYWORD; }
  "include"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenCONFIGKEYWORD; }
  "instance"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenCONFIGKEYWORD; }
  "liblist"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenCONFIGKEYWORD; }
  "library"		{ FL; VALTEXT; CALLBACK(keywordCb); return ygenCONFIGKEYWORD; }
  "use"			{ FL; VALTEXT; CALLBACK(keywordCb); return ygenCONFIGKEYWORD; }
}

  /* Verilog 2005 */
<V05,S05,S09,S12>{
  /*     Keywords */
  "uwire"		{ FL; VALTEXT; CALLBACK(keywordCb); return yWIRE; }
}

  /* System Verilog 2005 */
<S05,S09,S12>{
  /*     System Tasks */
  "$error"		{ FL; VALTEXT; CALLBACK(keywordCb); return yD_ERROR; }
  "$fatal"		{ FL; VALTEXT; CALLBACK(keywordCb); return yD_FATAL; }
  "$info"		{ FL; VALTEXT; CALLBACK(keywordCb); return yD_INFO; }
  "$root"		{ FL; VALTEXT; CALLBACK(keywordCb); return yD_ROOT; }
  "$unit"		{ FL; VALTEXT; CALLBACK(keywordCb); return yD_UNIT; }
  "$warning"		{ FL; VALTEXT; CALLBACK(keywordCb); return yD_WARNING; }
  /*     Keywords */
  "alias"		{ FL; VALTEXT; CALLBACK(keywordCb); return yALIAS; }
  "always_comb"		{ FL; VALTEXT; CALLBACK(keywordCb); return yALWAYS; }
  "always_ff"		{ FL; VALTEXT; CALLBACK(keywordCb); return yALWAYS; }
  "always_latch"	{ FL; VALTEXT; CALLBACK(keywordCb); return yALWAYS; }
  "assert"		{ FL; VALTEXT; CALLBACK(keywordCb); return yASSERT; }
  "assume"		{ FL; VALTEXT; CALLBACK(keywordCb); return yASSUME; }
  "before"		{ FL; VALTEXT; CALLBACK(keywordCb); return yBEFORE; }
  "bind"		{ FL; VALTEXT; CALLBACK(keywordCb); return yBIND; }
  "bins"		{ FL; VALTEXT; CALLBACK(keywordCb); return yBINS; }
  "binsof"		{ FL; VALTEXT; CALLBACK(keywordCb); return yBINSOF; }
  "bit"			{ FL; VALTEXT; CALLBACK(keywordCb); return yBIT; }
  "break"		{ FL; VALTEXT; CALLBACK(keywordCb); return yBREAK; }
  "byte"		{ FL; VALTEXT; CALLBACK(keywordCb); return yBYTE; }
  "chandle"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCHANDLE; }
  "class"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCLASS; }
  "clocking"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCLOCKING; }
  "const"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCONST__LEX; }
  "constraint"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCONSTRAINT; }
  "context"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCONTEXT; }
  "continue"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCONTINUE; }
  "cover"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCOVER; }
  "covergroup"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCOVERGROUP; }
  "coverpoint"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCOVERPOINT; }
  "cross"		{ FL; VALTEXT; CALLBACK(keywordCb); return yCROSS; }
  "dist"		{ FL; VALTEXT; CALLBACK(keywordCb); return yDIST; }
  "do"			{ FL; VALTEXT; CALLBACK(keywordCb); return yDO; }
  "endclass"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDCLASS; }
  "endclocking"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDCLOCKING; }
  "endgroup"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDGROUP; }
  "endinterface"	{ FL; VALTEXT; CALLBACK(keywordCb); return yENDINTERFACE; }
  "endpackage"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDPACKAGE; }
  "endprogram"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDPROGRAM; }
  "endproperty"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDPROPERTY; }
  "endsequence"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENDSEQUENCE; }
  "enum"		{ FL; VALTEXT; CALLBACK(keywordCb); return yENUM; }
  "expect"		{ FL; VALTEXT; CALLBACK(keywordCb); return yEXPECT; }
  "export"		{ FL; VALTEXT; CALLBACK(keywordCb); return yEXPORT; }
  "extends"		{ FL; VALTEXT; CALLBACK(keywordCb); return yEXTENDS; }
  "extern"		{ FL; VALTEXT; CALLBACK(keywordCb); return yEXTERN; }
  "final"		{ FL; VALTEXT; CALLBACK(keywordCb); return yFINAL; }
  "first_match"		{ FL; VALTEXT; CALLBACK(keywordCb); return yFIRST_MATCH; }
  "foreach"		{ FL; VALTEXT; CALLBACK(keywordCb); return yFOREACH; }
  "forkjoin"		{ FL; VALTEXT; CALLBACK(keywordCb); return yFORKJOIN; }
  "iff"			{ FL; VALTEXT; CALLBACK(keywordCb); return yIFF; }
  "ignore_bins"		{ FL; VALTEXT; CALLBACK(keywordCb); return yIGNORE_BINS; }
  "illegal_bins"	{ FL; VALTEXT; CALLBACK(keywordCb); return yILLEGAL_BINS; }
  "import"		{ FL; VALTEXT; CALLBACK(keywordCb); return yIMPORT; }
  "inside"		{ FL; VALTEXT; CALLBACK(keywordCb); return yINSIDE; }
  "int"			{ FL; VALTEXT; CALLBACK(keywordCb); return yINT; }
  "interface"		{ FL; VALTEXT; CALLBACK(keywordCb); return yINTERFACE; }
  "intersect"		{ FL; VALTEXT; CALLBACK(keywordCb); return yINTERSECT; }
  "join_any"		{ FL; VALTEXT; CALLBACK(keywordCb); return yJOIN; }
  "join_none"		{ FL; VALTEXT; CALLBACK(keywordCb); return yJOIN; }
  "local"		{ FL; VALTEXT; CALLBACK(keywordCb); return yLOCAL__LEX; }
  "logic"		{ FL; VALTEXT; CALLBACK(keywordCb); return yLOGIC; }
  "longint"		{ FL; VALTEXT; CALLBACK(keywordCb); return yLONGINT; }
  "matches"		{ FL; VALTEXT; CALLBACK(keywordCb); return yMATCHES; }
  "modport"		{ FL; VALTEXT; CALLBACK(keywordCb); return yMODPORT; }
  "new"			{ FL; VALTEXT; CALLBACK(keywordCb); return yNEW__LEX; }
  "null"		{ FL; VALTEXT; CALLBACK(keywordCb); return yNULL; }
  "package"		{ FL; VALTEXT; CALLBACK(keywordCb); return yPACKAGE; }
  "packed"		{ FL; VALTEXT; CALLBACK(keywordCb); return yPACKED; }
  "priority"		{ FL; VALTEXT; CALLBACK(keywordCb); return yPRIORITY; }
  "program"		{ FL; VALTEXT; CALLBACK(keywordCb); return yPROGRAM; }
  "property"		{ FL; VALTEXT; CALLBACK(keywordCb); return yPROPERTY; }
  "protected"		{ FL; VALTEXT; CALLBACK(keywordCb); return yPROTECTED; }
  "pure"		{ FL; VALTEXT; CALLBACK(keywordCb); return yPURE; }
  "rand"		{ FL; VALTEXT; CALLBACK(keywordCb); return yRAND; }
  "randc"		{ FL; VALTEXT; CALLBACK(keywordCb); return yRANDC; }
  "randcase"		{ FL; VALTEXT; CALLBACK(keywordCb); return yRANDCASE; }
  "randsequence"	{ FL; VALTEXT; CALLBACK(keywordCb); return yRANDSEQUENCE; }
  "ref"			{ FL; VALTEXT; CALLBACK(keywordCb); return yREF; }
  "return"		{ FL; VALTEXT; CALLBACK(keywordCb); return yRETURN; }
  "sequence"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySEQUENCE; }
  "shortint"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySHORTINT; }
  "shortreal"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySHORTREAL; }
  "solve"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySOLVE; }
  "static"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySTATIC__LEX; }
  "string"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySTRING; }
  "struct"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySTRUCT; }
  "super"		{ FL; VALTEXT; CALLBACK(keywordCb); return ySUPER; }
  "tagged"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTAGGED; }
  "this"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTHIS; }
  "throughout"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTHROUGHOUT; }
  "timeprecision"	{ FL; VALTEXT; CALLBACK(keywordCb); return yTIMEPRECISION; }
  "timeunit"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTIMEUNIT; }
  "type"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTYPE; }
  "typedef"		{ FL; VALTEXT; CALLBACK(keywordCb); return yTYPEDEF; }
  "union"		{ FL; VALTEXT; CALLBACK(keywordCb); return yUNION; }
  "unique"		{ FL; VALTEXT; CALLBACK(keywordCb); return yUNIQUE; }
  "var"			{ FL; VALTEXT; CALLBACK(keywordCb); return yVAR; }
  "virtual"		{ FL; VALTEXT; CALLBACK(keywordCb); return yVIRTUAL__LEX; }
  "void"		{ FL; VALTEXT; CALLBACK(keywordCb); return yVOID; }
  "wait_order"		{ FL; VALTEXT; CALLBACK(keywordCb); return yWAIT_ORDER; }
  "wildcard"		{ FL; VALTEXT; CALLBACK(keywordCb); return yWILDCARD; }
  "with"		{ FL; VALTEXT; CALLBACK(keywordCb); return yWITH__LEX; }
  "within"		{ FL; VALTEXT; CALLBACK(keywordCb); return yWITHIN; }
}

  /* System Verilog 2009 */
<S09,S12>{
  /*     Keywords */
  "accept_on"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yACCEPT_ON; }
  "checker"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yCHECKER; }
  "endchecker"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yENDCHECKER; }
  "eventually"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yEVENTUALLY; }
  "global"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yGLOBAL__LEX; }
  "implies"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yIMPLIES; }
  "let"		 	{ FL; VALTEXT; CALLBACK(keywordCb); return yLET; }
  "nexttime"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yNEXTTIME; }
  "reject_on"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yREJECT_ON; }
  "restrict"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yRESTRICT; }
  "s_always"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yS_ALWAYS; }
  "s_eventually" 	{ FL; VALTEXT; CALLBACK(keywordCb); return yS_EVENTUALLY; }
  "s_nexttime"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yS_NEXTTIME; }
  "s_until"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yS_UNTIL; }
  "s_until_with" 	{ FL; VALTEXT; CALLBACK(keywordCb); return yS_UNTIL_WITH; }
  "strong"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return ySTRONG; }
  "sync_accept_on" 	{ FL; VALTEXT; CALLBACK(keywordCb); return ySYNC_ACCEPT_ON; }
  "sync_reject_on" 	{ FL; VALTEXT; CALLBACK(keywordCb); return ySYNC_REJECT_ON; }
  "unique0"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yUNIQUE0; }
  "until"		{ FL; VALTEXT; CALLBACK(keywordCb); return yUNTIL; }
  "until_with"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yUNTIL_WITH; }
  "untyped"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yUNTYPED; }
  "weak"            	{ FL; VALTEXT; CALLBACK(keywordCb); return yWEAK; }
}

  /* System Verilog 2012 */
<S12>{
  /*     Keywords */
  "implements"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yIMPLEMENTS; }
  "interconnect" 	{ FL; VALTEXT; CALLBACK(keywordCb); return yINTERCONNECT; }
  "nettype"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return yNETTYPE; }
  "soft"	 	{ FL; VALTEXT; CALLBACK(keywordCb); return ySOFT; }
}

  /* Default PLI rule */
<V95,V01,V05,S05,S09,S12>{
    "$"[a-zA-Z_$][a-zA-Z0-9_$]*	{ FL; VALTEXT; CALLBACK(sysfuncCb); return ygenSYSCALL; }
}

  /************************************************************************/

  /* Single character operator thingies */
<V95,V01,V05,S05,S09,S12>{
  "{"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "}"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
}
<V95,V01,V05,S05,S09,S12>{
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
  "|"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
  "~"			{ FL; VALTEXT; CALLBACK(operatorCb); return yytext[0]; }
}

  /************************************************************************/
  /* Operators and multi-character symbols */

  /* Verilog 1995 Operators */
<V95,V01,V05,S05,S09,S12>{
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
  "->"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_MINUSGT; }
  "=>"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_EQGT; }
  "*>"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_ASTGT; }
  "&&&"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_ANDANDAND; }
}

  /* Verilog 2001 Operators */
<V01,V05,S05,S09,S12>{
  "<<<"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_SLEFT; }
  ">>>"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_SSRIGHT; }
  "**"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_POW; }
  "+:"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_PLUSCOLON; }
  "-:"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_MINUSCOLON; }
  ".*"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_DOTSTAR; }
}

  /* SystemVerilog 2005 Operators */
<S05,S09,S12>{
  "'"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_TICK; }
  "'{"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_TICKBRA; }
  "==?"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_WILDEQUAL; }
  "!=?"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_WILDNOTEQUAL; }
  "++"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_PLUSPLUS; }
  "--"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_MINUSMINUS; }
  "+="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_PLUSEQ; }
  "-="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_MINUSEQ; }
  "*="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_TIMESEQ; }
  "/="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_DIVEQ; }
  "%="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_MODEQ; }
  "&="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_ANDEQ; }
  "|="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_OREQ; }
  "^="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_XOREQ; }
  "<<="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_SLEFTEQ; }
  ">>="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_SRIGHTEQ; }
  "<<<="		{ FL; VALTEXT; CALLBACK(operatorCb); return yP_SLEFTEQ; }
  ">>>="		{ FL; VALTEXT; CALLBACK(operatorCb); return yP_SSRIGHTEQ; }
  "->>"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_MINUSGTGT; }
  "##"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_POUNDPOUND; }
  "@@"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_ATAT; }
  "::"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_COLONCOLON; }
  ":="			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_COLONEQ; }
  ":/"[^\/\*]		{ FL; VALTEXT; CALLBACK(operatorCb); return yP_COLONDIV; }  /* : then comment is not ":/" */
  "|->"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_ORMINUSGT; }
  "|=>"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_OREQGT; }
  /* Some simulators allow whitespace here. Grr */
  "["{ws}*"*"		{ FL; VALTEXT; CALLBACK(operatorCb); return yP_BRASTAR; }
  "["{ws}*"="		{ FL; VALTEXT; CALLBACK(operatorCb); return yP_BRAEQ; }
  "["{ws}*"->"		{ FL; VALTEXT; CALLBACK(operatorCb); return yP_BRAMINUSGT; }
  "["{ws}*"+"{ws}*"]"	{ FL; VALTEXT; CALLBACK(operatorCb); return yP_BRAPLUSKET; }
}

  /* SystemVerilog 2009 Operators */
<S09,S12>{
  "#-#"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_POUNDMINUSPD; }
  "#=#"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_POUNDEQPD; }
  "<->"			{ FL; VALTEXT; CALLBACK(operatorCb); return yP_LTMINUSGT; }
}

  /* Identifiers and numbers */
<V95,V01,V05,S05,S09,S12>{
  /* Consume a following space, as we're going to add one to the symbol, we'd like to avoid inserting an extra */
  {escid}{space}	{ if (VParseLex::symEscapeless(yytext+1,yyleng-1-1)) {
			      string sym = string(yytext+1,yyleng-1-1);
			      FL; CALLBACKS(symbolCb, sym); VALTEXTS(sym); unput(' ');
			  } else {
			      string sym = string(yytext,yyleng-1) + ' ';
			      FL; CALLBACKS(symbolCb, sym); VALTEXTS(sym);
			  }
			  return yaID__LEX; }
  {escid}		{ if (VParseLex::symEscapeless(yytext+1,yyleng-1)) {
			      string sym = string(yytext+1,yyleng-1);
			      FL; CALLBACKS(symbolCb, sym); VALTEXTS(sym);
			  } else {
			      string sym = string(yytext,yyleng) + ' ';
			      FL; CALLBACKS(symbolCb, sym); VALTEXTS(sym);
			  }
			  return yaID__LEX; }
  {id}			{ FL; VALTEXT; CALLBACK(symbolCb); return yaID__LEX; }
  \"[^\"\\]*\"		{ FL; VALTEXT; CALLBACK(stringCb); return yaSTRING;
			}
  \" 			{ yy_push_state(STRING); yymore(); }

  [0-9]*?['']s?[bcodhBCODH][ \t\n]*[A-Fa-f0-9xXzZ_?]*	{
			  FL; VALTEXT; LINECHECK(); CALLBACK(numberCb); return yaINTNUM;
			}
  [0-9]*?['']s?[01xXzZ]	{	/* SystemVerilog */
			  FL; VALTEXT; CALLBACK(numberCb); return yaINTNUM;
			}
  /* Note below is constructed to not match the ' that begins a '(  or '{ */
  [0-9][_0-9]*[ \t\n]*['']s?[bcodhBCODH]?[ \t]*[A-Fa-f0-9xXzZ_?]+	{
			  FL; VALTEXT; LINECHECK(); CALLBACK(numberCb); return yaINTNUM;
			}
  [0-9][_0-9]*[ \t\n]*['']s?[bcodhBCODH]	{
			  FL; VALTEXT; LINECHECK(); CALLBACK(numberCb); return yaINTNUM;
			}
  [0-9][_0-9]*[ \t\n]*['']s	{
			  FL; VALTEXT; LINECHECK(); CALLBACK(numberCb); return yaINTNUM;
			}
  [0-9][_0-9]*		{
			  FL; VALTEXT; CALLBACK(numberCb); return yaINTNUM;
			}
  [0-9][_0-9]*(\.[_0-9]+)([eE][-+]?[_0-9]+)? {
                          FL; VALTEXT; CALLBACK(numberCb); return yaFLOATNUM;
			}
  [0-9][_0-9]*(\.[_0-9]+)?([eE][-+]?[_0-9]+) {
                          FL; VALTEXT; CALLBACK(numberCb); return yaFLOATNUM;
			}
  [0-9][_0-9]*(\.[_0-9]+)?(fs|ps|ns|us|ms|s|step) {
                          FL; VALTEXT; CALLBACK(numberCb); return yaTIMENUM;
			}
}

  /************************************************************************/
  /* STRINGS */
<STRING><<EOF>>		{ yyerrorf("EOF in unterminated string"); yyleng = 0; yy_pop_state(); }
<STRING>{crnl}		{ yyerrorf("Unterminated string"); NEXTLINE(); }
<STRING>\\{crnl}	{ yymore(); NEXTLINE(); }
<STRING>\\.	 	{ yymore(); }
<STRING>\" 		{ yy_pop_state();
			  FL; VALTEXT; CALLBACK(stringCb); return yaSTRING; }
<STRING>{word}		{ yymore(); }
<STRING>.		{ yymore(); }

  /************************************************************************/
  /* Multi-line COMMENTS */
<CMTMODE>"*"+[^*/\n]* 	{ yymore(); }
<CMTMODE>\n		{ yymore(); NEXTLINE(); }
<CMTMODE>"*"+"/"	{ VALTEXT; CALLBACK(commentCb); yy_pop_state(); } // No FL; it's at comment begin
<CMTMODE>{word}		{ yymore(); }
<CMTMODE>. 		{ yymore(); }
<CMTMODE><<EOF>>	{ yyerrorf("EOF in '/* ... */' block comment");
			  yyleng = 0; yy_pop_state(); }

  /************************************************************************/
  /* Protected */
<PROTMODE>\n		{ yymore(); NEXTLINE(); }
<PROTMODE>"`endprotected"	{ FL; VALTEXT; CALLBACK(preprocCb); yy_pop_state(); }
<PROTMODE>. 		{ yymore(); }
<PROTMODE>{word}	{ yymore(); }
<PROTMODE><<EOF>>	{ yyerrorf("EOF in `protected");
			  yyleng = 0; yy_pop_state(); }

  /************************************************************************/
  /* Attributes */
<ATTRMODE>{crnl}	{ yymore(); NEXTLINE(); }
<ATTRMODE>"*)"		{ FL; VALTEXT; CALLBACK(attributeCb); yy_pop_state(); }
<ATTRMODE>{word}	{ yymore(); }
<ATTRMODE>. 		{ yymore(); }
<ATTRMODE><<EOF>>	{ yyerrorf("EOF in (*");
			  yyleng = 0; yy_pop_state(); }

  /************************************************************************/
  /* Attributes */
  /* Note simulators vary in support for "(* /_*something*_/ foo*)" where _ doesn't exist */
<V95,V01,V05,S05,S09,S12>{
    "(*"({ws}|{crnl})*({id}|{escid})	{ yymore(); yy_push_state(ATTRMODE); }	// Doesn't match (*), but (* attr_spec
}

  /************************************************************************/
  /* Preprocessor */
<V95,V01,V05,S05,S09,S12>{
  "`accelerate"				{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`autoexpand_vectornets"		{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`celldefine"				{ FL; VALTEXT; CALLBACK(preprocCb); LEXP->m_inCellDefine=true; }
  "`default_decay_time"{ws}+[^\n\r]*	{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog spec - delays only
  "`default_nettype"{ws}+[a-zA-Z0-9]*	{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog 2001
  "`default_trireg_strength"{ws}+[^\n\r]*	{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog 2009
  "`delay_mode_distributed"		{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog spec - delays only
  "`delay_mode_path"			{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog spec - delays only
  "`delay_mode_unit"			{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog spec - delays only
  "`delay_mode_zero"			{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog spec - delays only
  "`disable_portfaults"			{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`enable_portfaults"			{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`endcelldefine"			{ FL; VALTEXT; CALLBACK(preprocCb); LEXP->m_inCellDefine=false; }
  "`endprotect"				{ FL; VALTEXT; CALLBACK(preprocCb); }
  "`expand_vectornets"			{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`inline"				{ FL; VALTEXT; CALLBACK(preprocCb); }
  "`line"{ws}+[^\n\r]*{crnl}		{ LPARSEP->inLineDirective(yytext); FL; VALTEXT; CALLBACK(preprocCb); }
  "`noaccelerate"			{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`noexpand_vectornets"		{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`noremove_gatenames"			{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`noremove_netnames"			{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`nosuppress_faults"			{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`nounconnected_drive"		{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`portcoerce"				{ FL; VALTEXT; CALLBACK(preprocCb); }
  "`pragma"{ws}+[^\n\r]*		{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog 2005
  "`protect"				{ FL; VALTEXT; CALLBACK(preprocCb); }
  "`protected"				{ FL; VALTEXT; CALLBACK(preprocCb); yy_push_state(PROTMODE); }
  "`remove_gatenames"			{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`remove_netnames"			{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`resetall"				{ FL; VALTEXT; CALLBACK(preprocCb); }
  "`suppress_faults"			{ FL; VALTEXT; CALLBACK(preprocCb); } // Verilog-XL compatibility
  "`timescale"{ws}+[^\n\r]*		{ FL; VALTEXT; CALLBACK(preprocCb); }

  /* See also setLanguage below */
  "`begin_keywords"[ \t]*\"1364-1995\"		{ yy_push_state(V95); CALLBACK(preprocCb); }
  "`begin_keywords"[ \t]*\"1364-2001\"		{ yy_push_state(V01); CALLBACK(preprocCb); }
  "`begin_keywords"[ \t]*\"1364-2001-noconfig\"	{ yy_push_state(V01); CALLBACK(preprocCb); }
  "`begin_keywords"[ \t]*\"1364-2005\"		{ yy_push_state(V05); CALLBACK(preprocCb); }
  "`begin_keywords"[ \t]*\"1800-2005\"		{ yy_push_state(S05); CALLBACK(preprocCb); }
  "`begin_keywords"[ \t]*\"1800-2009\"		{ yy_push_state(S09); CALLBACK(preprocCb); }
  "`begin_keywords"[ \t]*\"1800-2012\"		{ yy_push_state(S12); CALLBACK(preprocCb); }
  "`end_keywords"				{ yy_pop_state();     CALLBACK(preprocCb); }
}

  /************************************************************************/
  /* Default rules - leave last */

<V95,V01,V05,S05,S09,S12>{
  "`"[a-zA-Z_0-9]+	{ FL; VALTEXT;
			  if (LPARSEP->sigParser()) { yyerrorf("Define or directive not defined: %s",yytext); }
			  else { CALLBACK(preprocCb); } }
  "//"[^\n]*		{ FL; VALTEXT; CALLBACK(commentCb); }  /* throw away single line comments */
  "/*"		       	{ FL; yy_push_state(CMTMODE); yymore(); }  // FL; marks start for COMMENT callback
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
    // Fetch next token from prefetch or real lexer
    s_currentLexp = this;
    int token;
    if (m_ahead) {
	// We prefetched an extra token, give it back
	m_ahead = false;
	token = m_aheadToken;
	*yylvalp = m_aheadVal;
    } else {
	// Parse new token
	s_yylvalp = yylvalp;  // Read by yylex()
	token = yylex();
    }
    // If a paren, read another
    if (token == '('
	|| token == yCONST__LEX
	|| token == yGLOBAL__LEX
	|| token == yLOCAL__LEX
	|| token == yNEW__LEX
	|| token == ySTATIC__LEX
	|| token == yVIRTUAL__LEX
	|| token == yWITH__LEX
	// Never put yID_* here; below symbol table resolution would break
	) {
#ifdef FLEX_DEBUG
	if (yy_flex_debug) { cout<<"   lexToken: reading ahead to find possible strength"<<endl; }
#endif
	VParseBisonYYSType curValue = *s_yylvalp;  // Remember value, as about to read ahead
	int nexttok = yylex();
	m_ahead = true;
	m_aheadToken = nexttok;
	m_aheadVal = *s_yylvalp;
	*s_yylvalp = curValue;
	// Now potentially munge the current token
	if (token == '(' && (nexttok == ygenSTRENGTH
			     || nexttok == ySUPPLY0
			     || nexttok == ySUPPLY1)) {
	    token = yP_PAR__STRENGTH;
	}
	else if (token == yCONST__LEX) {
	    if (nexttok == yREF) token = yCONST__REF;
	    else token = yCONST__ETC;
	}
	else if (token == yGLOBAL__LEX) {
	    if (nexttok == yCLOCKING) token = yGLOBAL__CLOCKING;
	    else { token = yaID__LEX; s_yylvalp->str = "global"; }  // Avoid 2009 "global" conflicting with old code when we can
	}
	else if (token == yLOCAL__LEX) {
	    if (nexttok == yP_COLONCOLON) token = yLOCAL__COLONCOLON;
	    else token = yLOCAL__ETC;
	}
	else if (token == yNEW__LEX) {
	    if (nexttok == '(') token = yNEW__PAREN;
	    else token = yNEW__ETC;
	}
	else if (token == ySTATIC__LEX) {
	    if (nexttok == yCONSTRAINT) token = ySTATIC__CONSTRAINT;
	    else token = ySTATIC__ETC;
	}
	else if (token == yVIRTUAL__LEX) {
	    if (nexttok == yCLASS) token = yVIRTUAL__CLASS;
	    else if (nexttok == yINTERFACE) token = yVIRTUAL__INTERFACE;
	    else if (nexttok == yaID__ETC || nexttok == yaID__LEX)
		     // || nexttok == yaID__aINTERFACE	// but we may not know interfaces yet.
		token = yVIRTUAL__anyID;
	    else token = yVIRTUAL__ETC;
	}
	else if (token == yWITH__LEX) {
	    if (nexttok == '(') token = yWITH__PAREN;
	    else if (nexttok == '[') token = yWITH__BRA;
	    else if (nexttok == '{') token = yWITH__CUR;
	    else token = yWITH__ETC;
	}
	// If add to above "else if", also add to "if (token" further above
    }

    // Non-lookahead conversions
    // If a function/task convert token based on earlier detection of yPURE yVIRTUAL
    switch (token) {
    case yPURE:
	m_pvstate = 1;  // found pure
	break;
    case yVIRTUAL__ETC:
	if (m_pvstate == 1) m_pvstate = 2;  // found pure virtual
	else m_pvstate = 0;
	break;
    case yFUNCTION__LEX:
	token = (m_pvstate==2) ? yFUNCTION__aPUREV : yFUNCTION__ETC;
	m_pvstate = 0;
	break;
    case yTASK__LEX:
	token = (m_pvstate==2) ? yTASK__aPUREV : yTASK__ETC;
	m_pvstate = 0;
	break;
    case ';':  // Just to be safe
	m_pvstate = 0;
	break;
    default:
	if (m_pvstate == 1) m_pvstate = 0;
	break;
    }

    // If an id, change the type based on symbol table
    // Note above sometimes converts yGLOBAL to a yaID__LEX
    s_yylvalp->scp = NULL;
    if (token == yaID__LEX) {
	VAstEnt* scp;
	if (VAstEnt* look_underp = LPARSEP->symTableNextId()) {
	    if (yy_flex_debug) { cout<<"   lexToken: next id lookup forced under "<<look_underp
				     <<" for \""<<s_yylvalp->str.c_str()<<"\""<<endl; }
	    scp = look_underp->findSym(s_yylvalp->str.c_str());
	    // "consume" it.  Must set again if want another token under temp scope
	    LPARSEP->symTableNextId(NULL);
	} else {
	    scp = LPARSEP->syms().findEntUpward(s_yylvalp->str);
	}
	if (scp) {
	    s_yylvalp->scp = scp;
	    switch (scp->type()) {
	    case VAstType::CLASS:	token = yaID__aCLASS;	    break;
	    case VAstType::PACKAGE:	token = yaID__aPACKAGE;	    break;
	    case VAstType::COVERGROUP:	token = yaID__aCOVERGROUP;  break;
	    case VAstType::TYPE:	token = yaID__aTYPE;	    break;
	    default:			token = yaID__ETC;	    break;
	    }
	} else {  // Not found
	    token = yaID__ETC;
	}
    }
    return token;
}

int VParseLex::lexToBison(VParseBisonYYSType* yylvalp) {
    int tok = lexToken(yylvalp);
    if (yy_flex_debug || LPARSEP->debug()>=6) {  // When debugging flex OR bison
	string shortstr = yylvalp->str; if (shortstr.length()>20) shortstr = string(shortstr,20)+"...";
	cout<<"   lexToBison  TOKEN="<<tok<<" "<<VParseGrammar::tokenName(tok)<<" str=\""<<shortstr<<"\"";
	if (yylvalp->scp) cout<<"  scp="<<yylvalp->scp->ascii();
	cout<<endl;
    }
    return tok;
}

void VParseLex::debug(int level) {
#ifdef FLEX_DEBUG
    yy_flex_debug = level;
#endif
}

void VParseLex::language(const char* value) {
    if (0==strcmp(value,"1364-1995"))		{ BEGIN V95; }
    else if (0==strcmp(value,"1364-2001"))	{ BEGIN V01; }
    else if (0==strcmp(value,"1364-2001-noconfig")) { BEGIN V01; }
    else if (0==strcmp(value,"1364-2005"))	{ BEGIN V05; }
    else if (0==strcmp(value,"1800-2005"))	{ BEGIN S05; }
    else if (0==strcmp(value,"1800-2009"))	{ BEGIN S09; }
    else if (0==strcmp(value,"1800-2012"))	{ BEGIN S12; }
    else yyerrorf("Unknown setLanguage code: %s", value);
}

/*###################################################################
 * Local Variables:
 * mode: C++
 * End:
 */
