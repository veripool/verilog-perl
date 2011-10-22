// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilog-Perl bison parser
//
// This file is part of Verilog-Perl.
//
// Author: Wilson Snyder <wsnyder@wsnyder.org>
//
// Code available from: http://www.veripool.org/systemperl
//
//*************************************************************************
//
// Copyright 2001-2011 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

%{

#include <cstdio>
#include <fstream>
#include <stack>
#include <vector>
#include <map>
#include <deque>
#include <cassert>

#include "VParse.h"
#include "VParseGrammar.h"

#define YYERROR_VERBOSE 1
#define YYINITDEPTH 5000	// Large as the stack won't grow, since YYSTYPE_IS_TRIVIAL isn't defined
#define YYMAXDEPTH 5000

// See VParseGrammar.h for the C++ interface to this parser
// Include that instead of VParseBison.h

//*************************************************************************

#define GRAMMARP VParseGrammar::staticGrammarp()
#define PARSEP VParseGrammar::staticParsep()

#define NEWSTRING(text) (string((text)))
#define SPACED(a,b)	((a)+(((a)=="" || (b)=="")?"":" ")+(b))

#define VARRESET_LIST(decl)    { GRAMMARP->pinNum(1); VARRESET(); VARDECL(decl); }	// Start of pinlist
#define VARRESET_NONLIST(decl) { GRAMMARP->pinNum(0); VARRESET(); VARDECL(decl); }	// Not in a pinlist
#define VARRESET()	 { VARDECL(""); VARIO(""); VARNET(""); VARDTYPE(""); }  // Start of one variable decl

// VARDECL("") indicates inside a port list or IO list and we shouldn't declare the variable
#define VARDECL(type)	 { GRAMMARP->m_varDecl = (type); }  // genvar, parameter, localparam
#define VARIO(type)	 { GRAMMARP->m_varIO   = (type); }  // input, output, inout, ref, const ref
#define VARNET(type)	 { GRAMMARP->m_varNet  = (type); }  // supply*,wire,tri
#define VARDTYPE(type)	 { GRAMMARP->m_varDType = (type); }  // "signed", "int", etc

#define PINNUMINC()	{ GRAMMARP->pinNumInc(); }

#define INSTPREP(cellmod,cellparam) { GRAMMARP->pinNum(1); GRAMMARP->m_cellMod=(cellmod); GRAMMARP->m_cellParam=(cellparam); }

static void VARDONE(VFileLine* fl, const string& name, const string& array, const string& value) {
    if (GRAMMARP->m_varIO!="" && GRAMMARP->m_varDecl=="") GRAMMARP->m_varDecl="port";
    if (GRAMMARP->m_varDecl!="") {
	PARSEP->varCb(fl, GRAMMARP->m_varDecl, name, PARSEP->symObjofUpward(), GRAMMARP->m_varNet,
		      GRAMMARP->m_varDType, array, value);
    }
    if (GRAMMARP->m_varIO!="" || GRAMMARP->pinNum()) {
	PARSEP->portCb(fl, name, PARSEP->symObjofUpward(),
		       GRAMMARP->m_varIO, GRAMMARP->m_varDType, array, GRAMMARP->pinNum());
    }
    if (GRAMMARP->m_varDType == "type") {
	PARSEP->syms().replaceInsert(VAstType::TYPE,name);
    }
}

static void VARDONETYPEDEF(VFileLine* fl, const string& name, const string& type, const string& array) {
    VARRESET(); VARDECL("typedef"); VARDTYPE(type);
    VARDONE(fl,name,array,"");
    // TYPE shouldn't override a more specific node type, as often is forward reference
    PARSEP->syms().replaceInsert(VAstType::TYPE,name);
}

static void PINDONE(VFileLine* fl, const string& name, const string& expr) {
    if (GRAMMARP->m_cellParam) {
	// Stack them until we create the instance itself
	GRAMMARP->m_pinStack.push_back(VParseGPin(fl, name, expr, GRAMMARP->pinNum()));
    } else {
	PARSEP->pinCb(fl, name, expr, GRAMMARP->pinNum());
    }
}

static void PINPARAMS() {
    // Throw out all the pins we found before we could do instanceCb
    while (!GRAMMARP->m_pinStack.empty()) {
	VParseGPin& pinr = GRAMMARP->m_pinStack.front();
	PARSEP->parampinCb(pinr.m_fl, pinr.m_name, pinr.m_conn, pinr.m_number);
	GRAMMARP->m_pinStack.pop_front();
    }
}

/* Yacc */
static int  VParseBisonlex(VParseBisonYYSType* yylvalp) { return PARSEP->lexToBison(yylvalp); }

static void VParseBisonerror(const char *s) { VParseGrammar::bisonError(s); }

static void ERRSVKWD(VFileLine* fileline, const string& tokname) {
    static int toldonce = 0;
    fileline->error((string)"Unexpected \""+tokname+"\": \""+tokname+"\" is a SystemVerilog keyword misused as an identifier.");
    if (!toldonce++) fileline->error("Modify the Verilog-2001 code to avoid SV keywords, or use `begin_keywords or --language.");
}

static void NEED_S09(VFileLine*, const string&) {
    //Let lint tools worry about it
    //fileline->error((string)"Advanced feature: \""+tokname+"\" is a 1800-2009 construct, but used under --lanugage 1800-2005 or earlier.");
}

%}

%pure_parser
%token_table
BISONPRE_VERSION(2.4, %define lr.keep_unreachable_states)

// When writing Bison patterns we use yTOKEN instead of "token",
// so Bison will error out on unknown "token"s.

// Generic lexer tokens, for example a number
// IEEE: real_number
%token<str>		yaFLOATNUM	"FLOATING-POINT NUMBER"

// IEEE: identifier, class_identifier, class_variable_identifier,
// covergroup_variable_identifier, dynamic_array_variable_identifier,
// enum_identifier, interface_identifier, interface_instance_identifier,
// package_identifier, type_identifier, variable_identifier,
%token<str>		yaID__ETC	"IDENTIFIER"
%token<str>		yaID__LEX	"IDENTIFIER-in-lex"
%token<str>		yaID__aCLASS	"CLASS-IDENTIFIER"
%token<str>		yaID__aCOVERGROUP "COVERGROUP-IDENTIFIER"
%token<str>		yaID__aPACKAGE	"PACKAGE-IDENTIFIER"
%token<str>		yaID__aTYPE	"TYPE-IDENTIFIER"
//			Can't predecode aFUNCTION, can declare after use
//			Can't predecode aINTERFACE, can declare after use
//			Can't predecode aTASK, can declare after use

// IEEE: integral_number
%token<str>		yaINTNUM	"INTEGER NUMBER"
// IEEE: time_literal + time_unit
%token<str>		yaTIMENUM	"TIME NUMBER"
// IEEE: string_literal
%token<str>		yaSTRING	"STRING"
%token<str>		yaSTRING__IGNORE "STRING-ignored"	// Used when expr:string not allowed

%token<str>		yaTIMINGSPEC	"TIMING SPEC ELEMENT"

%token<str>		ygenGATE	"GATE keyword"
%token<str>		ygenCONFIGKEYWORD "CONFIG keyword (cell/use/design/etc)"
%token<str>		ygenOPERATOR	"OPERATOR"
%token<str>		ygenSTRENGTH	"STRENGTH keyword (strong1/etc)"
%token<str>		ygenSYSCALL	"SYSCALL"

%token<str>		'!'
%token<str>		'#'
%token<str>		'%'
%token<str>		'&'
%token<str>		'('
%token<str>		')'
%token<str>		'*'
%token<str>		'+'
%token<str>		','
%token<str>		'-'
%token<str>		'.'
%token<str>		'/'
%token<str>		':'
%token<str>		';'
%token<str>		'<'
%token<str>		'='
%token<str>		'>'
%token<str>		'?'
%token<str>		'@'
%token<str>		'['
%token<str>		']'
%token<str>		'^'
%token<str>		'{'
%token<str>		'|'
%token<str>		'}'
%token<str>		'~'

// Specific keywords
// yKEYWORD means match "keyword"
// Other cases are yXX_KEYWORD where XX makes it unique,
// for example yP_ for punctuation based operators.
// Double underscores "yX__Y" means token X followed by Y,
// and "yX__ETC" means X folled by everything but Y(s).
%token<str>		yACCEPT_ON	"accept_on"
%token<str>		yALIAS		"alias"
%token<str>		yALWAYS		"always"
%token<str>		yAND		"and"
%token<str>		yASSERT		"assert"
%token<str>		yASSIGN		"assign"
%token<str>		yASSUME		"assume"
%token<str>		yAUTOMATIC	"automatic"
%token<str>		yBEFORE		"before"
%token<str>		yBEGIN		"begin"
%token<str>		yBIND		"bind"
%token<str>		yBINS		"bins"
%token<str>		yBINSOF		"binsof"
%token<str>		yBIT		"bit"
%token<str>		yBREAK		"break"
%token<str>		yBUF		"buf"
%token<str>		yBYTE		"byte"
%token<str>		yCASE		"case"
%token<str>		yCASEX		"casex"
%token<str>		yCASEZ		"casez"
%token<str>		yCHANDLE	"chandle"
%token<str>		yCHECKER	"checker"
%token<str>		yCLASS		"class"
%token<str>		yCLOCK		"clock"
%token<str>		yCLOCKING	"clocking"
%token<str>		yCONSTRAINT	"constraint"
%token<str>		yCONST__ETC	"const"
%token<str>		yCONST__LEX	"const-in-lex"
%token<str>		yCONST__LOCAL	"const-then-local"
%token<str>		yCONST__REF	"const-then-ref"
%token<str>		yCONTEXT	"context"
%token<str>		yCONTINUE	"continue"
%token<str>		yCOVER		"cover"
%token<str>		yCOVERGROUP	"covergroup"
%token<str>		yCOVERPOINT	"coverpoint"
%token<str>		yCROSS		"cross"
%token<str>		yDEASSIGN	"deassign"
%token<str>		yDEFAULT	"default"
%token<str>		yDEFPARAM	"defparam"
%token<str>		yDISABLE	"disable"
%token<str>		yDIST		"dist"
%token<str>		yDO		"do"
%token<str>		yEDGE		"edge"
%token<str>		yELSE		"else"
%token<str>		yEND		"end"
%token<str>		yENDCASE	"endcase"
%token<str>		yENDCHECKER	"endchecker"
%token<str>		yENDCLASS	"endclass"
%token<str>		yENDCLOCKING	"endclocking"
%token<str>		yENDFUNCTION	"endfunction"
%token<str>		yENDGENERATE	"endgenerate"
%token<str>		yENDGROUP	"endgroup"
%token<str>		yENDINTERFACE	"endinterface"
%token<str>		yENDMODULE	"endmodule"
%token<str>		yENDPACKAGE	"endpackage"
%token<str>		yENDPROGRAM	"endprogram"
%token<str>		yENDPROPERTY	"endproperty"
%token<str>		yENDSEQUENCE	"endsequence"
%token<str>		yENDSPECIFY	"endspecify"
%token<str>		yENDTABLE	"endtable"
%token<str>		yENDTASK	"endtask"
%token<str>		yENUM		"enum"
%token<str>		yEVENT		"event"
%token<str>		yEVENTUALLY	"eventually"
%token<str>		yEXPECT		"expect"
%token<str>		yEXPORT		"export"
%token<str>		yEXTENDS	"extends"
%token<str>		yEXTERN		"extern"
%token<str>		yFINAL		"final"
%token<str>		yFIRST_MATCH	"first_match"
%token<str>		yFOR		"for"
%token<str>		yFORCE		"force"
%token<str>		yFOREACH	"foreach"
%token<str>		yFOREVER	"forever"
%token<str>		yFORK		"fork"
%token<str>		yFORKJOIN	"forkjoin"
%token<str>		yFUNCTION__ETC	"function"
%token<str>		yFUNCTION__LEX	"function-in-lex"
%token<str>		yFUNCTION__aPUREV "function-is-pure-virtual"
%token<str>		yGENERATE	"generate"
%token<str>		yGENVAR		"genvar"
%token<str>		yGLOBAL__CLOCKING "global-then-clocking"
%token<str>		yGLOBAL__LEX	"global-in-lex"
%token<str>		yIF		"if"
%token<str>		yIFF		"iff"
%token<str>		yIGNORE_BINS	"ignore_bins"
%token<str>		yILLEGAL_BINS	"illegal_bins"
%token<str>		yIMPLIES	"implies"
%token<str>		yIMPORT		"import"
%token<str>		yINITIAL	"initial"
%token<str>		yINOUT		"inout"
%token<str>		yINPUT		"input"
%token<str>		yINSIDE		"inside"
%token<str>		yINT		"int"
%token<str>		yINTEGER	"integer"
%token<str>		yINTERFACE	"interface"
%token<str>		yINTERSECT	"intersect"
%token<str>		yJOIN		"join"
%token<str>		yLET		"let"
%token<str>		yLOCAL__COLONCOLON "local-then-::"
%token<str>		yLOCAL__ETC	"local"
%token<str>		yLOCAL__LEX	"local-in-lex"
%token<str>		yLOCALPARAM	"localparam"
%token<str>		yLOGIC		"logic"
%token<str>		yLONGINT	"longint"
%token<str>		yMATCHES	"matches"
%token<str>		yMODPORT	"modport"
%token<str>		yMODULE		"module"
%token<str>		yNAND		"nand"
%token<str>		yNEGEDGE	"negedge"
%token<str>		yNEW__ETC	"new"
%token<str>		yNEW__LEX	"new-in-lex"
%token<str>		yNEW__PAREN	"new-then-paren"
%token<str>		yNEXTTIME	"nexttime"
%token<str>		yNOR		"nor"
%token<str>		yNOT		"not"
%token<str>		yNULL		"null"
%token<str>		yOR		"or"
%token<str>		yOUTPUT		"output"
%token<str>		yPACKAGE	"package"
%token<str>		yPACKED		"packed"
%token<str>		yPARAMETER	"parameter"
%token<str>		yPOSEDGE	"posedge"
%token<str>		yPRIORITY	"priority"
%token<str>		yPROGRAM	"program"
%token<str>		yPROPERTY	"property"
%token<str>		yPROTECTED	"protected"
%token<str>		yPURE		"pure"
%token<str>		yRAND		"rand"
%token<str>		yRANDC		"randc"
%token<str>		yRANDCASE	"randcase"
%token<str>		yRANDSEQUENCE	"randsequence"
%token<str>		yREAL		"real"
%token<str>		yREALTIME	"realtime"
%token<str>		yREF		"ref"
%token<str>		yREG		"reg"
%token<str>		yREJECT_ON	"reject_on"
%token<str>		yRELEASE	"release"
%token<str>		yREPEAT		"repeat"
%token<str>		yRESTRICT	"restrict"
%token<str>		yRETURN		"return"
%token<str>		ySCALARED	"scalared"
%token<str>		ySEQUENCE	"sequence"
%token<str>		ySHORTINT	"shortint"
%token<str>		ySHORTREAL	"shortreal"
%token<str>		ySIGNED		"signed"
%token<str>		ySOLVE		"solve"
%token<str>		ySPECIFY	"specify"
%token<str>		ySPECPARAM	"specparam"
%token<str>		ySTATIC__CONSTRAINT "static-then-constraint"
%token<str>		ySTATIC__ETC	"static"
%token<str>		ySTATIC__LEX	"static-in-lex"
%token<str>		ySTRING		"string"
%token<str>		ySTRONG		"strong"
%token<str>		ySTRUCT		"struct"
%token<str>		ySUPER		"super"
%token<str>		ySUPPLY0	"supply0"
%token<str>		ySUPPLY1	"supply1"
%token<str>		ySYNC_ACCEPT_ON	"sync_accept_on"
%token<str>		ySYNC_REJECT_ON	"sync_reject_on"
%token<str>		yS_ALWAYS	"s_always"
%token<str>		yS_EVENTUALLY	"s_eventually"
%token<str>		yS_NEXTTIME	"s_nexttime"
%token<str>		yS_UNTIL	"s_until"
%token<str>		yS_UNTIL_WITH	"s_until_with"
%token<str>		yTABLE		"table"
%token<str>		yTAGGED		"tagged"
%token<str>		yTASK__ETC	"task"
%token<str>		yTASK__LEX	"task-in-lex"
%token<str>		yTASK__aPUREV	"task-is-pure-virtual"
%token<str>		yTHIS		"this"
%token<str>		yTHROUGHOUT	"throughout"
%token<str>		yTIME		"time"
%token<str>		yTIMEPRECISION	"timeprecision"
%token<str>		yTIMEUNIT	"timeunit"
%token<str>		yTRI		"tri"
%token<str>		yTRI0		"tri0"
%token<str>		yTRI1		"tri1"
%token<str>		yTRIAND		"triand"
%token<str>		yTRIOR		"trior"
%token<str>		yTRIREG		"trireg"
%token<str>		yTYPE		"type"
%token<str>		yTYPEDEF	"typedef"
%token<str>		yUNION		"union"
%token<str>		yUNIQUE		"unique"
%token<str>		yUNIQUE0	"unique0"
%token<str>		yUNSIGNED	"unsigned"
%token<str>		yUNTIL		"until"
%token<str>		yUNTIL_WITH	"until_with"
%token<str>		yUNTYPED	"untyped"
%token<str>		yVAR		"var"
%token<str>		yVECTORED	"vectored"
%token<str>		yVIRTUAL__CLASS	"virtual-then-class"
%token<str>		yVIRTUAL__ETC	"virtual"
%token<str>		yVIRTUAL__INTERFACE	"virtual-then-interface"
%token<str>		yVIRTUAL__LEX	"virtual-in-lex"
%token<str>		yVIRTUAL__anyID	"virtual-then-identifier"
%token<str>		yVOID		"void"
%token<str>		yWAIT		"wait"
%token<str>		yWAIT_ORDER	"wait_order"
%token<str>		yWAND		"wand"
%token<str>		yWEAK		"weak"
%token<str>		yWHILE		"while"
%token<str>		yWILDCARD	"wildcard"
%token<str>		yWIRE		"wire"
%token<str>		yWITHIN		"within"
%token<str>		yWITH__BRA	"with-then-["
%token<str>		yWITH__CUR	"with-then-{"
%token<str>		yWITH__ETC	"with"
%token<str>		yWITH__LEX	"with-in-lex"
%token<str>		yWITH__PAREN	"with-then-("
%token<str>		yWOR		"wor"
%token<str>		yXNOR		"xnor"
%token<str>		yXOR		"xor"

%token<str>		yD_ERROR	"$error"
%token<str>		yD_FATAL	"$fatal"
%token<str>		yD_INFO		"$info"
%token<str>		yD_ROOT		"$root"
%token<str>		yD_UNIT		"$unit"
%token<str>		yD_WARNING	"$warning"

%token<str>		yP_TICK		"'"
%token<str>		yP_TICKBRA	"'{"
%token<str>		yP_OROR		"||"
%token<str>		yP_ANDAND	"&&"
%token<str>		yP_NOR		"~|"
%token<str>		yP_XNOR		"^~"
%token<str>		yP_NAND		"~&"
%token<str>		yP_EQUAL	"=="
%token<str>		yP_NOTEQUAL	"!="
%token<str>		yP_CASEEQUAL	"==="
%token<str>		yP_CASENOTEQUAL	"!=="
%token<str>		yP_WILDEQUAL	"==?"
%token<str>		yP_WILDNOTEQUAL	"!=?"
%token<str>		yP_GTE		">="
%token<str>		yP_LTE		"<="
%token<str>		yP_LTE__IGNORE	"<=-ignored"	// Used when expr:<= means assignment
%token<str>		yP_SLEFT	"<<"
%token<str>		yP_SRIGHT	">>"
%token<str>		yP_SSRIGHT	">>>"
%token<str>		yP_POW		"**"

%token<str>		yP_PAR__IGNORE	"(-ignored"	// Used when sequence_expr:expr:( is ignored
%token<str>		yP_PAR__STRENGTH "(-for-strength"

%token<str>		yP_LTMINUSGT	"<->"
%token<str>		yP_PLUSCOLON	"+:"
%token<str>		yP_MINUSCOLON	"-:"
%token<str>		yP_MINUSGT	"->"
%token<str>		yP_MINUSGTGT	"->>"
%token<str>		yP_EQGT		"=>"
%token<str>		yP_ASTGT	"*>"
%token<str>		yP_ANDANDAND	"&&&"
%token<str>		yP_POUNDPOUND	"##"
%token<str>		yP_POUNDMINUSPD	"#-#"
%token<str>		yP_POUNDEQPD	"#=#"
%token<str>		yP_DOTSTAR	".*"

%token<str>		yP_ATAT		"@@"
%token<str>		yP_COLONCOLON	"::"
%token<str>		yP_COLONEQ	":="
%token<str>		yP_COLONDIV	":/"
%token<str>		yP_ORMINUSGT	"|->"
%token<str>		yP_OREQGT	"|=>"
%token<str>		yP_BRASTAR	"[*"
%token<str>		yP_BRAEQ	"[="
%token<str>		yP_BRAMINUSGT	"[->"
%token<str>		yP_BRAPLUSKET	"[+]"

%token<str>		yP_PLUSPLUS	"++"
%token<str>		yP_MINUSMINUS	"--"
%token<str>		yP_PLUSEQ	"+="
%token<str>		yP_MINUSEQ	"-="
%token<str>		yP_TIMESEQ	"*="
%token<str>		yP_DIVEQ	"/="
%token<str>		yP_MODEQ	"%="
%token<str>		yP_ANDEQ	"&="
%token<str>		yP_OREQ		"|="
%token<str>		yP_XOREQ	"^="
%token<str>		yP_SLEFTEQ	"<<="
%token<str>		yP_SRIGHTEQ	">>="
%token<str>		yP_SSRIGHTEQ	">>>="

// '( is not a operator, as "' (" is legal

//********************
// Verilog op precedence

%token<str>	prUNARYARITH
%token<str>	prREDUCTION
%token<str>	prNEGATION
%token<str>	prEVENTBEGIN
%token<str>	prTAGGED

// These prevent other conflicts
%left		yP_ANDANDAND
%left		yMATCHES
%left		prTAGGED
%left		prSEQ_CLOCKING

// Lowest precedence
// These are in IEEE 17.7.1
%nonassoc	yALWAYS yS_ALWAYS yEVENTUALLY yS_EVENTUALLY yACCEPT_ON yREJECT_ON ySYNC_ACCEPT_ON ySYNC_REJECT_ON

%right		yP_ORMINUSGT yP_OREQGT yP_POUNDMINUSPD yP_POUNDEQPD
%right		yUNTIL yS_UNTIL yUNTIL_WITH yS_UNTIL_WITH yIMPLIES
%right		yIFF
%left		yOR
%left		yAND
%nonassoc	yNOT yNEXTTIME yS_NEXTTIME
%left		yINTERSECT
%left		yWITHIN
%right		yTHROUGHOUT
%left		prPOUNDPOUND_MULTI
%left		yP_POUNDPOUND
%left		yP_BRASTAR yP_BRAEQ yP_BRAMINUSGT yP_BRAPLUSKET

// Not specified, but needed higher than yOR, lower than normal non-pexpr expressions
%left		yPOSEDGE yNEGEDGE yEDGE

%left		'{' '}'
//%nonassoc	'=' yP_PLUSEQ yP_MINUSEQ yP_TIMESEQ yP_DIVEQ yP_MODEQ yP_ANDEQ yP_OREQ yP_XOREQ yP_SLEFTEQ yP_SRIGHTEQ yP_SSRIGHTEQ yP_COLONEQ yP_COLONDIV yP_LTE
%right		yP_MINUSGT yP_LTMINUSGT
%right		'?' ':'
%left		yP_OROR
%left		yP_ANDAND
%left		'|' yP_NOR
%left		'^' yP_XNOR
%left		'&' yP_NAND
%left		yP_EQUAL yP_NOTEQUAL yP_CASEEQUAL yP_CASENOTEQUAL yP_WILDEQUAL yP_WILDNOTEQUAL
%left		'>' '<' yP_GTE yP_LTE yP_LTE__IGNORE yINSIDE yDIST
%left		yP_SLEFT yP_SRIGHT yP_SSRIGHT
%left		'+' '-'
%left		'*' '/' '%'
%left		yP_POW
%left		prUNARYARITH yP_MINUSMINUS yP_PLUSPLUS prREDUCTION prNEGATION
%left		'.'
// Not in IEEE, but need to avoid conflicts; TICK should bind tightly just lower than COLONCOLON
%left		yP_TICK
//%left		'(' ')' '[' ']' yP_COLONCOLON '.'

%nonassoc prLOWER_THAN_ELSE
%nonassoc yELSE

//BISONPRE_TYPES
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion

%start source_text

%%
//**********************************************************************
// Feedback to the Lexer
// Note we read a parenthesis ahead, so this may not change the lexer at the right point.

statePushVlg:			// For PSL lexing, escape current state into Verilog state
		/* empty */			 	{ }
	;
statePop:			// Return to previous lexing state
		/* empty */			 	{ }
	;

//**********************************************************************
// Files

source_text:			// ==IEEE: source_text
		/* empty */				{ }
	//			// timeunits_declaration moved into description:package_item
	|	descriptionList				{ }
	;

descriptionList:		// IEEE: part of source_text
		description				{ }
	|	descriptionList description		{ }
	;

description:			// ==IEEE: description
		module_declaration			{ }
	//			// udp_declaration moved into module_declaration
	|	interface_declaration			{ }
	|	program_declaration			{ }
	|	package_declaration			{ }
	|	package_item				{ }
	|	bind_directive				{ }
	//	unsupported	// IEEE: config_declaration
	|	error					{ }
	;

timeunits_declaration:		// ==IEEE: timeunits_declaration
		yTIMEUNIT yaTIMENUM ';'			{ }
	|	yTIMEUNIT yaTIMENUM '/' yaTIMENUM ';'	{ NEED_S09($<fl>1,"timeunit /"); }
	| 	yTIMEPRECISION  yaTIMENUM ';'		{ }
	;

//**********************************************************************
// Packages

package_declaration:		// ==IEEE: package_declaration
		packageFront package_itemListE yENDPACKAGE endLabelE
			{ PARSEP->endpackageCb($<fl>3,$3);
			  PARSEP->symPopScope(VAstType::PACKAGE); }
	;

packageFront:
	//			// Lifetime is 1800-2009
		yPACKAGE lifetimeE idAny ';'
			{ PARSEP->symPushNew(VAstType::PACKAGE, $3);
			  PARSEP->packageCb($<fl>1,$1, $3); }
	;

package_itemListE:		// IEEE: [{ package_item }]
		/* empty */				{ }
	|	package_itemList			{ }
	;

package_itemList:		// IEEE: { package_item }
		package_item				{ }
	|	package_itemList package_item		{ }
	;

package_item:			// ==IEEE: package_item
		package_or_generate_item_declaration	{ }
	|	anonymous_program			{ }
	|	package_export_declaration		{ }
	|	timeunits_declaration			{ }
	;

package_or_generate_item_declaration:	// ==IEEE: package_or_generate_item_declaration
		net_declaration				{ }
	|	data_declaration			{ }
	|	task_declaration			{ }
	|	function_declaration			{ }
	|	checker_declaration			{ }
	|	dpi_import_export			{ }
	|	extern_constraint_declaration		{ }
	|	class_declaration			{ }
	//			// class_constructor_declaration is part of function_declaration
	|	local_parameter_declaration ';'		{ }
	|	parameter_declaration ';'		{ }
	|	covergroup_declaration			{ }
	|	overload_declaration			{ }
	|	assertion_item_declaration		{ }
	|	';'					{ }
	;

package_import_declarationList:
		package_import_declaration		{ }
	|	package_import_declarationList ',' package_import_declaration { }
	;

package_import_declaration:	// ==IEEE: package_import_declaration
		yIMPORT package_import_itemList ';'	{ }
	;

package_import_itemList:
		package_import_item			{ }
	|	package_import_itemList ',' package_import_item { }
	;

package_import_item:		// ==IEEE: package_import_item
		yaID__aPACKAGE yP_COLONCOLON package_import_itemObj
			{ PARSEP->syms().import($<fl>1,$1,$3);
			  PARSEP->importCb($<fl>1,$1,$3); }
	;

package_import_itemObj<str>:	// IEEE: part of package_import_item
		idAny					{ $<fl>$=$<fl>1; $$=$1; }
	|	'*'					{ $<fl>$=$<fl>1; $$=$1; }
	;

package_export_declaration<str>: // IEEE: package_export_declaration
		yEXPORT '*' yP_COLONCOLON '*' ';'	{ }
	|	yEXPORT package_import_itemList ';'	{ }
	;

//**********************************************************************
// Module headers

module_declaration:		// ==IEEE: module_declaration
	//			// timeunits_declaration instead in module_item
	//			// IEEE: module_nonansi_header + module_ansi_header
		modFront importsAndParametersE portsStarE ';'
			module_itemListE yENDMODULE endLabelE
			{ PARSEP->endmoduleCb($<fl>6,$6);
			  PARSEP->symPopScope(VAstType::MODULE); }
	//
	|	yEXTERN modFront importsAndParametersE portsStarE ';'
			{ PARSEP->symPopScope(VAstType::MODULE); }
	;

modFront:
	//			// General note: all *Front functions must call symPushNew before
	//			// any formal arguments, as the arguments must land in the new scope.
		yMODULE lifetimeE idAny
			{ PARSEP->symPushNew(VAstType::MODULE, $3);
			  PARSEP->moduleCb($<fl>1,$1,$3,false,PARSEP->inCellDefine()); }
	;

importsAndParametersE:		// IEEE: common part of module_declaration, interface_declaration, program_declaration
	//			// { package_import_declaration } [ parameter_port_list ]
		parameter_port_listE			{ }
	|	package_import_declarationList parameter_port_listE	{ }
	;

parameter_value_assignmentE:	// IEEE: [ parameter_value_assignment ]
		/* empty */				{ }
	|	'#' '(' cellpinList ')'			{ }
	//			// Side effect of combining *_instantiations
	|	'#' delay_value				{ }
	;

parameter_port_listE:		// IEEE: parameter_port_list + empty == parameter_value_assignment
		/* empty */				{ }
	|	'#' '(' ')'				{ }
	//			// IEEE: '#' '(' list_of_param_assignments { ',' parameter_port_declaration } ')'
	//			// IEEE: '#' '(' parameter_port_declaration { ',' parameter_port_declaration } ')'
	//			// Can't just do that as "," conflicts with between vars and between stmts, so
	//			// split into pre-comma and post-comma parts
	|	'#' '(' {VARRESET_LIST("parameter");} paramPortDeclOrArgList ')'	{ VARRESET_NONLIST(""); }
	//			// Note legal to start with "a=b" with no parameter statement
	;

paramPortDeclOrArgList:		// IEEE: list_of_param_assignments + { parameter_port_declaration }
		paramPortDeclOrArg			{ }
	|	paramPortDeclOrArgList ',' paramPortDeclOrArg	{ }
	;

paramPortDeclOrArg:		// IEEE: param_assignment + parameter_port_declaration
	//			// We combine the two as we can't tell which follows a comma
		param_assignment			{ }
	|	parameter_port_declarationFront param_assignment	{ }
	;

portsStarE:			// IEEE: .* + list_of_ports + list_of_port_declarations + empty
		/* empty */					{ }
	//			// .* expanded from module_declaration
	//			// '(' ')' handled by list_of_ports:portE
	|	'(' yP_DOTSTAR ')'				{ }
	|	'(' {VARRESET_LIST("");} list_of_portsE ')'	{ VARRESET_NONLIST(""); }
	;

list_of_portsE:			// IEEE: list_of_ports + list_of_port_declarations
		portE					{ }
	|	list_of_portsE ',' portE 		{ }
	;

portE:				// ==IEEE: [ port ]
	//			// Though not type for interfaces, we factor out the port direction and type
	//			// so we can simply handle it in one place
	//
	//			// IEEE: interface_port_header port_identifier { unpacked_dimension }
	//			// Expanded interface_port_header
	//			// We use instantCb here because the non-port form looks just like a module instantiation
		/* empty */				{ }
	|	portDirNetE id/*interface*/                      idAny/*port*/ rangeListE sigAttrListE
			{ VARDTYPE($2); VARIO("interface"); VARDONE($<fl>2, $3, $4, ""); PINNUMINC();
			  PARSEP->instantCb($<fl>2, $2, $3, $4); PARSEP->endcellCb($<fl>2,""); }
	|	portDirNetE yINTERFACE                           idAny/*port*/ rangeListE sigAttrListE
			{ VARDTYPE($2); VARIO("interface"); VARDONE($<fl>2, $3, $4, ""); PINNUMINC(); }
	|	portDirNetE id/*interface*/ '.' idAny/*modport*/ idAny/*port*/ rangeListE sigAttrListE
			{ VARDTYPE($2+"."+$4); VARIO("interface"); VARDONE($<fl>2, $5, $6, ""); PINNUMINC();
			  PARSEP->instantCb($<fl>2, $2, $5, $6); PARSEP->endcellCb($<fl>2,""); }
	|	portDirNetE yINTERFACE      '.' idAny/*modport*/ idAny/*port*/ rangeListE sigAttrListE
			{ VARDTYPE($2+"."+$4); VARIO("interface"); VARDONE($<fl>2, $5, $6, ""); PINNUMINC(); }
	//
	//			// IEEE: ansi_port_declaration, with [port_direction] removed
	//			//   IEEE: [ net_port_header | interface_port_header ] port_identifier { unpacked_dimension } [ '=' constant_expression ]
	//			//   IEEE: [ net_port_header | variable_port_header ] '.' port_identifier '(' [ expression ] ')'
	//			//   IEEE: [ variable_port_header ] port_identifier { variable_dimension } [ '=' constant_expression ]
	//			//   Substitute net_port_header = [ port_direction ] net_port_type
	//			//   Substitute variable_port_header = [ port_direction ] variable_port_type
	//			//   Substitute net_port_type = [ net_type ] data_type_or_implicit
	//			//   Substitute variable_port_type = var_data_type
	//			//     [ [ port_direction ] net_port_type | interface_port_header            ] port_identifier { unpacked_dimension }
	//			//     [ [ port_direction ] var_data_type                                    ] port_identifier variable_dimensionListE [ '=' constant_expression ]
	//			//     [ [ port_direction ] net_port_type | [ port_direction ] var_data_type ] '.' port_identifier '(' [ expression ] ')'
	//
	//			// Remove optional '[...] id' is in portAssignment
	//			// Remove optional '[port_direction]' is in port
	//			//     net_port_type | interface_port_header            port_identifier { unpacked_dimension }
	//			//     net_port_type | interface_port_header            port_identifier { unpacked_dimension }
	//			//     var_data_type                                    port_identifier variable_dimensionListE [ '=' constExpr ]
	//			//     net_port_type | [ port_direction ] var_data_type '.' port_identifier '(' [ expr ] ')'
	//			// Expand implicit_type
	//
	//			// variable_dimensionListE instead of rangeListE to avoid conflicts
	//
	//			// Note implicit rules looks just line declaring additional followon port
	//			// No VARDECL("port") for implicit, as we don't want to declare variables for them
	|	portDirNetE var_data_type       '.' portSig '(' portAssignExprE ')' sigAttrListE	{ VARDTYPE($2); VARDONE($<fl>4, $4, "", ""); PINNUMINC(); }
	|	portDirNetE signingE rangeList  '.' portSig '(' portAssignExprE ')' sigAttrListE	{ VARDTYPE(SPACED($2,$3)); VARDONE($<fl>5, $5, "", ""); PINNUMINC(); }
	|	portDirNetE /*implicit*/        '.' portSig '(' portAssignExprE ')' sigAttrListE	{ /*VARDTYPE-same*/ VARDONE($<fl>3, $3, "", ""); PINNUMINC(); }
	//
	|	portDirNetE var_data_type       portSig variable_dimensionListE sigAttrListE	{ VARDTYPE($2); VARDONE($<fl>3, $3, $4, ""); PINNUMINC(); }
	|	portDirNetE signingE rangeList  portSig variable_dimensionListE sigAttrListE	{ VARDTYPE(SPACED($2,$3)); VARDONE($<fl>4, $4, $5, ""); PINNUMINC(); }
	|	portDirNetE /*implicit*/        portSig variable_dimensionListE sigAttrListE	{ /*VARDTYPE-same*/ VARDONE($<fl>2, $2, $3, ""); PINNUMINC(); }
	//
	|	portDirNetE var_data_type       portSig variable_dimensionListE sigAttrListE '=' constExpr	{ VARDTYPE($2); VARDONE($<fl>3, $3, $4, $7); PINNUMINC(); }
	|	portDirNetE signingE rangeList  portSig variable_dimensionListE sigAttrListE '=' constExpr	{ VARDTYPE(SPACED($2,$3)); VARDONE($<fl>4, $4, $5, $8); PINNUMINC(); }
	|	portDirNetE /*implicit*/        portSig variable_dimensionListE sigAttrListE '=' constExpr	{ /*VARDTYPE-same*/ VARDONE($<fl>2, $2, $3, $6); PINNUMINC(); }
	//
	|	'{' list_of_portsE '}'			{ }
	;

portDirNetE:			// IEEE: part of port, optional net type and/or direction
		/* empty */				{ }
	//			// Per spec, if direction given default the nettype.
	//			// The higher level rule may override this VARDTYPE with one later in the parse.
	|	port_direction				{ VARDTYPE(""/*default_nettype*/); }
	|	port_direction net_type			{ VARDTYPE(""/*default_nettype*/); } // net_type calls VARNET
	|	net_type				{ } // net_type calls VARNET
	;

port_declNetE:			// IEEE: part of port_declaration, optional net type
		/* empty */				{ }
	|	net_type				{ } // net_type calls VARNET
	;

portAssignExprE:		// IEEE: part of port, optional expression
		/* empty */				{ }
	|	expr					{ }
	;

portSig<str>:
		id/*port*/				{ $<fl>$=$<fl>1; $$=$1; }
	|	idSVKwd					{ $<fl>$=$<fl>1; $$=$1; }
	;

//**********************************************************************
// Interface headers

interface_declaration:		// IEEE: interface_declaration + interface_nonansi_header + interface_ansi_header:
	//			// timeunits_delcarationE is instead in interface_item
		intFront importsAndParametersE portsStarE ';'
			interface_itemListE yENDINTERFACE endLabelE
			{ PARSEP->endinterfaceCb($<fl>6, $6);
			  PARSEP->symPopScope(VAstType::INTERFACE); }
	|	yEXTERN	intFront importsAndParametersE portsStarE ';'	{ }
	;

intFront:
		yINTERFACE lifetimeE idAny/*new_interface*/
			{ PARSEP->symPushNew(VAstType::INTERFACE,$3);
			  PARSEP->interfaceCb($<fl>1,$1,$3); }
	;

interface_itemListE:
		/* empty */				{ }
	|	interface_itemList			{ }
	;

interface_itemList:
		interface_item				{ }
	|	interface_itemList interface_item	{ }
	;

interface_item:			// IEEE: interface_item + non_port_interface_item
		port_declaration ';'			{ }
	//			// IEEE: non_port_interface_item
	|	generate_region				{ }
	|	interface_or_generate_item		{ }
	|	program_declaration			{ }
	|	interface_declaration			{ }
	|	timeunits_declaration			{ }
	//			// See note in interface_or_generate item
	|	module_common_item			{ }
	;

interface_or_generate_item:	// ==IEEE: interface_or_generate_item
	//			// module_common_item in interface_item, as otherwise duplicated
	//			// with module_or_generate_item:module_common_item
		modport_declaration			{ }
	|	extern_tf_declaration			{ }
	;

//**********************************************************************
// Program headers

anonymous_program:		// ==IEEE: anonymous_program
	//			// See the spec - this doesn't change the scope, items still go up "top"
		yPROGRAM ';' anonymous_program_itemListE yENDPROGRAM	{ }
	;

anonymous_program_itemListE:	// IEEE: { anonymous_program_item }
		/* empty */				{ }
	|	anonymous_program_itemList		{ }
	;

anonymous_program_itemList:	// IEEE: { anonymous_program_item }
		anonymous_program_item			{ }
	|	anonymous_program_itemList anonymous_program_item	{ }
	;

anonymous_program_item:		// ==IEEE: anonymous_program_item
		task_declaration			{ }
	|	function_declaration			{ }
	|	class_declaration			{ }
	|	covergroup_declaration			{ }
	//			// class_constructor_declaration is part of function_declaration
	|	';'					{ }
	;

program_declaration:		// IEEE: program_declaration + program_nonansi_header + program_ansi_header:
	//			// timeunits_delcarationE is instead in program_item
		pgmFront importsAndParametersE portsStarE ';'
			program_itemListE yENDPROGRAM endLabelE
			{ PARSEP->endprogramCb($<fl>6,$6);
			  PARSEP->symPopScope(VAstType::PROGRAM); }
	|	yEXTERN	pgmFront importsAndParametersE portsStarE ';'
			{ PARSEP->symPopScope(VAstType::PROGRAM); }
	;

pgmFront:
		yPROGRAM lifetimeE idAny/*new_program*/
			{ PARSEP->symPushNew(VAstType::PROGRAM,$3);
			  PARSEP->programCb($<fl>1,$1, $3);
			 }
	;

program_itemListE:		// ==IEEE: [{ program_item }]
		/* empty */				{ }
	|	program_itemList			{ }
	;

program_itemList:		// ==IEEE: { program_item }
		program_item				{ }
	|	program_itemList program_item		{ }
	;

program_item:			// ==IEEE: program_item
		port_declaration ';'			{ }
	|	non_port_program_item			{ }
	;

non_port_program_item:		// ==IEEE: non_port_program_item
		continuous_assign			{ }
	|	module_or_generate_item_declaration	{ }
	|	initial_construct			{ }
	|	final_construct				{ }
	|	concurrent_assertion_item		{ }
	|	timeunits_declaration			{ }
	|	program_generate_item			{ }
	;

program_generate_item:		// ==IEEE: program_generate_item
		loop_generate_construct			{ }
	|	conditional_generate_construct		{ }
	|	generate_region				{ }
	|	elaboration_system_task			{ }
	;

extern_tf_declaration:		// ==IEEE: extern_tf_declaration
		yEXTERN task_prototype ';'		{ }
	|	yEXTERN function_prototype ';'		{ }
	|	yEXTERN yFORKJOIN task_prototype ';'	{ }
	;

modport_declaration:		// ==IEEE: modport_declaration
		yMODPORT modport_itemList ';'		{ }
	;

modport_itemList:		// IEEE: part of modport_declaration
		modport_item				{ }
	|	modport_itemList ',' modport_item	{ }
	;

modport_item:			// ==IEEE: modport_item
		modport_idFront '(' {VARRESET_LIST("");} modportPortsDeclList ')'
			{ VARRESET_NONLIST("");
			  PARSEP->endmodportCb($<fl>1, "endmodport");
			  PARSEP->symPopScope(VAstType::MODPORT); }
	;

modport_idFront:
		id/*new-modport*/
			{ PARSEP->symPushNew(VAstType::MODPORT,$1);
			  PARSEP->modportCb($<fl>1,"modport",$1); }
	;

modportPortsDeclList:
		modportPortsDecl			{ }
	|	modportPortsDeclList ',' modportPortsDecl	{ }
	;

// IEEE: modport_ports_declaration  + modport_simple_ports_declaration
//	+ (modport_tf_ports_declaration+import_export) + modport_clocking_declaration
// We've expanded the lists each take to instead just have standalone ID ports.
// We track the type as with the V2k series of defines, then create as each ID is seen.
modportPortsDecl:
	//			// IEEE: modport_simple_ports_declaration
		port_direction modportSimplePort	{ }
	//			// IEEE: modport_clocking_declaration
	|	yCLOCKING idAny/*clocking_identifier*/	{ }
	|	yIMPORT modport_tf_port			{ }
	|	yEXPORT modport_tf_port			{ }
	// Continuations of above after a comma.
	//			// IEEE: modport_simple_ports_declaration
	|	modportSimplePort			{ }
	;

modportSimplePort:		// IEEE: modport_simple_port or modport_tf_port, depending what keyword was earlier
	//			// Note 'init' field is used to say what to connect to
		id					{ VARDONE($<fl>1,$1,"",$1); PINNUMINC(); }
	|	'.' idAny '(' ')'			{ VARDONE($<fl>1,$2,"",""); PINNUMINC(); }
	|	'.' idAny '(' expr ')'			{ VARDONE($<fl>1,$2,"",$4); PINNUMINC(); }
	;

modport_tf_port:		// ==IEEE: modport_tf_port
		id/*tf_identifier*/			{ }
	|	method_prototype			{ }
	;

//************************************************
// Variable Declarations

genvar_declaration:		// ==IEEE: genvar_declaration
		yGENVAR list_of_genvar_identifiers ';'	{ }
	;

list_of_genvar_identifiers:	// IEEE: list_of_genvar_identifiers (for declaration)
		genvar_identifierDecl			{ }
	|	list_of_genvar_identifiers ',' genvar_identifierDecl	{ }
	;

genvar_identifierDecl:		// IEEE: genvar_identifier (for declaration)
		id/*new-genvar_identifier*/ sigAttrListE	{ VARRESET_NONLIST("genvar"); VARDONE($<fl>1, $1, "", ""); }
	;

local_parameter_declaration:	// IEEE: local_parameter_declaration
	//			// See notes in parameter_declaration
		local_parameter_declarationFront list_of_param_assignments	{ }
	;

parameter_declaration:		// IEEE: parameter_declaration
	//			// IEEE: yPARAMETER yTYPE list_of_type_assignments ';'
	//			// Instead of list_of_type_assignments
	//			// we use list_of_param_assignments because for port handling
	//			// it already must accept types, so simpler to have code only one place
		parameter_declarationFront list_of_param_assignments	{ }
	;

local_parameter_declarationFront: // IEEE: local_parameter_declaration w/o assignment
		varLParamReset implicit_typeE 		{ VARRESET(); VARDECL("localparam"); VARDTYPE($2); }
	|	varLParamReset data_type		{ VARRESET(); VARDECL("localparam"); VARDTYPE($2); }
	|	varLParamReset yTYPE			{ VARRESET(); VARDECL("localparam"); VARDTYPE($2); }
	;

parameter_declarationFront:	// IEEE: parameter_declaration w/o assignment
		varGParamReset implicit_typeE 		{ VARRESET(); VARDECL("parameter"); VARDTYPE($2); }
	|	varGParamReset data_type		{ VARRESET(); VARDECL("parameter"); VARDTYPE($2); }
	|	varGParamReset yTYPE			{ VARRESET(); VARDECL("parameter"); VARDTYPE($2); }
	;

parameter_port_declarationFront: // IEEE: parameter_port_declaration w/o assignment
	//			// IEEE: parameter_declaration (minus assignment)
		parameter_declarationFront		{ }
	|	local_parameter_declarationFront	{ /*NEED_S09(CURLINE(),"port localparams");*/ }
	//
	|	data_type				{ VARDTYPE($1); }
	|	yTYPE 					{ VARDTYPE($1); }
	;

net_declaration:		// IEEE: net_declaration - excluding implict
		net_declarationFront netSigList ';'	{ }
	;

net_declarationFront:		// IEEE: beginning of net_declaration
		net_declRESET net_type strengthSpecE net_scalaredE net_dataType { VARDTYPE(SPACED($4,$5)); }
	;

net_declRESET:
		/* empty */ 				{ VARRESET_NONLIST("net"); }
	;

net_scalaredE<str>:
		/* empty */ 				{ $$=""; }
	|	ySCALARED			 	{ $<fl>$=$<fl>1; $$=$1; }
	|	yVECTORED				{ $<fl>$=$<fl>1; $$=$1; }
	;

net_dataType<str>:
	//			// If there's a SV data type there shouldn't be a delay on this wire
	//			// Otherwise #(...) can't be determined to be a delay or parameters
	//			// Submit this as a footnote to the committee
		var_data_type	 			{ $<fl>$=$<fl>1; $$=$1; }
	|	signingE rangeList delayE 		{ $<fl>$=$<fl>1; $$=SPACED($1,$2); }
	|	signing delayE 				{ $<fl>$=$<fl>1; $$=$1; }
	|	/*implicit*/ delayE 			{ $<fl>$=$<fl>1; $$=""; }
	;

net_type:			// ==IEEE: net_type
		ySUPPLY0				{ VARNET($1); }
	|	ySUPPLY1				{ VARNET($1); }
	|	yTRI 					{ VARNET($1); }
	|	yTRI0 					{ VARNET($1); }
	|	yTRI1 					{ VARNET($1); }
	|	yTRIAND 				{ VARNET($1); }
	|	yTRIOR 					{ VARNET($1); }
	|	yTRIREG 				{ VARNET($1); }
	|	yWAND 					{ VARNET($1); }
	|	yWIRE 					{ VARNET($1); }
	|	yWOR 					{ VARNET($1); }
	;

varGParamReset:
		yPARAMETER				{ VARRESET_NONLIST($1); }
	;

varLParamReset:
		yLOCALPARAM				{ VARRESET_NONLIST($1); }
	;

port_direction:			// ==IEEE: port_direction + tf_port_direction
	//			// IEEE 19.8 just "input" FIRST forces type to wire - we'll ignore that here
		yINPUT					{ VARIO($1); }
	|	yOUTPUT					{ VARIO($1); }
	|	yINOUT					{ VARIO($1); }
	|	yREF					{ VARIO($1); }
	|	yCONST__REF yREF			{ VARIO($1); }
	;

port_directionReset:		// IEEE: port_direction that starts a port_declaraiton
	//			// Used only for declarations outside the port list
		yINPUT					{ VARRESET_NONLIST(""); VARIO($1); }
	|	yOUTPUT					{ VARRESET_NONLIST(""); VARIO($1); }
	|	yINOUT					{ VARRESET_NONLIST(""); VARIO($1); }
	|	yREF					{ VARRESET_NONLIST(""); VARIO($1); }
	|	yCONST__REF yREF			{ VARRESET_NONLIST(""); VARIO($1); }
	;

port_declaration:		// ==IEEE: port_declaration
	//			// Used inside block; followed by ';'
	//			// SIMILAR to tf_port_declaration
	//
	//			// IEEE: inout_declaration
	//			// IEEE: input_declaration
	//			// IEEE: output_declaration
	//			// IEEE: ref_declaration
		port_directionReset port_declNetE var_data_type       { VARDTYPE($3); } list_of_variable_decl_assignments	{ }
	|	port_directionReset port_declNetE signingE rangeList  { VARDTYPE(SPACED($3,$4)); } list_of_variable_decl_assignments	{ }
	|	port_directionReset port_declNetE signing	      { VARDTYPE($3); } list_of_variable_decl_assignments	{ }
	|	port_directionReset port_declNetE /*implicit*/        { VARDTYPE("");/*default_nettype*/} list_of_variable_decl_assignments	{ }
	;

tf_port_declaration:		// ==IEEE: tf_port_declaration
	//			// Used inside function; followed by ';'
	//			// SIMILAR to port_declaration
	//
		port_directionReset var_data_type	{ VARDTYPE($2); }  list_of_tf_variable_identifiers ';'	{ }
	|	port_directionReset implicit_typeE	{ VARDTYPE($2); }  list_of_tf_variable_identifiers ';'	{ }
	;

integer_atom_type<str>:		// ==IEEE: integer_atom_type
		yBYTE					{ $<fl>$=$<fl>1; $$=$1; }
	|	ySHORTINT				{ $<fl>$=$<fl>1; $$=$1; }
	|	yINT					{ $<fl>$=$<fl>1; $$=$1; }
	|	yLONGINT				{ $<fl>$=$<fl>1; $$=$1; }
	|	yINTEGER				{ $<fl>$=$<fl>1; $$=$1; }
	|	yTIME					{ $<fl>$=$<fl>1; $$=$1; }
	;

integer_vector_type<str>:	// ==IEEE: integer_atom_type
		yBIT					{ $<fl>$=$<fl>1; $$=$1; }
	|	yLOGIC					{ $<fl>$=$<fl>1; $$=$1; }
	|	yREG					{ $<fl>$=$<fl>1; $$=$1; }
	;

non_integer_type<str>:		// ==IEEE: non_integer_type
		ySHORTREAL				{ $<fl>$=$<fl>1; $$=$1; }
	|	yREAL					{ $<fl>$=$<fl>1; $$=$1; }
	|	yREALTIME				{ $<fl>$=$<fl>1; $$=$1; }
	;

signingE<str>:			// IEEE: signing - plus empty
		/*empty*/ 				{ $$=""; }
	|	signing					{ $<fl>$=$<fl>1; $$=$1; }
	;

signing<str>:			// ==IEEE: signing
		ySIGNED					{ $<fl>$=$<fl>1; $$=$1; }
	|	yUNSIGNED				{ $<fl>$=$<fl>1; $$=$1; }
	;

//************************************************
// Data Types

casting_type<str>:		// IEEE: casting_type
		simple_type				{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: constant_primary
	//			// In expr:cast this is expanded to just "expr"
	//
	//			// IEEE: signing
	|	ySIGNED					{ $<fl>$=$<fl>1; $$=$1; }
	|	yUNSIGNED				{ $<fl>$=$<fl>1; $$=$1; }
	|	ySTRING					{ $<fl>$=$<fl>1; $$=$1; }
	|	yCONST__ETC/*then `*/			{ $<fl>$=$<fl>1; $$=$1; }
	;

simple_type<str>:		// ==IEEE: simple_type
	//			// IEEE: integer_type
		integer_atom_type			{ $<fl>$=$<fl>1; $$=$1; }
	|	integer_vector_type			{ $<fl>$=$<fl>1; $$=$1; }
	|	non_integer_type			{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: ps_type_identifier
	//			// IEEE: ps_parameter_identifier (presumably a PARAMETER TYPE)
	|	ps_type					{ $<fl>$=$<fl>1; $$=$1; }
	//			// { generate_block_identifer ... } '.'
	//			// Need to determine if generate_block_identifier can be lex-detected
	;

data_typeVar<str>:		// IEEE: data_type + virtual_interface_declaration
		data_type				{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: virtual_interface_declaration
	|	yVIRTUAL__INTERFACE yINTERFACE id/*interface*/ parameter_value_assignmentE '.' id/*modport*/
			{ $<fl>$=$<fl>1; $$=SPACED($1,SPACED($2,$3)); }
	;

data_type<str>:			// ==IEEE: data_type, excluding class_type etc references
		integer_vector_type signingE rangeListE	{ $<fl>$=$<fl>1; $$=SPACED($1,SPACED($2,$3)); }
	|	integer_atom_type signingE		{ $<fl>$=$<fl>1; $$=SPACED($1,$2); }
	|	non_integer_type			{ $<fl>$=$<fl>1; $$=$1; }
	|	ySTRUCT        packedSigningE '{' { PARSEP->symPushNewAnon(VAstType::STRUCT); }
	/*cont*/	struct_union_memberList '}' packed_dimensionListE
			{ $<fl>$=$<fl>1; $$=$1; PARSEP->symPopScope(VAstType::STRUCT); }
	|	yUNION taggedE packedSigningE '{' { PARSEP->symPushNewAnon(VAstType::UNION); }
	/*cont*/	struct_union_memberList '}' packed_dimensionListE
			{ $<fl>$=$<fl>1; $$=$1; PARSEP->symPopScope(VAstType::UNION); }
	|	enumDecl				{ $<fl>$=$<fl>1; $$=$1; }
	|	ySTRING					{ $<fl>$=$<fl>1; $$=$1; }
	|	yCHANDLE				{ $<fl>$=$<fl>1; $$=$1; }
	//			// Rules overlap virtual_interface_declaration
	//			// Parameters here are SV2009
	|	yVIRTUAL__INTERFACE yINTERFACE id/*interface*/ parameter_value_assignmentE
			{ $<fl>$=$<fl>1; $$=SPACED($1,SPACED($2,$3)); }
	|	yVIRTUAL__anyID                id/*interface*/ parameter_value_assignmentE
			{ $<fl>$=$<fl>1; $$=SPACED($1,$2); }
	//
	//			// IEEE: [ class_scope | package_scope ] type_identifier { packed_dimension }
	//			// See data_type
	//			// IEEE: class_type
	//			// See data_type
	|	yEVENT					{ $<fl>$=$<fl>1; $$=$1; }
	|	type_reference				{ $<fl>$=$<fl>1; $$=$1; }
	//
	//----------------------
	//			// REFERENCES
	//
	//			// IEEE: [ class_scope | package_scope ] type_identifier { packed_dimension }
	|	ps_type  packed_dimensionListE		{ $<fl>$=$<fl>1; $$=$1+$2; }
	|	class_scope_type packed_dimensionListE	{ $<fl>$=$<fl>1; $$=$1+$2; }
	//			// IEEE: class_type
	|	class_typeWithoutId			{ $<fl>$=$<fl>1; $$=$<str>1; }
	//			// IEEE: ps_covergroup_identifier
	|	ps_covergroup_identifier		{ $<fl>$=$<fl>1; $$=$1; }
	;

// IEEE: struct_union - not needed, expanded in data_type

data_type_or_void<str>:		// ==IEEE: data_type_or_void
		data_type				{ $<fl>$=$<fl>1; $$=$1; }
	|	yVOID					{ $<fl>$=$<fl>1; $$=$1; }
	;

var_data_type<str>:		// ==IEEE: var_data_type
		data_type				{ $<fl>$=$<fl>1; $$=$1; }
	|	yVAR data_type				{ $<fl>$=$<fl>1; $$=$1; }
	|	yVAR implicit_typeE			{ $<fl>$=$<fl>1; $$=$1; }
	;

type_reference<str>:		// ==IEEE: type_reference
		yTYPE '(' exprOrDataType ')'		{ $<fl>$=$<fl>1; $$="type("+$3+")"; }
	;

struct_union_memberList:	// IEEE: { struct_union_member }
		struct_union_member				{ }
	|	struct_union_memberList struct_union_member	{ }
	;

struct_union_member:		// ==IEEE: struct_union_member
		random_qualifierE data_type_or_void { VARRESET_NONLIST("member"); VARDTYPE(SPACED($1,$2)); }
	/*cont*/	list_of_variable_decl_assignments ';'	{ }
	;

list_of_variable_decl_assignments:	// ==IEEE: list_of_variable_decl_assignments
		variable_decl_assignment			{ }
	|	list_of_variable_decl_assignments ',' variable_decl_assignment	{ }
	;

variable_decl_assignment:	// ==IEEE: variable_decl_assignment
		id variable_dimensionListE sigAttrListE
			{ VARDONE($<fl>1, $1, $2, ""); }
	|	id variable_dimensionListE sigAttrListE '=' variable_declExpr
			{ VARDONE($<fl>1, $1, $2, $5); }
	|	idSVKwd					{ }
	//
	//			// IEEE: "dynamic_array_variable_identifier '[' ']' [ '=' dynamic_array_new ]"
	//			// Matches above with variable_dimensionE = "[]"
	//			// IEEE: "class_variable_identifier [ '=' class_new ]"
	//			// variable_dimensionE must be empty
	//			// Pushed into variable_declExpr:dynamic_array_new
	//
	//			// IEEE: "[ covergroup_variable_identifier ] '=' class_new
	//			// Pushed into variable_declExpr:class_new
	|	'=' class_new				{ }
	;

list_of_tf_variable_identifiers: // ==IEEE: list_of_tf_variable_identifiers
		tf_variable_identifier			{ }
	|	list_of_tf_variable_identifiers ',' tf_variable_identifier	{ }
	;

tf_variable_identifier:		// IEEE: part of list_of_tf_variable_identifiers
		id variable_dimensionListE sigAttrListE
			{ VARDONE($<fl>1, $1, $2, ""); }
	|	id variable_dimensionListE sigAttrListE '=' expr
			{ VARDONE($<fl>1, $1, $2, $5); }
	;

variable_declExpr<str>:		// IEEE: part of variable_decl_assignment - rhs of expr
		expr					{ $<fl>$=$<fl>1; $$=$1; }
	|	dynamic_array_new			{ $<fl>$=$<fl>1; $$=$1; }
	|	class_new				{ $<fl>$=$<fl>1; $$=$1; }
	;

variable_dimensionListE<str>:	// IEEE: variable_dimension + empty
		/*empty*/				{ $$=""; }
	|	variable_dimensionList			{ $<fl>$=$<fl>1; $$=$1; }
	;

variable_dimensionList<str>:	// IEEE: variable_dimension + empty
		variable_dimension			{ $<fl>$=$<fl>1; $$=$1; }
	|	variable_dimensionList variable_dimension	{ $<fl>$=$<fl>1; $$=$1+$2; }
	;

variable_dimension<str>:	// ==IEEE: variable_dimension
	//			// IEEE: unsized_dimension
		'[' ']'					{ $<fl>$=$<fl>1; $$=""; }
	//			// IEEE: unpacked_dimension
	|	anyrange				{ $<fl>$=$<fl>1; $$=$1; }
	|	'[' constExpr ']'			{ $<fl>$=$<fl>1; $$="["+$2+"]"; }
	//			// IEEE: associative_dimension
	|	'[' data_type ']'			{ $<fl>$=$<fl>1; $$="["+$2+"]"; }
	|	yP_BRASTAR ']'				{ $<fl>$=$<fl>1; $$="[*]"; }
	|	'[' '*' ']'				{ $<fl>$=$<fl>1; $$="[*]"; }
	//			// IEEE: queue_dimension
	//			// '[' '$' ']' -- $ is part of expr
	//			// '[' '$' ':' expr ']' -- anyrange:expr:$
	;

random_qualifierE<str>:		// IEEE: random_qualifier + empty
		/*empty*/				{ $$=""; }
	|	random_qualifier			{ $<fl>$=$<fl>1; $$=$1; }
	;

random_qualifier<str>:		// ==IEEE: random_qualifier
		yRAND					{ $<fl>$=$<fl>1; $$=$1; }
	|	yRANDC					{ $<fl>$=$<fl>1; $$=$1; }
	;

taggedE:
		/*empty*/				{ }
	|	yTAGGED					{ }
	;

packedSigningE:
		/*empty*/				{ }
	|	yPACKED signingE			{ }
	;

// IEEE: part of data_type
enumDecl<str>:
		yENUM enum_base_typeE '{' enum_nameList '}' rangeListE { $$=$2; }
	;

enum_base_typeE<str>:	// IEEE: enum_base_type
		/* empty */				{ $$="enum"; }
	//			// Not in spec, but obviously "enum [1:0]" should work
	//			// implicit_type expanded, without empty
	|	signingE rangeList			{ $<fl>$=$<fl>1; $$=$1+$2; }
	|	signing					{ $<fl>$=$<fl>1; $$=$1; }
	//
	|	integer_atom_type signingE		{ $<fl>$=$<fl>1; $$=$1; }
	|	integer_vector_type signingE regrangeE	{ $<fl>$=$<fl>1; $$=$1; }
	|	yaID__aTYPE regrangeE			{ $<fl>$=$<fl>1; $$=$1; }
	;

enum_nameList:
		enum_name_declaration			{ }
	|	enum_nameList ',' enum_name_declaration	{ }
	;

enum_name_declaration:		// ==IEEE: enum_name_declaration
		idAny/*enum_identifier*/ enumNameRangeE enumNameStartE	{ }
	;

enumNameRangeE:			// IEEE: second part of enum_name_declaration
		/* empty */				{ }
	|	'[' yaINTNUM ']'			{ }
	|	'[' yaINTNUM ':' yaINTNUM ']'		{ }
	;

enumNameStartE:			// IEEE: third part of enum_name_declaration
		/* empty */				{ }
	|	'=' constExpr				{ }
	;

//************************************************
// Typedef

data_declaration:		// ==IEEE: data_declaration
	//			// VARRESET can't be called here - conflicts
		data_declarationVar			{ }
	|	type_declaration			{ }
	|	package_import_declaration		{ }
	//			// IEEE: virtual_interface_declaration
	//			// "yVIRTUAL yID yID" looks just like a data_declaration
	//			// Therefore the virtual_interface_declaration term isn't used
	;

class_property:			// ==IEEE: class_property, which is {property_qualifier} data_declaration
		memberQualResetListE data_declarationVarClass		{ }
	|	yCONST__ETC memberQualResetListE data_declarationVarClass	{ }
	|	memberQualResetListE type_declaration			{ }
	|	memberQualResetListE package_import_declaration	{ }
	//			// IEEE: virtual_interface_declaration
	//			// "yVIRTUAL yID yID" looks just like a data_declaration
	//			// Therefore the virtual_interface_declaration term isn't used
	;

data_declarationVar:		// IEEE: part of data_declaration
	//			// The first declaration has complications between assuming what's the type vs ID declaring
		data_declarationVarFront list_of_variable_decl_assignments ';'	{ }
	;

data_declarationVarClass:	// IEEE: part of data_declaration (for class_property)
	//			// The first declaration has complications between assuming what's the type vs ID declaring
		data_declarationVarFrontClass list_of_variable_decl_assignments ';'	{ }
	;

data_declarationVarFront:	// IEEE: part of data_declaration
	//			// implicit_type expanded into /*empty*/ or "signingE rangeList"
		constE yVAR lifetimeE data_type	 { VARRESET(); VARDECL("var"); VARDTYPE(SPACED($1,$4)); }
	|	constE yVAR lifetimeE		 { VARRESET(); VARDECL("var"); VARDTYPE($1); }
	|	constE yVAR lifetimeE signingE rangeList { VARRESET(); VARDECL("var"); VARDTYPE(SPACED($1,SPACED($4,$5))); }
	//
	//			// Expanded: "constE lifetimeE data_type"
	|	/**/		      data_typeVar	{ VARRESET(); VARDECL("var"); VARDTYPE($1); }
	|	/**/	    lifetime  data_typeVar	{ VARRESET(); VARDECL("var"); VARDTYPE($2); }
	|	yCONST__ETC lifetimeE data_typeVar	{ VARRESET(); VARDECL("var"); VARDTYPE(SPACED($1,$3)); }
	//			// = class_new is in variable_decl_assignment
	//
	//			// IEEE: virtual_interface_declaration
	//			// data_type includes VIRTUAL_INTERFACE, so added to data_typeVar
	;

data_declarationVarFrontClass:	// IEEE: part of data_declaration (for class_property)
	//			// VARRESET called before this rule
	//			// yCONST is removed, added to memberQual rules
	//			// implicit_type expanded into /*empty*/ or "signingE rangeList"
		yVAR lifetimeE data_type	 { VARDECL("var"); VARDTYPE(SPACED(GRAMMARP->m_varDType,$3)); }
	|	yVAR lifetimeE			 { VARDECL("var"); VARDTYPE(GRAMMARP->m_varDType); }
	|	yVAR lifetimeE signingE rangeList { VARDECL("var"); VARDTYPE(SPACED(GRAMMARP->m_varDType,SPACED($3,$4))); }
	//
	//			// Expanded: "constE lifetimeE data_type"
	|	/**/		      data_type	{ VARDECL("var"); VARDTYPE(SPACED(GRAMMARP->m_varDType,$1)); }
	//			// lifetime is removed, added to memberQual rules to avoid conflict
	//			// yCONST is removed, added to memberQual rules to avoid conflict
	//			// = class_new is in variable_decl_assignment
	;

constE<str>:			// IEEE: part of data_declaration
		/* empty */				{ $$ = ""; }
	|	yCONST__ETC				{ $$ = $1; }
	;

implicit_typeE<str>:		// IEEE: part of *data_type_or_implicit
	//			// Also expanded in data_declaration
		/* empty */				{ $$ = ""; }
	|	signingE rangeList			{ $$ = SPACED($1,$2); }
	|	signing					{ $$ = $1; }
	;

assertion_variable_declaration: // IEEE: assertion_variable_declaration
	//			// IEEE: var_data_type expanded
		var_data_type list_of_variable_decl_assignments ';'	{ }
	;

type_declaration:		// ==IEEE: type_declaration
	//			// Use idAny, as we can redeclare a typedef on an existing typedef
		yTYPEDEF data_type idAny variable_dimensionListE ';'	{ VARDONETYPEDEF($<fl>1,$3,$2,$4); }
	|	yTYPEDEF id/*interface*/ bit_selectE '.' idAny/*type*/ idAny/*type*/ ';'
			{ VARDONETYPEDEF($<fl>1,$6,$2+$3+"."+$5,""); }
	//			// Combines into above "data_type id" rule
	|	yTYPEDEF id ';'				{ VARDONETYPEDEF($<fl>1,$2,"",""); }
	|	yTYPEDEF yENUM idAny ';'		{ PARSEP->syms().replaceInsert(VAstType::ENUM, $3); }
	|	yTYPEDEF ySTRUCT idAny ';'		{ PARSEP->syms().replaceInsert(VAstType::STRUCT, $3); }
	|	yTYPEDEF yUNION idAny ';'		{ PARSEP->syms().replaceInsert(VAstType::UNION, $3); }
	|	yTYPEDEF yCLASS idAny ';'		{ PARSEP->syms().replaceInsert(VAstType::CLASS, $3); }
	;

//************************************************
// Module Items

module_itemListE:		// IEEE: Part of module_declaration
		/* empty */				{ }
	|	module_itemList				{ }
	;

module_itemList:		// IEEE: Part of module_declaration
		module_item				{ }
	|	module_itemList module_item		{ }
	;

module_item:			// ==IEEE: module_item
		port_declaration ';'			{ }
	|	non_port_module_item			{ }
	;

non_port_module_item:		// ==IEEE: non_port_module_item
		generate_region				{ }
	|	module_or_generate_item			{ }
	|	specify_block				{ }
	|	specparam_declaration			{ }
	|	program_declaration			{ }
	|	module_declaration			{ }
	|	interface_declaration			{ }
	|	timeunits_declaration			{ }
	;

module_or_generate_item:	// ==IEEE: module_or_generate_item
	//			// IEEE: parameter_override
		yDEFPARAM list_of_defparam_assignments ';'	{ }
	//			// IEEE: gate_instantiation + udp_instantiation + module_instantiation
	//			// not here, see etcInst in module_common_item
	//			// We joined udp & module definitions, so this goes here
	|	combinational_body			{ }
	//			// This module_common_item shared with interface_or_generate_item:module_common_item
	|	module_common_item			{ }
	;

module_common_item:		// ==IEEE: module_common_item
		module_or_generate_item_declaration	{ }
	//			// IEEE: interface_instantiation
	//			// + IEEE: program_instantiation
	//			// + module_instantiation from module_or_generate_item
	|	etcInst					{ }
	|	assertion_item				{ }
	|	bind_directive				{ }
	|	continuous_assign			{ }
	//			// IEEE: net_alias
	|	yALIAS variable_lvalue aliasEqList ';'	{ }
	|	initial_construct			{ }
	|	final_construct				{ }
	//			// IEEE: always_construct
	|	yALWAYS stmtBlock			{ }
	|	loop_generate_construct			{ }
	|	conditional_generate_construct		{ }
	|	elaboration_system_task			{ }
	//
	|	error ';'				{ }
	;

continuous_assign:		// IEEE: continuous_assign
		yASSIGN strengthSpecE delayE assignList ';'	{ }
	;

initial_construct:		// IEEE: initial_construct
		yINITIAL stmtBlock			{ }
	;

final_construct:		// IEEE: final_construct
		yFINAL stmtBlock			{ }
	;

module_or_generate_item_declaration:	// ==IEEE: module_or_generate_item_declaration
		package_or_generate_item_declaration	{ }
	| 	genvar_declaration			{ }
	|	clocking_declaration			{ }
	|	yDEFAULT yCLOCKING idAny/*new-clocking_identifier*/ ';'	{ }
	|	yDEFAULT yDISABLE yIFF expr/*expression_or_dist*/ ';'	{ }
	;

aliasEqList:			// IEEE: part of net_alias
		'=' variable_lvalue			{ }
	|	aliasEqList '=' variable_lvalue		{ }
	;

bind_directive:			// ==IEEE: bind_directive + bind_target_scope
	//			// ';' - Note IEEE grammar is wrong, includes extra ';' - it's already in module_instantiation
	//			// We merged the rules - id may be a bind_target_instance or module_identifier or interface_identifier
		yBIND id bit_selectE bind_instantiation	{ }
	|	yBIND id/*module_or_interface*/ ':' bind_target_instance_list bind_instantiation	{ }
	;

bind_target_instance_list:	// ==IEEE: bind_target_instance_list
		bind_target_instance			{ }
	|	bind_target_instance_list ',' bind_target_instance	{ }
	;

bind_target_instance:		// ==IEEE: bind_target_instance
		hierarchical_identifierBit		{ }
	;

bind_instantiation:		// ==IEEE: bind_instantiation
	//			// IEEE: program_instantiation
	//			// IEEE: + module_instantiation
	//			// IEEE: + interface_instantiation
		etcInst					{ }
	;

//************************************************
// Generates
//
// Way down in generate_item is speced a difference between module,
// interface and checker generates.  modules and interfaces are almost
// identical (minus DEFPARAMs) so we overlap them.  Checkers are too
// different, so we copy all rules for checkers.

generate_region:		// ==IEEE: generate_region
		yGENERATE ~c~genTopBlock yENDGENERATE	{ }
	;
c_generate_region:		// IEEE: generate_region (for checkers)
		BISONPRE_COPY(generate_region,{s/~c~/c_/g})	// {copied}
	;

generate_block:			// IEEE: generate_block
		~c~generate_item			{ }
	|	~c~genItemBegin				{ }
	;

c_generate_block:		// IEEE: generate_block (for checkers)
		BISONPRE_COPY(generate_block,{s/~c~/c_/g})	// {copied}
	;

genTopBlock:
		~c~genItemList				{ }
	|	~c~genItemBegin				{ }
	;

c_genTopBlock:			// (for checkers)
		BISONPRE_COPY(genTopBlock,{s/~c~/c_/g})		// {copied}
	;

genItemBegin:			// IEEE: part of generate_block
		yBEGIN ~c~genItemList yEND		{ }
	|	yBEGIN yEND				{ }
	|	id ':' yBEGIN ~c~genItemList yEND endLabelE	{ }
	|	id ':' yBEGIN             yEND endLabelE	{ }
	|	yBEGIN ':' idAny ~c~genItemList yEND endLabelE	{ }
	|	yBEGIN ':' idAny             yEND endLabelE	{ }
	;

c_genItemBegin:			// IEEE: part of generate_block (for checkers)
		BISONPRE_COPY(genItemBegin,{s/~c~/c_/g})		// {copied}
	;

genItemList:
		~c~generate_item			{ }
	|	~c~genItemList ~c~generate_item		{ }
	;

c_genItemList:			// (for checkers)
		BISONPRE_COPY(genItemList,{s/~c~/c_/g})		// {copied}
	;

generate_item:			// IEEE: module_or_interface_or_generate_item
	//			// Only legal when in a generate under a module (or interface under a module)
		module_or_generate_item			{ }
	//			// Only legal when in a generate under an interface
	|	interface_or_generate_item		{ }
	//			// IEEE: checker_or_generate_item
	//			// Only legal when in a generate under a checker
	//			// so below in c_generate_item
	;

c_generate_item:			// IEEE: generate_item (for checkers)
		checker_or_generate_item		{ }
	;

conditional_generate_construct:	// ==IEEE: conditional_generate_construct
	//			// IEEE: case_generate_construct
		yCASE  '(' expr ')' yENDCASE	{ }
	|	yCASE  '(' expr ')' ~c~case_generate_itemList yENDCASE	{ }
	//			// IEEE: if_generate_construct
	|	yIF '(' expr ')' ~c~generate_block	%prec prLOWER_THAN_ELSE	{ }
	|	yIF '(' expr ')' ~c~generate_block yELSE ~c~generate_block	{ }
	;

c_conditional_generate_construct:	// IEEE: conditional_generate_construct (for checkers)
		BISONPRE_COPY(conditional_generate_construct,{s/~c~/c_/g})	// {copied}
	;

loop_generate_construct:	// ==IEEE: loop_generate_construct
		yFOR '(' genvar_initialization ';' expr ';' genvar_iteration ')' ~c~generate_block
			{ }
	;

c_loop_generate_construct:	// IEEE: loop_generate_construct (for checkers)
		BISONPRE_COPY(loop_generate_construct,{s/~c~/c_/g})	// {copied}
	;

genvar_initialization:		// ==IEEE: genvar_initalization
	        id '=' constExpr			{ }
	|	yGENVAR genvar_identifierDecl '=' constExpr	{ }
	;

genvar_iteration:		// ==IEEE: genvar_iteration
	//			// IEEE: assignment_operator plus IDs
	|	id '=' 		expr			{ }
	|	id yP_PLUSEQ	expr			{ }
	|	id yP_MINUSEQ	expr			{ }
	|	id yP_TIMESEQ	expr			{ }
	|	id yP_DIVEQ	expr			{ }
	|	id yP_MODEQ	expr			{ }
	|	id yP_ANDEQ	expr			{ }
	|	id yP_OREQ	expr			{ }
	|	id yP_XOREQ	expr			{ }
	|	id yP_SLEFTEQ	expr			{ }
	|	id yP_SRIGHTEQ	expr			{ }
	|	id yP_SSRIGHTEQ	expr			{ }
	//			// inc_or_dec_operator
	|	yP_PLUSPLUS id				{ }
	|	yP_MINUSMINUS id			{ }
	|	id yP_PLUSPLUS				{ }
	|	id yP_MINUSMINUS			{ }
	;

case_generate_itemList:		// IEEE: { case_generate_item }
		~c~case_generate_item			{ }
	|	~c~case_generate_itemList ~c~case_generate_item	{ }
	;

c_case_generate_itemList:	// IEEE: { case_generate_item } (for checkers)
		BISONPRE_COPY(case_generate_itemList,{s/~c~/c_/g})	// {copied}
	;

case_generate_item:		// ==IEEE: case_generate_item
		caseCondList ':' ~c~generate_block	{ }
	|	yDEFAULT ':' ~c~generate_block		{ }
	|	yDEFAULT ~c~generate_block		{ }
	;

c_case_generate_item:		// IEEE: case_generate_item (for checkers)
		BISONPRE_COPY(case_generate_item,{s/~c~/c_/g})	// {copied}
	;

//************************************************
// Assignments and register declarations

assignList:
		assignOne				{ }
	|	assignList ',' assignOne		{ }
	;

assignOne:
		variable_lvalue '=' expr		{ PARSEP->contassignCb($<fl>2,"assign",$1,$3); }
	;

delay_or_event_controlE:			// IEEE: delay_or_event_control plus empty
		/* empty */				{ }
	|	delay_control				{ } /* ignored */
	|	event_control				{ } /* ignored */
	|	yREPEAT '(' expr ')' event_control	{ } /* ignored */
	;

delayE:
		/* empty */				{ }
	|	delay_control				{ } /* ignored */
	;

delay_control:			// ==IEEE: delay_control
		'#' delay_value				{ } /* ignored */
	|	'#' '(' minTypMax ')'			{ } /* ignored */
	|	'#' '(' minTypMax ',' minTypMax ')'		{ } /* ignored */
	|	'#' '(' minTypMax ',' minTypMax ',' minTypMax ')'	{ } /* ignored */
	;

delay_value:			// ==IEEE:delay_value
	//			// IEEE: ps_identifier
		ps_id_etc	 			{ }
	|	yaINTNUM 				{ }
	|	yaFLOATNUM 				{ }
	|	yaTIMENUM 				{ }
	;

delayExpr:
		expr					{ }
	;

minTypMax:			// IEEE: mintypmax_expression and constant_mintypmax_expression
		delayExpr				{ }
	|	delayExpr ':' delayExpr ':' delayExpr	{ }
	;

netSigList:			// IEEE: list_of_port_identifiers
		netSig  				{ }
	|	netSigList ',' netSig		       	{ }
	;

netSig:				// IEEE: net_decl_assignment -  one element from list_of_port_identifiers
		netId sigAttrListE			{ VARDONE($<fl>1, $1, "", ""); }
	|	netId sigAttrListE '=' expr		{ VARDONE($<fl>1, $1, "", $4); }
	|	netId rangeList sigAttrListE		{ VARDONE($<fl>1, $1, $2, ""); }
	;

netId<str>:
		id/*new-net*/				{ $<fl>$=$<fl>1; $$=$1; }
	|	idSVKwd					{ $<fl>$=$<fl>1; $$=$1; }
	;

sigAttrListE:
		/* empty */				{ }
	;

rangeListE<str>:		// IEEE: [{packed_dimension}]
		/* empty */				{ $$=""; }
	|	rangeList				{ $<fl>$=$<fl>1; $$ = $1; }
	;

rangeList<str>:			// IEEE: {packed_dimension}
		anyrange				{ $<fl>$=$<fl>1; $$ = $1; }
	|	rangeList anyrange			{ $<fl>$=$<fl>1; $$ = $1+$2; }
	;

regrangeE<str>:
		/* empty */    		               	{ $$=""; }
	|	anyrange 				{ $<fl>$=$<fl>1; $$=$1; }
	;

bit_selectE<str>:		// IEEE: constant_bit_select (IEEE included empty)
		/* empty */				{ $$ = ""; }
	|	'[' constExpr ']'			{ $<fl>$=$<fl>1; $$ = "["+$2+"]"; }
	;

// IEEE: select
// Merged into more general idArray

anyrange<str>:
		'[' constExpr ':' constExpr ']'		{ $<fl>$=$<fl>1; $$ = "["+$2+":"+$4+"]"; }
	;

packed_dimensionListE<str>:	// IEEE: [{ packed_dimension }]
		/* empty */				{ $$=""; }
	|	packed_dimensionList			{ $<fl>$=$<fl>1; $$=$1; }
	;

packed_dimensionList<str>:	// IEEE: { packed_dimension }
		packed_dimension			{ $<fl>$=$<fl>1; $$=$1; }
	|	packed_dimensionList packed_dimension	{ $<fl>$=$<fl>1; $$=$1+$2; }
	;

packed_dimension<str>:		// ==IEEE: packed_dimension
		anyrange				{ $<fl>$=$<fl>1; $$=$1; }
	|	'[' ']'					{ $$="[]"; }
	;

//************************************************
// Parameters

param_assignment:		// ==IEEE: param_assignment
	//			// IEEE: constant_param_expression
	//			// constant_param_expression: '$' is in expr
		id/*new-parameter*/ variable_dimensionListE sigAttrListE '=' exprOrDataType
			{ $<fl>$=$<fl>1; VARDONE($<fl>1, $1, $2, $5); }
	//			// only legal in port list; throws error if not set
	|	id/*new-parameter*/ variable_dimensionListE sigAttrListE
			{ $<fl>$=$<fl>1; VARDONE($<fl>1, $1, $2, ""); NEED_S09($<fl>1,"optional parameter defaults"); }
	;

list_of_param_assignments:	// ==IEEE: list_of_param_assignments
		param_assignment			{ }
	|	list_of_param_assignments ',' param_assignment	{ }
	;

list_of_defparam_assignments:	// ==IEEE: list_of_defparam_assignments
		defparam_assignment			{ }
	|	list_of_defparam_assignments ',' defparam_assignment	{ }
	;

defparam_assignment:		// ==IEEE: defparam_assignment
		hierarchical_identifier/*parameter*/ '=' expr	{ PARSEP->defparamCb($<fl>2,"defparam",$1,$3); }
	;

//************************************************
// Instances
// We don't know identifier types, so this matches all module,udp,etc instantiation
//   module_id      [#(params)]   name  (pins) [, name ...] ;	// module_instantiation
//   gate (strong0) [#(delay)]   [name] (pins) [, (pins)...] ;	// gate_instantiation
//   program_id     [#(params}]   name ;			// program_instantiation
//   interface_id   [#(params}]   name ;			// interface_instantiation
//   checker_id			  name  (pins) ;		// checker_instantiation

etcInst:			// IEEE: module_instantiation + gate_instantiation + udp_instantiation
		instName {INSTPREP($1,1);} strengthSpecE parameter_value_assignmentE {INSTPREP($1,0);} instnameList ';'
		 	{ }
	;

instName<str>:
		gateKwd					{ $<fl>$=$<fl>1; $$=$1; }
	//			// id is-a: interface_identifier
	//			//       or program_identifier
	//			//       or udp_identifier
	//			//       or module_identifier
	|	id					{ $<fl>$=$<fl>1; $$=$1; }
	;

instnameList:
		instnameParen				{ }
	|	instnameList ',' instnameParen		{ }
	;

instnameParen:
		instname cellpinList ')'		{ PARSEP->endcellCb($<fl>3,""); }
	;

instname:
	//			// id is-a: hierarchical_instance (interface)
	//			// 	 or instance_identifier   (module)
	//			// 	 or instance_identifier   (program)
	//			// 	 or udp_instance	  (udp)
		id instRangeE '(' 			{ PARSEP->instantCb($<fl>1, GRAMMARP->m_cellMod, $1, $2); PINPARAMS(); }
	|	instRangeE '(' 				{ PARSEP->instantCb($<fl>2, GRAMMARP->m_cellMod, "", $1); PINPARAMS(); } // UDP
	;

instRangeE<str>:
		/* empty */				{ $$ = ""; }
	|	'[' constExpr ']'			{ $<fl>$=$<fl>1; $$ = "["+$2+"]"; }
	|	'[' constExpr ':' constExpr ']'		{ $<fl>$=$<fl>1; $$ = "["+$2+":"+$4+"]"; }
	;

cellpinList:
		{ VARRESET_LIST(""); } cellpinItList	{ VARRESET_NONLIST(""); }
	;

cellpinItList:			// IEEE: list_of_port_connections + list_of_parameter_assignmente
		cellpinItemE				{ }
	|	cellpinItList ',' cellpinItemE		{ }
	;

cellpinItemE:			// IEEE: named_port_connection + named_parameter_assignment + empty
		/* empty: ',,' is legal */		{ PINNUMINC(); }  /*PINDONE(yylval.fl,"",""); <- No, as then () implies a pin*/
	|	yP_DOTSTAR				{ PINDONE($<fl>1,"*","*");PINNUMINC(); }
	|	'.' idSVKwd				{ PINDONE($<fl>1,$2,$2);  PINNUMINC(); }
	|	'.' idAny				{ PINDONE($<fl>1,$2,$2);  PINNUMINC(); }
	|	'.' idAny '(' ')'			{ PINDONE($<fl>1,$2,"");  PINNUMINC(); }
	//			// mintypmax is expanded here, as it might be a UDP or gate primitive
	//			// For checkers, this needs to not just expr, but include events + properties
	|	'.' idAny '(' pev_expr ')'		{ PINDONE($<fl>1,$2,$4);  PINNUMINC(); }
	|	'.' idAny '(' pev_expr ':' expr ')'	{ PINDONE($<fl>1,$2,$4);  PINNUMINC(); }
	|	'.' idAny '(' pev_expr ':' expr ':' expr ')' { PINDONE($<fl>1,$2,$4);  PINNUMINC(); }
	//			// For parameters
	|	'.' idAny '(' data_type ')'		{ PINDONE($<fl>1,$2,$4);  PINNUMINC(); }
	//			// For parameters
	|	data_type				{ PINDONE($<fl>1,"",$1);  PINNUMINC(); }
	//
	|	expr					{ PINDONE($<fl>1,"",$1);  PINNUMINC(); }
	|	expr ':' expr				{ PINDONE($<fl>1,"",$1);  PINNUMINC(); }
	|	expr ':' expr ':' expr			{ PINDONE($<fl>1,"",$1);  PINNUMINC(); }
	;

//************************************************
// EventControl lists

event_control:			// ==IEEE: event_control
		'@' '(' event_expression ')'		{ }
	|	'@' '*'					{ }
	|	'@' '(' '*' ')'				{ }
	//			// IEEE: hierarchical_event_identifier
	|	'@' idClassSel/*event_id or ps_or_hierarchical_sequence_identifier*/		{ }
	//			// IEEE: ps_or_hierarchical_sequence_identifier
	//			// sequence_instance without parens matches idClassSel above.
	//			// Ambiguity: "'@' sequence (-for-sequence" versus expr:delay_or_event_controlE "'@' id (-for-expr
	//			// For now we avoid this, as it's very unlikely someone would mix
	//			// 1995 delay with a sequence with parameters.
	//			// Alternatively split this out of event_control, and delay_or_event_controlE
	//			// and anywhere delay_or_event_controlE is called allow two expressions
	;

event_expression:		// IEEE: event_expression - split over several
	//			// ',' rules aren't valid in port lists - ev_expr is there.
	//			// Also eliminates left recursion to appease conflicts
		ev_expr					{ }
	|	event_expression ',' ev_expr %prec yOR	{ }	/* Verilog 2001 */
	;

senitemEdge<str>:		// IEEE: part of event_expression
	//			// Also called by pev_expr
		yPOSEDGE expr				{ $<fl>$=$<fl>1; $$=$1+" "+$2; }
	|	yPOSEDGE expr yIFF expr			{ $<fl>$=$<fl>1; $$=$1+" "+$2+" iff "+$4; }
	|	yNEGEDGE expr				{ $<fl>$=$<fl>1; $$=$1+" "+$2; }
	|	yNEGEDGE expr yIFF expr			{ $<fl>$=$<fl>1; $$=$1+" "+$2+" iff "+$4; }
	|	yEDGE expr				{ $<fl>$=$<fl>1; $$=$1+" "+$2; NEED_S09($<fl>1,"edge"); }
	|	yEDGE expr yIFF expr			{ $<fl>$=$<fl>1; $$=$1+" "+$2+" iff "+$4; NEED_S09($<fl>1,"edge"); }
	;

//************************************************
// Statements

stmtBlock:			// IEEE: statement + seq_block + par_block
		stmt					{ }
	;

seq_block:			// ==IEEE: seq_block
	//			// IEEE doesn't allow declarations in unnamed blocks, but several simulators do.
		seq_blockFront blockDeclStmtList yEND endLabelE	{ PARSEP->symPopScope(VAstType::BLOCK); }
	|	seq_blockFront /**/		 yEND endLabelE	{ PARSEP->symPopScope(VAstType::BLOCK); }
	;

par_block:			// ==IEEE: par_block
		par_blockFront blockDeclStmtList yJOIN endLabelE { PARSEP->symPopScope(VAstType::FORK); }
	|	par_blockFront /**/		 yJOIN endLabelE { PARSEP->symPopScope(VAstType::FORK); }
	;

seq_blockFront:			// IEEE: part of seq_block
		yBEGIN					 	{ PARSEP->symPushNewAnon(VAstType::BLOCK); }
	|	yBEGIN ':' idAny/*new-block_identifier*/	{ PARSEP->symPushNew(VAstType::BLOCK,$1); }
	;

par_blockFront:			// IEEE: part of par_block
		yFORK					{ PARSEP->symPushNewAnon(VAstType::FORK); }
	|	yFORK ':' idAny/*new-block_identifier*/	{ PARSEP->symPushNew(VAstType::FORK,$1); }
	;

blockDeclStmtList:		// IEEE: { block_item_declaration } { statement or null }
	//			// The spec seems to suggest a empty declaration isn't ok, but most simulators take it
		block_item_declarationList		{ }
	|	block_item_declarationList stmtList	{ }
	|	stmtList				{ }
	;

block_item_declarationList:	// IEEE: [ block_item_declaration ]
		block_item_declaration			{ }
	|	block_item_declarationList block_item_declaration	{ }
	;

block_item_declaration:		// ==IEEE: block_item_declaration
		data_declaration 			{ }
	|	local_parameter_declaration ';'		{ }
	|	parameter_declaration ';' 		{ }
	|	overload_declaration 			{ }
	|	let_declaration 			{ }
	;

stmtList:
		stmtBlock				{ }
	|	stmtList stmtBlock			{ }
	;

stmt:				// IEEE: statement_or_null == function_statement_or_null
		statement_item				{ }
	|	id/*block_identifier*/ ':' statement_item	{ }  /*S05 block creation rule*/
	//			// from _or_null
	|	';'					{ }
	;

statement_item:			// IEEE: statement_item
	//			// IEEE: operator_assignment
		foperator_assignment ';'		{ }
	//
	//		 	// IEEE: blocking_assignment
	//			// 1800-2009 restricts LHS of assignment to new to not have a range
	//			// This is ignored to avoid conflicts
	|	fexprLvalue '=' class_new ';'		{ }
	|	fexprLvalue '=' dynamic_array_new ';'	{ }
	//
	//			// IEEE: nonblocking_assignment
	|	fexprLvalue yP_LTE delay_or_event_controlE expr ';'	{ }
	//
	//			// IEEE: procedural_continuous_assignment
	|	yASSIGN expr '=' delay_or_event_controlE expr ';'	{ }
	|	yDEASSIGN variable_lvalue ';'		{ }
	|	yFORCE expr '=' expr ';'		{ }
	|	yRELEASE variable_lvalue ';'		{ }
	//
	//			// IEEE: case_statement
	|	unique_priorityE caseStart caseAttrE case_itemListE yENDCASE	{ }
	|	unique_priorityE caseStart caseAttrE yMATCHES case_patternListE yENDCASE	{ }
	|	unique_priorityE caseStart caseAttrE yINSIDE  case_insideListE yENDCASE	{ }
	//
	//			// IEEE: conditional_statement
	|	unique_priorityE yIF '(' expr ')' stmtBlock	%prec prLOWER_THAN_ELSE	{ }
	|	unique_priorityE yIF '(' expr ')' stmtBlock yELSE stmtBlock		{ }
	//
	|	finc_or_dec_expression ';'		{ }
	//			// IEEE: inc_or_dec_expression
	//			// Below under expr
	//
	//			// IEEE: subroutine_call_statement
	|	yVOID yP_TICK '(' function_subroutine_callNoMethod ')' ';' { }
	|	yVOID yP_TICK '(' expr '.' function_subroutine_callNoMethod ')' ';' { }
	//			// Expr included here to resolve our not knowing what is a method call
	//			// Expr here must result in a subroutine_call
	|	task_subroutine_callNoMethod ';'	{ }
	|	fexpr '.' array_methodNoRoot ';'	{ }
	|	fexpr '.' task_subroutine_callNoMethod ';'	{ }
	|	fexprScope ';'				{ }
	//			// Not here in IEEE; from class_constructor_declaration
	//			// Because we've joined class_constructor_declaration into generic functions
	//			// Way over-permissive;
	//			// IEEE: [ ySUPER '.' yNEW [ '(' list_of_arguments ')' ] ';' ]
	|	fexpr '.' class_new ';'		{ }
	//
	//			// IEEE: disable_statement
	|	yDISABLE hierarchical_identifier/*task_or_block*/ ';'	{ }
	|	yDISABLE yFORK ';'			{ }
	//			// IEEE: event_trigger
	|	yP_MINUSGT hierarchical_identifier/*event*/ ';'	{ }
	|	yP_MINUSGTGT delay_or_event_controlE hierarchical_identifier/*event*/ ';'	{ }
	//			// IEEE: loop_statement
	|	yFOREVER stmtBlock			{ }
	|	yREPEAT '(' expr ')' stmtBlock		{ }
	|	yWHILE '(' expr ')' stmtBlock		{ }
	//			// for's first ';' is in for_initalization
	|	yFOR '(' for_initialization expr ';' for_stepE ')' stmtBlock
				{ }
	|	yDO stmtBlock yWHILE '(' expr ')' ';'	{ }
	//			// IEEE says array_identifier here, but dotted accepted in VMM and 1800-2009
	|	yFOREACH '(' idClassForeach/*array_id[loop_variables]*/ ')' stmt	{ }
	//
	//			// IEEE: jump_statement
	|	yRETURN ';'				{ }
	|	yRETURN expr ';'			{ }
	|	yBREAK ';'				{ }
	|	yCONTINUE ';'				{ }
	//
	|	par_block				{ }
	//			// IEEE: procedural_timing_control_statement + procedural_timing_control
	|	delay_control stmtBlock			{ }
	|	event_control stmtBlock			{ }
	|	cycle_delay stmtBlock			{ }
	//
	|	seq_block				{ }
	//
	//			// IEEE: wait_statement
	|	yWAIT '(' expr ')' stmtBlock		{ }
	|	yWAIT yFORK ';'				{ }
	|	yWAIT_ORDER '(' hierarchical_identifierList ')' action_block	{ }
	//
	//			// IEEE: procedural_assertion_statement
	|	procedural_assertion_statement		{ }
	//
	//			// IEEE: clocking_drive ';'
	//			// clockvar_expression made to fexprLvalue to prevent reduce conflict
	//			// Note LTE in this context is highest precedence, so first on left wins
	|	fexprLvalue yP_LTE cycle_delay expr ';'	{ }
	//
	|	randsequence_statement			{ }
	//
	//			// IEEE: randcase_statement
	|	yRANDCASE case_itemList yENDCASE	{ }
	//
	|	expect_property_statement		{ }
	//
	|	error ';'				{ }
	;

operator_assignment:		// IEEE: operator_assignment
		~f~exprLvalue '=' delay_or_event_controlE expr { }
	|	~f~exprLvalue yP_PLUSEQ    expr		{ }
	|	~f~exprLvalue yP_MINUSEQ   expr		{ }
	|	~f~exprLvalue yP_TIMESEQ   expr		{ }
	|	~f~exprLvalue yP_DIVEQ     expr		{ }
	|	~f~exprLvalue yP_MODEQ     expr		{ }
	|	~f~exprLvalue yP_ANDEQ     expr		{ }
	|	~f~exprLvalue yP_OREQ      expr		{ }
	|	~f~exprLvalue yP_XOREQ     expr		{ }
	|	~f~exprLvalue yP_SLEFTEQ   expr		{ }
	|	~f~exprLvalue yP_SRIGHTEQ  expr		{ }
	|	~f~exprLvalue yP_SSRIGHTEQ expr		{ }
	;

foperator_assignment<str>:	// IEEE: operator_assignment (for first part of expression)
		BISONPRE_COPY(operator_assignment,{s/~f~/f/g})	// {copied}
	;

inc_or_dec_expression<str>:	// ==IEEE: inc_or_dec_expression
	//			// Need fexprScope instead of variable_lvalue to prevent conflict
		~l~exprScope yP_PLUSPLUS		{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	~l~exprScope yP_MINUSMINUS		{ $<fl>$=$<fl>1; $$ = $1+$2; }
	//			// Need expr instead of variable_lvalue to prevent conflict
	|	yP_PLUSPLUS	expr			{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	yP_MINUSMINUS	expr			{ $<fl>$=$<fl>1; $$ = $1+$2; }
	;

finc_or_dec_expression<str>:	// IEEE: inc_or_dec_expression (for first part of expression)
		BISONPRE_COPY(inc_or_dec_expression,{s/~l~/f/g})	// {copied}
	;

sinc_or_dec_expression<str>:	// IEEE: inc_or_dec_expression (for sequence_expression)
		BISONPRE_COPY(inc_or_dec_expression,{s/~l~/s/g})	// {copied}
	;

pinc_or_dec_expression<str>:	// IEEE: inc_or_dec_expression (for property_expression)
		BISONPRE_COPY(inc_or_dec_expression,{s/~l~/p/g})	// {copied}
	;

ev_inc_or_dec_expression<str>:	// IEEE: inc_or_dec_expression (for ev_expr)
		BISONPRE_COPY(inc_or_dec_expression,{s/~l~/ev_/g})	// {copied}
	;

pev_inc_or_dec_expression<str>:	// IEEE: inc_or_dec_expression (for pev_expr)
		BISONPRE_COPY(inc_or_dec_expression,{s/~l~/pev_/g})	// {copied}
	;

class_new<str>:			// ==IEEE: class_new
	//			// Special precence so (...) doesn't match expr
		yNEW__ETC				{ $<fl>$=$<fl>1; $$ = $1; }
	|	yNEW__ETC expr				{ $<fl>$=$<fl>1; $$ = $1+" "+$2; }
	//			// Grammer abiguity; we assume "new (x)" the () are a argument, not expr
	|	yNEW__PAREN '(' list_of_argumentsE ')'	{ $<fl>$=$<fl>1; $$ = $1+"("+$3+")"; }
	;

dynamic_array_new<str>:		// ==IEEE: dynamic_array_new
		yNEW__ETC '[' expr ']'			{ $<fl>$=$<fl>1; $$=$1+"["+$3+"]"; }
	|	yNEW__ETC '[' expr ']' '(' expr ')'	{ $<fl>$=$<fl>1; $$=$1+"["+$3+"]("+$6+")"; }
	;

//************************************************
// Case/If

unique_priorityE:		// IEEE: unique_priority + empty
		/*empty*/				{ }
	|	yPRIORITY				{ }
	|	yUNIQUE					{ }
	|	yUNIQUE0				{ NEED_S09($<fl>1, "unique0"); }
	;

action_block:			// ==IEEE: action_block
		stmt	%prec prLOWER_THAN_ELSE		{ }
	|	stmt yELSE stmt				{ }
	|	yELSE stmt				{ }
	;

caseStart:			// IEEE: part of case_statement
	 	yCASE  '(' expr ')'	{ }
	|	yCASEX '(' expr ')'	{ }
	|	yCASEZ '(' expr ')'	{ }
	;

caseAttrE:
	 	/*empty*/				{ }
	;

case_patternListE:		// IEEE: case_pattern_item
	//	&&& is part of expr so aliases to case_itemList
		case_itemListE				{ }
	;

case_itemListE:			// IEEE: [ { case_item } ]
		/* empty */				{ }
	|	case_itemList				{ }
	;

case_insideListE:		// IEEE: [ { case_inside_item } ]
		/* empty */				{ }
	|	case_inside_itemList			{ }
	;

case_itemList:			// IEEE: { case_item + ... }
		caseCondList ':' stmtBlock		{ }
	|	yDEFAULT ':' stmtBlock			{ }
	|	yDEFAULT stmtBlock			{ }
	|	case_itemList caseCondList ':' stmtBlock	{ }
	|       case_itemList yDEFAULT stmtBlock		{ }
	|	case_itemList yDEFAULT ':' stmtBlock		{ }
	;

case_inside_itemList:		// IEEE: { case_inside_item + open_range_list ... }
		open_range_list ':' stmtBlock		{ }
	|	yDEFAULT ':' stmtBlock			{ }
	|	yDEFAULT stmtBlock			{ }
	|	case_inside_itemList open_range_list ':' stmtBlock { }
	|       case_inside_itemList yDEFAULT stmtBlock	{ }
	|	case_inside_itemList yDEFAULT ':' stmtBlock	{ }
	;

open_range_list:		// ==IEEE: open_range_list + open_value_range
		open_value_range			{ }
	|	open_range_list ',' open_value_range	{ }
	;

open_value_range:		// ==IEEE: open_value_range
		value_range				{ }
	;

value_range:			// ==IEEE: value_range
		expr					{ }
	|	'[' expr ':' expr ']'			{ }
	;

caseCondList:			// IEEE: part of case_item
		expr 					{ }
	|	caseCondList ',' expr			{ }
	;

patternNoExpr<str>:		// IEEE: pattern **Excluding Expr*
		'.' id/*variable*/			{ $<fl>$=$<fl>1; $$="."+$2; }
	|	yP_DOTSTAR				{ $<fl>$=$<fl>1; $$=".*"; }
	//			// IEEE: "expr" excluded; expand in callers
	//			// "yTAGGED id [expr]" Already part of expr
	|	yTAGGED id/*member_identifier*/ patternNoExpr		{ $<fl>$=$<fl>1; $$=" tagged "+$2+" "+$3; }
	//			// "yP_TICKBRA patternList '}'" part of expr under assignment_pattern
	;

patternList<str>:		// IEEE: part of pattern
		patternOne				{ $<fl>$=$<fl>1; $$=$1; }
	|	patternList ',' patternOne		{ $<fl>$=$<fl>1; $$=$1+","+$3; }
	;

patternOne<str>:		// IEEE: part of pattern
		expr					{ $<fl>$=$<fl>1; $$=$1; }
	|	expr '{' argsExprList '}'		{ $<fl>$=$<fl>1; $$=$1; }
	|	patternNoExpr				{ $<fl>$=$<fl>1; $$=$1; }
	;

patternMemberList<str>:		// IEEE: part of pattern and assignment_pattern
		patternKey ':' expr			{ $<fl>$=$<fl>1; $$=$1+" : "+$2; }
	|	patternKey ':' patternNoExpr		{ $<fl>$=$<fl>1; $$=$1+" : "+$2; }
	|	patternMemberList ',' patternKey ':' expr		{ $<fl>$=$<fl>1; $$=$1+","+$3+":"+$4; }
	|	patternMemberList ',' patternKey ':' patternNoExpr	{ $<fl>$=$<fl>1; $$=$1+","+$3+":"+$4; }
	;

patternKey<str>:		// IEEE: merge structure_pattern_key, array_pattern_key, assignment_pattern_key
	//			// IEEE: structure_pattern_key
	//			// id/*member*/ is part of constExpr below
		constExpr				{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: assignment_pattern_key
	|	yDEFAULT				{ $<fl>$=$<fl>1; $$=$1; }
	|	simple_type				{ $<fl>$=$<fl>1; $$=$1; }
	//			// simple_type reference looks like constExpr
	;

assignment_pattern<str>:		// ==IEEE: assignment_pattern
	// This doesn't match the text of the spec.  I think a : is missing, or example code needed
	// yP_TICKBRA constExpr exprList '}'	{ $$="'{"+$2+" "+$3"}"; }
	//			// "'{ const_expression }" is same as patternList with one entry
	//			// From patternNoExpr
	//			// also IEEE: "''{' expression { ',' expression } '}'"
	//			//      matches since patternList includes expr
		yP_TICKBRA patternList '}'		{ $<fl>$=$<fl>1; $$="'{"+$2+"}"; }
	//			// From patternNoExpr
	//			// also IEEE "''{' structure_pattern_key ':' ...
	//			// also IEEE "''{' array_pattern_key ':' ...
	|	yP_TICKBRA patternMemberList '}'	{ $<fl>$=$<fl>1; $$="'{"+$2+"}"; }
	//			// IEEE: Not in grammar, but in VMM
	|	yP_TICKBRA '}'				{ $<fl>$=$<fl>1; $$="'{}"; }
	;

// "datatype id = x {, id = x }"  |  "yaId = x {, id=x}" is legal
for_initialization:		// ==IEEE: for_initialization + for_variable_declaration + extra terminating ";"
	//			// IEEE: for_variable_declaration
		for_initializationItemList ';'		{ }
	;

for_initializationItemList:	// IEEE: [for_variable_declaration...]
		for_initializationItem			{ }
	|	for_initializationItemList ',' for_initializationItem	{ }
	;

for_initializationItem:		// IEEE: variable_assignment + for_variable_declaration
	//			// IEEE: for_variable_declaration
		data_type idAny/*new*/ '=' expr		{ VARDTYPE($1); }
	//			// IEEE: variable_assignment
	|	variable_lvalue '=' expr		{ }
	;

for_stepE:			// IEEE: for_step + empty
		/* empty */				{ }
	|	for_step				{ }
	;

for_step:			// IEEE: for_step
		for_step_assignment			{ }
	|	for_step ',' for_step_assignment	{ }
	;

for_step_assignment:		// ==IEEE: for_step_assignment
		operator_assignment			{ }
	//
	|	inc_or_dec_expression			{ }
	//			// IEEE: subroutine_call
	|	function_subroutine_callNoMethod	{ }
	//			// method_call:array_method requires a '.'
	|	expr '.' array_methodNoRoot		{ }
	|	exprScope				{ }
	;

loop_variables<str>:			// ==IEEE: loop_variables
		id					{ $<fl>$=$<fl>1; $$=$1; }
	|	loop_variables ',' id			{ $<fl>$=$<fl>1; $$=$1+","+$3; }
	;

//************************************************
// Functions/tasks

funcRef<str>:			// IEEE: part of tf_call
	//			// package_scope/hierarchical_... is part of expr, so just need ID
	//			//	making-a		id-is-a
	//			//	-----------------	------------------
	//			//      tf_call			tf_identifier		expr (list_of_arguments)
	//			//      method_call(post .)	function_identifier	expr (list_of_arguments)
	//			//	property_instance	property_identifier	property_actual_arg
	//			//	sequence_instance	sequence_identifier	sequence_actual_arg
	//			//      let_expression		let_identifier		let_actual_arg
	//
		id '(' pev_list_of_argumentsE ')'	{ $<fl>$=$<fl>1; $$=$1+"("+$3+")"; }
	|	package_scopeIdFollows id '(' pev_list_of_argumentsE ')'	{ $<fl>$=$<fl>2; $$=$1+$2+"("+$4+")"; }
	|	class_scope_id '(' pev_list_of_argumentsE ')'	{ $<fl>$=$<fl>1; $$=$<str>1+"("+$3+")"; }
	;

task_subroutine_callNoMethod<str>:	// function_subroutine_callNoMethod (as task)
	//			// IEEE: tf_call
		funcRef					{ $<fl>$=$<fl>1; $$=$1; }
	|	funcRef yWITH__PAREN '(' expr ')'	{ $<fl>$=$<fl>1; $$=$1+" "+$2+$3+$4+$5; }
	|	system_t_call				{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: method_call requires a "." so is in expr
	//			// IEEE: ['std::'] not needed, as normal std package resolution will find it
	//			// IEEE: randomize_call
	//			// We implement randomize as a normal funcRef, since randomize isn't a keyword
	//			// Note yNULL is already part of expressions, so they come for free
	|	funcRef yWITH__CUR constraint_block	{ $<fl>$=$<fl>1; $$=$1+" with..."; }
	;

function_subroutine_callNoMethod<str>:	// IEEE: function_subroutine_call (as function)
	//			// IEEE: tf_call
		funcRef					{ $<fl>$=$<fl>1; $$=$1; }
	|	funcRef yWITH__PAREN '(' expr ')'	{ $<fl>$=$<fl>1; $$=$1+" "+$2+$3+$4+$5; }
	|	system_f_call				{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: method_call requires a "." so is in expr
	//			// IEEE: ['std::'] not needed, as normal std package resolution will find it
	//			// IEEE: randomize_call
	//			// We implement randomize as a normal funcRef, since randomize isn't a keyword
	//			// Note yNULL is already part of expressions, so they come for free
	|	funcRef yWITH__CUR constraint_block	{ $<fl>$=$<fl>1; $$=$1+" with..."; }
	;

system_t_call<str>:		// IEEE: system_tf_call (as task)
		system_f_call				{ $<fl>$=$<fl>1; $$ = $1; }
	;

system_f_call<str>:		// IEEE: system_tf_call (as func)
		ygenSYSCALL parenE			{ $<fl>$=$<fl>1; $$ = $1; }
	//			// Allow list of data_type to support "x,,,y"
	|	ygenSYSCALL '(' exprOrDataTypeList ')'	{ $<fl>$=$<fl>1; $$ = $1+"("+$3+")"; }
	//			// Standard doesn't explicity list system calls
	//			// But these match elaboration calls in 1800-2009
	|	yD_FATAL parenE				{ $<fl>$=$<fl>1; $$ = $1; }
	|	yD_FATAL '(' exprOrDataTypeList ')'	{ $<fl>$=$<fl>1; $$ = $1+"("+$3+")"; }
	|	yD_ERROR parenE				{ $<fl>$=$<fl>1; $$ = $1; }
	|	yD_ERROR '(' exprOrDataTypeList ')'	{ $<fl>$=$<fl>1; $$ = $1+"("+$3+")"; }
	|	yD_WARNING parenE			{ $<fl>$=$<fl>1; $$ = $1; }
	|	yD_WARNING '(' exprOrDataTypeList ')'	{ $<fl>$=$<fl>1; $$ = $1+"("+$3+")"; }
	|	yD_INFO parenE				{ $<fl>$=$<fl>1; $$ = $1; }
	|	yD_INFO '(' exprOrDataTypeList ')'	{ $<fl>$=$<fl>1; $$ = $1+"("+$3+")"; }
	;

elaboration_system_task<str>:	// IEEE: elaboration_system_task (1800-2009)
	//			// $fatal first argument is exit number, must be constant
		yD_FATAL parenE ';'			{ $<fl>$=$<fl>1; $$ = $1;            NEED_S09($<fl>1,"elaboration system tasks"); }
	|	yD_FATAL '(' exprOrDataTypeList ')' ';'	{ $<fl>$=$<fl>1; $$ = $1+"("+$3+")"; NEED_S09($<fl>1,"elaboration system tasks"); }
	|	yD_ERROR parenE	';'			{ $<fl>$=$<fl>1; $$ = $1;            NEED_S09($<fl>1,"elaboration system tasks"); }
	|	yD_ERROR '(' exprOrDataTypeList ')' ';'	{ $<fl>$=$<fl>1; $$ = $1+"("+$3+")"; NEED_S09($<fl>1,"elaboration system tasks"); }
	|	yD_WARNING parenE ';'			{ $<fl>$=$<fl>1; $$ = $1;            NEED_S09($<fl>1,"elaboration system tasks"); }
	|	yD_WARNING '(' exprOrDataTypeList ')' ';' {$<fl>$=$<fl>1; $$ = $1+"("+$3+")"; NEED_S09($<fl>1,"elaboration system tasks"); }
	|	yD_INFO parenE ';'			{ $<fl>$=$<fl>1; $$ = $1;            NEED_S09($<fl>1,"elaboration system tasks"); }
	|	yD_INFO '(' exprOrDataTypeList ')' ';'	{ $<fl>$=$<fl>1; $$ = $1+"("+$3+")"; NEED_S09($<fl>1,"elaboration system tasks"); }
	;

property_actual_arg<str>:	// ==IEEE: property_actual_arg
	//			// IEEE: property_expr
	//			// IEEE: sequence_actual_arg
		pev_expr				{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: sequence_expr
	//			// property_expr already includes sequence_expr
	;

task<fl>:
		yTASK__ETC				{ $<fl>$=$<fl>1; }
	|	yTASK__aPUREV				{ $<fl>$=$<fl>1; }
	;

task_declaration:		// IEEE: task_declaration
		yTASK__ETC lifetimeE taskId tfGuts yENDTASK endLabelE
			{ PARSEP->endtaskfuncCb($<fl>5,$5);
			  PARSEP->symPopScope(VAstType::TASK); }
	|	yTASK__aPUREV lifetimeE taskId tfGutsPureV
			{ PARSEP->endtaskfuncCb($<fl>1,"endtask");
			  PARSEP->symPopScope(VAstType::TASK); }
	;

task_prototype:			// ==IEEE: task_prototype
	//			// IEEE: has '(' tf_port_list ')'
	//			// However the () should be optional for OVA
		task taskId '(' tf_port_listE ')'	{ PARSEP->symPopScope(VAstType::TASK); }
	|	task taskId				{ PARSEP->symPopScope(VAstType::TASK); }
	;

function<fl>:
		yFUNCTION__ETC				{ $<fl>$=$<fl>1; }
	|	yFUNCTION__aPUREV			{ $<fl>$=$<fl>1; }
	;

function_declaration:		// IEEE: function_declaration + function_body_declaration
	 	yFUNCTION__ETC lifetimeE funcId tfGuts yENDFUNCTION endLabelE
			{ PARSEP->endtaskfuncCb($<fl>5,$5);
			  PARSEP->symPopScope(VAstType::FUNCTION); }
	| 	yFUNCTION__ETC lifetimeE funcIdNew tfGuts yENDFUNCTION endLabelE
			{ PARSEP->endtaskfuncCb($<fl>5,$5);
			  PARSEP->symPopScope(VAstType::FUNCTION); }
	|	yFUNCTION__aPUREV lifetimeE funcId tfGutsPureV
			{ PARSEP->endtaskfuncCb($<fl>1,"endfunction");
			  PARSEP->symPopScope(VAstType::FUNCTION); }
	| 	yFUNCTION__aPUREV lifetimeE funcIdNew tfGutsPureV
			{ PARSEP->endtaskfuncCb($<fl>1,"endfunction");
			  PARSEP->symPopScope(VAstType::FUNCTION); }
	;

function_prototype:		// IEEE: function_prototype
	//			// IEEE: has '(' tf_port_list ')'
	//			// However the () should be optional for OVA
		function funcId '(' tf_port_listE ')'	{ PARSEP->symPopScope(VAstType::FUNCTION); }
	|	function funcId 			{ PARSEP->symPopScope(VAstType::FUNCTION); }
	;

class_constructor_prototype:	// ==IEEE: class_constructor_prototype
		function funcIdNew '(' tf_port_listE ')' ';'	{ PARSEP->symPopScope(VAstType::FUNCTION); }
	|	function funcIdNew ';'				{ PARSEP->symPopScope(VAstType::FUNCTION); }
	;

method_prototype:
		task_prototype				{ }
	|	function_prototype			{ }
	;

lifetimeE:			// IEEE: [lifetime]
		/* empty */		 		{ }
	|	lifetime		 		{ }
	;

lifetime:			// ==IEEE: lifetime
	//			// Note lifetime used by members is instead under memberQual
		ySTATIC__ETC		 		{ }
	|	yAUTOMATIC		 		{ }
	;

taskId:
		tfIdScoped
			{ PARSEP->symPushNewUnder(VAstType::TASK, $<str>1, $<scp>1);
			  PARSEP->taskCb($<fl>1,"task",$<str>1); }
	;

funcId:				// IEEE: function_data_type_or_implicit + part of function_body_declaration
	//			// IEEE: function_data_type_or_implicit must be expanded here to prevent conflict
	//			// function_data_type expanded here to prevent conflicts with implicit_type:empty vs data_type:ID
		/**/			tfIdScoped
			{ PARSEP->symPushNewUnder(VAstType::FUNCTION, $<str>1, $<scp>1);
			  PARSEP->functionCb($<fl>1,"function",$<str>1,""); }
	|	signingE rangeList	tfIdScoped
			{ PARSEP->symPushNewUnder(VAstType::FUNCTION, $<str>3, $<scp>3);
			  PARSEP->functionCb($<fl>3,"function",$<str>3,SPACED($1,$2)); }
	|	signing			tfIdScoped
			{ PARSEP->symPushNewUnder(VAstType::FUNCTION, $<str>2, $<scp>2);
			  PARSEP->functionCb($<fl>2,"function",$<str>2,$1); }
	|	yVOID			tfIdScoped
			{ PARSEP->symPushNewUnder(VAstType::FUNCTION, $<str>2, $<scp>2);
			  PARSEP->functionCb($<fl>2,"function",$<str>2,$1); }
	|	data_type		tfIdScoped
			{ PARSEP->symPushNewUnder(VAstType::FUNCTION, $<str>2, $<scp>2);
			  PARSEP->functionCb($<fl>2,"function",$<str>2,$1); }
	;

funcIdNew:			// IEEE: from class_constructor_declaration
	 	yNEW__ETC
			{ PARSEP->symPushNewUnder(VAstType::FUNCTION, "new", NULL);
			  PARSEP->functionCb($<fl>1,"function","new",""); }
	| 	yNEW__PAREN
			{ PARSEP->symPushNewUnder(VAstType::FUNCTION, "new", NULL);
			  PARSEP->functionCb($<fl>1,"function","new",""); }
	|	class_scopeWithoutId yNEW__PAREN
			{ PARSEP->symPushNewUnder(VAstType::FUNCTION, "new", $<scp>1);
			  PARSEP->functionCb($<fl>2,"function","new",""); }
	;

tfIdScoped<str_scp>:		// IEEE: part of function_body_declaration/task_body_declaration
 	//			// IEEE: [ interface_identifier '.' | class_scope ] function_identifier
		id					{ $<fl>$=$<fl>1; $<scp>$=NULL;     $<str>$ = $1; }
	|	id/*interface_identifier*/ '.' id	{ $<fl>$=$<fl>1; $<scp>$=NULL;     $<str>$ = $1+"."+$2; }
	|	class_scope_id				{ $<fl>$=$<fl>1; $<scp>$=$<scp>1; $<str>$ = $<str>1; }
	;

tfGuts:
		'(' tf_port_listE ')' ';' tfBodyE	{ }
	|	';' tfBodyE				{ }
	;

tfGutsPureV:
		'(' tf_port_listE ')' ';'		{ }
	|	';'					{ }
	;

tfBodyE:		// IEEE: part of function_body_declaration/task_body_declaration
		/* empty */				{ }
	|	tf_item_declarationList			{ }
	|	tf_item_declarationList stmtList	{ }
	|	stmtList				{ }
	;

function_data_type<str>:	// IEEE: function_data_type
		yVOID					{ $$ = $1; }
	|	data_type				{ $$ = $1; }
	;

tf_item_declarationList:
		tf_item_declaration			{ }
	|	tf_item_declarationList tf_item_declaration	{ }
	;

tf_item_declaration:		// ==IEEE: tf_item_declaration
		block_item_declaration			{ }
	| 	tf_port_declaration			{ }
	;

tf_port_listE:			// IEEE: tf_port_list + empty
	//			// Empty covered by tf_port_item
		{ VARRESET_LIST(""); VARIO("input"); }
			tf_port_listList		{ VARRESET_NONLIST(""); }
	;

tf_port_listList:		// IEEE: part of tf_port_list
		tf_port_item				{ }
	|	tf_port_listList ',' tf_port_item	{ }
	;

tf_port_item:			// ==IEEE: tf_port_item
	//			// We split tf_port_item into the type and assignment as don't know what follows a comma
		/* empty */				{ PINNUMINC(); }	// For example a ",," port
	|	tf_port_itemFront tf_port_itemAssignment { PINNUMINC(); }
	|	tf_port_itemAssignment 			{ PINNUMINC(); }
	;

tf_port_itemFront:		// IEEE: part of tf_port_item, which has the data type
		data_type				{ VARDTYPE($1); }
	|	signingE rangeList			{ VARDTYPE(SPACED($1,$2)); }
	|	signing					{ VARDTYPE($1); }
	|	yVAR data_type				{ VARDTYPE($2); }
	|	yVAR implicit_typeE			{ VARDTYPE($2); }
	//
	|	tf_port_itemDir /*implicit*/		{ VARDTYPE(""); /*default_nettype-see spec*/ }
	|	tf_port_itemDir data_type		{ VARDTYPE($2); }
	|	tf_port_itemDir signingE rangeList	{ VARDTYPE(SPACED($2,$3)); }
	|	tf_port_itemDir signing			{ VARDTYPE($2); }
	|	tf_port_itemDir yVAR data_type		{ VARDTYPE($3); }
	|	tf_port_itemDir yVAR implicit_typeE	{ VARDTYPE($3); }
	;

tf_port_itemDir:		// IEEE: part of tf_port_item, direction
		port_direction				{ }  // port_direction sets VARIO
	;

tf_port_itemAssignment:		// IEEE: part of tf_port_item, which has assignment
		id variable_dimensionListE sigAttrListE
			{ VARDONE($<fl>1, $1, $2, ""); }
	|	id variable_dimensionListE sigAttrListE '=' expr
			{ VARDONE($<fl>1, $1, $2, $5); }
	;

//	method_call:		// ==IEEE: method_call + method_call_body
//				// IEEE: method_call_root '.' method_identifier [ '(' list_of_arguments ')' ]
//				//   "method_call_root '.' method_identifier" looks just like "expr '.' id"
//				//   "method_call_root '.' method_identifier (...)" looks just like "expr '.' tf_call"
//				// IEEE: built_in_method_call
//				//   method_call_root not needed, part of expr resolution
//				// What's left is below array_methodNoRoot

parenE:
		/* empty */				{ }
	|	'(' ')'					{ }
	;

array_methodNoRoot<str>:	// ==IEEE: built_in_method_call without root
	//			//   method_call_root not needed, part of expr resolution
		array_method_nameNoId method_callWithE	{ $<fl>$=$<fl>1; $$=$1+$2; }
	|	array_method_nameNoId '(' list_of_argumentsE ')' method_callWithE	{ $<fl>$=$<fl>1; $$=$1+$2+$3+$4+$5; }
	//			//  "method_call_root '.' randomize_call" matches function_subroutine_call:randomize_call
	;

method_callWithE<str>:
	//			// Code duplicated elsewhere
		/* empty */				{ $$=""; }
	|	yWITH__PAREN '(' expr ')'		{ $<fl>$=$<fl>1; $$=$1+$2+$3+$4; }
	;

array_method_nameNoId<str>:	// IEEE: array_method_name minus method_identifier
		yUNIQUE					{ $<fl>$=$<fl>1; $$=$1; }
	|	yAND					{ $<fl>$=$<fl>1; $$=$1; }
	|	yOR					{ $<fl>$=$<fl>1; $$=$1; }
	|	yXOR					{ $<fl>$=$<fl>1; $$=$1; }
	;

dpi_import_export:		// ==IEEE: dpi_import_export
		yIMPORT yaSTRING dpi_tf_import_propertyE dpi_importLabelE function_prototype ';'	{ }
	|	yIMPORT yaSTRING dpi_tf_import_propertyE dpi_importLabelE task_prototype ';'	{ }
	|	yEXPORT yaSTRING dpi_importLabelE function idAny ';'	{ }
	|	yEXPORT yaSTRING dpi_importLabelE task     idAny ';'	{ }
	;

dpi_importLabelE:		// IEEE: part of dpi_import_export
		/* empty */				{ }
	|	idAny/*c_identifier*/ '='		{ }
	;

dpi_tf_import_propertyE:	// IEEE: [ dpi_function_import_property + dpi_task_import_property ]
		/* empty */				{ }
	|	yCONTEXT				{ }
	|	yPURE					{ }
	;

overload_declaration:		// ==IEEE: overload_declaration
		yBIND overload_operator function data_type idAny/*new-function_identifier*/
			'(' overload_proto_formals ')' ';'	{ }
	;

overload_operator<str>:		// ==IEEE: overload_operator
		"+"		{ $$="+"; }
	|	yP_PLUSPLUS	{ $$="++"; }
	|	"-"		{ $$="-"; }
	|	yP_MINUSMINUS	{ $$="--"; }
	|	"*"		{ $$="*"; }
	|	yP_POW		{ $$="**"; }
	|	"/"		{ $$="/"; }
	|	"%"		{ $$="%"; }
	|	yP_EQUAL	{ $$="=="; }
	|	yP_NOTEQUAL	{ $$="!="; }
	|	"<"		{ $$="<"; }
	|	yP_LTE		{ $$="<="; }
	|	">"		{ $$=">"; }
	|	yP_GTE		{ $$=">="; }
	|	"="		{ $$="="; }
	;

overload_proto_formals:		// ==IEEE: overload_proto_formals
		data_type				{ }
	|	overload_proto_formals ',' data_type	{ }
	;

//************************************************
// Expressions
//
// ~l~ means this is the (l)eft hand side of any operator
//     it will get replaced by "", "f" or "s"equence
// ~r~ means this is a (r)ight hand later expansion in the same statement,
//     not under parenthesis for <= disambiguation
//     it will get replaced by "", or "f"
// ~p~ means this is a (p)arenthetized expression
//     it will get replaced by "", or "s"equence

constExpr<str>:
		expr					{ $<fl>$=$<fl>1; $$ = $1; }
	;

expr<str>:			// IEEE: part of expression/constant_expression/primary
	// *SEE BELOW*		// IEEE: primary/constant_primary
	//
	//			// IEEE: unary_operator primary
		'+' ~r~expr	%prec prUNARYARITH	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	'-' ~r~expr	%prec prUNARYARITH	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	'!' ~r~expr	%prec prNEGATION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	'&' ~r~expr	%prec prREDUCTION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	'~' ~r~expr	%prec prNEGATION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	'|' ~r~expr	%prec prREDUCTION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	'^' ~r~expr	%prec prREDUCTION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	yP_NAND ~r~expr	%prec prREDUCTION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	yP_NOR  ~r~expr	%prec prREDUCTION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	yP_XNOR ~r~expr	%prec prREDUCTION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	//
	//			// IEEE: inc_or_dec_expression
	|	~l~inc_or_dec_expression		{ $<fl>$=$<fl>1; $$ = $1; }
	//
	//			// IEEE: '(' operator_assignment ')'
	//			// Need exprScope of variable_lvalue to prevent conflict
	|	'(' ~p~exprScope '=' 	      expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+$3+$4+")"; }
	|	'(' ~p~exprScope yP_PLUSEQ    expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+$3+$4+")"; }
	|	'(' ~p~exprScope yP_MINUSEQ   expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+$3+$4+")"; }
	|	'(' ~p~exprScope yP_TIMESEQ   expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+$3+$4+")"; }
	|	'(' ~p~exprScope yP_DIVEQ     expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+$3+$4+")"; }
	|	'(' ~p~exprScope yP_MODEQ     expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+$3+$4+")"; }
	|	'(' ~p~exprScope yP_ANDEQ     expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+$3+$4+")"; }
	|	'(' ~p~exprScope yP_OREQ      expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+$3+$4+")"; }
	|	'(' ~p~exprScope yP_XOREQ     expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+$3+$4+")"; }
	|	'(' ~p~exprScope yP_SLEFTEQ   expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+$3+$4+")"; }
	|	'(' ~p~exprScope yP_SRIGHTEQ  expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+$3+$4+")"; }
	|	'(' ~p~exprScope yP_SSRIGHTEQ expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+$3+$4+")"; }
	//
	//			// IEEE: expression binary_operator expression
	|	~l~expr '+' ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr '-' ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr '*' ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr '/' ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr '%' ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_EQUAL ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_NOTEQUAL ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_CASEEQUAL ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_CASENOTEQUAL ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_WILDEQUAL ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_WILDNOTEQUAL ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_ANDAND ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_OROR ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_POW ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr '<' ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr '>' ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_GTE ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr '&' ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr '|' ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr '^' ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_XNOR ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_NOR  ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_NAND ~r~expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_SLEFT ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_SRIGHT ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_SSRIGHT ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_LTMINUSGT ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	//
	//			// IEEE: expr yP_MINUSGT expr  (1800-2009)
	//			// Conflicts with constraint_expression:"expr yP_MINUSGT constraint_set"
	//			// To duplicating expr for constraints, just allow the more general form
	//			// Later Ast processing must ignore constraint terms where inappropriate
	|	~l~expr yP_MINUSGT constraint_set		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	//
	//			// <= is special, as we need to disambiguate it with <= assignment
	//			// We copy all of expr to fexpr and rename this token to a fake one.
	|	~l~expr yP_LTE~f__IGNORE~ ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	//
	//			// IEEE: conditional_expression
	|	~l~expr '?' ~r~expr ':' ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+"?"+$3+":"+$5; }
	//
	//			// IEEE: inside_expression
	|	~l~expr yINSIDE '{' open_range_list '}'	{ $<fl>$=$<fl>1; $$ = $1+" inside {"+$3+"}"; }
	//
	//			// IEEE: tagged_union_expression
	|	yTAGGED id/*member*/ %prec prTAGGED		{ $<fl>$=$<fl>1; $$ = " tagged "+$1; }
	|	yTAGGED id/*member*/ %prec prTAGGED expr	{ $<fl>$=$<fl>1; $$ = " tagged "+$1+" "+$2; }
	//
	//======================// IEEE: primary/constant_primary
	//
	//			// IEEE: primary_literal (minus string, which is handled specially)
	|	yaINTNUM				{ $<fl>$=$<fl>1; $$ = $1; }
	|	yaFLOATNUM				{ $<fl>$=$<fl>1; $$ = $1; }
	|	yaTIMENUM				{ $<fl>$=$<fl>1; $$ = $1; }
	|	strAsInt~noStr__IGNORE~ 		{ $<fl>$=$<fl>1; $$ = $1; }
	//
	//			// IEEE: "... hierarchical_identifier select"  see below
	//
	//			// IEEE: empty_queue
	|	'{' '}'
	//
	//			// IEEE: concatenation/constant_concatenation
	//			// Part of exprOkLvalue below
	//
	//			// IEEE: multiple_concatenation/constant_multiple_concatenation
	|	'{' constExpr '{' cateList '}' '}'	{ $<fl>$=$<fl>1; $$ = "{"+$2+"{"+$4+"}}"; }
	//			// IEEE: multiple_concatenation/constant_multiple_concatenation+ range_expression (1800-2009)
	|	'{' constExpr '{' cateList '}' '}' '[' expr ']'
			{ $<fl>$=$<fl>1; $$ = "{"+$2+"{"+$4+"}}["+$8+"]";        NEED_S09($<fl>6,"{}[]"); }
	|	'{' constExpr '{' cateList '}' '}' '[' expr ':' expr ']'
			{ $<fl>$=$<fl>1; $$ = "{"+$2+"{"+$4+"}}["+$8+$9+$10+"]"; NEED_S09($<fl>6,"{}[]"); }
	|	'{' constExpr '{' cateList '}' '}' '[' expr yP_PLUSCOLON  expr ']'
			{ $<fl>$=$<fl>1; $$ = "{"+$2+"{"+$4+"}}["+$8+$9+$10+"]"; NEED_S09($<fl>6,"{}[]"); }
	|	'{' constExpr '{' cateList '}' '}' '[' expr yP_MINUSCOLON expr ']'
			{ $<fl>$=$<fl>1; $$ = "{"+$2+"{"+$4+"}}["+$8+$9+$10+"]"; NEED_S09($<fl>6,"{}[]"); }
	//
	|	function_subroutine_callNoMethod	{ $$ = $1; }
	//			// method_call
	|	~l~expr '.' function_subroutine_callNoMethod	{ $<fl>$=$<fl>1; $$=$1+"."+$3; }
	//			// method_call:array_method requires a '.'
	|	~l~expr '.' array_methodNoRoot		{ $<fl>$=$<fl>1; $$ = $1+"."+$3; }
	//
	//			// IEEE: let_expression
	//			// see funcRef
	//
	//			// IEEE: '(' mintypmax_expression ')'
	|	~noPar__IGNORE~'(' expr ')'			{ $<fl>$=$<fl>1; $$ = "("+$2+")"; }
	|	~noPar__IGNORE~'(' expr ':' expr ':' expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+":"+$4+":"+$5+")"; }
	//			// PSL rule
	|	'_' '(' statePushVlg expr statePop ')'	{ $<fl>$=$<fl>1; $$ = "_("+$4+")"; }	// Arbitrary Verilog inside PSL
	//
	//			// IEEE: cast/constant_cast
	|	casting_type yP_TICK '(' expr ')'	{ $<fl>$=$<fl>1; $$ = $1+"'("+$4+")"; }
	//			// Spec only allows primary with addition of a type reference
	//			// We'll be more general, and later assert LHS was a type.
	|	~l~expr yP_TICK '(' expr ')'		{ $<fl>$=$<fl>1; $$ = $1+"'("+$4+")"; }
	//
	//			// IEEE: assignment_pattern_expression
	//			// IEEE: streaming_concatenation
	//			// See exprOkLvalue
	//
	//			// IEEE: sequence_method_call
	//			// Indistinguishable from function_subroutine_call:method_call
	//
	|	'$'					{ $<fl>$=$<fl>1; $$ = "$"; }
	|	yNULL					{ $<fl>$=$<fl>1; $$ = $1; }
	//			// IEEE: yTHIS
	//			// See exprScope
	//
	//----------------------
	//
	|	~l~exprOkLvalue				{ $<fl>$=$<fl>1; $$ = $1; }
	//
	//----------------------
	//
	//			// IEEE: cond_predicate - here to avoid reduce problems
	//			// Note expr includes cond_pattern
	|	~l~expr yP_ANDANDAND ~r~expr		{ $<fl>$=$<fl>1; $$ = $1 + "&&&" + $3; }
	//
	//			// IEEE: cond_pattern - here to avoid reduce problems
	//			// "expr yMATCHES pattern"
	//			// IEEE: pattern - expanded here to avoid conflicts
	|	~l~expr yMATCHES patternNoExpr		{ $<fl>$=$<fl>1; $$ = $1 + " matches " + $3; }
	|	~l~expr yMATCHES ~r~expr		{ $<fl>$=$<fl>1; $$ = $1 + " matches " + $3; }
	//
	//			// IEEE: expression_or_dist - here to avoid reduce problems
	//			// "expr yDIST '{' dist_list '}'"
	|	~l~expr yDIST '{' dist_list '}'		{ $<fl>$=$<fl>1; $$ = $1 + " dist " + $3+"..."+$5; }
	;

fexpr<str>:			// For use as first part of statement (disambiguates <=)
		BISONPRE_COPY(expr,{s/~l~/f/g; s/~r~/f/g; s/~f__IGNORE~/__IGNORE/g;})	// {copied}
	;

ev_expr<str>:			// IEEE: event_expression
	//			// for yOR/, see event_expression
	//
	//			// IEEE: [ edge_identifier ] expression [ yIFF expression ]
	//			// expr alone see below
		senitemEdge				{ }
	|	ev_expr yIFF expr			{ }
	//
	//			// IEEE: sequence_instance [ yIFF expression ]
	//			// seq_inst is in expr, so matches senitem rule above
	//
	//			// IEEE: event_expression yOR event_expression
	|	ev_expr yOR ev_expr			{ }
	//			// IEEE: event_expression ',' event_expression
	//			// See real event_expression rule
	//
	//---------------------
	//			// IEEE: expr
	|	BISONPRE_COPY(expr,{s/~l~/ev_/g; s/~r~/ev_/g; s/~p~/ev_/g; s/~noPar__IGNORE~/yP_PAR__IGNORE /g;})	// {copied}
	//
	//			// IEEE: '(' event_expression ')'
	//			// expr:'(' x ')' conflicts with event_expression:'(' event_expression ')'
	//			// so we use a special expression class
	|	'(' event_expression ')'		{ $<fl>$=$<fl>1; $$ = "(...)"; }
	//			// IEEE: From normal expr: '(' expr ':' expr ':' expr ')'
	//			// But must avoid conflict
	|	'(' event_expression ':' expr ':' expr ')'	{ $<fl>$=$<fl>1; $$ = "(...)"; }
	;

//sexpr: See elsewhere
//pexpr: See elsewhere

exprLvalue<str>:		// expression that should be a variable_lvalue
		~f~exprOkLvalue				{ $<fl>$=$<fl>1; $$ = $1; }
	;

fexprLvalue<str>:		// For use as first part of statement (disambiguates <=)
		BISONPRE_COPY(exprLvalue,{s/~f~/f/g})	// {copied}
	;

exprOkLvalue<str>:		// expression that's also OK to use as a variable_lvalue
		~l~exprScope				{ $<fl>$=$<fl>1; $$ = $1; }
	//			// IEEE: concatenation/constant_concatenation
	|	'{' cateList '}'			{ $<fl>$=$<fl>1; $$ = "{"+$2+"}"; }
	//			// IEEE: concatenation/constant_concatenation+ constant_range_expression (1800-2009)
	|	'{' cateList '}' '[' expr ']'				{ $<fl>$=$<fl>1; $$ = "{"+$2+"}["+$5+"]";       NEED_S09($<fl>4,"{}[]"); }
	|	'{' cateList '}' '[' expr ':' expr ']'			{ $<fl>$=$<fl>1; $$ = "{"+$2+"}["+$5+$6+$7+"]"; NEED_S09($<fl>4,"{}[]"); }
	|	'{' cateList '}' '[' expr yP_PLUSCOLON  expr ']'	{ $<fl>$=$<fl>1; $$ = "{"+$2+"}["+$5+$6+$7+"]"; NEED_S09($<fl>4,"{}[]"); }
	|	'{' cateList '}' '[' expr yP_MINUSCOLON expr ']'	{ $<fl>$=$<fl>1; $$ = "{"+$2+"}["+$5+$6+$7+"]"; NEED_S09($<fl>4,"{}[]"); }
	//			// IEEE: assignment_pattern_expression
	//			// IEEE: [ assignment_pattern_expression_type ] == [ ps_type_id /ps_paremeter_id/data_type]
	//			// We allow more here than the spec requires
	|	~l~exprScope assignment_pattern		{ $<fl>$=$<fl>1; $$=$1+$2; }
	|	data_type assignment_pattern		{ $<fl>$=$<fl>1; $$=$1+$2; }
	|	assignment_pattern			{ $<fl>$=$<fl>1; $$=$1; }
	//
	|	streaming_concatenation			{ $<fl>$=$<fl>1; $$ = $1; }
	;

fexprOkLvalue<str>:		// exprOkLValue, For use as first part of statement (disambiguates <=)
		BISONPRE_COPY(exprOkLvalue,{s/~l~/f/g})	// {copied}
	;

sexprOkLvalue<str>:		// exprOkLValue, For use by sequence_expr
		BISONPRE_COPY(exprOkLvalue,{s/~l~/s/g})	// {copied}
	;

pexprOkLvalue<str>:		// exprOkLValue, For use by property_expr
		BISONPRE_COPY(exprOkLvalue,{s/~l~/p/g})	// {copied}
	;

ev_exprOkLvalue<str>:		// exprOkLValue, For use by ev_expr
		BISONPRE_COPY(exprOkLvalue,{s/~l~/ev_/g})	// {copied}
	;

pev_exprOkLvalue<str>:		// exprOkLValue, For use by ev_expr
		BISONPRE_COPY(exprOkLvalue,{s/~l~/pev_/g})	// {copied}
	;

exprScope<str>:			// scope and variable for use to inside an expression
	// 			// Here we've split method_call_root | implicit_class_handle | class_scope | package_scope
	//			// from the object being called and let expr's "." deal with resolving it.
	//			// (note method_call_root was simplified to require a primary in 1800-2009)
	//
	//			// IEEE: [ implicit_class_handle . | class_scope | package_scope ] hierarchical_identifier select
	//			// Or method_call_body without parenthesis
	//			// See also varRefClassBit, which is the non-expr version of most of this
		yTHIS					{ $<fl>$=$<fl>1; $$ = $1; }
	|	idArrayed				{ $<fl>$=$<fl>1; $$ = $1; }
	|	package_scopeIdFollows idArrayed	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	class_scopeIdFollows idArrayed		{ $<fl>$=$<fl>1; $$ = $<str>1+$2; }
	|	~l~expr '.' idArrayed			{ $<fl>$=$<fl>1; $$ = $1+"."+$3; }
	//			// expr below must be a "yTHIS"
	|	~l~expr '.' ySUPER			{ $<fl>$=$<fl>1; $$ = $1+"."+$3; }
	//			// Part of implicit_class_handle
	|	ySUPER					{ $<fl>$=$<fl>1; $$ = $1; }
	;

fexprScope<str>:		// exprScope, For use as first part of statement (disambiguates <=)
		BISONPRE_COPY(exprScope,{s/~l~/f/g})	// {copied}
	;

sexprScope<str>:		// exprScope, For use by sequence_expr
		BISONPRE_COPY(exprScope,{s/~l~/s/g})	// {copied}
	;

pexprScope<str>:		// exprScope, For use by property_expr
		BISONPRE_COPY(exprScope,{s/~l~/p/g})	// {copied}
	;

ev_exprScope<str>:		// exprScope, For use by ev_expr
		BISONPRE_COPY(exprScope,{s/~l~/ev_/g})	// {copied}
	;

pev_exprScope<str>:		// exprScope, For use by ev_expr
		BISONPRE_COPY(exprScope,{s/~l~/pev_/g})	// {copied}
	;

// Generic expressions
exprOrDataType<str>:		// expr | data_type: combined to prevent conflicts
		expr					{ $<fl>$=$<fl>1; $$ = $1; }
	//			// data_type includes id that overlaps expr, so special flavor
	|	data_type				{ $<fl>$=$<fl>1; $$ = $1; }
	//			// not in spec, but needed for $past(sig,1,,@(posedge clk))
	|	event_control				{ $$ = "event_control"; }
	;

cateList<str>:
	//			// Not just 'expr' to prevent conflict via stream_concOrExprOrType
		stream_expression			{ $<fl>$=$<fl>1; $$ = $1; }
	|	cateList ',' stream_expression		{ $<fl>$=$<fl>1; $$ = $1+","+$3; }
	;

exprOrDataTypeList<str>:
		exprOrDataType				{ $<fl>$=$<fl>1; $$ = $1; }
	|	exprOrDataTypeList ',' exprOrDataType	{ $<fl>$=$<fl>1; $$ = $1+","+$3; }
	|	exprOrDataTypeList ','			{ $<fl>$=$<fl>1; $$ = $1+","; }   // Verilog::Parser only: ,, is ok
	;

list_of_argumentsE<str>:	// IEEE: [list_of_arguments]
	//			// See comments under funcRef
		argsDottedList				{ $<fl>$=$<fl>1; $$=$1; }
	|	argsExprListE				{ $<fl>$=$<fl>1; $$=$1; }
	|	argsExprListE ',' argsDottedList	{ $<fl>$=$<fl>1; $$=$1+","+$3; }
	;

pev_list_of_argumentsE<str>:	// IEEE: [list_of_arguments] - pev_expr at bottom
	//			// See comments under funcRef
		pev_argsDottedList			{ $<fl>$=$<fl>1; $$=$1; }
	|	pev_argsExprListE			{ $<fl>$=$<fl>1; $$=$1; }
	|	pev_argsExprListE ',' pev_argsDottedList	{ $<fl>$=$<fl>1; $$=$1+","+$3; }
	;

argsExprList<str>:		// IEEE: part of list_of_arguments (used where ,, isn't legal)
		expr					{ $<fl>$=$<fl>1; $$ = $1; }
	|	argsExprList ',' expr			{ $<fl>$=$<fl>1; $$ = $1+","+$3; }
	;

argsExprListE<str>:		// IEEE: part of list_of_arguments
		argsExprOneE				{ $<fl>$=$<fl>1; $$ = $1; }
	|	argsExprListE ',' argsExprOneE		{ $<fl>$=$<fl>1; $$ = $1+","+$3; }
	;

pev_argsExprListE<str>:		// IEEE: part of list_of_arguments - pev_expr at bottom
		pev_argsExprOneE			{ $<fl>$=$<fl>1; $$ = $1; }
	|	pev_argsExprListE ',' pev_argsExprOneE	{ $<fl>$=$<fl>1; $$ = $1+","+$3; }
	;

argsExprOneE<str>:		// IEEE: part of list_of_arguments
		/*empty*/				{ $$ = ""; }	// ,, is legal in list_of_arguments
	|	expr					{ $<fl>$=$<fl>1; $$ = $1; }
	;

pev_argsExprOneE<str>:		// IEEE: part of list_of_arguments - pev_expr at bottom
		/*empty*/				{ $$ = ""; }	// ,, is legal in list_of_arguments
	|	pev_expr				{ $<fl>$=$<fl>1; $$ = $1; }
	;

argsDottedList<str>:		// IEEE: part of list_of_arguments
		argsDotted				{ $<fl>$=$<fl>1; $$=$1; }
	|	argsDottedList ',' argsDotted		{ $<fl>$=$<fl>1; $$=$1+","+$3; }
	;

pev_argsDottedList<str>:	// IEEE: part of list_of_arguments - pev_expr at bottom
		pev_argsDotted				{ $<fl>$=$<fl>1; $$=$1; }
	|	pev_argsDottedList ',' pev_argsDotted	{ $<fl>$=$<fl>1; $$=$1+","+$3; }
	;

argsDotted<str>:		// IEEE: part of list_of_arguments
		'.' idAny '(' expr ')'			{ $<fl>$=$<fl>1; $$=$1+$2+$3+$4+$5; }
	;

pev_argsDotted<str>:		// IEEE: part of list_of_arguments - pev_expr at bottom
		'.' idAny '(' pev_expr ')'		{ $<fl>$=$<fl>1; $$=$1+$2+$3+$4+$5; }
	;

streaming_concatenation<str>:	// ==IEEE: streaming_concatenation
	//	 		// Need to disambiguate {<< expr-{ ... expr-} stream_concat }
	//			// From                 {<< stream-{ ... stream-} }
	//			// Likewise simple_type's idScoped from constExpr's idScope
	//			// Thus we allow always any two operations.  Sorry
	//			// IEEE: "'{' yP_SL/R             stream_concatenation '}'"
	//			// IEEE: "'{' yP_SL/R simple_type stream_concatenation '}'"
	//			// IEEE: "'{' yP_SL/R constExpr	  stream_concatenation '}'"
		'{' yP_SLEFT              stream_concOrExprOrType '}'	{ $<fl>$=$<fl>1; $$="{<<"+$3+"}"; }
	|	'{' yP_SRIGHT             stream_concOrExprOrType '}'	{ $<fl>$=$<fl>1; $$="{>>"+$3+"}"; }
	|	'{' yP_SLEFT  stream_concOrExprOrType stream_concatenation '}'	{ $<fl>$=$<fl>1; $$="{<<"+$3+" "+$4+"}"; }
	|	'{' yP_SRIGHT stream_concOrExprOrType stream_concatenation '}'	{ $<fl>$=$<fl>1; $$="{>>"+$3+" "+$4+"}"; }
	;

stream_concOrExprOrType<str>:	// IEEE: stream_concatenation | slice_size:simple_type | slice_size:constExpr
		cateList				{ $<fl>$=$<fl>1; $$=$1; }
	|	simple_type				{ $<fl>$=$<fl>1; $$=$1; }
	//			// stream_concatenation found via cateList:stream_expr:'{-normal-concat'
	//			// simple_typeRef found via cateList:stream_expr:expr:id
	//			// constant_expression found via cateList:stream_expr:expr
	;

stream_concatenation<str>:	// ==IEEE: stream_concatenation
		'{' stream_expressionList '}'		{ $<fl>$=$<fl>1; $$="{"+$2+"}"; }
	;

stream_expressionList<str>:	// IEEE: part of stream_concatenation
		stream_expression				{ $<fl>$=$<fl>1; $$=$1; }
	|	stream_expressionList ',' stream_expression	{ $<fl>$=$<fl>1; $$=$1+","+$3; }
	;

stream_expression<str>:		// ==IEEE: stream_expression
	//			// IEEE: array_range_expression expanded below
		expr					{ $<fl>$=$<fl>1; $$=$1; }
	|	expr yWITH__BRA '[' expr ']'		{ $<fl>$=$<fl>1; $$=$1; }
	|	expr yWITH__BRA '[' expr ':' expr ']'	{ $<fl>$=$<fl>1; $$=$1; }
	|	expr yWITH__BRA '[' expr yP_PLUSCOLON  expr ']'	{ $<fl>$=$<fl>1; $$=$1; }
	|	expr yWITH__BRA '[' expr yP_MINUSCOLON expr ']'	{ $<fl>$=$<fl>1; $$=$1; }
	;

//************************************************
// Gate declarations

// We can't tell between UDPs and modules as they aren't declared yet.
// For simplicity, assume everything is a module, perhaps nameless,
// and deal with it later.

// IEEE: cmos_switchtype + enable_gatetype + mos_switchtype
//	+ n_input_gatetype + n_output_gatetype + pass_en_switchtype
//	+ pass_switchtype
gateKwd<str>:
		ygenGATE				{ $<fl>$=$<fl>1; INSTPREP($1,0); }
	|	yAND					{ $<fl>$=$<fl>1; INSTPREP($1,0); }
	| 	yBUF					{ $<fl>$=$<fl>1; INSTPREP($1,0); }
	|	yNAND					{ $<fl>$=$<fl>1; INSTPREP($1,0); }
	|	yNOR					{ $<fl>$=$<fl>1; INSTPREP($1,0); }
	|	yNOT					{ $<fl>$=$<fl>1; INSTPREP($1,0); }
	|	yOR					{ $<fl>$=$<fl>1; INSTPREP($1,0); }
	|	yXNOR					{ $<fl>$=$<fl>1; INSTPREP($1,0); }
	|	yXOR					{ $<fl>$=$<fl>1; INSTPREP($1,0); }
	;

// This list is also hardcoded in VParseLex.l
strength:			// IEEE: strength0+strength1 - plus HIGHZ/SMALL/MEDIUM/LARGE
		ygenSTRENGTH				{ }
	|	ySUPPLY0				{ }
	|	ySUPPLY1				{ }
	;

strengthSpecE:			// IEEE: drive_strength + pullup_strength + pulldown_strength + charge_strength - plus empty
		/* empty */				{ }
	|	strengthSpec				{ }
	;

strengthSpec:			// IEEE: drive_strength + pullup_strength + pulldown_strength + charge_strength - plus empty
		yP_PAR__STRENGTH strength ')'			{ }
	|	yP_PAR__STRENGTH strength ',' strength ')'	{ }
	;

//************************************************
// Tables

combinational_body:		// ==IEEE: combinational_body
		yTABLE tableJunkList yENDTABLE		{ }
	;

tableJunkList:
		tableJunk 				{ } /* ignored */
	|	tableJunkList tableJunk			{ } /* ignored */
	;

tableJunk:
		BISONPRE_NOT(yTABLE,yENDTABLE)		{ }
	|	yTABLE tableJunk yENDTABLE		{ }
	|	error {}
	;

//************************************************
// Specify

specify_block:			// ==IEEE: specify_block
		ySPECIFY specifyJunkList yENDSPECIFY	{ }
	|	ySPECIFY yENDSPECIFY			{ }
	;

specifyJunkList:
		specifyJunk 				{ } /* ignored */
	|	specifyJunkList specifyJunk		{ } /* ignored */
	;

specifyJunk:
		BISONPRE_NOT(ySPECIFY,yENDSPECIFY)	{ }
	|	ySPECIFY specifyJunk yENDSPECIFY	{ }
	|	error {}
	;

specparam_declaration:		// ==IEEE: specparam_declaration
		ySPECPARAM junkToSemiList ';'		{ }
	;

junkToSemiList:
		junkToSemi 				{ } /* ignored */
	|	junkToSemiList junkToSemi		{ } /* ignored */
	;

junkToSemi:
		BISONPRE_NOT(';',yENDSPECIFY,yENDMODULE)	{ }
	|	error {}
	;

//************************************************
// IDs

id<str>:
		yaID__ETC				{ $<fl>$=$<fl>1; $$=$1; }
	;

idAny<str>:			// Any kind of identifier
		yaID__aCLASS				{ $<fl>$=$<fl>1; $$=$1; }
	|	yaID__aCOVERGROUP			{ $<fl>$=$<fl>1; $$=$1; }
	|	yaID__aPACKAGE				{ $<fl>$=$<fl>1; $$=$1; }
	|	yaID__aTYPE				{ $<fl>$=$<fl>1; $$=$1; }
	|	yaID__ETC				{ $<fl>$=$<fl>1; $$=$1; }
	;

idSVKwd<str>:			// Warn about non-forward compatible Verilog 2001 code
	//			// yBIT, yBYTE won't work here as causes conflicts
		yDO					{ $<fl>$=$<fl>1; $$=$1; ERRSVKWD($<fl>1,$$); }
	|	yFINAL					{ $<fl>$=$<fl>1; $$=$1; ERRSVKWD($<fl>1,$$); }
	;

variable_lvalue<str>:		// IEEE: variable_lvalue or net_lvalue
	//			// Note many variable_lvalue's must use exprOkLvalue when arbitrary expressions may also exist
		idClassSel				{ $<fl>$=$<fl>1; $$ = $1; }
	|	'{' variable_lvalueConcList '}'		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	//			// IEEE: [ assignment_pattern_expression_type ] assignment_pattern_variable_lvalue
	//			// We allow more assignment_pattern_expression_types then strictly required
	|	data_type  yP_TICKBRA variable_lvalueList '}'	{ $<fl>$=$<fl>1; $$ = $1+" "+$2+$3+$4; }
	|	idClassSel yP_TICKBRA variable_lvalueList '}'	{ $<fl>$=$<fl>1; $$ = $1+" "+$2+$3+$4; }
	|	/**/       yP_TICKBRA variable_lvalueList '}'	{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	streaming_concatenation			{ $<fl>$=$<fl>1; $$ = $1; }
	;

variable_lvalueConcList<str>:	// IEEE: part of variable_lvalue: '{' variable_lvalue { ',' variable_lvalue } '}'
		variable_lvalue					{ $<fl>$=$<fl>1; $$ = $1; }
	|	variable_lvalueConcList ',' variable_lvalue	{ $<fl>$=$<fl>1; $$ = $1+","+$3; }
	;

variable_lvalueList<str>:	// IEEE: part of variable_lvalue: variable_lvalue { ',' variable_lvalue }
		variable_lvalue				{ $<fl>$=$<fl>1; $$ = $1; }
	|	variable_lvalueList ',' variable_lvalue	{ $<fl>$=$<fl>1; $$ = $1+","+$3; }
	;

idClassSel<str>:		// Misc Ref to dotted, and/or arrayed, and/or bit-ranged variable
		idDotted				{ $<fl>$=$<fl>1; $$ = $1; }
	//			// IEEE: [ implicit_class_handle . | package_scope ] hierarchical_variable_identifier select
	|	yTHIS '.' idDotted			{ $<fl>$=$<fl>1; $$ = "this."+$3; }
	|	ySUPER '.' idDotted			{ $<fl>$=$<fl>1; $$ = "super."+$3; }
	|	yTHIS '.' ySUPER '.' idDotted		{ $<fl>$=$<fl>1; $$ = "this.super."+$3; }
	//			// Expanded: package_scope idDotted
	|	class_scopeIdFollows idDotted		{ $<fl>$=$<fl>1; $$ = $<str>1+$2; }
	|	package_scopeIdFollows idDotted		{ $<fl>$=$<fl>1; $$ = $<str>1+$2; }
	;

idClassForeach<str>:		// Misc Ref to dotted, and/or arrayed, no bit range for foreach statement
	//			// We can't just use the more general idClassSel
	//			// because ,'s are allowed in the []'s
		idDottedForeach				{ $<fl>$=$<fl>1; $$ = $1; }
	//			// IEEE: [ implicit_class_handle . | package_scope ] hierarchical_variable_identifier select
	|	yTHIS '.' idDottedForeach		{ $<fl>$=$<fl>1; $$ = "this."+$3; }
	|	ySUPER '.' idDottedForeach		{ $<fl>$=$<fl>1; $$ = "super."+$3; }
	|	yTHIS '.' ySUPER '.' idDottedForeach	{ $<fl>$=$<fl>1; $$ = "this.super."+$3; }
	//			// Expanded: package_scope idDotted
	|	class_scopeIdFollows idDottedForeach	{ $<fl>$=$<fl>1; $$ = $<str>1+$2; }
	|	package_scopeIdFollows idDottedForeach	{ $<fl>$=$<fl>1; $$ = $<str>1+$2; }
	;

hierarchical_identifierList:	// IEEE: part of wait_statement
		hierarchical_identifier			{ }
	|	hierarchical_identifierList ',' hierarchical_identifier		{ }
	;

hierarchical_identifierBit:	// IEEE: "hierarchical_identifier bit_select"
	//			// Not in grammar but "this." believed legal here
		idClassSel				{ }
	;

hierarchical_identifier<str>:	// IEEE: hierarchical_identifier, including extra bit_select
	//			//	  +hierarchical_parameter_identifier
	//			// Not in grammar but "this." believed legal here
		idClassSel				{ $<fl>$=$<fl>1; $$ = $1; }
	;

idDotted<str>:
		yD_ROOT '.' idDottedMore		{ $<fl>$=$<fl>1; $$ = $1+"."+$3; }
	|	idDottedMore		 		{ $<fl>$=$<fl>1; $$ = $1; }
	;

idDottedForeach<str>:
		yD_ROOT '.' idDottedForeachMore		{ $<fl>$=$<fl>1; $$ = $1+"."+$3; }
	|	idDottedForeachMore	 		{ $<fl>$=$<fl>1; $$ = $1; }
	;

idDottedMore<str>:
		idArrayed 				{ $<fl>$=$<fl>1; $$ = $1; }
	|	idDottedMore '.' idArrayed		{ $<fl>$=$<fl>1; $$ = $1+"."+$3; }
	;

idDottedForeachMore<str>:
		idForeach 				{ $<fl>$=$<fl>1; $$ = $1; }
	|	idDottedForeachMore '.' idForeach	{ $<fl>$=$<fl>1; $$ = $1+"."+$3; }
	;

// Single component of dotted path, maybe [#].
// Due to lookahead constraints, we can't know if [:] or [+:] are valid (last dotted part),
// we'll assume so and cleanup later.
// id below includes:
//	 enum_identifier
idArrayed<str>:			// IEEE: id + select
		id					{ $<fl>$=$<fl>1; $$ = $1; }
	//			// IEEE: part_select_range/constant_part_select_range
	|	idArrayed '[' expr ']'				{ $<fl>$=$<fl>1; $$ = $1+"["+$3+"]"; }
	|	idArrayed '[' constExpr ':' constExpr ']'	{ $<fl>$=$<fl>1; $$ = $1+"["+$3+":"+$5+"]"; }
	//	 		// IEEE: indexed_range/constant_indexed_range
	|	idArrayed '[' expr yP_PLUSCOLON  constExpr ']'	{ $<fl>$=$<fl>1; $$ = $1+"["+$3+"+:"+$5+"]"; }
	|	idArrayed '[' expr yP_MINUSCOLON constExpr ']'	{ $<fl>$=$<fl>1; $$ = $1+"["+$3+"-:"+$5+"]"; }
	;

idForeach<str>:			// IEEE: id + select + [loop_variables]
	//			// Merge of foreach and idArrayed to prevent conflict
		id					{ $<fl>$=$<fl>1; $$ = $1; }
	//			// IEEE: part_select_range/constant_part_select_range
	|	idForeach '[' expr ']'				{ $<fl>$=$<fl>1; $$ = $1+"["+$3+"]"; }
	|	idForeach '[' constExpr ':' constExpr ']'	{ $<fl>$=$<fl>1; $$ = $1+"["+$3+":"+$5+"]"; }
	//	 		// IEEE: indexed_range/constant_indexed_range
	|	idForeach '[' expr yP_PLUSCOLON  constExpr ']'	{ $<fl>$=$<fl>1; $$ = $1+"["+$3+"+:"+$5+"]"; }
	|	idForeach '[' expr yP_MINUSCOLON constExpr ']'	{ $<fl>$=$<fl>1; $$ = $1+"["+$3+"-:"+$5+"]"; }
	//			// IEEE: part of foreach: [ loop_variables ]
	|	idForeach '[' expr ',' loop_variables ']'	{ $<fl>$=$<fl>1; $$ = $1+"["+$3+","+$5+"]"; }
	;

strAsInt<str>:
		yaSTRING				{ $<fl>$=$<fl>1; $$ = $1; }
	;

endLabelE:
		/* empty */				{ }
	|	':' idAny				{ }
	|	':' yNEW__ETC				{ }
	;

//************************************************
// Clocking

clocking_declaration:		// IEEE: clocking_declaration
		clockingFront clocking_event ';'
			clocking_itemListE yENDCLOCKING endLabelE { PARSEP->symPopScope(VAstType::CLOCKING); }
	//			// global clocking below - we allow item list, though not in grammar
	;

clockingFront:			// IEEE: part of class_declaration
		yCLOCKING				{ PARSEP->symPushNewAnon(VAstType::CLOCKING); }
	|	yCLOCKING idAny/*clocking_identifier*/	{ PARSEP->symPushNew(VAstType::CLOCKING,$2); }
	|	yDEFAULT yCLOCKING			{ PARSEP->symPushNewAnon(VAstType::CLOCKING); }
	|	yDEFAULT yCLOCKING idAny/*clocking_identifier*/	{ PARSEP->symPushNew(VAstType::CLOCKING,$3); }
	|	yGLOBAL__CLOCKING yCLOCKING			{ PARSEP->symPushNewAnon(VAstType::CLOCKING); }
	|	yGLOBAL__CLOCKING yCLOCKING idAny/*clocking_identifier*/	{ PARSEP->symPushNew(VAstType::CLOCKING,$3); }
	;

clocking_event:			// ==IEEE: clocking_event
		'@' id					{ }
	|	'@' '(' event_expression ')'		{ }
	;

clocking_itemListE:
		/* empty */				{ }
	|	clocking_itemList			{ }
	;

clocking_itemList:		// IEEE: [ clocking_item ]
		clocking_item				{ }
	|	clocking_itemList clocking_item		{ }
	;

clocking_item:			// ==IEEE: clocking_item
		yDEFAULT default_skew ';'		{ }
	|	clocking_direction list_of_clocking_decl_assign ';'	{ }
	|	assertion_item_declaration		{ }
	;

default_skew:			// ==IEEE: default_skew
		yINPUT clocking_skew			{ }
	|	yOUTPUT clocking_skew			{ }
	|	yINPUT clocking_skew yOUTPUT clocking_skew	{ }
	;

clocking_direction:		// ==IEEE: clocking_direction
		yINPUT clocking_skewE			{ }
	|	yOUTPUT clocking_skewE			{ }
	|	yINPUT clocking_skewE yOUTPUT clocking_skewE	{ }
	|	yINOUT					{ }
	;

list_of_clocking_decl_assign:	// ==IEEE: list_of_clocking_decl_assign
		clocking_decl_assign			{ }
	|	list_of_clocking_decl_assign ',' clocking_decl_assign	{ }
	;

clocking_decl_assign:		// ==IEEE: clocking_decl_assign
		idAny/*new-signal_identifier*/		{ }
	|	idAny/*new-signal_identifier*/ '=' expr	{ }
	;

clocking_skewE:			// IEEE: [clocking_skew]
		/* empty */				{ }
	|	clocking_skew				{ }
	;

clocking_skew:			// ==IEEE: clocking_skew
		yPOSEDGE				{ }
	|	yPOSEDGE delay_control			{ }
	|	yNEGEDGE				{ }
	|	yNEGEDGE delay_control			{ }
	|	yEDGE					{ NEED_S09($<fl>1,"edge"); }
	|	yEDGE delay_control			{ NEED_S09($<fl>1,"edge"); }
	|	delay_control				{ }
	;

cycle_delay:			// ==IEEE: cycle_delay
		yP_POUNDPOUND yaINTNUM			{ }
	|	yP_POUNDPOUND id			{ }
	|	yP_POUNDPOUND '(' expr ')'		{ }
	;

//************************************************
// Asserts

assertion_item_declaration:	// ==IEEE: assertion_item_declaration
		property_declaration			{ }
	|	sequence_declaration			{ }
	|	let_declaration				{ }
	;

assertion_item:			// ==IEEE: assertion_item
		concurrent_assertion_item		{ }
	|	deferred_immediate_assertion_item	{ }
	;

deferred_immediate_assertion_item:	// ==IEEE: deferred_immediate_assertion_item
		deferred_immediate_assertion_statement	{ }
	|	id/*block_identifier*/ ':' deferred_immediate_assertion_statement	{ }
	;

procedural_assertion_statement:	// ==IEEE: procedural_assertion_statement
		concurrent_assertion_statement		{ }
	|	immediate_assertion_statement		{ }
	//			// IEEE: checker_instantiation
	//			// Unlike modules, checkers are the only "id id (...)" form in statements.
	|	checker_instantiation			{ }
	;

immediate_assertion_statement:	// ==IEEE: immediate_assertion_statement
		simple_immediate_assertion_statement	{ }
	|	deferred_immediate_assertion_statement	{ }
	;

simple_immediate_assertion_statement:	// ==IEEE: simple_immediate_assertion_statement
	//			// IEEE: simple_immediate_assert_statement
		yASSERT '(' expr ')' action_block	{ }
	//			// IEEE: simple_immediate_assume_statement
	|	yASSUME '(' expr ')' action_block	{ }
	//			// IEEE: simple_immediate_cover_statement
	|	yCOVER '(' expr ')' stmt 		{ }
	;

deferred_immediate_assertion_statement:	// ==IEEE: deferred_immediate_assertion_statement
	//			// IEEE: deferred_immediate_assert_statement
		yASSERT '#' yaINTNUM '(' expr ')' action_block	{ }	// yaINTNUM is always a '0'
	//			// IEEE: deferred_immediate_assume_statement
	|	yASSUME '#' yaINTNUM '(' expr ')' action_block	{ }	// yaINTNUM is always a '0'
	//			// IEEE: deferred_immediate_cover_statement
	|	yCOVER '#' yaINTNUM '(' expr ')' stmt	{ }	// yaINTNUM is always a '0'
	;

expect_property_statement:	// ==IEEE: expect_property_statement
		yEXPECT '(' property_spec ')' action_block	{ }
	;

concurrent_assertion_item:	// IEEE: concurrent_assertion_item
		concurrent_assertion_statement		{ }
	|	id/*block_identifier*/ ':' concurrent_assertion_statement	{ }
	//			// IEEE: checker_instantiation
	//			// identical to module_instantiation; see etcInst
	;

concurrent_assertion_statement:	// ==IEEE: concurrent_assertion_statement
	//			// IEEE: assert_property_statement
		yASSERT yPROPERTY '(' property_spec ')' action_block	{ }
	//			// IEEE: assume_property_statement
	|	yASSUME yPROPERTY '(' property_spec ')' action_block	{ }
	//			// IEEE: cover_property_statement
	|	yCOVER yPROPERTY '(' property_spec ')' stmtBlock	{ }
	//			// IEEE: cover_sequence_statement
	|	yCOVER ySEQUENCE '(' sexpr ')' stmt	{ }
	//			// IEEE: yCOVER ySEQUENCE '(' clocking_event sexpr ')' stmt
	//			// sexpr already includes "clocking_event sexpr"
	|	yCOVER ySEQUENCE '(' clocking_event yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' sexpr ')' stmt	{ }
	|	yCOVER ySEQUENCE '(' yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' sexpr ')' stmt	{ }
	//			// IEEE: restrict_property_statement
	|	yRESTRICT yPROPERTY '(' property_spec ')' ';'		{ }
	;

property_declaration:		// ==IEEE: property_declaration
		property_declarationFront property_port_listE ';' property_declarationBody
			yENDPROPERTY endLabelE
			{ PARSEP->symPopScope(VAstType::PROPERTY); }
	;

property_declarationFront:	// IEEE: part of property_declaration
		yPROPERTY idAny/*property_identifier*/
			{ PARSEP->symPushNew(VAstType::PROPERTY,$2); }
	;

property_port_listE:		// IEEE: [ ( [ property_port_list ] ) ]
		/* empty */				{ }
	|	'(' {VARRESET_LIST(""); VARIO("input"); } property_port_list ')'
			{ VARRESET_NONLIST(""); }
	;

property_port_list:		// ==IEEE: property_port_list
		property_port_item			{ }
	|	property_port_list ',' property_port_item	{ }
	;

property_port_item:		// IEEE: property_port_item/sequence_port_item
	//			// Merged in sequence_port_item
	//			// IEEE: property_lvar_port_direction ::= yINPUT
	//			// prop IEEE: [ yLOCAL [ yINPUT ] ] property_formal_type
	//			//	     id {variable_dimension} [ '=' property_actual_arg ]
	//			// seq IEEE: [ yLOCAL [ sequence_lvar_port_direction ] ] sequence_formal_type
	//			//           id {variable_dimension} [ '=' sequence_actual_arg ]
		property_port_itemFront property_port_itemAssignment { }
	;

property_port_itemFront:	// IEEE: part of property_port_item/sequence_port_item
	//
		property_port_itemDirE property_formal_typeNoDt		{ VARDTYPE($2); }
	//			// data_type_or_implicit
	|	property_port_itemDirE data_type           	{ VARDTYPE($2); }
	|	property_port_itemDirE yVAR data_type      	{ VARDTYPE($3); }
	|	property_port_itemDirE yVAR implicit_typeE 	{ VARDTYPE($3); }
	|	property_port_itemDirE signingE rangeList  	{ VARDTYPE(SPACED($2,$3)); }
	|	property_port_itemDirE /*implicit*/        	{ /*VARDTYPE-same*/ }
	;

property_port_itemAssignment:	// IEEE: part of property_port_item/sequence_port_item
		portSig variable_dimensionListE		{ VARDONE($<fl>1, $1, $2, ""); PINNUMINC(); }
	|	portSig variable_dimensionListE '=' property_actual_arg
			{ VARDONE($<fl>1, $1, $2, $4); PINNUMINC(); }
	;

property_port_itemDirE:
		/* empty */				{ }
	|	yLOCAL__ETC				{ }
	|	yLOCAL__ETC port_direction		{ }
	;

property_declarationBody:	// IEEE: part of property_declaration
		assertion_variable_declarationList property_statement_spec	{ }
	|	property_statement_spec			{ }
	;

assertion_variable_declarationList: // IEEE: part of assertion_variable_declaration
		assertion_variable_declaration		{ }
	|	assertion_variable_declarationList assertion_variable_declaration	{ }
	;

sequence_declaration:		// ==IEEE: sequence_declaration
		sequence_declarationFront sequence_port_listE ';' sequence_declarationBody
			yENDSEQUENCE endLabelE
			{ PARSEP->symPopScope(VAstType::SEQUENCE); }
	;

sequence_declarationFront:	// IEEE: part of sequence_declaration
		ySEQUENCE idAny/*new_sequence*/
			{ PARSEP->symPushNew(VAstType::SEQUENCE,$2); }
	;

sequence_port_listE:		// IEEE: [ ( [ sequence_port_list ] ) ]
	//			// IEEE: sequence_lvar_port_direction ::= yINPUT | yINOUT | yOUTPUT
	//			// IEEE: [ yLOCAL [ sequence_lvar_port_direction ] ] sequence_formal_type
	//			//           id {variable_dimension} [ '=' sequence_actual_arg ]
	//			// All this is almost identically the same as a property.
	//			// Difference is only yINOUT/yOUTPUT (which might be added to 1800-2012)
	//			// and yPROPERTY.  So save some work.
		property_port_listE			{ }
	;

property_formal_typeNoDt<str>:	// IEEE: property_formal_type (w/o implicit)
		sequence_formal_typeNoDt		{ $$ = $1; }
	|	yPROPERTY				{ $$ = "property"; }
	;

sequence_formal_typeNoDt<str>:	// ==IEEE: sequence_formal_type (w/o data_type_or_implicit)
	//			// IEEE: data_type_or_implicit
	//			// implicit expanded where used
		ySEQUENCE				{ $$ = "sequence"; }
	//			// IEEE: yEVENT
	//			// already part of data_type
	|	yUNTYPED				{ $$ = "untyped"; }
	;

sequence_declarationBody:	// IEEE: part of sequence_declaration
		assertion_variable_declarationList sexpr ';'	{ }
	|	sexpr ';'				{ }
	;

property_spec:			// IEEE: property_spec
	//			// IEEE: [clocking_event ] [ yDISABLE yIFF '(' expression_or_dist ')' ] property_expr
	//			// matches property_spec: "clocking_event property_expr" so we put it there
		yDISABLE yIFF '(' expr ')' pexpr	{ }
	|	pexpr			 		{ }
	;

property_statement_spec:	// ==IEEE: property_statement_spec
	//			// IEEE: [ clocking_event ] [ yDISABLE yIFF '(' expression_or_dist ')' ] property_statement
		property_statement			{ }
	|	yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' property_statement	{ }
	//			// IEEE: clocking_event property_statement
	//			// IEEE: clocking_event yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' property_statement
	//			// Both overlap pexpr:"clocking_event pexpr"  the difference is
	//			// property_statement:property_statementCaseIf so replicate it
	|	clocking_event property_statementCaseIf	{ }
	|	clocking_event yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' property_statementCaseIf	{ }
	;

property_statement:		// ==IEEE: property_statement
	//			// Doesn't make sense to have "pexpr ;" in pexpr rule itself, so we split out case/if
		pexpr ';'				{ }
	//			// Note this term replicated in property_statement_spec
	//			// If committee adds terms, they may need to be there too.
	|	property_statementCaseIf		{ }
	;

property_statementCaseIf:	// IEEE: property_statement - minus pexpr
		yCASE '(' expr/*expression_or_dist*/ ')' property_case_itemList yENDCASE	{ }
	|	yCASE '(' expr/*expression_or_dist*/ ')' yENDCASE		{ }
	|	yIF '(' expr/*expression_or_dist*/ ')' pexpr  %prec prLOWER_THAN_ELSE	{ }
	|	yIF '(' expr/*expression_or_dist*/ ')' pexpr yELSE pexpr	{ }
	;

property_case_itemList:		// IEEE: {property_case_item}
		property_case_item			{ }
	|	property_case_itemList ',' property_case_item	{ }
	;

property_case_item:		// ==IEEE: property_case_item
	//			// IEEE: expression_or_dist { ',' expression_or_dist } ':' property_statement
		caseCondList ':' property_statement	{ }
	|	yDEFAULT property_statement		{ }
	|	yDEFAULT ':' property_statement		{ }
	;

pev_expr<str>:			// IEEE: property_actual_arg | expr
	//			//       which expands to pexpr | event_expression
	//			// Used in port and function calls, when we can't know yet if something
	//			// is a function/sequence/property or instance/checker pin.
	//
	//			// '(' pev_expr ')'
	//			// Already in pexpr
	//			// IEEE: event_expression ',' event_expression
	//			// ','s are legal in event_expressions, but parens required to avoid conflict with port-sep-,
	//			// IEEE: event_expression yOR event_expression
	//			// Already in pexpr - needs removal there
	//			// IEEE: event_expression yIFF expr
	//			// Already in pexpr - needs removal there
	//
		senitemEdge				{ $$=$1; }
	//
	//============= pexpr rules copied for pev_expr
	|	BISONPRE_COPY_ONCE(pexpr,{s/~o~p/pev_/g; })	// {copied}
	//
	//============= sexpr rules copied for pev_expr
	|	BISONPRE_COPY_ONCE(sexpr,{s/~p~s/pev_/g; })	// {copied}
	//
	//============= expr rules copied for pev_expr
	|	BISONPRE_COPY_ONCE(expr,{s/~l~/pev_/g; s/~p~/pev_/g; s/~noPar__IGNORE~/yP_PAR__IGNORE /g; })	// {copied}
	;

pexpr<str>:			// IEEE: property_expr  (The name pexpr is important as regexps just add an "p" to expr.)
	//
	//			// IEEE: sequence_expr
	//			// Expanded below
	//
	//			// IEEE: '(' pexpr ')'
	//			// Expanded below
	//
		yNOT pexpr %prec prNEGATION		{ }
	|	ySTRONG '(' sexpr ')'			{ }
	|	yWEAK '(' sexpr ')'			{ }
	//			// IEEE: pexpr yOR pexpr
	//			// IEEE: pexpr yAND pexpr
	//			// Under ~p~sexpr and/or ~p~sexpr
	//
	//			// IEEE: "sequence_expr yP_ORMINUSGT pexpr"
	//			// Instead we use pexpr to prevent conflicts
	|	~o~pexpr yP_ORMINUSGT pexpr		{ }
	|	~o~pexpr yP_OREQGT pexpr		{ }
	//
	//			// IEEE: property_statement
	|	property_statementCaseIf		{ }
	//
	|	~o~pexpr/*sexpr*/ yP_POUNDMINUSPD pexpr	{ }
	|	~o~pexpr/*sexpr*/ yP_POUNDEQPD pexpr	{ }
	|	yNEXTTIME pexpr				{ }
	|	yS_NEXTTIME pexpr			{ }
	|	yNEXTTIME '[' expr/*const*/ ']' pexpr %prec yNEXTTIME		{ }
	|	yS_NEXTTIME '[' expr/*const*/ ']' pexpr	%prec yS_NEXTTIME	{ }
	|	yALWAYS pexpr				{ }
	|	yALWAYS '[' cycle_delay_const_range_expression ']' pexpr  %prec yALWAYS	{ }
	|	yS_ALWAYS '[' constant_range ']' pexpr  %prec yS_ALWAYS		{ }
	|	yS_EVENTUALLY pexpr			{ }
	|	yEVENTUALLY '[' constant_range ']' pexpr  %prec yEVENTUALLY	{ }
	|	yS_EVENTUALLY '[' cycle_delay_const_range_expression ']' pexpr  %prec yS_EVENTUALLY	{ }
	|	~o~pexpr yUNTIL pexpr			{ }
	|	~o~pexpr yS_UNTIL pexpr			{ }
	|	~o~pexpr yUNTIL_WITH pexpr		{ }
	|	~o~pexpr yS_UNTIL_WITH pexpr		{ }
	|	~o~pexpr yIMPLIES pexpr			{ }
	//			// yIFF also used by event_expression
	|	~o~pexpr yIFF ~o~pexpr			{ }
	|	yACCEPT_ON '(' expr/*expression_or_dist*/ ')' pexpr  %prec yACCEPT_ON	{ }
	|	yREJECT_ON '(' expr/*expression_or_dist*/ ')' pexpr  %prec yREJECT_ON	{ }
	|	ySYNC_ACCEPT_ON '(' expr/*expression_or_dist*/ ')' pexpr %prec ySYNC_ACCEPT_ON	{ }
	|	ySYNC_REJECT_ON '(' expr/*expression_or_dist*/ ')' pexpr %prec ySYNC_REJECT_ON	{ }
	//
	//			// IEEE: "property_instance"
	//			// Looks just like a function/method call
	//
	//			// Note "clocking_event pexpr" overlaps property_statement_spec: clocking_event property_statement
	//
	//			// Include property_specDisable to match property_spec rule
	|	clocking_event yDISABLE yIFF '(' expr ')' pexpr	%prec prSEQ_CLOCKING	{ }
	//
	//============= sexpr rules copied for property_expr
	|	BISONPRE_COPY_ONCE(sexpr,{s/~p~s/p/g; })	// {copied}
	//
	//============= expr rules copied for property_expr
	|	BISONPRE_COPY_ONCE(expr,{s/~l~/p/g; s/~p~/p/g; s/~noPar__IGNORE~/yP_PAR__IGNORE /g; })	// {copied}
	;


sexpr<str>:			// ==IEEE: sequence_expr  (The name sexpr is important as regexps just add an "s" to expr.)
	//			// ********* RULES COPIED IN sequence_exprProp
	//			// For precedence, see IEEE 17.7.1
	//
	// 			// IEEE: "cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }"
	//			// IEEE: "sequence_expr cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }"
	//			// Both rules basically mean we can repeat sequences, so make it simpler:
		cycle_delay_range sexpr	 %prec yP_POUNDPOUND	{ }
	|	~p~sexpr cycle_delay_range sexpr %prec prPOUNDPOUND_MULTI	{ }
	//
	//			// IEEE: expression_or_dist [ boolean_abbrev ]
	//			// Note expression_or_dist includes "expr"!
	//			// sexpr/*sexpression_or_dist*/	 --- Hardcoded below
	|	~p~sexpr/*sexpression_or_dist*/ boolean_abbrev	{ }
	//
	//			// IEEE: "sequence_instance [ sequence_abbrev ]"
	//			// version without sequence_abbrev looks just like normal function call
	//			// version w/sequence_abbrev matches above; expression_or_dist:expr:func boolean_abbrev:sequence_abbrev
	//
	//			// IEEE: '(' expression_or_dist {',' sequence_match_item } ')' [ boolean_abbrev ]
	//			// IEEE: '(' sexpr {',' sequence_match_item } ')' [ sequence_abbrev ]
	//			// As sequence_expr includes expression_or_dist, and boolean_abbrev includes sequence_abbrev:
	//			// '(' sequence_expr {',' sequence_match_item } ')' [ boolean_abbrev ]
	//			// "'(' sexpr ')' boolean_abbrev" matches "[sexpr:'(' expr ')'] boolean_abbrev" so we can simply drop it
	|	'(' ~p~sexpr ')'			{ $<fl>$=$<fl>1; $$=$1+$2+$3; }
	|	'(' ~p~sexpr ',' sequence_match_itemList ')'	{ }
	//
	//			// AND/OR are between pexprs OR sexprs
	|	~p~sexpr yAND ~p~sexpr			{ $<fl>$=$<fl>1; $$=$1+$2+$3; }
	|	~p~sexpr yOR ~p~sexpr			{ $<fl>$=$<fl>1; $$=$1+$2+$3; }
	//			// Intersect always has an sexpr rhs
	|	~p~sexpr yINTERSECT sexpr		{ $<fl>$=$<fl>1; $$=$1+$2+$3; }
	//
	|	yFIRST_MATCH '(' sexpr ')'		{ }
	|	yFIRST_MATCH '(' sexpr ',' sequence_match_itemList ')'	{ }
	|	~p~sexpr/*sexpression_or_dist*/ yTHROUGHOUT sexpr		{ }
	//			// Below pexpr's are really sequence_expr, but avoid conflict
	//			// IEEE: sexpr yWITHIN sexpr
	|	~p~sexpr yWITHIN sexpr			{ $<fl>$=$<fl>1; $$=$1+$2+$3; }
	//			// Note concurrent_assertion had duplicate rule for below
	|	clocking_event ~p~sexpr %prec prSEQ_CLOCKING	{ }
	//
	//============= expr rules copied for sequence_expr
	|	BISONPRE_COPY_ONCE(expr,{s/~l~/s/g; s/~p~/s/g; s/~noPar__IGNORE~/yP_PAR__IGNORE /g; })	// {copied}
	;

cycle_delay_range:		// IEEE: ==cycle_delay_range
	//			// These three terms in 1800-2005 ONLY
		yP_POUNDPOUND yaINTNUM			{ }
	|	yP_POUNDPOUND id			{ }
	|	yP_POUNDPOUND '(' constExpr ')'		{ }
	//			// In 1800-2009 ONLY:
	//			// IEEE: yP_POUNDPOUND constant_primary
	//			// UNSUP: This causes a big grammer ambiguity
	//			// as ()'s mismatch between primary and the following statement
	//			// the sv-ac committee has been asked to clarify  (Mantis 1901)
	|	yP_POUNDPOUND '[' cycle_delay_const_range_expression ']'	{ }
	|	yP_POUNDPOUND yP_BRASTAR ']'		{ }
	|	yP_POUNDPOUND yP_BRAPLUSKET		{ }
	;

sequence_match_itemList:	// IEEE: [sequence_match_item] part of sequence_expr
		sequence_match_item			{ }
	|	sequence_match_itemList ',' sequence_match_item	{ }
	;

sequence_match_item:		// ==IEEE: sequence_match_item
	//			// IEEE says: operator_assignment
	//			// IEEE says: inc_or_dec_expression
	//			// IEEE says: subroutine_call
	//			// This is the same list as...
		for_step_assignment			{ }
	;

boolean_abbrev:			// ==IEEE: boolean_abbrev
	//			// IEEE: consecutive_repetition
		yP_BRASTAR const_or_range_expression ']'	{ }
	|	yP_BRASTAR ']'				{ }
	|	yP_BRAPLUSKET				{ }
	//			// IEEE: non_consecutive_repetition
	|	yP_BRAEQ const_or_range_expression ']'		{ }
	//			// IEEE: goto_repetition
	|	yP_BRAMINUSGT const_or_range_expression ']'	{ }
	;

const_or_range_expression:	// ==IEEE: const_or_range_expression
		constExpr				{ }
	|	cycle_delay_const_range_expression	{ }
	;


constant_range:			// ==IEEE: constant_range
		constExpr ':' constExpr			{ }
	;

cycle_delay_const_range_expression:	// ==IEEE: cycle_delay_const_range_expression
	//				// Note '$' is part of constExpr
		constExpr ':' constExpr			{ }
	;

//************************************************
// Let

let_declaration:		// ==IEEE: let_declaration
		let_declarationFront let_port_listE '=' expr ';'
			{ PARSEP->symPopScope(VAstType::LET); }
	;

let_declarationFront:		// IEEE: part of let_declaration
		yLET idAny/*let_identifier*/
			{ PARSEP->symPushNew(VAstType::LET,$2); }
	;

let_port_listE:			// ==IEEE: let_port_list
		/* empty */
	//			// IEEE: let_port_list
	//			// No significant difference from task ports
	|	'(' tf_port_listE ')'
			{ VARRESET_NONLIST(""); }
	;

//************************************************
// Covergroup

covergroup_declaration:		// ==IEEE: covergroup_declaration
		covergroup_declarationFront coverage_eventE ';' coverage_spec_or_optionListE
			yENDGROUP endLabelE
			{ PARSEP->endgroupCb($<fl>5,$5);
			  PARSEP->symPopScope(VAstType::COVERGROUP); }
	|	covergroup_declarationFront '(' tf_port_listE ')' coverage_eventE ';' coverage_spec_or_optionListE
			yENDGROUP endLabelE
			{ PARSEP->endgroupCb($<fl>8,$8);
			  PARSEP->symPopScope(VAstType::COVERGROUP); }
	;

covergroup_declarationFront:	// IEEE: part of covergroup_declaration
		yCOVERGROUP idAny
 			{ PARSEP->symPushNew(VAstType::COVERGROUP,$2);
			  PARSEP->covergroupCb($<fl>1,$1,$2); }
	;

coverage_spec_or_optionListE:	// IEEE: [{coverage_spec_or_option}]
		/* empty */				{ }
	|	coverage_spec_or_optionList		{ }
	;

coverage_spec_or_optionList:	// IEEE: {coverage_spec_or_option}
		coverage_spec_or_option			{ }
	|	coverage_spec_or_optionList coverage_spec_or_option	{ }
	;

coverage_spec_or_option:	// ==IEEE: coverage_spec_or_option
	//			// IEEE: coverage_spec
		cover_point				{ }
	|	cover_cross				{ }
	|	coverage_option ';'			{ }
	|	error					{ }
	;

coverage_option:		// ==IEEE: coverage_option
	//			// option/type_option aren't really keywords
		id/*yOPTION | yTYPE_OPTION*/ '.' idAny/*member_identifier*/ '=' expr	{ }
	;

cover_point:			// ==IEEE: cover_point
		id ':' yCOVERPOINT expr iffE bins_or_empty	{ }
	|	/**/   yCOVERPOINT expr iffE bins_or_empty	{ }
	;

iffE:				// IEEE: part of cover_point, others
		/* empty */				{ }
	|	yIFF '(' expr ')'			{ }
	;

bins_or_empty:			// ==IEEE: bins_or_empty
		'{' bins_or_optionsList '}'		{ }
	|	'{' '}'					{ }
	|	';'					{ }
	;

bins_or_optionsList:		// IEEE: { bins_or_options ';' }
		bins_or_options ';'			{ }
	|	bins_or_optionsList bins_or_options ';'	{ }
	;

bins_or_options:		// ==IEEE: bins_or_options
		coverage_option				{ }
	//			// Can't use wildcardE as results in conflicts
	|	/**/      bins_keyword id/*bin_identifier*/ '[' expr ']' '=' '{' open_range_list '}' iffE	{ }
	|	/**/      bins_keyword id/*bin_identifier*/ '[' ']'      '=' '{' open_range_list '}' iffE	{ }
	|	/**/      bins_keyword id/*bin_identifier*/              '=' '{' open_range_list '}' iffE	{ }
	|	yWILDCARD bins_keyword id/*bin_identifier*/ '[' expr ']' '=' '{' open_range_list '}' iffE	{ }
	|	yWILDCARD bins_keyword id/*bin_identifier*/ '[' ']'      '=' '{' open_range_list '}' iffE	{ }
	|	yWILDCARD bins_keyword id/*bin_identifier*/              '=' '{' open_range_list '}' iffE	{ }
	//
	|	/**/      bins_keyword id/*bin_identifier*/         '=' trans_list iffE	{ }
	|	/**/      bins_keyword id/*bin_identifier*/ '[' ']' '=' trans_list iffE	{ }
	|	yWILDCARD bins_keyword id/*bin_identifier*/         '=' trans_list iffE	{ }
	|	yWILDCARD bins_keyword id/*bin_identifier*/ '[' ']' '=' trans_list iffE	{ }
	//
	|	bins_keyword id/*bin_identifier*/ '[' expr ']' '=' yDEFAULT iffE	{ }
	|	bins_keyword id/*bin_identifier*/ '[' ']'      '=' yDEFAULT iffE	{ }
	|	bins_keyword id/*bin_identifier*/              '=' yDEFAULT iffE	{ }
	//
	|	bins_keyword id/*bin_identifier*/              '=' yDEFAULT ySEQUENCE iffE { }
	;

bins_keyword:			// ==IEEE: bins_keyword
		yBINS					{ }
	|	yILLEGAL_BINS				{ }
	|	yIGNORE_BINS				{ }
	;

range_list:			// ==IEEE: range_list
	 	value_range				{ }
	|	range_list ',' value_range		{ }
	;

trans_list:			// ==IEEE: trans_list
		'(' trans_set ')'			{ }
	|	trans_list ',' '(' trans_set ')'	{ }
	;

trans_set:			// ==IEEE: trans_set
		trans_range_list			{ }
	//			// Note the { => } in the grammer, this is really a list
	|	trans_set yP_EQGT trans_range_list	{ }
	;

trans_range_list:		// ==IEEE: trans_range_list
		trans_item				{ }
	|	trans_item yP_BRASTAR repeat_range ']'	{ }
	|	trans_item yP_BRAMINUSGT repeat_range ']' { }
	|	trans_item yP_BRAEQ repeat_range ']'	{ }
	;

trans_item:			// ==IEEE: range_list
		 range_list				{ }
	;

repeat_range:			// ==IEEE: repeat_range
		expr					{ }
	|	expr ':' expr				{ }
	;

cover_cross:			// ==IEEE: cover_cross
	 	id/*cover_point_identifier*/ ':' yCROSS list_of_coverpoints iffE	{ }
	|	/**/				 yCROSS list_of_coverpoints iffE	{ }
	|	select_bins_or_empty			{ }
	;

list_of_coverpoints:		// ==IEEE: list_of_coverpoints
		cross_item ',' cross_item		{ }
	|	cross_item ',' cross_item ',' cross_itemList	{ }
	;

cross_itemList:			// IEEE: part of list_of_coverpoints
		cross_item
	|	cross_itemList ',' cross_item		{ }
	;

cross_item:			// ==IEEE: cross_item
		idAny/*cover_point_identifier or variable_identifier*/		{ }
	;

select_bins_or_empty:		// ==IEEE: select_bins_or_empty
		'{' '}'					{ }
	|	'{' bins_selection_or_optionSemiList '}'	{ }
	|	';'					{ }
	;

bins_selection_or_optionSemiList: // IEEE: part of select_bins_or_empty
		bins_selection_or_option ';'		{ }
	|	bins_selection_or_optionSemiList bins_selection_or_option ';' { }
	;

bins_selection_or_option:	// ==IEEE: bins_selection_or_option
		coverage_option				{ }
	|	bins_selection				{ }
	;

bins_selection:			// ==IEEE: bins_selection
		bins_keyword idAny/*new-bin_identifier*/ '=' select_expression iffE	{ }
	;

select_expression:		// ==IEEE: select_expression
		select_condition			{ }
	|	'!' select_condition			{ }
	|	select_expression yP_ANDAND select_expression	{ }
	|	select_expression yP_OROR   select_expression	{ }
	|	'(' select_expression ')'		{ }
	;

select_condition:		// ==IEEE: select_condition
		yBINSOF '(' bins_expression ')'		{ }
	|	yBINSOF '(' bins_expression ')' yINTERSECT '{' open_range_list '}'	{ }
	;

bins_expression:		// ==IEEE: bins_expression
	//			// "cover_point_identifier" and "variable_identifier" look identical
		id/*variable_identifier or cover_point_identifier*/	{ }
	|	id/*cover_point_identifier*/ '.' idAny/*bins_identifier*/	{ }
	;

coverage_eventE:		// IEEE: [ coverage_event ]
		/* empty */				{ }
	|	clocking_event				{ }
	|	yWITH__ETC function idAny/*"sample"*/ '(' tf_port_listE ')'	{ }
	|	yP_ATAT '(' block_event_expression ')'	{ }
	;

block_event_expression:		// ==IEEE: block_event_expression
		block_event_expressionTerm		{ }
	|	block_event_expression yOR block_event_expressionTerm	{ }
	;

block_event_expressionTerm:	// IEEE: part of block_event_expression
		yBEGIN hierarchical_btf_identifier	{ }
	|	yEND   hierarchical_btf_identifier	{ }
	;

hierarchical_btf_identifier:	// ==IEEE: hierarchical_btf_identifier
	//			// hierarchical_tf_identifier + hierarchical_block_identifier
		hierarchical_identifier/*tf_or_block*/	{ }
	//			// method_identifier
	|	hierarchical_identifier class_scope_id	{ }
	|	hierarchical_identifier id		{ }
	;

//**********************************************************************
// Randsequence

randsequence_statement:		// ==IEEE: randsequence_statement
		yRANDSEQUENCE '('    ')' productionList yENDSEQUENCE	{ }
	|	yRANDSEQUENCE '(' id/*production_identifier*/ ')' productionList yENDSEQUENCE	{ }
	;

productionList:			// IEEE: production+
		production				{ }
	|	productionList production		{ }
	;

production:			// ==IEEE: production
		productionFront ':' rs_ruleList ';'	{ }
	;

productionFront:		// IEEE: part of production
		function_data_type id/*production_identifier*/	{ }
	|	/**/		   id/*production_identifier*/	{ }
	|	function_data_type id/*production_identifier*/ '(' tf_port_listE ')'	{ }
	|	/**/		   id/*production_identifier*/ '(' tf_port_listE ')'	{ }
	;

rs_ruleList:			// IEEE: rs_rule+ part of production
		rs_rule					{ }
	|	rs_ruleList '|' rs_rule			{ }
	;

rs_rule:			// ==IEEE: rs_rule
		rs_production_list			{ }
	|	rs_production_list yP_COLONEQ weight_specification	{ }
	|	rs_production_list yP_COLONEQ weight_specification rs_code_block	{ }
	;

rs_production_list:		// ==IEEE: rs_production_list
		rs_prodList				{ }
	|	yRAND yJOIN /**/         production_item production_itemList	{ }
	|	yRAND yJOIN '(' expr ')' production_item production_itemList	{ }
	;

weight_specification:		// ==IEEE: weight_specification
		yaINTNUM				{ }
	|	idClassSel/*ps_identifier*/		{ }
	|	'(' expr ')'				{ }
	;

rs_code_block:			// ==IEEE: rs_code_block
		'{' '}'					{ }
	|	'{' rs_code_blockItemList '}'		{ }
	;

rs_code_blockItemList:		// IEEE: part of rs_code_block
		rs_code_blockItem			{ }
	|	rs_code_blockItemList rs_code_blockItem	{ }
	;

rs_code_blockItem:		// IEEE: part of rs_code_block
		data_declaration			{ }
	|	stmt					{ }
	;

rs_prodList:			// IEEE: rs_prod+
		rs_prod					{ }
	|	rs_prodList rs_prod			{ }
	;

rs_prod:			// ==IEEE: rs_prod
		production_item				{ }
	|	rs_code_block				{ }
	//			// IEEE: rs_if_else
	|	yIF '(' expr ')' production_item %prec prLOWER_THAN_ELSE	{ }
	|	yIF '(' expr ')' production_item yELSE production_item		{ }
	//			// IEEE: rs_repeat
	|	yREPEAT '(' expr ')' production_item	{ }
	//			// IEEE: rs_case
	|	yCASE '(' expr ')' rs_case_itemList yENDCASE	{ }
	;

production_itemList:		// IEEE: production_item+
		production_item				{ }
	|	production_itemList production_item	{ }
	;

production_item:		// ==IEEE: production_item
		id/*production_identifier*/ 		{ }
	|	id/*production_identifier*/ '(' list_of_argumentsE ')'	{ }
	;

rs_case_itemList:		// IEEE: rs_case_item+
		rs_case_item				{ }
	|	rs_case_itemList rs_case_item		{ }
	;

rs_case_item:			// ==IEEE: rs_case_item
		caseCondList ':' production_item ';'	{ }
	|	yDEFAULT production_item ';'		{ }
	|	yDEFAULT ':' production_item ';'	{ }
	;

//**********************************************************************
// Checker

checker_declaration:		// ==IEEE: part of checker_declaration
		checkerFront checker_port_listE ';'
			checker_or_generate_itemListE yENDCHECKER endLabelE
			{ PARSEP->symPopScope(VAstType::CHECKER); }
	;

checkerFront:			// IEEE: part of checker_declaration
		yCHECKER idAny/*checker_identifier*/
			{ PARSEP->symPushNew(VAstType::CHECKER, $2); }
	;

checker_port_listE:		// IEEE: [ ( [ checker_port_list ] ) ]
	//			// checker_port_item is basically the same as property_port_item, minus yLOCAL::
	//			// Want to bet 1800-2012 adds local to checkers?
		property_port_listE			{ }
	;

checker_or_generate_itemListE:	// IEEE: [{ checker_or_generate_itemList }]
		/* empty */				{ }
	|	checker_or_generate_itemList		{ }
	;

checker_or_generate_itemList:	// IEEE: { checker_or_generate_itemList }
		checker_or_generate_item		{ }
	|	checker_or_generate_itemList checker_or_generate_item	{ }
	;

checker_or_generate_item:	// ==IEEE: checker_or_generate_item
		checker_or_generate_item_declaration	{ }
	|	initial_construct			{ }
	//			// IEEE: checker_always_construct
	|	yALWAYS stmt				{ }
	|	final_construct				{ }
	|	assertion_item				{ }
	|	checker_generate_item			{ }
	;

checker_or_generate_item_declaration:	// ==IEEE: checker_or_generate_item_declaration
		data_declaration			{ }
	|	yRAND data_declaration			{ }
	|	function_declaration			{ }
	|	assertion_item_declaration		{ }
	|	covergroup_declaration			{ }
	|	overload_declaration			{ }
	|	genvar_declaration			{ }
	|	clocking_declaration			{ }
	|	yDEFAULT yCLOCKING id/*clocking_identifier*/ ';'	{ }
	|	yDEFAULT yDISABLE yIFF expr/*expression_or_dist*/ ';'	{ }
	|	';'					{ }
	;

checker_generate_item:		// ==IEEE: checker_generate_item
	//			// Specialized for checker so need "c_" prefixes here
		c_loop_generate_construct		{ }
	|	c_conditional_generate_construct	{ }
	|	c_generate_region			{ }
	//
	|	elaboration_system_task			{ }
	;

checker_instantiation:
	//			// Only used for procedural_assertion_item's
	//			// Version in concurrent_assertion_item looks like etcInst
	//			// Thus instead of *_checker_port_connection we can use etcInst's cellpinList
		id/*checker_identifier*/ id '(' cellpinList ')' ';'	{ }
	;

//**********************************************************************
// Class

class_declaration:		// ==IEEE: part of class_declaration
	//			// The classExtendsE rule relys on classFront having the
	//			// new class scope correct via classFront
		classFront parameter_port_listE classExtendsE ';'
			class_itemListE yENDCLASS endLabelE
			{ PARSEP->endclassCb($<fl>6,$6);
			  PARSEP->symPopScope(VAstType::CLASS); }
	;

classFront:			// IEEE: part of class_declaration
		classVirtualE yCLASS lifetimeE idAny/*class_identifier*/
			{ PARSEP->symPushNew(VAstType::CLASS, $4);
			  PARSEP->classCb($<fl>1,$2,$4,$1); }
	;

classVirtualE<str>:
		/* empty */				{ $$=""; }
	|	yVIRTUAL__CLASS				{ $<fl>$=$<fl>1; $$=$1; }
	;

classExtendsE:			// IEEE: part of class_declaration
	//			// The classExtendsE rule relys on classFront having the
	//			// new class scope correct via classFront
		/* empty */				{ }
	|	yEXTENDS class_typeWithoutId		{ PARSEP->syms().import($<fl>1,$<str>2,$<scp>2,"*"); }
	|	yEXTENDS class_typeWithoutId '(' list_of_argumentsE ')'	{ PARSEP->syms().import($<fl>1,$<str>2,$<scp>2,"*"); }
	;

//=========
// Package scoping - to traverse the symbol table properly, the final identifer
// must be included in the rules below.
// Each of these must end with {symsPackageDone | symsClassDone}

ps_id_etc<str>:			// package_scope + general id
		package_scopeIdFollowsE id		{ $<fl>$=$<fl>1; $$=$1+$2; }
	;

ps_type<str>:			// IEEE: ps_parameter_identifier | ps_type_identifier
		package_scopeIdFollowsE yaID__aTYPE	{ $<fl>$=$<fl>1; $$=$1+$2; }
	;

ps_covergroup_identifier<str>:	// ==IEEE: ps_covergroup_identifier
		package_scopeIdFollowsE yaID__aCOVERGROUP	{ $<fl>$=$<fl>1; $$=$1+$2; }
	;

class_scope_type<str>:		// class_scope + type
		class_scopeIdFollows yaID__aTYPE	{ $<fl>$=$<fl>1; $$=$<str>1+$2; }
	;

class_scope_id<str_scp>:	// class_scope + id etc
		class_scopeIdFollows id			{ $<fl>$=$<fl>1; $<scp>$=$<scp>1; $<str>$=$<str>1+$<str>2; }
	;

//=== Below rules assume special scoping per above

class_typeWithoutId<str_scp>:	// class_type standalone without following id
	//			// and we thus don't need to resolve it in specified package
		package_scopeIdFollowsE class_typeOneList	{ $<fl>$=$<fl>2; $<scp>$=$<scp>2; $<str>$=$1+$<str>2; }
	;

class_scopeWithoutId<str_scp>:	// class_type standalone without following id
	//			// and we thus don't need to resolve it in specified package
		class_scopeIdFollows			{ $<fl>$=$<fl>1; $<scp>$=$<scp>1; $<str>$=$<str>1; PARSEP->symTableNextId(NULL); }
	;

class_scopeIdFollows<str_scp>:	// IEEE: class_scope
	//			// IEEE: "class_type yP_COLONCOLON"
	//			// IMPORTANT: The lexer will parse the following ID to be in the found package
	//			// But class_type:'::' conflicts with class_scope:'::' so expand here
		package_scopeIdFollowsE class_typeOneListColonIdFollows	{ $<fl>$=$<fl>2; $<scp>$=$<scp>2; $<str>$=$1+$<str>2; }
	;

class_typeOneListColonIdFollows<str_scp>: // IEEE: class_type ::
		class_typeOneList yP_COLONCOLON 	{ $<fl>$=$<fl>1; $<scp>$=$<scp>1; $<str>$=$<str>1+$<str>2; PARSEP->symTableNextId($<scp>1); }
	;

class_typeOneList<str_scp>:	// IEEE: class_type: "id [ parameter_value_assignment ]"
	//			// If you follow the rules down, class_type is really a list via ps_class_identifier
	//			// Must propagate scp up for next id
		class_typeOne					{ $<fl>$=$<fl>1; $<scp>$=$<scp>1; $<str>$=$<str>1; }
	|	class_typeOneListColonIdFollows class_typeOne	{ $<fl>$=$<fl>1; $<scp>$=$<scp>2; $<str>$=$<str>1+$<str>2; }
	;

class_typeOne<str_scp>:		// IEEE: class_type: "id [ parameter_value_assignment ]"
	//			// If you follow the rules down, class_type is really a list via ps_class_identifier
		yaID__aCLASS parameter_value_assignmentE
			{ $<fl>$=$<fl>1; $<scp>$=$<scp>1; $<str>$=$<str>1; }
	;

package_scopeIdFollowsE<str>:	// IEEE: [package_scope]
	//			// IMPORTANT: The lexer will parse the following ID to be in the found package
		/* empty */				{ $$=""; }
	|	package_scopeIdFollows			{ $<fl>$=$<fl>1; $$=$1; }
	;

package_scopeIdFollows<str>:	// IEEE: package_scope
	//			// IMPORTANT: The lexer will parse the following ID to be in the found package
	//			// class_qualifier := [ yLOCAL '::'  ] [ implicit_class_handle '.' | class_scope ]
	//			//vv mid rule action needed otherwise we might not have NextId in time to parse the id token
		yD_UNIT        { PARSEP->symTableNextId(PARSEP->syms().netlistSymp()); }
	/*cont*/	yP_COLONCOLON	{ $<fl>$=$<fl>1; $<str>$=$<str>1+$<str>3; }
	|	yaID__aPACKAGE { PARSEP->symTableNextId($<scp>1); }
	/*cont*/	yP_COLONCOLON	{ $<fl>$=$<fl>1; $<str>$=$<str>1+$<str>3; }
	|	yLOCAL__COLONCOLON { PARSEP->symTableNextId($<scp>1); }
	/*cont*/	yP_COLONCOLON	{ $<fl>$=$<fl>1; $<str>$=$<str>1+$<str>3; }
	;

//^^^=========

class_itemListE:
		/* empty */				{ }
	|	class_itemList				{ }
	;

class_itemList:
		class_item				{ }
	|	class_itemList class_item  		{ }
	;

class_item:			// ==IEEE: class_item
		class_property				{ }
	|	class_method				{ }
	|	class_constraint			{ }
	//
	|	class_declaration			{ }
	|	timeunits_declaration			{ }
	|	covergroup_declaration			{ }
	|	local_parameter_declaration ';'		{ } // 1800-2009
	|	parameter_declaration ';'		{ } // 1800-2009
	|	';'					{ }
	//
	|	error ';'				{ }
	;

class_method:			// ==IEEE: class_method
		memberQualResetListE task_declaration			{ }
	|	memberQualResetListE function_declaration		{ }
	|	yEXTERN memberQualResetListE method_prototype ';'	{ }
	//			// IEEE: "method_qualifierE class_constructor_declaration"
	//			// part of function_declaration
	|	yEXTERN memberQualResetListE class_constructor_prototype	{ }
	;

// IEEE: class_constructor_prototype
// See function_declaration

class_item_qualifier<str>:	// IEEE: class_item_qualifier minus ySTATIC
	//			// IMPORTANT: yPROTECTED | yLOCAL is in a lex rule
		yPROTECTED				{ $<fl>$=$<fl>1; $$=$1; }
	|	yLOCAL__ETC				{ $<fl>$=$<fl>1; $$=$1; }
	|	ySTATIC__ETC				{ $<fl>$=$<fl>1; $$=$1; }
	;

memberQualResetListE:		// Called from class_property for all qualifiers before yVAR
	//			// Also before method declarations, to prevent grammar conflict
	//			// Thus both types of qualifiers (method/property) are here
		/*empty*/				{ VARRESET(); VARDTYPE(""); }
	|	memberQualList				{ VARRESET(); VARDTYPE($1); }
	;

memberQualList<str>:
		memberQualOne				{ $<fl>$=$<fl>1; $$=$1; }
	|	memberQualList memberQualOne		{ $<fl>$=$<fl>1; $$=SPACED($1,$2); }
	;

memberQualOne<str>:			// IEEE: property_qualifier + method_qualifier
	//			// Part of method_qualifier and property_qualifier
		class_item_qualifier			{ $<fl>$=$<fl>1; $$=$1; }
	//			// Part of method_qualifier only
	|	yVIRTUAL__ETC				{ $<fl>$=$<fl>1; $$=$1; }
	//			// IMPORTANT: lexer looks for yPURE yVIRTUAL
	|	yPURE yVIRTUAL__ETC			{ $<fl>$=$<fl>1; $$=$1+" "+$2; }
	//			// Part of property_qualifier only
	|	random_qualifier			{ $<fl>$=$<fl>1; $$=$1; }
	//			// Part of lifetime, but here as ySTATIC can be in different positions
	|	yAUTOMATIC		 		{ $<fl>$=$<fl>1; $$=$1; }
	;

//**********************************************************************
// Constraints

class_constraint:		// ==IEEE: class_constraint
	//			// IEEE: constraint_declaration
		constraintStaticE yCONSTRAINT idAny constraint_block	{ }
	//			// IEEE: constraint_prototype + constraint_prototype_qualifier
	|	constraintStaticE yCONSTRAINT idAny ';'		{ }
	|	yEXTERN constraintStaticE yCONSTRAINT idAny ';'	{ }
	|	yPURE constraintStaticE yCONSTRAINT idAny ';'	{ }
	;

constraint_block:		// ==IEEE: constraint_block
		'{' constraint_block_itemList '}'	{ }
	;

constraint_block_itemList:	// IEEE: { constraint_block_item }
		constraint_block_item			{ }
	|	constraint_block_itemList constraint_block_item	{ }
	;

constraint_block_item:		// ==IEEE: constraint_block_item
		ySOLVE solve_before_list yBEFORE solve_before_list ';'	{ }
	|	constraint_expression			{ }
	;

solve_before_list:		// ==IEEE: solve_before_list
		solve_before_primary			{ }
	|	solve_before_list ',' solve_before_primary	{ }
	;

solve_before_primary:		// ==IEEE: solve_before_primary
	//			// exprScope more general than: [ implicit_class_handle '.' | class_scope ] hierarchical_identifier select
		exprScope				{ }
	;

constraint_expressionList<str>:	// ==IEEE: { constraint_expression }
		constraint_expression				{ $$=$1; }
	|	constraint_expressionList constraint_expression	{ $$=$1+" "+$2; }
	;

constraint_expression<str>:	// ==IEEE: constraint_expression
		expr/*expression_or_dist*/ ';'		{ $$=$1; }
	//			// IEEE: expr yP_MINUSGT constraint_set
	//			// Conflicts with expr:"expr yP_MINUSGT expr"; rule moved there
	//
	|	yIF '(' expr ')' constraint_set	%prec prLOWER_THAN_ELSE	{ $$=$1; }
	|	yIF '(' expr ')' constraint_set	yELSE constraint_set	{ $$=$1;}
	//			// IEEE says array_identifier here, but dotted accepted in VMM + 1800-2009
	|	yFOREACH '(' idClassForeach/*array_id[loop_variables]*/ ')' constraint_set	{ $$=$1; }
	;

constraint_set<str>:		// ==IEEE: constraint_set
		constraint_expression			{ $$=$1; }
	|	'{' constraint_expressionList '}'	{ $$=$1+$2+$3; }
	;

dist_list:			// ==IEEE: dist_list
		dist_item				{ }
	|	dist_list ',' dist_item			{ }
	;

dist_item:			// ==IEEE: dist_item + dist_weight
		value_range				{ }
	|	value_range yP_COLONEQ  expr		{ }
	|	value_range yP_COLONDIV expr		{ }
	;

extern_constraint_declaration:	// ==IEEE: extern_constraint_declaration
		constraintStaticE yCONSTRAINT class_scope_id constraint_block	{ }
	;

constraintStaticE:		// IEEE: part of extern_constraint_declaration
		/* empty */				{ }
	|	ySTATIC__CONSTRAINT			{ }
	;

//**********************************************************************
%%

int VParseGrammar::parse() {
    s_grammarp = this;
    return VParseBisonparse();
}
void VParseGrammar::debug(int level) {
    VParseBisondebug = level;
}
const char* VParseGrammar::tokenName(int token) {
#if YYDEBUG || YYERROR_VERBOSE
    if (token >= 255) {
	switch (token) {
	/*BISONPRE_TOKEN_NAMES*/
	default: return yytname[token-255];
	}
    } else {
	static char ch[2];  ch[0]=token; ch[1]='\0';
	return ch;
    }
#else
    return "";
#endif
}

//YACC = /kits/sources/bison-2.4.1/src/bison --report=lookahead
// --report=lookahead
// --report=itemset
// --graph
//
// Local Variables:
// compile-command: "cd .. ; make -j 8 && make test"
// End:
