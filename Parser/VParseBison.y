// -*- C++ -*-
//*****************************************************************************
// DESCRIPTION: SystemC bison parser
//
// This file is part of SystemC-Perl.
//
// Author: Wilson Snyder <wsnyder@wsnyder.org>
//
// Code available from: http://www.veripool.org/systemperl
//
//*****************************************************************************
//
// Copyright 2001-2009 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//****************************************************************************/

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
#define SPACED3(a,b,c)	(SPACED(SPACED(a,b),c))

#define VARRESET_LIST(decl)    { GRAMMARP->pinNum(1); VARRESET(); VARDECL(decl); }	// Start of pinlist
#define VARRESET_NONLIST(decl) { GRAMMARP->pinNum(0); VARRESET(); VARDECL(decl); }	// Not in a pinlist
#define VARRESET()	 { VARDECL(""); VARIO(""); VARNET(""); VARTYPE(""); }  // Start of one variable decl

// VARDECL("") indicates inside a port list or IO list and we shouldn't declare the variable
#define VARDECL(type)	 { GRAMMARP->m_varDecl = (type); }  // genvar, parameter, localparam
#define VARIO(type)	 { GRAMMARP->m_varIO   = (type); }  // input, output, inout, ref, const ref
#define VARNET(type)	 { GRAMMARP->m_varNet  = (type); }  // supply*,wire,tri
#define VARTYPE(type)	 { GRAMMARP->m_varType = (type); }  // "signed", "int", etc

#define INSTPREP(cellmod,cellparam) { GRAMMARP->pinNum(1); GRAMMARP->m_cellMod=(cellmod); GRAMMARP->m_cellParam=(cellparam); }

static void VARDONE(VFileLine* fl, const string& name, const string& array, const string& value) {
    if (GRAMMARP->m_varIO!="" && GRAMMARP->m_varDecl=="") GRAMMARP->m_varDecl="port";
    if (GRAMMARP->m_varDecl!="") {
	PARSEP->varCb(fl, GRAMMARP->m_varDecl, name, PARSEP->symObjofUpward(), GRAMMARP->m_varNet,
		      GRAMMARP->m_varType, array, value);
    }
    if (GRAMMARP->m_varIO!="" || GRAMMARP->pinNum()) {
	PARSEP->portCb(fl, name, PARSEP->symObjofUpward(),
		       GRAMMARP->m_varIO, GRAMMARP->m_varType, array, GRAMMARP->pinNum());
    }
    if (GRAMMARP->m_varType == "type") {
	PARSEP->symReinsert(VAstType::TYPE,name);
    }
}

static void VARDONETYPEDEF(VFileLine* fl, const string& name, const string& type, const string& array) {
    VARRESET(); VARDECL("typedef"); VARTYPE(type);
    VARDONE(fl,name,array,"");
    // TYPE shouldn't override a more specific node type, as often is forward reference
    PARSEP->symReinsert(VAstType::TYPE,name);
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

%}

%pure_parser
%token_table

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
%token<str>		yELSE		"else"
%token<str>		yEND		"end"
%token<str>		yENDCASE	"endcase"
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
%token<str>		yFUNCTION	"function"
%token<str>		yGENERATE	"generate"
%token<str>		yGENVAR		"genvar"
%token<str>		yIF		"if"
%token<str>		yIFF		"iff"
%token<str>		yIGNORE_BINS	"ignore_bins"
%token<str>		yILLEGAL_BINS	"illegal_bins"
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
%token<str>		yLOCAL		"local"
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
%token<str>		yRANDOMIZE	"randomize"
%token<str>		yRANDSEQUENCE	"randsequence"
%token<str>		yREAL		"real"
%token<str>		yREALTIME	"realtime"
%token<str>		yREF		"ref"
%token<str>		yREG		"reg"
%token<str>		yRELEASE	"release"
%token<str>		yREPEAT		"repeat"
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
%token<str>		ySTATIC__TF	"static-then-taskf"
%token<str>		ySTRING		"string"
%token<str>		ySTRUCT		"struct"
%token<str>		ySUPER		"super"
%token<str>		ySUPPLY0	"supply0"
%token<str>		ySUPPLY1	"supply1"
%token<str>		yTABLE		"table"
%token<str>		yTAGGED		"tagged"
%token<str>		yTASK		"task"
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
%token<str>		yUNSIGNED	"unsigned"
%token<str>		yVAR		"var"
%token<str>		yVECTORED	"vectored"
%token<str>		yVIRTUAL__CLASS	"virtual-then-class"
%token<str>		yVIRTUAL__ETC	"virtual"
%token<str>		yVIRTUAL__LEX	"virtual-in-lex"
%token<str>		yVIRTUAL__TF	"virtual-then-taskf"
%token<str>		yVOID		"void"
%token<str>		yWAIT		"wait"
%token<str>		yWAIT_ORDER	"wait_order"
%token<str>		yWAND		"wand"
%token<str>		yWHILE		"while"
%token<str>		yWILDCARD	"wildcard"
%token<str>		yWIRE		"wire"
%token<str>		yWITHIN		"within"
%token<str>		yWITH__BRA	"with-then-["
%token<str>		yWITH__ETC	"with"
%token<str>		yWITH__LEX	"with-in-lex"
%token<str>		yWITH__PAREN	"with-then-("
%token<str>		yWOR		"wor"
%token<str>		yXNOR		"xnor"
%token<str>		yXOR		"xor"

%token<str>		yD_ROOT		"$root"
%token<str>		yD_UNIT		"$unit"

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

%token<str>		yP_PLUSCOLON	"+:"
%token<str>		yP_MINUSCOLON	"-:"
%token<str>		yP_MINUSGT	"->"
%token<str>		yP_MINUSGTGT	"->>"
%token<str>		yP_EQGT		"=>"
%token<str>		yP_ASTGT	"*>"
%token<str>		yP_ANDANDAND	"&&&"
%token<str>		yP_POUNDPOUND	"##"
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
// Assumed yP_ORMINUSGT yP_OREQGT matches yOR
%left		yOR    yP_ORMINUSGT yP_OREQGT
%left		yAND
%left		yINTERSECT
%left		yWITHIN
%right		yTHROUGHOUT
%left		prPOUNDPOUND_MULTI
%left		yP_POUNDPOUND
%left		yP_BRASTAR yP_BRAEQ yP_BRAMINUSGT

%left		'{' '}'
//%nonassoc	'=' yP_PLUSEQ yP_MINUSEQ yP_TIMESEQ yP_DIVEQ yP_MODEQ yP_ANDEQ yP_OREQ yP_XOREQ yP_SLEFTEQ yP_SRIGHTEQ yP_SSRIGHTEQ yP_COLONEQ yP_COLONDIV yP_LTE
%right		yP_MINUSGT
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

%nonassoc prLOWER
%nonassoc prHIGHER

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
	|	interface_declaration			{ }
	|	program_declaration			{ }
	|	package_declaration			{ }
	|	package_item				{ }
	|	bind_directive				{ }
	//	unsupported	// IEEE: config_declaration
	|	error					{ }
	;

timeunits_declaration:		// ==IEEE: timeunits_declaration
		yTIMEUNIT       yaTIMENUM ';'		{ }
	| 	yTIMEPRECISION  yaTIMENUM ';'		{ }
	;

//**********************************************************************
// Packages

package_declaration:		// ==IEEE: package_declaration
		packageHdr package_itemListE yENDPACKAGE endLabelE
			{ PARSEP->endpackageCb($<fl>3,$3);
			  PARSEP->symPopScope(VAstType::PACKAGE); }
	;

packageHdr:
		yPACKAGE idAny ';'
			{ PARSEP->symPushNew(VAstType::PACKAGE, $2);
			  PARSEP->packageCb($<fl>1,$1, $2); }
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
	|	timeunits_declaration			{ }
	;

package_or_generate_item_declaration:	// ==IEEE: package_or_generate_item_declaration
		net_declaration				{ }
	|	data_declaration			{ }
	|	task_declaration			{ }
	|	function_declaration			{ }
	|	dpi_import_export			{ }
	|	extern_constraint_declaration		{ }
	|	class_declaration			{ }
	//			// class_constructor_declaration is part of function_declaration
	|	parameter_declaration ';'		{ }
	|	local_parameter_declaration		{ }
	|	covergroup_declaration			{ }
	|	overload_declaration			{ }
	|	concurrent_assertion_item_declaration	{ }
	|	';'					{ }
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

//**********************************************************************
// Module headers

module_declaration:		// ==IEEE: module_declaration
	//			// timeunits_declaration instead in module_item
	//			// IEEE: module_nonansi_header + module_ansi_header
		modFront parameter_port_listE portsStarE ';'
			module_itemListE yENDMODULE endLabelE
			{ PARSEP->endmoduleCb($<fl>6,$6);
			  PARSEP->symPopScope(VAstType::MODULE); }
	//
	|	yEXTERN modFront parameter_port_listE portsStarE ';'
			{ PARSEP->symPopScope(VAstType::MODULE); }
	;

modFront:
		yMODULE lifetimeE idAny
			{ PARSEP->symPushNew(VAstType::MODULE, $3);
			  PARSEP->moduleCb($<fl>1,$1,$3,false,PARSEP->inCellDefine()); }
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
	|	'(' ')'						{ }
	//			// .* expanded from module_declaration
	|	'(' yP_DOTSTAR ')'				{ }
	|	'(' {VARRESET_LIST("");} list_of_ports ')'	{ VARRESET_NONLIST(""); }
	;

list_of_ports:			// IEEE: list_of_ports + list_of_port_declarations
		port					{ }
	|	list_of_ports ',' port	 		{ }
	;

port:				// ==IEEE: port
	//			// Though not type for interfaces, we factor out the port direction and type
	//			// so we can simply handle it in one place
	//
	//			// IEEE: interface_port_header port_identifier { unpacked_dimension }
	//			// Expanded interface_port_header
	//			// We use instantCb here because the non-port form looks just like a module instantiation
		portDirNetE id/*interface*/                   id/*port*/ regArRangeE	{ VARTYPE($2); VARDONE($<fl>2, $3, $4, ""); PARSEP->instantCb($<fl>2, $2, $3, $4); GRAMMARP->pinNumInc(); }
	|	portDirNetE yINTERFACE                        id/*port*/ regArRangeE	{ VARTYPE($2); VARDONE($<fl>2, $3, $4, ""); GRAMMARP->pinNumInc(); }
	|	portDirNetE id/*interface*/ '.' id/*modport*/ id/*port*/ regArRangeE	{ VARTYPE($2); VARDONE($<fl>2, $5, $6, ""); PARSEP->instantCb($<fl>2, $2, $5, $6); GRAMMARP->pinNumInc(); }
	|	portDirNetE yINTERFACE      '.' id/*modport*/ id/*port*/ regArRangeE	{ VARTYPE($2); VARDONE($<fl>2, $5, $6, ""); GRAMMARP->pinNumInc(); }
	//
	//			// IEEE: ansi_port_declaration, with [port_direction] removed
	//			//   IEEE: [ net_port_header | interface_port_header ] port_identifier { unpacked_dimension }
	//			//   IEEE: [ net_port_header | variable_port_header ] '.' port_identifier '(' [ expression ] ')'
	//			//   IEEE: [ variable_port_header ] port_identifier { variable_dimension } [ '=' constant_expression ]
	//			//   Substitute net_port_header = [ port_direction ] net_port_type
	//			//   Substitute variable_port_header = [ port_direction ] variable_port_type
	//			//   Substitute net_port_type = [ net_type ] data_type_or_implicit
	//			//   Substitute variable_port_type = var_data_type
	//			//   Substitute var_data_type = data_type | yVAR data_type_or_implicit
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
	//			// variable_dimensionListE instead of regArRangeE to avoid conflicts
	//
	//			// Note implicit rules looks just line declaring additional followon port
	//			// No VARDECL("port") for implicit, as we don't want to declare variables for them
	|	portDirNetE data_type	       '.' portSig '(' portAssignExprE ')'	{ VARTYPE($2); VARDONE($<fl>4, $4, "", ""); GRAMMARP->pinNumInc(); }
	|	portDirNetE yVAR data_type     '.' portSig '(' portAssignExprE ')'	{ VARTYPE($3); VARDONE($<fl>5, $5, "", ""); GRAMMARP->pinNumInc(); }
	|	portDirNetE yVAR implicit_type '.' portSig '(' portAssignExprE ')'	{ VARTYPE($3); VARDONE($<fl>5, $5, "", ""); GRAMMARP->pinNumInc(); }
	|	portDirNetE signingE rangeList '.' portSig '(' portAssignExprE ')'	{ VARTYPE(SPACED($2,$3)); VARDONE($<fl>5, $5, "", ""); GRAMMARP->pinNumInc(); }
	|	portDirNetE /*implicit*/       '.' portSig '(' portAssignExprE ')'	{ /*VARTYPE-same*/ VARDONE($<fl>3, $3, "", ""); GRAMMARP->pinNumInc(); }
	//
	|	portDirNetE data_type          portSig variable_dimensionListE	{ VARTYPE($2); VARDONE($<fl>3, $3, $4, ""); GRAMMARP->pinNumInc(); }
	|	portDirNetE yVAR data_type     portSig variable_dimensionListE	{ VARTYPE($3); VARDONE($<fl>4, $4, $5, ""); GRAMMARP->pinNumInc(); }
	|	portDirNetE yVAR implicit_type portSig variable_dimensionListE	{ VARTYPE($3); VARDONE($<fl>4, $4, $5, ""); GRAMMARP->pinNumInc(); }
	|	portDirNetE signingE rangeList portSig variable_dimensionListE	{ VARTYPE(SPACED($2,$3)); VARDONE($<fl>4, $4, $5, ""); GRAMMARP->pinNumInc(); }
	|	portDirNetE /*implicit*/       portSig variable_dimensionListE	{ /*VARTYPE-same*/ VARDONE($<fl>2, $2, $3, ""); GRAMMARP->pinNumInc(); }
	//
	|	portDirNetE data_type          portSig variable_dimensionListE '=' constExpr	{ VARTYPE($2); VARDONE($<fl>3, $3, $4, $6); GRAMMARP->pinNumInc(); }
	|	portDirNetE yVAR data_type     portSig variable_dimensionListE '=' constExpr	{ VARTYPE($3); VARDONE($<fl>4, $4, $5, $7); GRAMMARP->pinNumInc(); }
	|	portDirNetE yVAR implicit_type portSig variable_dimensionListE '=' constExpr	{ VARTYPE($3); VARDONE($<fl>4, $4, $5, $7); GRAMMARP->pinNumInc(); }
	|	portDirNetE /*implicit*/       portSig variable_dimensionListE '=' constExpr	{ /*VARTYPE-same*/ VARDONE($<fl>2, $2, $3, $5); GRAMMARP->pinNumInc(); }
	;

portDirNetE:			// IEEE: part of port, optional net type and/or direction
		/* empty */				{ }
	//			// Per spec, if direction given default the nettype.
	//			// The higher level rule may override this VARTYPE with one later in the parse.
	|	port_direction				{ VARTYPE(""/*default_nettype*/); }
	|	port_direction net_type			{ VARTYPE(""/*default_nettype*/); } // net_type calls VARNET
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
		id/*port*/ sigAttrListE			{ $<fl>$=$<fl>1; $$=$1; }
	;

//**********************************************************************
// Interface headers

interface_declaration:		// IEEE: interface_declaration + interface_nonansi_header + interface_ansi_header:
	//			// timeunits_delcarationE is instead in interface_item
		intFront parameter_port_listE portsStarE ';'
			interface_itemListE yENDINTERFACE endLabelE
			{ PARSEP->endinterfaceCb($<fl>6, $6);
			  PARSEP->symPopScope(VAstType::INTERFACE); }
	|	yEXTERN	intFront parameter_port_listE portsStarE ';'	{ }
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
	//			// with module_or_generate_item's module_common_item
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
		task_declaration
	|	function_declaration
	|	class_declaration
	|	covergroup_declaration
	//			// class_constructor_declaration is part of function_declaration
	|	';'
	;

program_declaration:		// IEEE: program_declaration + program_nonansi_header + program_ansi_header:
	//			// timeunits_delcarationE is instead in program_item
		pgmFront parameter_port_listE portsStarE ';'
			program_itemListE yENDPROGRAM endLabelE
			{ PARSEP->endprogramCb($<fl>6,$6);
			  PARSEP->symPopScope(VAstType::PROGRAM); }
	|	yEXTERN	pgmFront parameter_port_listE portsStarE ';'
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
		id/*new modport*/ '(' modportPortsDeclList ')'		{ }
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
		id					{ }
	|	'.' id '(' ')'				{ }
	|	'.' id '(' expr ')'			{ }
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
		id/*genvar_identifier*/			{ VARRESET_NONLIST("genvar"); VARDONE($<fl>1, $1, "", ""); }
	;

local_parameter_declaration:	// IEEE: local_parameter_declaration
	//			// See notes in parameter_declaration
		local_parameter_declarationFront list_of_param_assignments ';'	{ }
	;

parameter_declaration:		// IEEE: parameter_declaration
	//			// IEEE: yPARAMETER yTYPE list_of_type_assignments ';'
	//			// Instead of list_of_type_assignments
	//			// we use list_of_param_assignments because for port handling
	//			// it already must accept types, so simpler to have code only one place
		parameter_declarationFront list_of_param_assignments	{ }
	;

local_parameter_declarationFront: // IEEE: local_parameter_declaration w/o assignment
		varLParam implicit_type 		{ VARTYPE($2); }
	|	varLParam data_type			{ VARTYPE($2); }
	|	varLParam yTYPE				{ VARTYPE($2); }
	;

parameter_declarationFront:	// IEEE: parameter_declaration w/o assignment
		varGParam implicit_type 		{ VARTYPE($2); }
	|	varGParam data_type			{ VARTYPE($2); }
	|	varGParam yTYPE				{ VARTYPE($2); }
	;

parameter_port_declarationFront: // IEEE: parameter_port_declaration w/o assignment
	//			// IEEE: parameter_declaration (minus assignment)
		parameter_declarationFront		{ }
	//
	|	data_type				{ VARTYPE($1); }
	|	yTYPE 					{ VARTYPE($1); }
	;

net_declaration:		// IEEE: net_declaration - excluding implict
		net_declarationFront netSigList ';'	{ }
	;

net_declarationFront:		// IEEE: beginning of net_declaration
		net_declRESET net_type   strengthSpecE signingE delayrange { VARTYPE(SPACED($4,$5));}
	;

net_declRESET:
		/* empty */ 				{ VARRESET_NONLIST("net"); }
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
varGParam:
		yPARAMETER				{ VARRESET_NONLIST($1); }
	;
varLParam:
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

port_directionDecl:		// IEEE: port_direction that starts a port_declaraiton
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
		port_directionDecl port_declNetE data_type          { VARTYPE($3); } list_of_variable_decl_assignments	{ }
	|	port_directionDecl port_declNetE yVAR data_type     { VARTYPE($4); } list_of_variable_decl_assignments	{ }
	|	port_directionDecl port_declNetE yVAR implicit_type { VARTYPE($4); } list_of_variable_decl_assignments	{ }
	|	port_directionDecl port_declNetE signingE rangeList { VARTYPE(SPACED($3,$4)); } list_of_variable_decl_assignments	{ }
	|	port_directionDecl port_declNetE signing	    { VARTYPE($3); } list_of_variable_decl_assignments	{ }
	|	port_directionDecl port_declNetE /*implicit*/       { VARTYPE("");/*default_nettype*/} list_of_variable_decl_assignments	{ }
	;

tf_port_declaration:		// ==IEEE: tf_port_declaration
	//			// Used inside function; followed by ';'
	//			// SIMILAR to port_declaration
	//
		port_directionDecl      data_type     { VARTYPE($2); }  list_of_tf_variable_identifiers ';'	{ }
	|	port_directionDecl      implicit_type { VARTYPE($2); }  list_of_tf_variable_identifiers ';'	{ }
	|	port_directionDecl yVAR data_type     { VARTYPE($3); }  list_of_tf_variable_identifiers ';'	{ }
	|	port_directionDecl yVAR implicit_type { VARTYPE($3); }  list_of_tf_variable_identifiers ';'	{ }
	;

// There's no point in subdividing the integer types into atom/vector
// because once we go through a typedef we can't tell them apart.
// Later parsing needs to determine if a range is appropriate or not.
integer_type<str>:		// ==IEEE: integer_type
	//			// IEEE: integer_atom_type
		yBYTE					{ $<fl>$=$<fl>1; $$=$1; }
	|	ySHORTINT				{ $<fl>$=$<fl>1; $$=$1; }
	|	yINT					{ $<fl>$=$<fl>1; $$=$1; }
	|	yLONGINT				{ $<fl>$=$<fl>1; $$=$1; }
	|	yINTEGER				{ $<fl>$=$<fl>1; $$=$1; }
	|	yTIME					{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: integer_vector_type
	|	yBIT					{ $<fl>$=$<fl>1; $$=$1; }
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
// Enums

casting_type<str>:		// IEEE: casting_type
	//			// IEEE: signing
		ySIGNED					{ $<fl>$=$<fl>1; $$=$1; }
	|	yUNSIGNED				{ $<fl>$=$<fl>1; $$=$1; }
	|	simple_type				{ $<fl>$=$<fl>1; $$=$1; }
	;

simple_type<str>:		// ==IEEE: simple_type
		integer_type				{ $<fl>$=$<fl>1; $$=$1; }
	|	non_integer_type			{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: ps_type_identifier
	//			// IEEE: ps_parameter_identifier (presumably a PARAMETER TYPE)
	|	ps_type					{ $<fl>$=$<fl>1; $$=$1; }
	//			// { generate_block_identifer ... } '.'
	//			// Need to determine if generate_block_identifier can be lex-detected
	;

data_type<str>:			// ==IEEE: data_type
	//			// This expansion also replicated elsewhere, IE data_type__AndID
		data_typeNoRef				{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: [ class_scope | package_scope ] type_identifier { packed_dimension }
	|	ps_type  packed_dimensionE		{ $<fl>$=$<fl>1; $$=$1+$2; }
	|	class_scope_type packed_dimensionE	{ $<fl>$=$<fl>1; $$=$1+$2; }
	//			// IEEE: class_type
	|	class_typeWithoutId			{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: ps_covergroup_identifier
	|	ps_covergroup_identifier		{ $<fl>$=$<fl>1; $$=$1; }
	;

data_typeNoRef<str>:		// ==IEEE: data_type, excluding class_type etc references
		integer_type signingE regArRangeE	{ $<fl>$=$<fl>1; $$=SPACED($1,SPACED($2,$3)); }
	|	non_integer_type			{ $<fl>$=$<fl>1; $$=$1; }
	|	ySTRUCT        packedSigningE '{' struct_union_memberList '}' packed_dimensionE	{ $<fl>$=$<fl>1; $$=$1; }
	|	yUNION taggedE packedSigningE '{' struct_union_memberList '}' packed_dimensionE	{ $<fl>$=$<fl>1; $$=$1; }
	|	enumDecl				{ $<fl>$=$<fl>1; $$=$1; }
	|	ySTRING					{ $<fl>$=$<fl>1; $$=$1; }
	|	yCHANDLE				{ $<fl>$=$<fl>1; $$=$1; }
	|	yEVENT					{ $<fl>$=$<fl>1; $$=$1; }
	|	yVIRTUAL__ETC yINTERFACE id/*interface*/	{ $<fl>$=$<fl>1; $$=SPACED($1,SPACED($2,$3)); }
	|	yVIRTUAL__ETC            id/*interface*/	{ $<fl>$=$<fl>1; $$=SPACED($1,$2); }
	|	type_reference				{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: class_scope: see data_type above
	//			// IEEE: class_type: see data_type above
	//			// IEEE: ps_covergroup: see data_type above
	;

// IEEE: struct_union - not needed, expanded in data_type

data_type_or_void<str>:		// ==IEEE: data_type_or_void
		data_type				{ $<fl>$=$<fl>1; $$=$1; }
	|	yVOID					{ $<fl>$=$<fl>1; $$=$1; }
	;

var_data_type:			// ==IEEE: var_data_type
		data_type				{ }
	|	yVAR data_type				{ }
	|	yVAR implicit_type			{ }
	;

type_reference<str>:		// ==IEEE: type_reference
		yTYPE '(' exprOrDataType ')'		{ $<fl>$=$<fl>1; $$="type("+$3+")"; }
	;

struct_union_memberList:	// IEEE: { struct_union_member }
		struct_union_member				{ }
	|	struct_union_memberList struct_union_member	{ }
	;

struct_union_member:		// ==IEEE: struct_union_member
		random_qualifierE data_type_or_void list_of_variable_decl_assignments ';'
	;

list_of_variable_decl_assignments:	// ==IEEE: list_of_variable_decl_assignments
		variable_decl_assignment			{ }
	|	list_of_variable_decl_assignments ',' variable_decl_assignment	{ }
	;

variable_decl_assignment:	// ==IEEE: variable_decl_assignment
		id sigAttrListE variable_dimensionListE
			{ VARDONE($<fl>1, $1, $3, ""); }
	|	id sigAttrListE variable_dimensionListE '=' variable_declExpr
			{ VARDONE($<fl>1, $1, $3, $5); }
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

tf_variable_identifier:		// IEEE: part of list_of_tf_variable_identifiers
		yaID__ETC sigAttrListE variable_dimensionListE
			{ VARDONE($<fl>1, $1, $3, ""); }
	|	yaID__ETC sigAttrListE variable_dimensionListE '=' expr
			{ VARDONE($<fl>1, $1, $3, $5); }
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
	//			// "'[' constExpr ']'" merged with associative_dimension
	|	'[' exprOrDataType ']'			{ $<fl>$=$<fl>1; $$="["+$2+"]"; }
	|	anyrange				{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: associative_dimension
	//			// '[' data_type ']' is above
	|	yP_BRASTAR ']'				{ $<fl>$=$<fl>1; $$="[*]"; }
	|	'[' '*' ']'				{ $<fl>$=$<fl>1; $$="[*]"; }
	//			// IEEE: queue_dimension
	//			// '[' '$' ']' -- $ is part of expr
	//			// '[' '$' ':' expr ']' -- anyrange:expr:$
	;

random_qualifierE:		// IEEE: random_qualifier + empty
		/*empty*/				{ }
	|	yRAND					{ }
	|	yRANDC					{ }
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
		yENUM enum_base_typeE '{' enum_nameList '}' { $$=$2; }
	;

enum_base_typeE<str>:	// IEEE: enum_base_type
		/* empty */				{ $$="enum"; }
	|	integer_type signingE regrangeE		{ $<fl>$=$<fl>1; $$=$1; }
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
		data_declarationVar			{ }
	|	type_declaration			{ }
	|	package_import_declaration		{ }
	//			// IEEE: virtual_interface_declaration
	//			// "yVIRTUAL yID yID" looks just like a data_declaration
	//			// Therefore the virtual_interface_declaration term isn't used
	;

data_declarationVar:		// IEEE: part of data_declaration (called elsewhere)
	//			// The first declaration has complications between assuming what's the type vs ID declaring
		data_declarationVarFront list_of_variable_decl_assignments ';'	{ }
	;

// NOTE implicit_type is expanded
data_declarationVarFront:	// IEEE: part of data_declaration
	//			// implicit_type expanded into /*empty*/ or "signingE rangeList"
		constE yVAR lifetimeE data_type	 { VARRESET(); VARDECL("var"); VARTYPE(SPACED($1,$4)); }
	|	constE yVAR lifetimeE		 { VARRESET(); VARDECL("var"); VARTYPE($1); }
	|	constE yVAR lifetimeE signingE rangeList { VARRESET(); VARDECL("var"); VARTYPE(SPACED($1,SPACED($4,$5))); }
	//
	//			// Expanded: "constE lifetimeE data_type"
	|	/**/		      data_type	{ VARRESET(); VARDECL("var"); VARTYPE($1); }
	|	/**/	    lifetime  data_type	{ VARRESET(); VARDECL("var"); VARTYPE($2); }
	|	yCONST__ETC lifetimeE data_type	{ VARRESET(); VARDECL("var"); VARTYPE(SPACED($1,$3)); }
	//			// = class_new is in variable_decl_assignment
	;

constE<str>:			// IEEE: part of data_declaration
		/* empty */				{ $$ = ""; }
	|	yCONST__ETC				{ $$ = $1; }
	;

implicit_type<str>:		// IEEE: part of *data_type_or_implicit
	//			// Also expanded in data_declaration
		/* empty */				{ $$ = ""; }
	|	signingE rangeList			{ $$ = SPACED($1,$2); }
	|	signing					{ $$ = $1; }
	;

assertion_variable_declaration: // IEEE: assertion_variable_declaration
	//			// IEEE: var_data_type expanded
		var_data_type      assertion_variable_declarationId ';'	{ }
	;

assertion_variable_declarationId: // IEEE: part of assertion_variable_declaration
		id					{ }
	|	assertion_variable_declarationId id	{ }
	;

type_declaration:		// ==IEEE: type_declaration
	//			// Use idAny, as we can redeclare a typedef on an existing typedef
		yTYPEDEF data_type idAny variable_dimensionListE ';'	{ VARDONETYPEDEF($<fl>1,$3,$2,$4); }
	|	yTYPEDEF id/*interface*/ '.' idAny/*type*/ idAny/*type*/ ';'	{ VARDONETYPEDEF($<fl>1,$5,$2+"."+$4,""); }
	//			// Combines into above "data_type id" rule
	|	yTYPEDEF id ';'				{ VARDONETYPEDEF($<fl>1,$2,"",""); }
	|	yTYPEDEF yENUM idAny ';'		{ PARSEP->symReinsert(VAstType::ENUM, $3); }
	|	yTYPEDEF ySTRUCT idAny ';'		{ PARSEP->symReinsert(VAstType::STRUCT, $3); }
	|	yTYPEDEF yUNION idAny ';'		{ PARSEP->symReinsert(VAstType::UNION, $3); }
	|	yTYPEDEF yCLASS idAny ';'		{ PARSEP->symReinsert(VAstType::CLASS, $3); }
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

generate_region:		// ==IEEE: generate_region
		yGENERATE genTopBlock yENDGENERATE	{ }
	;

module_or_generate_item:	// ==IEEE: module_or_generate_item
	//			// IEEE: parameter_override
		yDEFPARAM list_of_defparam_assignments ';'	{ }
	//			// IEEE: gate_instantiation + udp_instantiation + module_instantiation
	//			// not here, see etcInst in module_common_item
	//			// We joined udp & module definitions, so this goes here
	|	combinational_body			{ }
	|	module_common_item			{ }
	;

module_common_item:		// ==IEEE: module_common_item
		module_or_generate_item_declaration	{ }
	//			// IEEE: interface_instantiation
	//			// + IEEE: program_instantiation
	//			// + module_instantiation from module_or_generate_item
	|	etcInst					{ }
	|	concurrent_assertion_item		{ }
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
	|	yDEFAULT yCLOCKING id/*clocking_identifier*/ ';'	{ }
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

generate_block_or_null:		// IEEE: generate_block_or_null
	//	';'		// is included in
	//			// IEEE: generate_block
		genItem					{ }
	|	genItemBegin				{ }
	;

genTopBlock:
		genItemList				{ }
	|	genItemBegin				{ }
	;

genItemBegin:			// IEEE: part of generate_block
		yBEGIN genItemList yEND			{ }
	|	yBEGIN yEND				{ }
	|	id ':' yBEGIN genItemList yEND endLabelE	{ }
	|	id ':' yBEGIN             yEND endLabelE	{ }
	|	yBEGIN ':' id genItemList yEND endLabelE	{ }
	|	yBEGIN ':' id             yEND endLabelE	{ }
	;

genItemList:
		genItem					{ }
	|	genItemList genItem			{ }
	;

genItem:			// IEEE: module_or_interface_or_generate_item
		module_or_generate_item			{ }
	|	interface_or_generate_item		{ }
	;

conditional_generate_construct:	// ==IEEE: conditional_generate_construct
		yCASE  '(' expr ')' case_generate_itemListE yENDCASE	{ }
	|	yIF '(' expr ')' generate_block_or_null	%prec prLOWER_THAN_ELSE	{ }
	|	yIF '(' expr ')' generate_block_or_null yELSE generate_block_or_null	{ }
	;

loop_generate_construct:	// ==IEEE: loop_generate_construct
		yFOR '(' genvar_initialization ';' expr ';' genvar_iteration ')' generate_block_or_null
			{ }
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

case_generate_itemListE:	// IEEE: [{ case_generate_itemList }]
		/* empty */				{ }
	|	case_generate_itemList			{ }
	;

case_generate_itemList:		// IEEE: { case_generate_itemList }
		case_generate_item			{ }
	|	case_generate_itemList case_generate_item	{ }
	;

case_generate_item:		// ==IEEE: case_generate_item
		caseCondList ':' generate_block_or_null	{ }
	|	yDEFAULT ':' generate_block_or_null	{ }
	|	yDEFAULT generate_block_or_null		{ }
	;

//************************************************
// Assignments and register declarations

assignList:
		assignOne				{ }
	|	assignList ',' assignOne		{ }
	;

assignOne:
		variable_lvalue '=' expr		{ }
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

minTypMax:			// IEEE: mintypmax_expression and constant_mintypmax_expression
		expr 					{ }
	|	expr ':' expr ':' expr			{ }
	;

netSigList:			// IEEE: list_of_port_identifiers
		netSig  				{ }
	|	netSigList ',' netSig		       	{ }
	;

netSig:				// IEEE: net_decl_assignment -  one element from list_of_port_identifiers
		netId sigAttrListE			{ VARDONE($<fl>1, $1, "", ""); }
	|	netId sigAttrListE '=' expr		{ VARDONE($<fl>1, $1, "", $4); }
	|	id rangeList sigAttrListE		{ VARDONE($<fl>1, $1, $2, ""); }
	;

netId<str>:
		id/*net*/				{ $<fl>$=$<fl>1; $$=$1; }
	;

sigAttrListE:
		/* empty */				{ }
	;

rangeListE<str>:			// IEEE: packed_dimension + ...
		/* empty */				{ $$=""; }
	|	rangeList				{ $<fl>$=$<fl>1; $$ = $1; }
	;

rangeList<str>:			// IEEE: packed_dimension + ...
		anyrange				{ $<fl>$=$<fl>1; $$ = $1; }
	|	rangeList anyrange			{ $<fl>$=$<fl>1; $$ = $1+$2; }
	;

regrangeE<str>:
		/* empty */    		               	{ $$=""; }
	|	anyrange 				{ $<fl>$=$<fl>1; $$=$1; }
	;

regArRangeE<str>:
		/* empty */    		               	{ $$=""; }
	|	regArRangeList 				{ $<fl>$=$<fl>1; $$=$1; }
	;

// Complication here is "[#:#]" is a range, while "[#:#][#:#]" is an array and range.
regArRangeList<str>:
		anyrange				{ $<fl>$=$<fl>1; $$=$1; }
	|	regArRangeList anyrange			{ $<fl>$=$<fl>1; $$=$1+$2; }
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

packed_dimensionE<str>:		// IEEE: [ packed_dimension ]
		/* empty */				{ $$=""; }
	|	packed_dimension			{ $<fl>$=$<fl>1; $$=$1; }
	;

packed_dimension<str>:		// ==IEEE: packed_dimension
		anyrange				{ $<fl>$=$<fl>1; $$=$1; }
	|	'[' ']'					{ $$="[]"; }
	;

delayrange<str>:
		rangeListE delayE 			{ $<fl>$=$<fl>1; $$=$1; }
	|	ySCALARED rangeListE delayE 		{ $<fl>$=$<fl>1; $$=SPACED($1,$2); }
	|	yVECTORED rangeListE delayE		{ $<fl>$=$<fl>1; $$=SPACED($1,$2); }
	;

//************************************************
// Parameters

param_assignment:		// ==IEEE: param_assignment
	//			// IEEE: constant_param_expression
	//			// constant_param_expression: '$' is in expr
		id/*parameter*/ sigAttrListE '=' exprOrDataType
			{ $<fl>$=$<fl>1; VARDONE($<fl>1, $1, "", $4); }
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
		hierarchical_identifier/*parameter*/ '=' expr	{ }
	;

//************************************************
// Instances
// We don't know identifier types, so this matches all module,udp,etc instantiation
//   module_id      [#(params)]   name  (pins) [, name ...] ;	// module_instantiation
//   gate (strong0) [#(delay)]   [name] (pins) [, (pins)...] ;	// gate_instantiation
//   program_id     [#(params}]   name ;			// program_instantiation
//   interface_id   [#(params}]   name ;			// interface_instantiation

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
		/* empty: ',,' is legal */		{ GRAMMARP->pinNumInc(); }  /*PINDONE(yylval.fl,"",""); <- No, as then () implys a pin*/
	|	yP_DOTSTAR				{ PINDONE($<fl>1,"*","*");GRAMMARP->pinNumInc(); }
	|	'.' id					{ PINDONE($<fl>1,$2,$2);  GRAMMARP->pinNumInc(); }
	|	'.' id '(' ')'				{ PINDONE($<fl>1,$2,"");  GRAMMARP->pinNumInc(); }
	|	'.' id '(' expr ')'			{ PINDONE($<fl>1,$2,$4);  GRAMMARP->pinNumInc(); }
	//			// For parameters
	|	'.' id '(' data_type ')'		{ PINDONE($<fl>1,$2,$4);  GRAMMARP->pinNumInc(); }
	//			// For parameters
	|	data_type				{ PINDONE($<fl>1,"",$1);  GRAMMARP->pinNumInc(); }
	//
	|	expr					{ PINDONE($<fl>1,"",$1);  GRAMMARP->pinNumInc(); }
	;

//************************************************
// EventControl lists

event_control:			// ==IEEE: event_control
		'@' '(' event_expression ')'		{ }
	|	'@' '(' '*' ')'				{ }
	|	'@' '*'					{ }
	//			// IEEE: hierarchical_event_identifier
	|	'@' idClass/*event_id*/			{ }
	//			// IEEE: sequence_instance
	//			// sequence_instance without parens matches idClass above.
	//			// Ambiguity: "'@' sequence (-for-sequence" versus expr:delay_or_event_controlE "'@' id (-for-expr
	//			// For now we avoid this, as it's very unlikely someone would mix
	//			// 1995 delay with a sequence with parameters.
	//			// Alternatively split this out of event_control, and delay_or_event_controlE
	//			// and anywhere delay_or_event_controlE is called allow two expressions
	//|	'@' idClass '(' list_of_argumentsE ')'	{ }
	;

event_expression:		// IEEE: event_expression - split over several
		senitem					{ }
	|	event_expression yOR senitem		{ }
	|	event_expression ',' senitem		{ }	/* Verilog 2001 */
	;

senitem:			// IEEE: part of event_expression, non-'OR' ',' terms
		senitemEdge				{ }
	|	expr					{ }
	|	expr yIFF expr				{ }
	;

senitemEdge:			// IEEE: part of event_expression
		yPOSEDGE expr				{ }
	|	yPOSEDGE expr yIFF expr			{ }
	|	yNEGEDGE expr				{ }
	|	yNEGEDGE expr yIFF expr			{ }
	;

//************************************************
// Statements

stmtBlock:			// IEEE: statement + seq_block + par_block
		stmt					{ }
	;

seq_block:			// ==IEEE: seq_block
	//			// IEEE doesn't allow declarations in unnamed blocks, but several simulators do.
		yBEGIN blockDeclStmtList yEND			{ }
	|	yBEGIN /**/	yEND			{ }
	|	yBEGIN ':' seq_blockId blockDeclStmtList yEND endLabelE	{ PARSEP->symPopScope(VAstType::BLOCK); }
	|	yBEGIN ':' seq_blockId /**/		 yEND endLabelE	{ PARSEP->symPopScope(VAstType::BLOCK); }
	;

seq_blockId:			// IEEE: part of seq_block
		id/*block_identifier*/			{ PARSEP->symPushNew(VAstType::BLOCK,$1); }
	;

par_block:			// ==IEEE: par_block
		yFORK blockDeclStmtList	yJOIN			{ }
	|	yFORK /**/	yJOIN			{ }
	|	yFORK ':' par_blockId blockDeclStmtList	yJOIN endLabelE	{ PARSEP->symPopScope(VAstType::FORK); }
	|	yFORK ':' par_blockId /**/		yJOIN endLabelE	{ PARSEP->symPopScope(VAstType::FORK); }
	;

par_blockId:			// IEEE: part of par_block
		id/*block_identifier*/			{ PARSEP->symPushNew(VAstType::FORK,$1); }
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
	|	local_parameter_declaration 		{ }
	|	parameter_declaration ';' 		{ }
	|	overload_declaration 			{ }
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
	//			// IEEE: operator_assignment ';'
		foperator_assignment ';'		{ }
	//
	//		 	// IEEE: blocking_assignment
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
	|	caseStart caseAttrE case_itemListE yENDCASE	{ }
	|	caseStart caseAttrE yMATCHES case_patternListE yENDCASE	{ }
	|	caseStart caseAttrE yINSIDE  case_insideListE yENDCASE	{ }
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
	//			// Expr included here to resolve our not knowing what is a method call
	//			// Expr here must result in a subroutine_call
	|	function_subroutine_callNoMethod ';'	{ }
	|	fexpr '.' array_methodNoRoot ';'	{ }
	|	fexpr '.' function_subroutine_callNoMethod ';'	{ }
	|	fexprScope ';'				{ }
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
	|	yDO stmtBlock yWHILE '(' expr ')'	{ }
	|	yFOREACH '(' id/*array_identifier*/ '[' loop_variables ']' ')' stmt	{ }
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
	|	concurrent_assertion_statement		{ }
	|	immediate_assert_statement		{ }
	//
	//			// IEEE: clocking_drive ';'
	//			// Pattern w/o cycle_delay handled by nonblocking_assign above
	//			// clockvar_expression made to fexprLvalue to prevent reduce conflict
	//			// Note LTE in this context is highest precedence, so first on left wins
	|	cycle_delay fexprLvalue yP_LTE ';'	{ }
	|	fexprLvalue yP_LTE cycle_delay expr ';'	{ }
	//
	|	randsequence_statement			{ }
	//
	//			// IEEE: randcase_statement
	|	yRANDCASE case_itemList yENDCASE	{ }
	//
	|	expect_property_statement
	//
	|	error ';'				{ }
	;

operator_assignment:		// IEEE: operator_assignment ';'
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
	;

action_block:			// ==IEEE: action_block
		stmt	%prec prLOWER_THAN_ELSE		{ }
	|	stmt yELSE stmt				{ }
	;

caseStart:			// IEEE: part of case_statement
	 	unique_priorityE yCASE  '(' expr ')'	{ }
	|	unique_priorityE yCASEX '(' expr ')'	{ }
	|	unique_priorityE yCASEZ '(' expr ')'	{ }
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
		data_type id '=' expr			{ VARTYPE($1); }
	//			// IEEE: variable_assignment
	|	variable_lvalue '=' expr		{ }
	;

for_stepE:			// IEEE: for_step + empty
		for_step				{ }
	;

for_step:			// IEEE: for_step + empty
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

loop_variables:			// ==IEEE: loop_variables
		id					{ }
	|	loop_variables ',' id			{ }
	;

//************************************************
// Functions/tasks

funcRef<str>:			// IEEE: part of tf_call
	//			// package_scope/hierarchical_... is part of expr, so just need ID
	//			// id is-a sequence_identifier
	//			//      or function_identifier
	//			//      or property_identifier
		id '(' list_of_argumentsE ')'		{ $<fl>$=$<fl>1; $$=$1+"("+$3+")"; }
	|	package_scopeIdFollows id '(' list_of_argumentsE ')'	{ $<fl>$=$<fl>2; $$=$2+"("+$4+")"; }
	;

function_subroutine_callNoMethod<str>:	// IEEE: function_subroutine_call or property_instance
	//			// IEEE: tf_call
		funcRef					{ $<fl>$=$<fl>1; $$=$1; }
	|	system_f_call				{ $<fl>$=$<fl>1; $$=$1; }
	//			// IEEE: method_call requires a "." so is in expr
	|	randomize_call 				{ $<fl>$=$<fl>1; $$=$1; }
	;

system_f_call<str>:		// IEEE: system_tf_call (as func)
		ygenSYSCALL				{ $<fl>$=$<fl>1; $$ = $1; }
	|	ygenSYSCALL '(' ')'			{ $<fl>$=$<fl>1; $$ = $1; }
	//			// Allow list of data_type to support "x,,,y"
	|	ygenSYSCALL '(' exprOrDataTypeList ')'	{ $<fl>$=$<fl>1; $$ = $1+"("+$3+")"; }
	;

list_of_argumentsE<str>:	// IEEE: [list_of_arguments]
		/* empty */				{ $$=""; }
	|	list_of_arguments			{ $<fl>$=$<fl>1; $$=$1; }
	;

list_of_arguments<str>:		// ==IEEE: list_of_arguments - empty (handled above)
		argsDottedList				{ $<fl>$=$<fl>1; $$=$1; }
	|	argsExprList				{ $<fl>$=$<fl>1; $$=$1; }
	|	argsExprList ',' argsDottedList		{ $<fl>$=$<fl>1; $$=$1+","+$3; }
	;

task_declaration:		// ==IEEE: task_declaration
	 	yTASK lifetimeE taskId tfGuts yENDTASK endLabelE
			{ PARSEP->endtaskfuncCb($<fl>5,$5);
			  PARSEP->symPopScope(VAstType::TASK); }
	;

task_prototype:			// ==IEEE: task_prototype
		yTASK taskId '(' tf_port_listE ')'	{ PARSEP->symPopScope(VAstType::TASK); }
	;

function_declaration:		// IEEE: function_declaration + function_body_declaration
	 	yFUNCTION lifetimeE funcId tfGuts yENDFUNCTION endLabelE
			{ PARSEP->endtaskfuncCb($<fl>5,$5);
			  PARSEP->symPopScope(VAstType::FUNCTION); }
	;

function_prototype:		// IEEE: function_prototype
		yFUNCTION funcId '(' tf_port_listE ')'	{ PARSEP->symPopScope(VAstType::FUNCTION); }
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
		ySTATIC__ETC		 		{ }
	|	yAUTOMATIC		 		{ }
	;

taskId:
		tfIdScoped
			{ PARSEP->symPushNew(VAstType::TASK, $1);
			  PARSEP->taskCb($<fl>1,"task",$1); }
	;

funcId:				// IEEE: function_data_type_or_implicit + part of function_body_declaration
	//			// IEEE: function_data_type_or_implicit must be expanded here to prevent conflict
	//			// function_data_type expanded here to prevent conflicts with implicit_type:empty vs data_type:ID
		/**/			tfIdScoped
			{ PARSEP->symPushNew(VAstType::FUNCTION, $1);
			  PARSEP->functionCb($<fl>1,"function",$1,""); }
	|	signingE rangeList	tfIdScoped
			{ PARSEP->symPushNew(VAstType::FUNCTION, $3);
			  PARSEP->functionCb($<fl>3,"function",$3,SPACED($1,$2)); }
	|	signing			tfIdScoped
			{ PARSEP->symPushNew(VAstType::FUNCTION, $2);
			  PARSEP->functionCb($<fl>2,"function",$2,$1); }
	|	yVOID			tfIdScoped
			{ PARSEP->symPushNew(VAstType::FUNCTION, $2);
			  PARSEP->functionCb($<fl>2,"function",$2,$1); }
	|	data_type		tfIdScoped
			{ PARSEP->symPushNew(VAstType::FUNCTION, $2);
			  PARSEP->functionCb($<fl>2,"function",$2,$1); }
	//
	//			// IEEE: from class_constructor_declaration
	| 	yNEW__ETC
			{ PARSEP->symPushNew(VAstType::FUNCTION, "new");
			  PARSEP->functionCb($<fl>1,"function","new",""); }
	| 	yNEW__PAREN
			{ PARSEP->symPushNew(VAstType::FUNCTION, "new");
			  PARSEP->functionCb($<fl>1,"function","new",""); }
	|	class_scopeWithoutId yNEW__PAREN
			{ PARSEP->symPushNew(VAstType::FUNCTION, "new");
			  PARSEP->functionCb($<fl>2,"function","new",""); }
	;

tfIdScoped<str>:		// IEEE: part of function_body_declaration/task_body_declaration
	//			// IEEE: [ interface_identifier '.' | class_scope ] function_identifier
		id					{ $<fl>$=$<fl>1; $$ = $1; }
	|	id/*interface_identifier*/ '.' id	{ $<fl>$=$<fl>1; $$ = $1+"."+$2; }
	|	class_scope_id				{ $<fl>$=$<fl>1; $$ = $1; }
	;

tfGuts:
		'(' tf_port_listE ')' ';' tfBodyE	{ }
	|	';' tfBodyE				{ }
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

list_of_tf_variable_identifiers: // ==IEEE: list_of_tf_variable_identifiers
		tf_variable_identifier			{ }
	|	list_of_tf_variable_identifiers ',' tf_variable_identifier	{ }
	;

tf_port_listE:			// IEEE: tf_port_list + empty
	//			// Empty covered by tf_port_item
		{VARRESET_LIST(""); } tf_port_listList	{ VARRESET_NONLIST(""); }
	;

tf_port_listList:		// IEEE: part of tf_port_list
		tf_port_item				{ }
	|	tf_port_listList ',' tf_port_item	{ }
	;

tf_port_item:			// ==IEEE: tf_port_item
	//			// We split tf_port_item into the type and assignment as don't know what follows a comma
		/* empty */				{ }	// For example a ",," port
	|	tf_port_itemFront tf_port_itemAssignment { }
	|	tf_port_itemAssignment 			{ }
	;

tf_port_itemFront:		// IEEE: part of tf_port_item, which has the data type
		data_type				{ VARTYPE($1); }
	|	signingE rangeList			{ VARTYPE(SPACED($1,$2)); }
	|	signing					{ VARTYPE($1); }
	|	yVAR data_type				{ VARTYPE($2); }
	|	yVAR implicit_type			{ VARTYPE($2); }
	//
	|	tf_port_itemDir /*implicit*/		{ VARTYPE(""); /*default_nettype-see spec*/ }
	|	tf_port_itemDir data_type		{ VARTYPE($2); }
	|	tf_port_itemDir signingE rangeList	{ VARTYPE(SPACED($2,$3)); }
	|	tf_port_itemDir signing			{ VARTYPE($2); }
	|	tf_port_itemDir yVAR data_type		{ VARTYPE($3); }
	|	tf_port_itemDir yVAR implicit_type	{ VARTYPE($3); }
	;

tf_port_itemDir:		// IEEE: part of tf_port_item, direction
		port_direction				{ }
	;

tf_port_itemAssignment:		// IEEE: part of tf_port_item, which has assignment
		yaID__ETC variable_dimensionListE
			{ VARDONE($<fl>1, $1, $2, ""); }
	|	yaID__ETC variable_dimensionListE '=' expr
			{ VARDONE($<fl>1, $1, $2, $4); }
	;

//	method_call:		// ==IEEE: method_call + method_call_body
//				// IEEE: method_call_root '.' method_identifier [ '(' list_of_arguments ')' ]
//				//   "method_call_root '.' method_identifier" looks just like "expr '.' id"
//				//   "method_call_root '.' method_identifier (...)" looks just like "expr '.' tf_call"
//				// IEEE: built_in_method_call
//				//   method_call_root not needed, part of expr resolution
//				// What's left is below array_methodNoRoot

array_methodNoRoot<str>:	// ==IEEE: built_in_method_call without root
	//			//   method_call_root not needed, part of expr resolution
		array_method_nameNoId method_callWithE	{ $<fl>$=$<fl>1; $$=$1+$2; }
	|	array_method_nameNoId '(' list_of_argumentsE ')' method_callWithE	{ $<fl>$=$<fl>1; $$=$1+$2+$3+$4+$5; }
	//			//  "method_call_root '.' randomize_call" matches function_subroutine_call:randomize_call
	;

method_callWithE<str>:
		/* empty */				{ $$=""; }
	|	yWITH__PAREN '(' expr ')'		{ $<fl>$=$<fl>1; $$=$1+$2+$3+$4; }
	;

array_method_nameNoId<str>:	// IEEE: array_method_name minus method_identifier
		yUNIQUE					{ $<fl>$=$<fl>1; $$=$1; }
	|	yAND					{ $<fl>$=$<fl>1; $$=$1; }
	|	yOR					{ $<fl>$=$<fl>1; $$=$1; }
	|	yXOR					{ $<fl>$=$<fl>1; $$=$1; }
	;

randomize_call<str>:		// ==IEEE: randomize_call
		yRANDOMIZE		 randomize_callWithE	{ $<fl>$=$<fl>1; $$=$1; }
	|	yRANDOMIZE '(' ')'	 randomize_callWithE	{ $<fl>$=$<fl>1; $$=$1; }
	|	yRANDOMIZE '(' yNULL ')' randomize_callWithE	{ $<fl>$=$<fl>1; $$=$1; }
	|	yRANDOMIZE '(' identifier_list/*variable*/ ')' randomize_callWithE	{ $<fl>$=$<fl>1; $$=$1; }
	;

randomize_callWithE<str>:	// IEEE: part of randomize_call
		/* empty */		%prec prLOWER	{ $$=""; }
	|	constraint_block	%prec prHIGHER	{ $<fl>$=$<fl>1; $$=" with... "; }
	;

dpi_import_export:		// ==IEEE: dpi_import_export
		yIMPORT yaSTRING dpi_tf_import_propertyE dpi_importLabelE function_prototype ';'	{ }
	|	yIMPORT yaSTRING dpi_tf_import_propertyE dpi_importLabelE task_prototype ';'	{ }
	|	yEXPORT yaSTRING dpi_importLabelE yFUNCTION idAny ';'	{ }
	|	yEXPORT yaSTRING dpi_importLabelE yTASK     idAny ';'	{ }
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
		yBIND overload_operator yFUNCTION data_type id/*function_identifier*/
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
	|	~l~expr yP_SRIGHT ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_SLEFT ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	~l~expr yP_SSRIGHT ~r~expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
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
	|	~noStr__IGNORE~ strAsInt		{ $<fl>$=$<fl>1; $$ = $1; }
	//
	//			// IEEE: "... hierarchical_identifier select"  see below
	//
	//			// IEEE: empty_queue
	|	'{' '}'
	//
	//			// IEEE: concatenation/constant_concatenation
	//			// Part of exprOkLvalue below
	//
	//			// IEEE: multiple_concatencation/constant_multiple_concatenation
	|	'{' constExpr '{' cateList '}' '}'	{ $<fl>$=$<fl>1; $$ = "{"+$2+"{"+$4+"}}"; }
	//
	|	function_subroutine_callNoMethod	{ $$ = $1; }
	//			// method_call
	|	~l~expr '.' function_subroutine_callNoMethod	{ $<fl>$=$<fl>1; $$=$1+"."+$3; }
	//			// method_call:array_method requires a '.'
	|	~l~expr '.' array_methodNoRoot		{ $<fl>$=$<fl>1; $$ = $1+"."+$3; }
	//
	//			// IEEE: '(' mintypmax_expression ')'
	|	~noPar__IGNORE~ '(' expr ')'			{ $<fl>$=$<fl>1; $$ = "("+$2+")"; }
	|	~noPar__IGNORE~ '(' expr ':' expr ':' expr ')'	{ $<fl>$=$<fl>1; $$ = "("+$2+")"; }
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
	//			// IEEE: assignment_pattern_expression
	//			// IEEE: [ assignment_pattern_expression_type ] == [ ps_type_id /ps_paremeter_id]
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

exprScope<str>:			// scope and variable for use to inside an expression
	// 			// Here we've split method_call_root | implicit_class_handle | class_scope | package_scope
	//			// from the object being called and let expr's "." deal with resolving it.
	//
	//			// IEEE: [ implicit_class_handle . | class_scope | package_scope ] hierarchical_identifier select
	//			// Or method_call_body without parenthesis
	//			// See also varRefClassBit, which is the non-expr version of most of this
		yTHIS					{ $<fl>$=$<fl>1; $$ = $1; }
	|	idArrayed				{ $<fl>$=$<fl>1; $$ = $1; }
	|	package_scopeIdFollows idArrayed	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	~l~expr '.' idArrayed			{ $<fl>$=$<fl>1; $$ = $1+"."+$2; }
	//			// expr below must be a "yTHIS"
	|	~l~expr '.' ySUPER			{ $<fl>$=$<fl>1; $$ = $1+"."+$2; }
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

// Generic expressions
exprOrDataType<str>:		// expr | data_type: combined to prevent conflicts
		expr					{ $<fl>$=$<fl>1; $$ = $1; }
	//			// data_type includes id that overlaps expr, so special flavor
	|	data_type				{ $<fl>$=$<fl>1; $$ = $1; }
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

argsExprList<str>:		// IEEE: part of list_of_arguments
		expr					{ $<fl>$=$<fl>1; $$ = $1; }
	|	argsExprList ',' expr			{ $<fl>$=$<fl>1; $$ = $1+","+$3; }
	;

argsDottedList<str>:		// IEEE: part of list_of_arguments
		argsDotted				{ $<fl>$=$<fl>1; $$=$1; }
	|	argsDottedList ',' argsDotted		{ $<fl>$=$<fl>1; $$=$1+","+$3; }
	;

argsDotted<str>:		// IEEE: part of list_of_arguments
		'.' id '(' expr ')'			{ $<fl>$=$<fl>1; $$=$1+$2+$3+$4+$5; }
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
		ySPECPARAM junkToSemi ';'		{ }
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

variable_lvalue<str>:		// IEEE: variable_lvalue or net_lvalue
	//			// Note many variable_lvalue's must use exprOkLvalue when arbitrary expressions may also exist
		idClass					{ $<fl>$=$<fl>1; $$ = $1; }
	|	'{' variable_lvalueList '}'		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	//			// IEEE: [ assignment_pattern_expression_type ] assignment_pattern_variable_lvalue
	//			// We allow more assignment_pattern_expression_types then strictly required
	|	data_type yP_TICKBRA variable_lvalueList '}'	{ $<fl>$=$<fl>1; $$ = $1+" "+$2+$3+$4; }
	|	idClass   yP_TICKBRA variable_lvalueList '}'	{ $<fl>$=$<fl>1; $$ = $1+" "+$2+$3+$4; }
	|	/**/      yP_TICKBRA variable_lvalueList '}'	{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	streaming_concatenation			{ $<fl>$=$<fl>1; $$ = $1; }
	;

variable_lvalueList<str>:	// IEEE: part of variable_lvalue: variable_lvalue { ',' variable_lvalue }
		variable_lvalue				{ $<fl>$=$<fl>1; $$ = $1; }
	|	variable_lvalueList ',' variable_lvalue	{ $<fl>$=$<fl>1; $$ = $1+","+$3; }
	;

idClass<str>:			// Misc Ref to dotted, and/or arrayed, and/or bit-ranged variable
		idDotted				{ $<fl>$=$<fl>1; $$ = $1; }
	//			// IEEE: [ implicit_class_handle . | package_scope ] hierarchical_variable_identifier select
	|	yTHIS '.' idDotted			{ $<fl>$=$<fl>1; $$ = "this."+$3; }
	|	ySUPER '.' idDotted			{ $<fl>$=$<fl>1; $$ = "super."+$3; }
	|	yTHIS '.' ySUPER '.' idDotted		{ $<fl>$=$<fl>1; $$ = "this.super."+$3; }
	//			// Expanded: package_scope idDotted
	|	package_scopeIdFollows idDotted		{ $<fl>$=$<fl>1; $$ = $1+$2; }
	;

hierarchical_identifierList:	// IEEE: part of wait_statement
		hierarchical_identifier				{ }
	|	hierarchical_identifierList ',' hierarchical_identifier		{ }
	;

hierarchical_identifierBit:	// IEEE: "hierarchical_identifier bit_select"
		idDotted				{ }
	;

hierarchical_identifier:	// IEEE: hierarchical_identifier, including extra bit_select
	//			//	  +hierarchical_parameter_identifier
		idDotted				{ }
	;

idDotted<str>:
		yD_ROOT '.' idDottedMore		{ $<fl>$=$<fl>1; $$ = $1+"."+$3; }
	|	idDottedMore		 		{ $<fl>$=$<fl>1; $$ = $1; }
	;

idDottedMore<str>:
		idArrayed 				{ $<fl>$=$<fl>1; $$ = $1; }
	|	idDottedMore '.' idArrayed		{ $<fl>$=$<fl>1; $$ = $1+"."+$3; }
	;

// Single component of dotted path, maybe [#].
// Due to lookahead constraints, we can't know if [:] or [+:] are valid (last dotted part),
// we'll assume so and cleanup later.
// id below includes:
//	 enum_identifier
idArrayed<str>:			// IEEE: id + select
		id selectE				{ $<fl>$=$<fl>1; $$ = $1+$2; }
	;

selectE<str>:			// IEEE: select
		/*empty*/				{ $$ = ""; }
	|	selectList				{ $<fl>$=$<fl>1; $$ = $1; }
	;

selectList<str>:		// IEEE: part of select
		selectOne				{ $<fl>$=$<fl>1; $$ = $1; }
	|	selectList selectOne			{ $<fl>$=$<fl>1; $$ = $1+$2; }
	;

selectOne<str>:			// IEEE: part of select
	//			// IEEE: part_select_range/constant_part_select_range
		'[' expr ']'				{ $<fl>$=$<fl>1; $$ = "["+$2+"]"; }
	|	'[' constExpr ':' constExpr ']'		{ $<fl>$=$<fl>1; $$ = "["+$2+":"+$4+"]"; }
	//			// IEEE: indexed_range/constant_indexed_range
	|	'[' expr yP_PLUSCOLON  constExpr ']'	{ $<fl>$=$<fl>1; $$ = "["+$2+"+:"+$4+"]"; }
	|	'[' expr yP_MINUSCOLON constExpr ']'	{ $<fl>$=$<fl>1; $$ = "["+$2+"-:"+$4+"]"; }
	;

strAsInt<str>:
		yaSTRING				{ $<fl>$=$<fl>1; $$ = $1; }
	;

identifier_list<str>:		// ==IEEE: identifier_list
		id					{ $<fl>$=$<fl>1; $$ = $1; }
	|	identifier_list ',' id			{ $<fl>$=$<fl>1; $$ = $1+","+$3; }
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
	;

clockingFront:			// IEEE: part of class_declaration
		yCLOCKING				{ PARSEP->symPushNewAnon(VAstType::CLOCKING); }
	|	yCLOCKING idAny/*clocking_identifier*/	{ PARSEP->symPushNew(VAstType::CLOCKING,$1); }
	|	yDEFAULT yCLOCKING			{ PARSEP->symPushNewAnon(VAstType::CLOCKING); }
	|	yDEFAULT yCLOCKING idAny/*clocking_identifier*/	{ PARSEP->symPushNew(VAstType::CLOCKING,$1); }
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
	|	concurrent_assertion_item_declaration	{ }
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
		id/*signal_identifier*/			{ }
	|	id/*signal_identifier*/ '=' expr	{ }
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
	|	delay_control				{ }
	;

cycle_delay:			// ==IEEE: cycle_delay
		yP_POUNDPOUND yaINTNUM			{ }
	|	yP_POUNDPOUND id			{ }
	|	yP_POUNDPOUND '(' expr ')'		{ }
	;

//************************************************
// Asserts

expect_property_statement:	// ==IEEE: expect_property_statement
		yEXPECT '(' property_spec ')' action_block	{ }
	;

concurrent_assertion_item:	// IEEE: concurrent_assertion_item
		concurrent_assertion_statement		{ }
	|	id/*block_identifier*/ ':' concurrent_assertion_statement	{ }
	;

concurrent_assertion_statement:	// ==IEEE: concurrent_assertion_statement
	//			// IEEE: assert_property_statement
		yASSERT yPROPERTY '(' property_spec ')' action_block	{ }
	//			// IEEE: assume_property_statement
	|	yASSUME yPROPERTY '(' property_spec ')' ';'		{ }
	//			// IEEE: cover_property_statement
	|	yCOVER yPROPERTY '(' property_spec ')' stmtBlock	{ }
	;

concurrent_assertion_item_declaration:	// ==IEEE: concurrent_assertion_item_declaration
		property_declaration			{ }
	|	sequence_declaration			{ }
	;

property_declaration:		// ==IEEE: property_declaration
		property_declarationFront property_declarationBody
			yENDPROPERTY endLabelE
			{ PARSEP->symPopScope(VAstType::PROPERTY); }
	;

property_declarationFront:	// IEEE: part of property_declaration
		yPROPERTY property_declarationId ';'			{ }
	|	yPROPERTY property_declarationId '(' tf_port_listE ')' ';'	{ }
	;

property_declarationId:		// IEEE: part of property_declaration
		idAny/*property_identifier*/
			{ PARSEP->symPushNew(VAstType::PROPERTY,$1); }
	;

property_declarationBody:	// IEEE: part of property_declaration
		assertion_variable_declarationList property_spec ';'	{ }
	|	property_spec ';'			{ }
	;

assertion_variable_declarationList: // IEEE: part of assertion_variable_declaration
		assertion_variable_declaration		{ }
	|	assertion_variable_declarationList assertion_variable_declaration	{ }
	;

sequence_declaration:		// ==IEEE: sequence_declaration
		sequence_declarationHead sequence_declarationBody
			yENDSEQUENCE endLabelE
			{ PARSEP->symPopScope(VAstType::SEQUENCE); }
	;

sequence_declarationHead:	// IEEE: part of sequence_declaration
		ySEQUENCE sequence_declarationId ';'			{ }
	|	ySEQUENCE sequence_declarationId '(' tf_port_listE ')' ';'	{ }
	;

sequence_declarationId:		// IEEE: part of sequence_declaration
		idAny/*new_sequence*/
			{ PARSEP->symPushNew(VAstType::SEQUENCE,$1); }
	;

sequence_declarationBody:	// IEEE: part of property_declaration
		assertion_variable_declarationList sexpr ';'	{ }
	|	sexpr ';'				{ }
	;

property_spec:			// IEEE: property_spec
	//			// IEEE: [clocking_event ] [ yDISABLE yIFF '(' expression_or_dist ')' ] property_expr
	//			// matches property_spec: "clocking_event property_expr" so we put it there
	|	property_specDisable pexpr		{ }
	|	pexpr			 		{ }
	;

property_specDisable:		// IEEE: part of property_spec
		yDISABLE yIFF '(' expr ')'		{ }
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
	|	pexpr yOR pexpr				{ }
	|	pexpr yAND pexpr			{ }
	//
	//			// IEEE: "sequence_expr yP_ORMINUSGT pexpr"
	//			// Instead we use pexpr to prevent conflicts
	|	pexpr yP_ORMINUSGT pexpr		{ }
	|	pexpr yP_OREQGT pexpr			{ }
	//
	|	yIF '(' expr/*expression_or_dist*/ ')' pexpr %prec prLOWER_THAN_ELSE	{ }
	|	yIF '(' expr/*expression_or_dist*/ ')' pexpr yELSE pexpr	{ }
	//
	//			// IEEE: "property_instance"
	//			// Looks just like a function/method call
	//
	|	clocking_event pexpr             %prec prSEQ_CLOCKING	{ }
	//			// Include property_specDisable to match property_spec rule
	|	clocking_event property_specDisable expr %prec prSEQ_CLOCKING	{ }
	//
	//
	//============= sequence_expr rules copied for pexpr
	//			// ********* RULES COPIED FROM sequence_expr
	|	cycle_delay_range sexpr	 %prec yP_POUNDPOUND	{ }
	|	pexpr cycle_delay_range sexpr %prec prPOUNDPOUND_MULTI	{ }
	//
	//			// sexpr/*sexpression_or_dist*/	 --- Hardcoded below
	|	pexpr/*pexpression_or_dist*/ boolean_abbrev	{ }
	//
	//			// Instead above:  '(' pexpr ')'
	//			// Below pexpr's are really sequence_expr, but avoid conflict
	//			// "'(' sexpr ')' boolean_abbrev" matches "[sexpr:'(' expr ')'] boolean_abbrev" so we can simply drop it
	|	'(' pexpr ')'				{ }
	|	'(' pexpr ',' sequence_match_itemList ')'			{ }
	//
	|	pexpr yINTERSECT sexpr			{ }
	//			// Instead above:  sequence_expr yAND sequence_expr
	//			// Instead above:  sequence_expr yOR sequence_expr
	//
	|	yFIRST_MATCH '(' sexpr ')'		{ }
	|	yFIRST_MATCH '(' sexpr ',' sequence_match_itemList ')'	{ }
	|	pexpr/*pexpression_or_dist*/ yTHROUGHOUT sexpr		{ }
	//			// Below pexpr's are really sequence_expr, but avoid conflict
	|	pexpr yWITHIN sexpr			{ }
	//			// Instead above: clocking_event sequence_expr %prec prSEQ_CLOCKING	{ }
	//
	//============= expr rules copied for property_expr
	//			// ********* RULES COPIED FROM expr
	|	BISONPRE_COPY(expr,{s/~l~/p/g; s/~p~/p/g; s/~noPar__IGNORE~/yP_PAR__IGNORE/g; })	// {copied}
	;


sexpr<str>:			// ==IEEE: sequence_expr  (The name sexpr is important as regexps just add an "s" to expr.)
	//			// ********* RULES COPIED IN sequence_exprProp
	//			// For precedence, see IEEE 17.7.1
	//
	// 			// IEEE: "cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }"
	//			// IEEE: "sequence_expr cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }"
	//			// Both rules basically mean we can repeat sequences, so make it simpler:
		cycle_delay_range sexpr	 %prec yP_POUNDPOUND	{ }
	|	sexpr cycle_delay_range sexpr %prec prPOUNDPOUND_MULTI	{ }
	//
	//			// IEEE: expression_or_dist [ boolean_abbrev ]
	//			// Note expression_or_dist includes "expr"!
	//			// sexpr/*sexpression_or_dist*/	 --- Hardcoded below
	|	sexpr/*sexpression_or_dist*/ boolean_abbrev	{ }
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
	|	'(' sexpr ')'				{ }
	|	'(' sexpr ',' sequence_match_itemList ')'			{ }
	//
	|	sexpr yAND sexpr			{ }
	|	sexpr yINTERSECT sexpr			{ }
	|	sexpr yOR sexpr				{ }
	//
	|	yFIRST_MATCH '(' sexpr ')'		{ }
	|	yFIRST_MATCH '(' sexpr ',' sequence_match_itemList ')'	{ }
	|	sexpr/*sexpression_or_dist*/ yTHROUGHOUT sexpr		{ }
	|	sexpr yWITHIN sexpr			{ }
	|	clocking_event sexpr %prec prSEQ_CLOCKING	{ }
	//
	//============= expr rules copied for sequence_expr
	//			// ********* RULES COPIED FROM expr
	|	BISONPRE_COPY(expr,{s/~l~/s/g; s/~p~/s/g; s/~noPar__IGNORE~/yP_PAR__IGNORE/g; })	// {copied}
	;

cycle_delay_range:		// IEEE: ==cycle_delay_range
		yP_POUNDPOUND yaINTNUM			{ }
	|	yP_POUNDPOUND id			{ }
	|	yP_POUNDPOUND '(' constExpr ')'		{ }
	|	yP_POUNDPOUND '[' cycle_delay_const_range_expression ']'	{ }
	;

sequence_match_itemList:	// IEEE: [sequence_match_item] part of sequence_expr
		sequence_match_item			{ }
	|	sequence_match_itemList ',' sequence_match_item	{ }
	;

sequence_match_item:		// ==IEEE: sequence_match_item
	//			// IEEE says: operator_assignment			{ }
	//			// IEEE says: inc_or_dec_expression
	//			// IEEE says: subroutine_call
	//			// This is the same list as...
		for_step_assignment			{ }
	;

boolean_abbrev:			// ==IEEE: boolean_abbrev
	//			// IEEE: consecutive_repetition
		yP_BRASTAR const_or_range_expression ']'	{ }
	//			// IEEE: non_consecutive_repetition
	|	yP_BRAEQ const_or_range_expression ']'		{ }
	//			// IEEE: goto_repetition
	|	yP_BRAMINUSGT const_or_range_expression ']'	{ }
	;

const_or_range_expression:	// ==IEEE: const_or_range_expression
		constExpr				{ }
	|	cycle_delay_const_range_expression	{ }
	;

cycle_delay_const_range_expression:	// ==IEEE: cycle_delay_const_range_expression
	//				// Note '$' is part of constExpr
		constExpr ':' constExpr			{ }
	;

immediate_assert_statement:	// ==IEEE: immediate_assert_statement
		yASSERT '(' expr ')' action_block	{ }
	;

//************************************************
// Covergroup

covergroup_declaration:		// ==IEEE: covergroup_declaration
		covergroup_declarationHead coverage_spec_or_optionListE
			yENDGROUP endLabelE
			{ PARSEP->symPopScope(VAstType::COVERGROUP); }
	;

covergroup_declarationHead:	// IEEE: part of covergroup_declaration
		yCOVERGROUP covergroup_declarationId coverage_eventE ';'	{ }
	|	yCOVERGROUP covergroup_declarationId '(' tf_port_listE ')' coverage_eventE ';'	{ }
	;

covergroup_declarationId:	// IEEE: part of covergroup_declaration
		idAny					{ PARSEP->symPushNew(VAstType::COVERGROUP,$1); }
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
		id/*yOPTION | yTYPE_OPTION*/ '.' id/*member_identifier*/ '=' expr	{ }
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
		id/*cover_point_identifier or variable_identifier*/		{ }
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
		bins_keyword id/*bin_identifier*/ '=' select_expression iffE	{ }
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
	|	id/*cover_point_identifier*/ '.' id/*bins_identifier*/	{ }
	;

coverage_eventE:		// IEEE: [ coverage_event ]
		/* empty */				{ }
	|	clocking_event				{ }
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
	|	idClass/*ps_identifier*/		{ }
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
// Class

class_declaration:		// ==IEEE: part of class_declaration
		classFront parameter_port_listE classExtendsE ';'
			class_itemListE yENDCLASS endLabelE
			{ PARSEP->symPopScope(VAstType::CLASS); }
	;

classFront:			// IEEE: part of class_declaration
		classVirtualE yCLASS lifetimeE idAny/*class_identifier*/
			{ PARSEP->symPushNew(VAstType::CLASS, $4); }
	;

classVirtualE:
		/* empty */				{ }
	|	yVIRTUAL__CLASS				{ }
	;

classExtendsE:			// IEEE: part of class_declaration
		/* empty */				{ }
	|	yEXTENDS class_typeWithoutId		{ }
	|	yEXTENDS class_typeWithoutId '(' list_of_argumentsE ')'	{ }
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
		package_scopeIdFollowsE yaID__aCOVERGROUP	{ $<fl>$=$<fl>1; $$=$1; }
	;

class_scope_type<str>:		// class_scope + type
		class_scopeIdFollows yaID__aTYPE	{ $<fl>$=$<fl>1; $$=$1+$2; }
	;

class_scope_id<str>:		// class_scope + id etc
		class_scopeIdFollows id			{ $<fl>$=$<fl>1; $$=$1+$2; }
	;

//=== Below rules assume special scoping per above

class_typeWithoutId<str>:	// class_type standalone without following id
	//			// and we thus don't need to resolve it in specified package
		package_scopeIdFollowsE class_typeOneList	{ $<fl>$=$<fl>2; $$=$1+$<str>2; }
	;

class_scopeWithoutId<str>:	// class_type standalone without following id
	//			// and we thus don't need to resolve it in specified package
		class_scopeIdFollows			{ $<fl>$=$<fl>1; $$=$1; PARSEP->symTableNextId(NULL); }
	;

class_scopeIdFollows<str>:	// IEEE: class_scope
	//			// IEEE: "class_type yP_COLONCOLON"
	//			// IMPORTANT: The lexer will parse the following ID to be in the found package
	//			// But class_type:'::' conflicts with class_scope:'::' so expand here
		package_scopeIdFollowsE class_typeOneListColonIdFollows	{ $<fl>$=$<fl>2; $$=$1+$<str>2; }
	;

class_typeOneListColonIdFollows<str_entp>: // IEEE: class_type ::
		class_typeOneList yP_COLONCOLON 	{ $<fl>$=$<fl>1; $<str>$=$<str>1+$<str>2; $<entp>$=$<entp>1; PARSEP->symTableNextId($<entp>1); }
	;

class_typeOneList<str_entp>: // IEEE: class_type: "id [ parameter_value_assignment ]"
	//			// If you follow the rules down, class_type is really a list via ps_class_identifier
	//			// Must propagate entp up for next id
		class_typeOne				{ $<fl>$=$<fl>1; $<str>$=$<str>1; $<entp>$=$<entp>1; }
	|	class_typeOneListColonIdFollows class_typeOne	{ $<fl>$=$<fl>1; $<str>$=$<str>1+$<str>2; $<entp>$=$<entp>2; }
	;

class_typeOne<str_entp>:	// IEEE: class_type: "id [ parameter_value_assignment ]"
	//			// If you follow the rules down, class_type is really a list via ps_class_identifier
		yaID__aCLASS parameter_value_assignmentE
			{ $<fl>$=$<fl>1; $<str>$=$<str>1; $<entp>$=$<entp>1; }
	;

package_scopeIdFollowsE<str>:	// IEEE: [package_scope]
	//			// IMPORTANT: The lexer will parse the following ID to be in the found package
		/* empty */				{ $$=""; }
	|	package_scopeIdFollows			{ $<fl>$=$<fl>1; $$=$1; }
	;

package_scopeIdFollows<str>:	// IEEE: package_scope
	//			// IMPORTANT: The lexer will parse the following ID to be in the found package
	//			//vv mid rule action needed otherwise we might not have NextId in time to parse the id token
		yD_UNIT        { PARSEP->symTableNextId(PARSEP->syms().netlistSymp()); } yP_COLONCOLON	{ $<fl>$=$<fl>1; $<str>$=$<str>1+$<str>3; }
	|	yaID__aPACKAGE { PARSEP->symTableNextId($<entp>1); }			 yP_COLONCOLON	{ $<fl>$=$<fl>1; $<str>$=$<str>1+$<str>3; }
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
	|	';'					{ }
	;

class_property:			// ==IEEE: class_property
	//			// property_qualifier == random_qualifier
	//			// data_declaration includes [yCONST] [ySTATIC|yAUTOMATIC] var
		random_qualifierE data_declaration	{ }
	//			// yCONST {no-qualifier} data_type id" is part of data_declaration
	//			// yCONST ySTATIC        data_type id" is part of data_declaration
	|	yCONST__LOCAL class_item_qualifierNoStatic data_type id ';'		{ }
	|	yCONST__LOCAL class_item_qualifierNoStatic data_type id '=' constExpr ';'	{ }
	;

class_method:			// ==IEEE: class_method
		method_qualifierE task_declaration			{ }
	|	method_qualifierE function_declaration			{ }
	|	yEXTERN method_qualifierE method_prototype ';'		{ }
	//			// IEEE: "method_qualifierE class_constructor_declaration"		{ }
	//			// IEEE: "yEXTERN method_qualifierE class_constructor_prototype"
	//			// Both part of function_declaration
	;

// IEEE: class_constructor_prototype
// See function_declaration

class_item_qualifierNoStatic:	// IEEE: class_item_qualifier minus ySTATIC
	//			// IMPORTANT: yPROTECTED | yLOCAL is in a lex rule
		yPROTECTED				{ }
	|	yLOCAL					{ }
	;

method_qualifierE:
		/* empty */				{ }
	|	yVIRTUAL__TF				{ }
	//			// IEEE: class_item_qualifier
	|	ySTATIC__TF				{ }
	|	yPROTECTED				{ }
	|	yLOCAL					{ }
	;

//**********************************************************************
// Constraints

class_constraint:		// ==IEEE: class_constraint
	//			// IEEE: constraint_declaration
		constraintStaticE yCONSTRAINT idAny constraint_block	{ }
	//			// IEEE: constraint_prototype
	|	constraintStaticE yCONSTRAINT idAny ';'	{ }
	;

constraint_block:		// ==IEEE: constraint_block
		'{' constraint_block_itemList '}'	{ }
	;

constraint_block_itemList:	// IEEE: { constraint_block_item }
		constraint_block_item			{ }
	|	constraint_block_itemList constraint_block_item	{ }
	;

constraint_block_item:		// ==IEEE: constraint_block_item
		ySOLVE identifier_list yBEFORE identifier_list ';'	{ }
	|	constraint_expression			{ }
	;

constraint_expressionList:	// ==IEEE: { constraint_expression }
		constraint_expression				{ }
	|	constraint_expressionList constraint_expression	{ }
	;

constraint_expression:		// ==IEEE: constraint_expression
		expr/*expression_or_dist*/ ';'			{ }
	|	expr yP_MINUSGT constraint_set		{ }
	|	yIF '(' expr ')' constraint_set	%prec prLOWER_THAN_ELSE	{ }
	|	yIF '(' expr ')' constraint_set	yELSE constraint_set	{ }
	|	yFOREACH '(' id/*array_identifier*/ '[' loop_variables ']' ')' constraint_set	{ }
	;

constraint_set:			// ==IEEE: constraint_set
		constraint_expression			{ }
	|	'{' constraint_expressionList '}'	{ }
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
    if (token >= 255)
	return yytname[token-255];
    else {
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
