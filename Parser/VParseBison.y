%{
/* $Id$
 ******************************************************************************
 * DESCRIPTION: SystemC bison parser
 *
 * This file is part of SystemC-Perl.
 *
 * Author: Wilson Snyder <wsnyder@wsnyder.org>
 *
 * Code available from: http://www.veripool.com/systemperl
 *
 ******************************************************************************
 *
 * Copyright 2001-2007 by Wilson Snyder.  This program is free software;
 * you can redistribute it and/or modify it under the terms of either the GNU
 * General Public License or the Perl Artistic License.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 *****************************************************************************/

#include <stdio.h>
#include <fstream>
#include <stack>
#include <vector>
#include <map>
#include <deque>
#include <assert.h>

#include "VParse.h"
#include "VParseGrammar.h"

#define YYERROR_VERBOSE 1
#define YYINITDEPTH 5000	// Large as the stack won't grow, since YYSTYPE_IS_TRIVIAL isn't defined
#define YYMAXDEPTH 5000

// See VParseGrammar.h for the C++ interface to this parser
// Include that instead of VParseBison.h

VParseGrammar*	VParseGrammar::s_grammarp = NULL;

//*************************************************************************

#define GRAMMARP VParseGrammar::staticGrammarp()
#define PARSEP VParseGrammar::staticParsep()

#define NEWSTRING(text) (string((text)))

#define VARRESET()	 { VARDECL(""); VARIO(""); VARSIGNED(""); VARRANGE(""); }
#define VARDECL(type)	 { GRAMMARP->m_varDecl = (type); }
#define VARIO(type)	 { GRAMMARP->m_varIO   = (type); }
#define VARSIGNED(value) { GRAMMARP->m_varSigned=(value); }
#define VARRANGE(range)	 { GRAMMARP->m_varRange=(range); }
#define VARDONE(fl,name,array,value) {\
	if (GRAMMARP->m_varIO!="")   PARSEP->signalCb((fl),GRAMMARP->m_varIO,  (name),GRAMMARP->m_varRange,array, GRAMMARP->m_varSigned, "",      GRAMMARP->m_inFTask); \
	if (GRAMMARP->m_varDecl!="") PARSEP->signalCb((fl),GRAMMARP->m_varDecl,(name),GRAMMARP->m_varRange,array, GRAMMARP->m_varSigned, (value), GRAMMARP->m_inFTask); \
}

#define INSTPREP(cellmod,cellparam) { GRAMMARP->pinNum(1); GRAMMARP->m_cellMod=(cellmod); GRAMMARP->m_cellParam=(cellparam); }

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
	PARSEP->paramPinCb(pinr.m_fl, pinr.m_name, pinr.m_conn, pinr.m_number);
	GRAMMARP->m_pinStack.pop_front();
    }
}

/* Yacc */
int  VParseBisonlex(VParseBisonYYSType* yylvalp) { return PARSEP->lexToBison(yylvalp); }

void VParseBisonerror(const char *s) { VParseGrammar::bisonError(s); }

%}

%pure_parser
%token_table

// Generic types used by Verilog::Parser
%token<str>		yaFLOATNUM	"FLOATING-POINT NUMBER"
%token<str>		yaID		"IDENTIFIER"
%token<str>		yaINTNUM	"INTEGER NUMBER"
%token<str>		yaTIMENUM	"TIME NUMBER"
%token<str>		yaSTRING	"STRING"
%token<str>		yaTIMINGSPEC	"TIMING SPEC ELEMENT"

%token<str>		ygenGATE	"GATE keyword"
%token<str>		ygenKEYWORD	"KEYWORD"
%token<str>		ygenNETTYPE	"NETTYPE keyword (tri0/wand/etc)"
%token<str>		ygenOPERATOR	"OPERATOR"
%token<str>		ygenSTRENGTH	"STRENGTH keyword (strong1/etc)"
%token<str>		ygenSYSCALL	"SYSCALL"

%token<str>		'!'
%token<str>		'#'
%token<str>		'('
%token<str>		')'
%token<str>		','
%token<str>		'.'
%token<str>		';'
%token<str>		'='
%token<str>		'@'
%token<str>		'['
%token<str>		']'
%token<str>		'~'

// Specific keywords
// yKEYWORD means match "keyword"
// Other cases are yXX_KEYWORD where XX makes it unique,
// for example yP_ for punctuation based operators.
%token<str>		yALWAYS		"always"
%token<str>		yAND		"and"
%token<str>		yASSERT		"assert"
%token<str>		yASSIGN		"assign"
%token<str>		yAUTOMATIC	"automatic"
%token<str>		yBEGIN		"begin"
%token<str>		yBUF		"buf"
%token<str>		yCASE		"case"
%token<str>		yCASEX		"casex"
%token<str>		yCASEZ		"casez"
%token<str>		yCLOCK		"clock"
%token<str>		yCOVER		"cover"
%token<str>		yDEASSIGN	"deassign"
%token<str>		yDEFAULT	"default"
%token<str>		yDEFPARAM	"defparam"
%token<str>		yDISABLE	"disable"
%token<str>		yDO		"do"
%token<str>		yELSE		"else"
%token<str>		yEND		"end"
%token<str>		yENDCASE	"endcase"
%token<str>		yENDFUNCTION	"endfunction"
%token<str>		yENDGENERATE	"endgenerate"
%token<str>		yENDMODULE	"endmodule"
%token<str>		yENDSPECIFY	"endspecify"
%token<str>		yENDTABLE	"endtable"
%token<str>		yENDTASK	"endtask"
%token<str>		yFINAL		"final"
%token<str>		yFOR		"for"
%token<str>		yFORCE		"force"
%token<str>		yFOREVER	"forever"
%token<str>		yFORK		"fork"
%token<str>		yFUNCTION	"function"
%token<str>		yGENERATE	"generate"
%token<str>		yGENVAR		"genvar"
%token<str>		yIF		"if"
%token<str>		yINITIAL	"initial"
%token<str>		yINOUT		"inout"
%token<str>		yINPUT		"input"
%token<str>		yINTEGER	"integer"
%token<str>		yJOIN		"join"
%token<str>		yLOCALPARAM	"localparam"
%token<str>		yMODULE		"module"
%token<str>		yNAND		"nand"
%token<str>		yNEGEDGE	"negedge"
%token<str>		yNOR		"nor"
%token<str>		yNOT		"not"
%token<str>		yOR		"or"
%token<str>		yOUTPUT		"output"
%token<str>		yPARAMETER	"parameter"
%token<str>		yPOSEDGE	"posedge"
%token<str>		yREAL		"real"
%token<str>		yREALTIME	"realtime"
%token<str>		yREG		"reg"
%token<str>		yRELEASE	"release"
%token<str>		yREPEAT		"repeat"
%token<str>		ySCALARED	"scalared"
%token<str>		ySIGNED		"signed"
%token<str>		ySPECIFY	"specify"
%token<str>		ySUPPLY0	"supply0"
%token<str>		ySUPPLY1	"supply1"
%token<str>		yTABLE		"table"
%token<str>		yTASK		"task"
%token<str>		yTIME		"time"
%token<str>		yTRI		"tri"
%token<str>		yUNSIGNED	"unsigned"
%token<str>		yVECTORED	"vectored"
%token<str>		yWAIT		"wait"
%token<str>		yWHILE		"while"
%token<str>		yWIRE		"wire"
%token<str>		yXNOR		"xnor"
%token<str>		yXOR		"xor"

%token<str>		yP_PARSTRENGTH	"(-for-strength"
%token<str>		yP_PLUSCOLON	"+:"
%token<str>		yP_MINUSCOLON	"-:"
%token<str>		yP_MINUSGT	"->"
%token<str>		yP_EQGT		"=>"
%token<str>		yP_ASTGT	"*>"
%token<str>		yP_PLUSEQGT	"+=>"
%token<str>		yP_PLUSASTGT	"+*>"
%token<str>		yP_MINUSEQGT	"-=>"
%token<str>		yP_MINUSASTGT	"-*>"
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


//********************
// Verilog op precedence
%left<str>	':'
%left<str>	'?'
%left<str>	yP_OROR
%left<str>	yP_ANDAND
%left<str>	'|' yP_NOR
%left<str>	'^'
%left<str>	yP_XNOR
%left<str>	'&' yP_NAND
%left<str>	yP_EQUAL yP_NOTEQUAL yP_CASEEQUAL yP_CASENOTEQUAL yP_WILDEQUAL yP_WILDNOTEQUAL
%left<str>	'>' '<' yP_GTE yP_LTE
%left<str>	yP_SLEFT yP_SRIGHT yP_SSRIGHT
%left<str>	'+' '-'
%left<str>	'*' '/' '%'
%left<str>	yP_POW
%left<str>	'{' '}'
%left<str>	prUNARYARITH
%left<str>	prREDUCTION
%left<str>	prNEGATION

%nonassoc prLOWER_THAN_ELSE
%nonassoc yELSE

// Types
%type<str>	anyrange
%type<str>	cateList
%type<str>	concIdList
%type<str>	constExpr
%type<str>	expr
%type<str>	exprList
%type<str>	exprNoStr
%type<str>	funcTypeE
%type<str>	funcRef
%type<str>	gateKwd
%type<str>	idArrayed
%type<str>	idDotted
%type<str>	instModName
%type<str>	instRangeE
%type<str>	portRangeE
%type<str>	portV2kSig
%type<str>	rangeList
%type<str>	rangeListE
%type<str>	sigAndAttr
%type<str>	sigId
%type<str>	strAsInt
%type<str>	varInout
%type<str>	varInput
%type<str>	varOutput
%type<str>	varRefBase
%type<str>	varRefDotBit
%type<str>	varTypeKwds

%start fileE

%%
//**********************************************************************
// Feedback to the Lexer
// Note we read a parenthesis ahead, so this may not change the lexer at the right point.

statePushVlg:	/* empty */			 	{ }
	;
statePop:	/* empty */			 	{ }
	;

//**********************************************************************
// Files

fileE:		/* empty */				{ }
	|	file					{ }
	;

file:		mod 					{ }
	|	file mod 				{ }
	;

//**********************************************************************
// Module headers

mod:		modHdr modParE modPortsE ';' modItemListE yENDMODULE endLabelE
			{ PARSEP->endmoduleCb($<fl>1,$6); }
	;

modHdr:		yMODULE	yaID				{ PARSEP->moduleCb($<fl>1,$1,$2,PARSEP->inCellDefine()); }
	;

modParE:	/* empty */				{ }
	|	'#' '(' ')'				{ }
	|	'#' '(' modParArgs ')'			{ }
	;

modParArgs:	modParDecl				{ }
	|	modParDecl ',' modParList		{ }
	;

modParList:	modParSecond				{ }
	|	modParList ',' modParSecond 		{ }
	;

// Called only after a comma in a v2k list, to allow parsing "parameter a,b, parameter x"
modParSecond:	modParDecl				{ }
	|	param					{ }
	;

modPortsE:	/* empty */					{ }
	|	'(' ')'						{ }
	|	'(' {GRAMMARP->pinNum(1);} portList ')'		{ }
	|	'(' {GRAMMARP->pinNum(1);} portV2kArgs ')'	{ }
	;

portList:	port					{ }
	|	portList ',' port	  		{ }
	;

port:		yaID portRangeE				{ PARSEP->portCb($<fl>1, $1); }
	;

portV2kArgs:	portV2kDecl				{ }
	|	portV2kDecl ',' portV2kList		{ }
	;

portV2kList:	portV2kSecond				{ }
	|	portV2kList ',' portV2kSecond		{ }
	;

// Called only after a comma in a v2k list, to allow parsing "input a,b"
portV2kSecond:	portV2kDecl				{ }
	|	portV2kSig				{ }
	;

portV2kSig:	sigAndAttr				{ $<fl>$=$<fl>1; PARSEP->portCb($<fl>1, $1); }
	;

//************************************************
// Variable Declarations

varDeclList:	varDecl					{ }
	|	varDecl varDeclList			{ }
	;

regsigList:	regsig  				{ }
	|	regsigList ',' regsig		       	{ }
	;

portV2kDecl:	varRESET varInput  varSignedE v2kNetDeclE regrangeE portV2kSig	{ }
	|	varRESET varInout  varSignedE v2kNetDeclE regrangeE portV2kSig	{ }
	|	varRESET varOutput varSignedE v2kVarDeclE regrangeE portV2kSig	{ }
	;

ioDecl:		varRESET varInput  varSignedE v2kVarDeclE regrangeE  sigList ';'	{ }
     	|	varRESET varInout  varSignedE v2kVarDeclE regrangeE  sigList ';'	{ }
     	|	varRESET varOutput varSignedE v2kVarDeclE regrangeE  sigList ';'	{ }
	;

varDecl:	varRESET varReg     varSignedE regrangeE  regsigList ';'	{ }
	|	varRESET varGParam  varSignedE regrangeE  paramList ';'		{ }
	|	varRESET varLParam  varSignedE regrangeE  paramList ';'		{ }
	|	varRESET varNet     strengthSpecE varSignedE delayrange netSigList ';'	{ }
	|	varRESET varGenVar  varSignedE                          regsigList ';'	{ }
	;

modParDecl:	varRESET varGParam  varSignedE regrangeE   param 	{ }
	;

varRESET:	/* empty */ 				{ VARRESET(); }
	;

varNet:		ySUPPLY0				{ VARDECL($1); }
	|	ySUPPLY1				{ VARDECL($1); }
	|	yWIRE 					{ VARDECL($1); }
	|	yTRI 					{ VARDECL($1); }
	|	ygenNETTYPE				{ VARDECL($1); }
	;
varGParam:	yPARAMETER				{ VARDECL($1); }
	;
varLParam:	yLOCALPARAM				{ VARDECL($1); }
	;
varGenVar:	yGENVAR					{ VARDECL($1); }
	;
varReg:		yREG					{ VARDECL($1); }
	|	varTypeKwds				{ VARDECL($1); }
	;
varInput:	yINPUT					{ VARIO($1); }
	;
varOutput:	yOUTPUT					{ VARIO($1); }
	;
varInout:	yINOUT					{ VARIO($1); }
	;

varTypeKwds:	yINTEGER				{ $<fl>$=$<fl>1; $$=$1; }
	|	yREAL					{ $<fl>$=$<fl>1; $$=$1; }
	|	yREALTIME				{ $<fl>$=$<fl>1; $$=$1; }
	|	yTIME					{ $<fl>$=$<fl>1; $$=$1; }
	;

varSignedE:	/*empty*/ 				{ }
	|	ySIGNED					{ VARSIGNED("signed"); }
	|	yUNSIGNED				{ VARSIGNED("unsigned"); }
	;

v2kNetDeclE:	/*empty*/ 				{ }
	|	varNet 					{ }
	;

v2kVarDeclE:	v2kNetDeclE 				{ }
	|	varReg 					{ }
	;

//************************************************
// Module Items

modItemListE:	/* empty */				{ }
	|	modItemList				{ }
	;

modItemList:	modItem					{ }
	|	modItemList modItem			{ }
	;

modItem:	modOrGenItem 				{ }
	|	yGENERATE genTopBlock yENDGENERATE	{ }
	|	ySPECIFY specifyJunkList yENDSPECIFY	{ }
	|	ySPECIFY yENDSPECIFY			{ }
	;

modOrGenItem:	yALWAYS stmtBlock			{ }
	|	yFINAL stmtBlock			{ }
	|	yINITIAL stmtBlock			{ }
	|	yASSIGN strengthSpecE delayE assignList ';'	{ }
	|	yDEFPARAM defpList ';'			{ }
	|	instDecl 				{ }
	|	taskDecl 				{ }
	|	funcDecl 				{ }
	|	ioDecl	 				{ }
	|	varDecl 				{ }
	|	tableDecl 				{ }

	|	error ';'				{ }
	;

//************************************************
// Generates

// Because genItemList includes variable declarations, we don't need beginNamed
genItemBlock:	genItem					{ }
	|	genItemBegin				{ }
	;

genTopBlock:	genItemList				{ }
	|	genItemBegin				{ }
	;

genItemBegin:	yBEGIN genItemList yEND			{ }
	|	yBEGIN yEND				{ }
	|	yBEGIN ':' yaID genItemList yEND endLabelE	{ }
	|	yBEGIN ':' yaID             yEND endLabelE	{ }
	;

genItemList:	genItem					{ }
	|	genItemList genItem			{ }
	;

genItem:	modOrGenItem 				{ }
	|	yCASE  '(' expr ')' genCaseListE yENDCASE	{ }
	|	yIF expr genItemBlock	%prec prLOWER_THAN_ELSE	{ }
	|	yIF expr genItemBlock yELSE genItemBlock	{ }
	|	yFOR '(' varRefBase '=' expr ';' expr ';' varRefBase '=' expr ')' genItemBlock
							{ }
	;

genCaseListE:	/* empty */				{ }
	|	genCaseList				{ }
	;

genCaseList:	caseCondList ':' genItemBlock		{ }
	|	yDEFAULT ':' genItemBlock		{ }
	|	yDEFAULT genItemBlock			{ }
	|	genCaseList caseCondList ':' genItemBlock	{ }
	|       genCaseList yDEFAULT genItemBlock		{ }
	|	genCaseList yDEFAULT ':' genItemBlock		{ }
	;

//************************************************
// Assignments and register declarations

assignList:	assignOne				{ }
	|	assignList ',' assignOne		{ }
	;

assignOne:	varRefDotBit '=' expr			{ }
	|	'{' concIdList '}' '=' expr		{ }
	;

// IEEE: delay_or_event_control
delayOrEvE:	/* empty */				{ }
	|	delay					{ } /* ignored */
	|	sensitivity				{ } /* ignored */
	|	yREPEAT '(' expr ')' delayOrEvE		{ } /* ignored */
	;

delayE:		/* empty */				{ }
	|	delay					{ } /* ignored */
	;

delay:		'#' dlyTerm				{ } /* ignored */
	|	'#' '(' dlyInParen ')'			{ } /* ignored */
	|	'#' '(' dlyInParen ',' dlyInParen ')'		{ } /* ignored */
	|	'#' '(' dlyInParen ',' dlyInParen ',' dlyInParen ')'	{ } /* ignored */
	|	'#' '(' dlyInParen ':' dlyInParen ':' dlyInParen ')'	{ } /* ignored */
	;

dlyTerm:	yaID 					{ }
	|	yaINTNUM 				{ }
	|	yaFLOATNUM 				{ }
	|	yaTIMENUM 				{ }
	;

dlyInParen:	expr 					{ }
	;

sigAndAttr:	sigId sigAttrListE			{ $<fl>$=$<fl>1; $$=$1; }
	;

netSigList:	netSig  				{ }
	|	netSigList ',' netSig		       	{ }
	;

netSig:		sigId sigAttrListE			{ }
	|	yaID  sigAttrListE '=' expr		{ VARDONE($<fl>1, $1, "", $4); }
	|	sigIdRange sigAttrListE			{ }
	;

sigIdRange:	yaID rangeList				{ $<fl>$=$<fl>1; VARDONE($<fl>1, $1, $2, ""); }
	;

regSigId:	yaID rangeListE				{ $<fl>$=$<fl>1; VARDONE($<fl>1, $1, $2, ""); }
	|	yaID rangeListE '=' constExpr		{ $<fl>$=$<fl>1; VARDONE($<fl>1, $1, $2, $4); }
	;

sigId:		yaID					{ $<fl>$=$<fl>1; VARDONE($<fl>1, $1, "", ""); }
	;

sigList:	sigAndAttr				{ }
	|	sigList ',' sigAndAttr			{ }
	;

regsig:		regSigId sigAttrListE			{}
	;

sigAttrListE:	/* empty */				{}
	;

rangeListE:	/* empty */    		               	{ $$ = ""; }
	|	rangeList 				{ $$ = $1; }
	;

rangeList:	anyrange				{ $$ = $1; }
        |	rangeList anyrange			{ $$ = $1+$2; }
	;

regrangeE:	/* empty */    		               	{ VARRANGE(""); }
	|	anyrange 				{ VARRANGE($1); }
	;

anyrange:	'[' constExpr ':' constExpr ']'		{ $$ = "["+$2+":"+$4+"]"; }
	;

delayrange:	regrangeE delayE 			{ }
	|	ySCALARED regrangeE delayE 		{ }
	|	yVECTORED regrangeE delayE		{ }
	;

portRangeE:	/* empty */	                   	{ $$ = ""; }
	|	'[' constExpr ']'              		{ $$ = "["+$2+"]"; }
	|	'[' constExpr ':' constExpr  ']'    	{ $$ = "["+$2+":"+$4+"]"; }
	;

//************************************************
// Parameters

param:		yaID sigAttrListE '=' expr		{ $<fl>$=$<fl>1; VARDONE($<fl>1, $1, "", $4); }
	;

paramList:	param					{ }
	|	paramList ',' param			{ }
	;

defpList:	defpOne					{ }
	|	defpList ',' defpOne			{ }
	;

defpOne:	varRefDotBit '=' expr 			{ }
	;

//************************************************
// Instances
// We don't know if its a gate or module instantiation
//   modname        [#(params)]  name  (pins) [, name ...]
//   gate (strong0) [#(delay)]  [name] (pins) [, (pins)...]

instDecl:	instModName {INSTPREP($1,1);} strengthSpecE instparamListE {INSTPREP($1,0);} instnameList ';' 	{ }

instModName:	yaID 					{ $<fl>$=$<fl>1; $$ = $1; }
	|	gateKwd			 		{ $<fl>$=$<fl>1; $$ = $1; }
	;

instparamListE:	/* empty */				{ }
	|	'#' '(' cellpinList ')'			{ }
	|	'#' dlyTerm				{ }
	;

instnameList:	instnameParen				{ }
	|	instnameList ',' instnameParen		{ }
	;

instnameParen:	instname cellpinList ')'		{ PARSEP->endcellCb($<fl>1,""); }
	;

instname:	yaID instRangeE '(' 			{ PARSEP->instantCb($<fl>1, GRAMMARP->m_cellMod, $1, $2); PINPARAMS(); }
	|	instRangeE '(' 				{ PARSEP->instantCb($<fl>2, GRAMMARP->m_cellMod, "", $1); PINPARAMS(); } // UDP
	;

instRangeE:	/* empty */				{ $$ = ""; }
	|	'[' constExpr ':' constExpr ']'		{ $$ = "["+$2+":"+$4+"]"; }
	;

cellpinList:	{ } cellpinItList			{ }
	;

cellpinItList:	cellpinItemE				{ }
	|	cellpinItList ',' cellpinItemE		{ }
	;

cellpinItemE:	/* empty: ',,' is legal */		{ GRAMMARP->pinNumInc(); }  /*PINDONE(yylval.fl,"",""); <- No, as then () implys a pin*/
	|	'.' '*'					{ PINDONE($<fl>1,"*","*");GRAMMARP->pinNumInc(); }
	|	'.' yaID				{ PINDONE($<fl>1,$2,$2);  GRAMMARP->pinNumInc(); }
	|	'.' yaID '(' ')'			{ PINDONE($<fl>1,$2,"");  GRAMMARP->pinNumInc(); }
	|	'.' yaID '(' expr ')'			{ PINDONE($<fl>1,$2,$4);  GRAMMARP->pinNumInc(); }
	|	expr					{ PINDONE($<fl>1,"",$1);  GRAMMARP->pinNumInc(); }
	;

//************************************************
// Sensitivity lists

//IEEE: event_control
sensitivity:	'@' '(' senList ')'			{ }
	|	'@' senitemVar				{ }
	|	'@' '(' '*' ')'				{ }
	|	'@' '*'					{ }  /* Verilog 2001 */
	;

//IEEE: event_expression - split over several
senList:	senitem					{ }
	|	senList yOR senitem			{ }
	|	senList ',' senitem			{ }	/* Verilog 2001 */
	;

senitem:	senitemEdge				{ }
	|	expr					{ }
	;

senitemVar:	varRefDotBit				{ }
	;

senitemEdge:	yPOSEDGE expr				{ }
	|	yNEGEDGE expr				{ }
	;

//************************************************
// Statements

stmtBlock:	stmt					{ }
	|	yBEGIN stmtList yEND			{ }
	|	yBEGIN yEND				{ }
	|	beginNamed stmtList yEND endLabelE	{ }
	|	beginNamed 	    yEND endLabelE	{ }
	|	yFORK stmtList	   yJOIN		{ }
	|	yFORK 		   yJOIN		{ }
	|	forkNamed stmtList yJOIN endLabelE	{ }
	|	forkNamed 	   yJOIN endLabelE	{ }
	;

beginNamed:	yBEGIN ':' yaID varDeclList		{ }
	|	yBEGIN ':' yaID 			{ }
	;

forkNamed:	yFORK ':' yaID varDeclList		{ }
	|	yFORK ':' yaID 				{ }
	;

stmtList:	stmtBlock				{ }
	|	stmtList stmtBlock			{ }
	;

assignLhs:	varRefDotBit				{ }
	|	'{' concIdList '}'			{ }
	;

stmt:		';'					{ }
	|	labeledStmt				{ }
	|	yaID ':' labeledStmt			{ }  /*S05 block creation rule*/

	|	assignLhs yP_LTE delayOrEvE expr ';'	{ }
	|	assignLhs '=' delayOrEvE expr ';'	{ }
	|	stateCaseForIf				{ }
	|	taskRef ';' 				{ }

	|	yFOREVER stmtBlock			{ }

	|	yP_MINUSGT expr ';' 			{ }  /* event trigger */
	|	ygenSYSCALL '(' ')' ';'			{ }
	|	ygenSYSCALL '(' exprList ')' ';'	{ }
	|	ygenSYSCALL ';'				{ }
	|	delay stmtBlock				{ }
	|	sensitivity stmtBlock			{ }
	|	yASSIGN expr '=' delayOrEvE expr ';'	{ }
	|	yDEASSIGN expr ';'			{ }
	|	yDISABLE expr ';'			{ }
	|	yFORCE expr '=' expr ';'		{ }
	|	yRELEASE expr ';'			{ }
	|	error ';'				{ }
	;

//************************************************
// Case/If

stateCaseForIf: caseStmt caseAttrE caseListE yENDCASE	{ }
	|	yIF expr stmtBlock	%prec prLOWER_THAN_ELSE	{ }
	|	yIF expr stmtBlock yELSE stmtBlock	{ }
	|	yFOR '(' assignLhs '=' expr ';' expr ';' assignLhs '=' expr ')' stmtBlock
							{ }
	|	yWHILE '(' expr ')' stmtBlock		{ }
	|	yDO stmtBlock yWHILE '(' expr ')'	{ }
	|	yREPEAT '(' expr ')' stmtBlock		{ }
	|	yWAIT '(' expr ')' stmtBlock		{ }
	;

caseStmt: 	yCASE  '(' expr ')' 			{ }
	|	yCASEX '(' expr ')' 			{ }
	|	yCASEZ '(' expr ')'	 		{ }
	;

caseAttrE: 	/*empty*/				{ }
	;

caseListE:	/* empty */				{ }
	|	caseList				{ }
	;

caseList:	caseCondList ':' stmtBlock		{ }
	|	yDEFAULT ':' stmtBlock			{ }
	|	yDEFAULT stmtBlock			{ }
	|	caseList caseCondList ':' stmtBlock	{ }
	|       caseList yDEFAULT stmtBlock		{ }
	|	caseList yDEFAULT ':' stmtBlock		{ }
	;

caseCondList:	expr 					{ }
	|	caseCondList ',' expr			{ }
	;

//************************************************
// Functions/tasks

taskRef:	idDotted		 		{ }
	|	idDotted '(' exprList ')'		{ }
	;

funcRef:	idDotted '(' exprList ')'		{ }
	;

taskDecl: 	yTASK taskAutoE taskId funcGuts yENDTASK endLabelE
			{ GRAMMARP->m_inFTask=false; PARSEP->endtaskfuncCb($<fl>1,$5); }
	;

funcDecl: 	yFUNCTION taskAutoE funcId funcGuts yENDFUNCTION endLabelE
		 	{ GRAMMARP->m_inFTask=false; PARSEP->endtaskfuncCb($<fl>1,$5); }
	;

taskAutoE:	/* empty */		 		{ }
	|	yAUTOMATIC		 		{ }
	;

taskId:		yaID 					{ GRAMMARP->m_inFTask=true; PARSEP->taskCb($<fl>1,"task",$1); }
	;

funcId: 	funcTypeE yaID				{ GRAMMARP->m_inFTask=true; PARSEP->functionCb($<fl>2,"function",$2,$1); }
	|	ySIGNED funcTypeE yaID			{ GRAMMARP->m_inFTask=true; PARSEP->functionCb($<fl>3,"function",$3,"signed "+$2); }
	;

funcGuts:	'(' {GRAMMARP->pinNum(1);} portV2kArgs ')' ';' funcBody	{ }
	|	';' funcBody				{ }
	;

funcBody:	funcVarList stmtBlock			{ }
	|	stmtBlock				{ }
 	;

funcTypeE:	/* empty */				{ $$ = ""; }
	|	varTypeKwds				{ $$ = $1; }
	|	'[' constExpr ':' constExpr ']'		{ $$ = "["+$2+":"+$4+"]"; }
	;

funcVarList:	funcVar					{ }
	|	funcVarList funcVar			{ }
	;

funcVar: 	ioDecl					{ }
	|	varDecl 				{ }
	;

//************************************************
// Expressions

constExpr:	expr					{ $<fl>$=$<fl>1; $$ = $1; }
	;

exprNoStr:	expr yP_OROR expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_ANDAND expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr '&' expr				{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr '|' expr				{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_NAND expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_NOR expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr '^' expr				{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_XNOR expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_EQUAL expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_NOTEQUAL expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_CASEEQUAL expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_CASENOTEQUAL expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_WILDEQUAL expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_WILDNOTEQUAL expr		{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr '>' expr				{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr '<' expr				{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_GTE expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_LTE expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_SLEFT expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_SRIGHT expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_SSRIGHT expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr '+' expr				{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr '-' expr				{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr '*' expr				{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr '/' expr				{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr '%' expr				{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }
	|	expr yP_POW expr			{ $<fl>$=$<fl>1; $$ = $1+$2+$3; }

	|	'-' expr	%prec prUNARYARITH	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	'+' expr	%prec prUNARYARITH	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	'&' expr	%prec prREDUCTION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	'|' expr	%prec prREDUCTION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	'^' expr	%prec prREDUCTION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	yP_XNOR expr	%prec prREDUCTION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	yP_NAND expr	%prec prREDUCTION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	yP_NOR expr	%prec prREDUCTION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	'!' expr	%prec prNEGATION	{ $<fl>$=$<fl>1; $$ = $1+$2; }
	|	'~' expr	%prec prNEGATION	{ $<fl>$=$<fl>1; $$ = $1+$2; }

	|	expr '?' expr ':' expr			{ $<fl>$=$<fl>1; $$ = $1+"?"+$3+":"+$5; }
	|	'(' expr ')'				{ $<fl>$=$<fl>1; $$ = "("+$2+")"; }
	|	'_' '(' statePushVlg expr statePop ')'	{ $<fl>$=$<fl>1; $$ = "_("+$4+")"; }	// Arbitrary Verilog inside PSL
	|	'{' cateList '}'			{ $<fl>$=$<fl>1; $$ = "{"+$2+"}"; }
	|	'{' constExpr '{' cateList '}' '}'	{ $<fl>$=$<fl>1; $$ = "{"+$2+"{"+$4+"}}"; }

	|	ygenSYSCALL				{ $<fl>$=$<fl>1; $$ = $1; }
	|	ygenSYSCALL '(' ')'			{ $<fl>$=$<fl>1; $$ = $1; }
	|	ygenSYSCALL '(' exprList ')'		{ $<fl>$=$<fl>1; $$ = $1+"("+$3+")"; }

	|	funcRef					{ $<fl>$=$<fl>1; $$ = $1; }

	|	yaINTNUM				{ $<fl>$=$<fl>1; $$ = $1; }
	|	yaFLOATNUM				{ $<fl>$=$<fl>1; $$ = $1; }
	|	yaTIMENUM				{ $<fl>$=$<fl>1; $$ = $1; }

	|	varRefDotBit	  			{ $<fl>$=$<fl>1; $$ = $1; }
	;

// Generic expressions
expr:		exprNoStr				{ $<fl>$=$<fl>1; $$ = $1; }
	|	strAsInt				{ $<fl>$=$<fl>1; $$ = $1; }
	;

cateList:	expr					{ $<fl>$=$<fl>1; $$ = $1; }
	|	cateList ',' expr			{ $<fl>$=$<fl>1; $$ = $1+","+$3; }
	;

exprList:	expr					{ $<fl>$=$<fl>1; $$ = $1; }
	|	exprList ',' expr			{ $<fl>$=$<fl>1; $$ = $1+","+$3; }
	|	exprList ','				{ $<fl>$=$<fl>1; $$ = $1+","; }   // Verilog::Parser only: ,, is ok
	;

//************************************************
// Gate declarations

// We can't tell between UDPs and modules as they aren't declared yet.
// For simplicty, assume everything is a module, perhaps nameless,
// and deal with it later.

gateKwd:	ygenGATE				{ $<fl>$=$<fl>1; INSTPREP($1,0); }
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
strength:	ygenSTRENGTH				{ }
	|	ySUPPLY0				{ }
	|	ySUPPLY1				{ }
	;

strengthSpecE:	/* empty */					{ }
	|	yP_PARSTRENGTH strength ')'			{ }
	|	yP_PARSTRENGTH strength ',' strength ')'	{ }
	;

//************************************************
// Tables

tableDecl:	yTABLE specifyJunkList yENDTABLE	{ }

//************************************************
// Specify

specifyJunkList:	specifyJunk 			{} /* ignored */
	|	specifyJunkList specifyJunk		{} /* ignored */
	;

specifyJunk:	dlyTerm 	{} /* ignored */
	|	';' {}
	|	'!' {}
	|	'&' {}
	|	'(' {}
	|	')' {}
	|	'*' {} | '/' {} | '%' {}
	|	'+' {} | '-' {}
	|	',' {}
	|	':' {}
	|	'$' {}
	|	'=' {}
	|	'>' {} | '<' {}
	|	'?' {}
	|	'^' {}
	|	'{' {} | '}' {}
	|	'[' {} | ']' {}
	|	'|' {}
	|	'~' {}

	|	yIF {}
	|	yNEGEDGE {}
	|	yPOSEDGE {}

	|	yaSTRING {}
	|	yaTIMINGSPEC {}
	|	ygenSYSCALL {}

	|	yP_ANDAND {} | yP_GTE {} | yP_LTE {}
	|	yP_EQUAL {} | yP_NOTEQUAL {}
	|	yP_CASEEQUAL {} | yP_CASENOTEQUAL {}
	|	yP_WILDEQUAL {} | yP_WILDNOTEQUAL {}
	|	yP_XNOR {} | yP_NOR {} | yP_NAND {}
	|	yP_OROR {}
	|	yP_SLEFT {} | yP_SRIGHT {} | yP_SSRIGHT {}
	|	yP_PLUSCOLON {} | yP_MINUSCOLON {}
	|	yP_POW {}
	|	yP_MINUSGT {}
	|	yP_EQGT {}	| yP_ASTGT {}
	|	yP_PLUSEQGT {}	| yP_PLUSASTGT {}
	|	yP_MINUSEQGT {} | yP_MINUSASTGT {}

	|	yP_PLUSEQ {}	| yP_MINUSEQ {}
	|	yP_TIMESEQ {}
	|	yP_DIVEQ {}	| yP_MODEQ {}
	|	yP_ANDEQ {}	| yP_OREQ {}
	|	yP_XOREQ {}
	|	yP_SLEFTEQ {}	| yP_SRIGHTEQ {} | yP_SSRIGHTEQ {}

	|	error {}
	;

//************************************************
// IDs

// VarRef to dotted, and/or arrayed, and/or bit-ranged variable
varRefDotBit:	idDotted				{ $<fl>$=$<fl>1; $$ = $1; }
	;

idDotted:	idArrayed 				{ $<fl>$=$<fl>1; $$ = $1; }
	|	idDotted '.' idArrayed	 		{ $<fl>$=$<fl>1; $$ = $1+"."+$3; }
	;

// Single component of dotted path, maybe [#].
// Due to lookahead constraints, we can't know if [:] or [+:] are valid (last dotted part),
// we'll assume so and cleanup later.
idArrayed:	yaID						{ $<fl>$=$<fl>1; $$ = $1; }
	|	idArrayed '[' expr ']'				{ $<fl>$=$<fl>1; $$ = $1+"["+$3+"]"; }
	|	idArrayed '[' constExpr ':' constExpr ']'	{ $<fl>$=$<fl>1; $$ = $1+"["+$3+":"+$5+"]"; }
	|	idArrayed '[' expr yP_PLUSCOLON  constExpr ']'	{ $<fl>$=$<fl>1; $$ = $1+"["+$3+"+:"+$5+"]"; }
	|	idArrayed '[' expr yP_MINUSCOLON constExpr ']'	{ $<fl>$=$<fl>1; $$ = $1+"["+$3+"-:"+$5+"]"; }
	;

// VarRef without any dots or vectorizaion
varRefBase:	yaID					{ $<fl>$=$<fl>1; $$ = $1; }
	;

strAsInt:	yaSTRING				{ $<fl>$=$<fl>1; $$ = $1; }
	;

concIdList:	varRefDotBit				{ $<fl>$=$<fl>1; $$ = $1; }
	|	concIdList ',' varRefDotBit		{ $<fl>$=$<fl>1; $$ = $1+","+$3; }
	;

endLabelE:	/* empty */				{ }
	|	':' yaID				{ }
	;

//************************************************
// Asserts

labeledStmt:	assertStmt				{ }
	;

assertStmt:	yASSERT '(' expr ')' stmtBlock %prec prLOWER_THAN_ELSE	{ }
	|	yASSERT '(' expr ')'           yELSE stmtBlock		{ }
	|	yASSERT '(' expr ')' stmtBlock yELSE stmtBlock		{ }
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
