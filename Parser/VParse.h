// -*- C++ -*-
//*************************************************************************
//
// Copyright 2000-2011 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
/// \file
/// \brief Verilog::Parse: Parses verilog code
///
/// Authors: Wilson Snyder
///
/// Code available from: http://www.veripool.org/verilog-perl
///
//*************************************************************************

#ifndef _VPREPROC_H_
#define _VPREPROC_H_ 1

#include <string>
#include <map>
#include <set>
#include <deque>
#include <iostream>
using namespace std;
#include "VFileLine.h"
#include "VSymTable.h"

class VParseLex;  // Be sure not to include it, or the Bison class will get upset
class VParseGrammar;  // Be sure not to include it, or the Lex class will get upset
class VParseBisonYYSType;

struct av;

//**********************************************************************
// VParse

class VParse {
private:
    // MEMBERS
    // Mode
    bool	m_sigParser;	///< SigParser not simple Verilog::Parser

    // State
    VFileLine*	m_inFilelinep;	///< Next token's starting point
    int		m_debug;	///< Debugging level
    VParseLex*	m_lexp;		///< Current lexer state (NULL = closed)
    VParseGrammar* m_grammarp;	///< Current bison state (NULL = closed)
    bool	m_eof;		///< At end of file
    bool	m_callbackMasterEna; ///< Callbacks are enabled

    bool	m_useUnreadback;///< Need m_unreadback tracking
    string	m_unreadback;	///< Otherwise unprocessed whitespace before current token
    deque<string> m_buffers;	///< Buffer of characters to process

    int		m_anonNum;	///< Number of next anonymous object

    VSymStack	m_syms;		///< Symbol stack

    VAstEnt*	m_symTableNextId;	///< Symbol table for next lexer lookup

public:  // But for internalish use only
    // METHODS
    int lexToBison(VParseBisonYYSType* yylvalp);
    bool eofToLex() const { return m_eof && m_buffers.empty(); }
    bool inCellDefine() const;
    size_t inputToLex(char* buf, size_t max_size);

    // Symbol table
    VSymStack&	syms() { return m_syms; }
    VAstEnt* symTableNextId() const { return m_symTableNextId; }
    void symTableNextId(VAstEnt* entp) {
	if (debug()) {
	    if (entp) cout <<"symTableNextId under "<<entp<<"-"<<entp->type().ascii()<<endl;
	    else cout <<"symTableNextId under NULL"<<endl;
	}
	m_symTableNextId = entp;
    }
    string symObjofUpward() {
	return m_syms.objofUpward();
    }
    void symPushNew(VAstType type, const string& name) {
	symPushNewUnder(type, name, NULL);
    }
    void symPushNewUnder(VAstType type, const string& name, VAstEnt* parentp) {
	if (!parentp) parentp = m_syms.currentSymp();
	m_syms.pushScope(parentp->replaceInsert(type,name));
    }
    void symPushNewAnon(VAstType type) {
	string name = "__anon";
	name += type.ascii() + cvtToStr(++m_anonNum);
	symPushNew(type,name);
    }
    void symPopScope(VAstType type) {
	if (m_syms.curType() != type) {
	    string msg = (string)("Symbols suggest ending a '")+m_syms.curType().ascii()+"' but parser thinks ending a '"+type.ascii()+"'";
	    this->error(msg);
	    return;
	}
	m_syms.popScope(inFilelinep());
    }

private:
    void fakeBison();

public:
    // CONSTRUCTORS
    VParse(VFileLine* filelinep, av* symsp, bool sigParser, bool useUnreadbackFlag);
    virtual ~VParse();

    // ACCESSORS
    /// Insert given file into this point in input stream
    int debug() const { return m_debug; }	///< Set debugging level
    void debug(int level);			///< Set debugging level
    void parse(const string& text);		///< Add given text to
    void setEof();				///< Got a end of file
    bool sigParser() const { return m_sigParser; }
    void language(const char* valuep);
    void callbackMasterEna(bool flag) { m_callbackMasterEna=flag; }
    bool callbackMasterEna() const { return m_callbackMasterEna; }

    VFileLine* inFilelinep() const;		///< File/Line number for last callback
    void inFileline(const string& filename, int lineno) { m_inFilelinep = m_inFilelinep->create(filename, lineno); }
    void inFilelineInc() { m_inFilelinep = inFilelinep()->create(inFilelinep()->lineno()+1); }
    void inLineDirective(const char* text) { int ign; m_inFilelinep = inFilelinep()->lineDirective(text, ign/*ref*/); }

    string unreadback() const { return (m_useUnreadback ? m_unreadback : "new(...,use_unreadback=>0) was used"); }
    void unreadback(const string& text) { if (m_useUnreadback && callbackMasterEna()) m_unreadback = text; }
    void unreadbackCat(const string& text) { if (m_useUnreadback && callbackMasterEna()) m_unreadback += text; }
    void unreadbackCat(const char* textp, size_t len) { unreadbackCat(string(textp,len)); }

    // The default behavior is to pass all unknown `defines right through.
    // This lets the user determine how to report the errors.  It also nicely
    // allows `celldefine and such to remain in the output stream.

    // CONTROL METHODS
    // These options control how the parsing proceeds

    // CALLBACK METHODS
    // This probably will want to be overridden for given child users of this class.

    // CALLBACKGEN_H_VIRTUAL_0
    // CALLBACKGEN_GENERATED_BEGIN - GENERATED AUTOMATICALLY by callbackgen
    // Verilog::Parser Callback methods
    virtual void attributeCb(VFileLine* fl, const string& text) = 0;
    virtual void commentCb(VFileLine* fl, const string& text) = 0;
    virtual void endparseCb(VFileLine* fl, const string& text) = 0;
    virtual void keywordCb(VFileLine* fl, const string& text) = 0;
    virtual void numberCb(VFileLine* fl, const string& text) = 0;
    virtual void operatorCb(VFileLine* fl, const string& text) = 0;
    virtual void preprocCb(VFileLine* fl, const string& text) = 0;
    virtual void stringCb(VFileLine* fl, const string& text) = 0;
    virtual void symbolCb(VFileLine* fl, const string& text) = 0;
    virtual void sysfuncCb(VFileLine* fl, const string& text) = 0;
    // Verilog::SigParser Callback methods
    virtual void contassignCb(VFileLine* fl, const string& kwd, const string& lhs, const string& rhs) = 0;
    virtual void defparamCb(VFileLine* fl, const string& kwd, const string& lhs, const string& rhs) = 0;
    virtual void endcellCb(VFileLine* fl, const string& kwd) = 0;
    virtual void endinterfaceCb(VFileLine* fl, const string& kwd) = 0;
    virtual void endmodportCb(VFileLine* fl, const string& kwd) = 0;
    virtual void endmoduleCb(VFileLine* fl, const string& kwd) = 0;
    virtual void endpackageCb(VFileLine* fl, const string& kwd) = 0;
    virtual void endprogramCb(VFileLine* fl, const string& kwd) = 0;
    virtual void endtaskfuncCb(VFileLine* fl, const string& kwd) = 0;
    virtual void functionCb(VFileLine* fl, const string& kwd, const string& name, const string& data_type) = 0;
    virtual void importCb(VFileLine* fl, const string& package, const string& id) = 0;
    virtual void instantCb(VFileLine* fl, const string& mod, const string& cell, const string& range) = 0;
    virtual void interfaceCb(VFileLine* fl, const string& kwd, const string& name) = 0;
    virtual void modportCb(VFileLine* fl, const string& kwd, const string& name) = 0;
    virtual void moduleCb(VFileLine* fl, const string& kwd, const string& name, bool, bool celldefine) = 0;
    virtual void packageCb(VFileLine* fl, const string& kwd, const string& name) = 0;
    virtual void parampinCb(VFileLine* fl, const string& name, const string& conn, int index) = 0;
    virtual void pinCb(VFileLine* fl, const string& name, const string& conn, int index) = 0;
    virtual void portCb(VFileLine* fl, const string& name, const string& objof, const string& direction, const string& data_type
	, const string& array, int index) = 0;
    virtual void programCb(VFileLine* fl, const string& kwd, const string& name) = 0;
    virtual void taskCb(VFileLine* fl, const string& kwd, const string& name) = 0;
    virtual void varCb(VFileLine* fl, const string& kwd, const string& name, const string& objof, const string& net
	, const string& data_type, const string& array, const string& value) = 0;
    // CALLBACKGEN_GENERATED_END - GENERATED AUTOMATICALLY by callbackgen

    // CALLBACKGEN_KEYWORDS
    // CALLBACKGEN_GENERATED_BEGIN - GENERATED AUTOMATICALLY by callbackgen
    static bool isKeyword(const char* kwd, int leng) {
	static set<string> s_map;
	if (s_map.empty()) {
	    const char* kwds[] = {
		"accept_on","alias","always","always_comb","always_ff","always_latch","and",
		"assert","assign","assume","automatic","before","begin","bind",
		"bins","binsof","bit","break","buf","bufif0","bufif1",
		"byte","case","casex","casez","cell","chandle","checker",
		"class","clocking","cmos","config","const","constraint","context",
		"continue","cover","covergroup","coverpoint","cross","deassign","default",
		"defparam","design","disable","dist","do","edge","else",
		"end","endcase","endchecker","endclass","endclocking","endconfig","endfunction",
		"endgenerate","endgroup","endinterface","endmodule","endpackage","endprimitive","endprogram",
		"endproperty","endsequence","endspecify","endtable","endtask","enum","event",
		"eventually","expect","export","extends","extern","final","first_match",
		"for","force","foreach","forever","fork","forkjoin","function",
		"generate","genvar","global","highz0","highz1","if","iff",
		"ifnone","ignore_bins","illegal_bins","implies","import","incdir","include",
		"initial","inout","input","inside","instance","int","integer",
		"interface","intersect","join","join_any","join_none","large","let",
		"liblist","library","local","localparam","logic","longint","macromodule",
		"matches","medium","modport","module","nand","negedge","new",
		"nexttime","nmos","nor","noshowcancelled","not","notif0","notif1",
		"null","or","output","package","packed","parameter","pmos",
		"posedge","primitive","priority","program","property","protected","pull0",
		"pull1","pulldown","pullup","pulsestyle_ondetect","pulsestyle_onevent","pure","rand",
		"randc","randcase","randsequence","rcmos","real","realtime","ref",
		"reg","reject_on","release","repeat","restrict","return","rnmos",
		"rpmos","rtran","rtranif0","rtranif1","s_always","s_eventually","s_nexttime",
		"s_until","s_until_with","scalared","sequence","shortint","shortreal","showcancelled",
		"signed","small","solve","specify","specparam","static","strength",
		"string","strong","strong0","strong1","struct","super","supply0",
		"supply1","sync_accept_on","sync_reject_on","table","tagged","task","this",
		"throughout","time","timeprecision","timeunit","tran","tranif0","tranif1",
		"tri","tri0","tri1","triand","trior","trireg","type",
		"typedef","union","unique","unique0","unsigned","until","until_with",
		"untyped","use","uwire","var","vectored","virtual","void",
		"wait","wait_order","wand","weak","weak0","weak1","while",
		"wildcard","wire","with","within","wor","xnor","xor",""};
	    for (const char** k=kwds; **k; k++) s_map.insert(*k);
	}
	string str(kwd,leng);
	return s_map.end() != s_map.find(str);
    }
    // CALLBACKGEN_GENERATED_END - GENERATED AUTOMATICALLY by callbackgen

    // UTILITIES
    void error(const string& msg) { inFilelinep()->error(msg); }	///< Report a error
    void fatal(const string& msg) { inFilelinep()->fatal(msg); }	///< Report a fatal error
};

#endif // Guard
