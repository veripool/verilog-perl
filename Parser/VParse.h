// -*- C++ -*-
//*************************************************************************
//
// Copyright 2000-2009 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License or the Perl Artistic License.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
/// \file
/// \brief Verilog::Parse: Parseess verilog code
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
#include <deque>
#include <iostream>
using namespace std;
#include "VFileLine.h"

class VParseLex;  // Be sure not to include it, or the Bison class will get upset
class VParseGrammar;  // Be sure not to include it, or the Lex class will get upset
class VParseBisonYYSType;

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

    bool	m_useUnreadback;///< Need m_unreadback tracking
    string	m_unreadback;	///< Otherwise unprocessed whitespace before current token
    deque<string> m_buffers;	///< Buffer of characters to process

public:  // But for internalish use only
    // METHODS
    int lexToBison(VParseBisonYYSType* yylvalp);
    bool eofToLex() const { return m_eof && m_buffers.empty(); }
    bool inCellDefine() const;
    int inputToLex(char* buf, int max_size);

private:
    void fakeBison();

public:
    // CONSTRUCTORS
    VParse(VFileLine* filelinep, bool sigParser, bool useUnreadbackFlag);
    virtual ~VParse();

    // ACCESSORS
    /// Insert given file into this point in input stream
    int debug() const { return m_debug; }	///< Set debugging level
    void debug(int level);			///< Set debugging level
    void parse(const string& text);		///< Add given text to
    void setEof();				///< Got a end of file
    bool sigParser() const { return m_sigParser; }
    void language(const char* valuep);

    VFileLine* inFilelinep() const;		///< File/Line number for last callback
    void inFileline(const string& filename, int lineno) { m_inFilelinep = m_inFilelinep->create(filename, lineno); }
    void inFilelineInc() { m_inFilelinep = inFilelinep()->create(inFilelinep()->lineno()+1); }
    void inLineDirective(const char* text) { m_inFilelinep = inFilelinep()->lineDirective(text); }

    string unreadback() const { return (m_useUnreadback ? m_unreadback : "new(...,use_unreadback=>0) was used"); }
    void unreadback(const string& text) { if (m_useUnreadback) m_unreadback = text; }
    void unreadbackCat(const char* textp, int len) { if (m_useUnreadback) m_unreadback += string(textp,len); }

    // The default behavior is to pass all unknown `defines right through.
    // This lets the user determine how to report the errors.  It also nicely
    // allows `celldefine and such to remain in the output stream.

    // CONTROL METHODS
    // These options control how the parsing proceeds

    // CALLBACK METHODS
    // This probably will want to be overridden for given child users of this class.
    virtual void attributeCb(VFileLine* fl, const string& text) = 0;
    virtual void commentCb(VFileLine* fl, const string& text) = 0;
    virtual void endparseCb(VFileLine* fl) = 0;
    virtual void keywordCb(VFileLine* fl, const string& text) = 0;
    virtual void numberCb(VFileLine* fl, const string& text) = 0;
    virtual void operatorCb(VFileLine* fl, const string& text) = 0;
    virtual void preprocCb(VFileLine* fl, const string& text) = 0;
    virtual void stringCb(VFileLine* fl, const string& text) = 0;
    virtual void symbolCb(VFileLine* fl, const string& text) = 0;
    virtual void sysfuncCb(VFileLine* fl, const string& text) = 0;

    virtual void endcellCb(VFileLine* fl, const string& kwd) = 0;
    virtual void endinterfaceCb(VFileLine* fl, const string& kwd) = 0;
    virtual void endmoduleCb(VFileLine* fl, const string& kwd) = 0;
    virtual void endtaskfuncCb(VFileLine* fl, const string& kwd) = 0;
    virtual void functionCb(VFileLine* fl, const string& kwd, const string& name, const string& type) = 0;
    virtual void instantCb(VFileLine* fl, const string& mod, const string& cell, const string& range) = 0;
    virtual void interfaceCb(VFileLine* fl, const string& kwd, const string& name) = 0;
    virtual void moduleCb(VFileLine* fl, const string& kwd, const string& name, bool celldefine) = 0;
    virtual void paramPinCb(VFileLine* fl, const string& name, const string& conn, int number) = 0;
    virtual void pinCb(VFileLine* fl, const string& name, const string& conn, int number) = 0;
    virtual void portCb(VFileLine* fl, const string& name) = 0;
    virtual void signalCb(VFileLine* fl, const string& kwd, const string& name,
			  const string& vec, const string& mem, const string& signd,
			  const string& value,
			  bool inFunc) = 0;
    virtual void taskCb(VFileLine* fl, const string& kwd, const string& name) = 0;
    virtual void unsupportedCb(VFileLine* fl, const string& text, const string& token) = 0;

    // UTILITIES
    void error(string msg) { inFilelinep()->error(msg); }	///< Report a error
    void fatal(string msg) { inFilelinep()->fatal(msg); }	///< Report a fatal error
};

#endif // Guard
