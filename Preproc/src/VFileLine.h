// $Revision: 1.12 $$Date$$Author$  -*- C++ -*-
//*************************************************************************
//
// Copyright 2000-2005 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
/// \file
/// \brief Verilog::Preproc: Error handling
///
/// Authors: Wilson Snyder
///
/// Code available from: http://www.veripool.com/verilog-perl
///
//*************************************************************************

#ifndef _VFILELINE_H_
#define _VFILELINE_H_ 1
#include <string>
#include <iostream>
using namespace std;

//============================================================================
// VFileLine
/// User information and error reporting functions
////
/// Users can override this class to implement their own error handling

class VFileLine {
private:
    int		m_lineno;		///< Line number in file
    string	m_filename;		///< File name
    static int	s_numErrors;		///< Number of errors detected

protected:
    VFileLine(int called_only_for_default) {init("",0);}

public:
    // CONSTRUCTORS
    /// Create a new fileline, for a new file and/or line number.
    /// Member functions, so that if a user provides another class, a change in the
    /// filename/linenumber will create a new element using the derived class.
    virtual VFileLine* create(const string filename, int lineno);
    /// Create with same filename, new line number; just calls create(fn,ln)
    virtual VFileLine* create(int lineno);
    static VFileLine* create_default();
    virtual void init(const string filename, int lineno);
    virtual ~VFileLine() {}
    // ACCESSORS
    virtual int lineno () const { return m_lineno; }	///< Return line number
    virtual const string filename () const { return m_filename; }	///< Return filename
    virtual const string filebasename () const;	///< Filename with any directory stripped
    virtual const char* cfilename () const { return m_filename.c_str(); }
    // METHODS
    virtual void fatal(const string msg);	///< Report a fatal error at given location
    virtual void error(const string msg);	///< Report a error at given location
    // STATIC METHODS
    static int numErrors() {return s_numErrors;}	///< Return total errors detected

    // Internal methods -- special use
    static const char* itoa(int i);	///< Internal: Not reentrant! - for fatalSrc() only
};
ostream& operator<<(ostream& os, VFileLine* fileline);

/// Use this instead of fatal() to mention the source code line.
#define fatalSrc(msg) fatal((string)"Internal Error: "+__FILE__+":"+VFileLine::itoa(__LINE__)+": "+(msg))

#endif // Guard
