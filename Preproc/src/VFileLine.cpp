// $Revision: 1.13 $$Date$$Author$  -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilog::Preproc: Error handling implementation
//
// Code available from: http://www.veripool.com/verilog-perl
//
// Authors: Wilson Snyder
//
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

#include <stdio.h>

#include "VFileLine.h"

int VFileLine::s_numErrors = 0;

//============================================================================

VFileLine* VFileLine::create(const string filename, int lineno) {
    VFileLine* filelp = new VFileLine(true);
    filelp->init(filename, lineno);
    return filelp;
}

VFileLine* VFileLine::create(int lineno) {
    return (this->create(this->filename(), lineno));
}

VFileLine* VFileLine::create_default() {
    VFileLine* filelp = new VFileLine(true);
    return filelp;
}

void VFileLine::init(const string filename, int lineno) {
    m_filename = filename;
    m_lineno = lineno;
}

const string VFileLine::filebasename () const {
    string name = filename();
    string::size_type slash;
    if ((slash = name.rfind("/")) != string::npos) {
	name.erase(0,slash+1);
    }
    return name;
}

void VFileLine::fatal(const string msg) {
    error(msg);
    error("Fatal Error detected");
    abort();
}
void VFileLine::error(const string msg) {
    VFileLine::s_numErrors++;
    if (msg[msg.length()-1] != '\n') {
	fprintf (stderr, "%%Error: %s", msg.c_str());
    } else {
	fprintf (stderr, "%%Error: %s\n", msg.c_str());	// Append newline, as user ommitted it.
    }
}

const char* VFileLine::itoa(int i) {
    static char buf[100];
    sprintf(buf,"%d",i);
    return buf;
}

//======================================================================
// Global scope

ostream& operator<<(ostream& os, VFileLine* flp) {
    if (flp->filename()!="") {
	os <<flp->cfilename()<<":"<<dec<<flp->lineno()<<": "<<hex;
    }
    return(os);
}
