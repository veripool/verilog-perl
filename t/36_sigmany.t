#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2014 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
######################################################################
# VERILOG_TEST_FILES="$V4/test_regress/t/t_case*.v" VERILOG_TEST_DEBUGIF=1 t/36_sigmany.t
#  (delete-matching-lines "^#\\|^ok \\|^1\\.\\.\\|^not ok")

use strict;
use Test;  # Not Test::More due to skip usage
use Data::Dumper; $Data::Dumper::Indent = 1;

BEGIN { plan tests => 3 }
BEGIN { require "t/test_utils.pl"; }

our $Any_Error;
our $Got_Eof_Module;

######################################################################

package MyParser;
use Verilog::SigParser;
use strict;
use base qw(Verilog::SigParser);

sub module {
    my ($self,$kwd,$name)=@_;
    $Got_Eof_Module = 1 if $name eq '_GOT_EOF_MODULE';
}

sub error {
    my ($self,$text,$token)=@_;
    my $fileline = $self->filename.":".$self->lineno;
    if ($text !~ /\`math/) {
	if (!$ENV{VERILOG_TEST_SILENT}) {
	    warn ("%Warning: $fileline: $text\n");
	    $self->{_errored} = 1;
	    $::Any_Error = 1;
	} else {
	    warn ("-Silent-Warning: $fileline: $text\n");
	}
	# Try to print source line
	if (my $fh=IO::File->new("<".$self->filename)) {
	    my @lines = $fh->getlines;
	    my $line = $lines[$self->lineno-1] || "";
	    $line =~ s/^\s+//;
	    warn ("\t".$line) if $line;
	    $fh->close();
	}
    }
}

######################################################################

package main;

use Verilog::SigParser;
use Verilog::Preproc;
use Verilog::Getopt;
ok(1);

my @files;
if ($ENV{VERILOG_TEST_FILES}) {
    ok(1);
    @files = split(/:/,$ENV{VERILOG_TEST_FILES});
    @files = map {glob $_} @files;
}
else {
    skip("VERILOG_TEST_FILES not set (harmless)",1);
    # export VERILOG_TEST_FILES="$V4/test_regress/t/t_case*.v"
    @files = glob("verilog/*.v");
    @files = grep {!m!/inc!} @files;
}
check_series(@files);

######################################################################

sub check_series {
    my @files = @_;
    $Any_Error = 0;
    foreach my $file (@files) {
	read_test($file);
    }
    ok(!$Any_Error);
}

sub read_test {
    my $filename = shift;
    my $parser = one_parse($filename, 0);
    if ($ENV{VERILOG_TEST_DEBUGIF} && $parser->{_errored}) {
	print "======== REPARSING w/debug\n";
	one_parse($filename, 9);
    }
}

sub one_parse {
    my $filename = shift;
    my $debug = shift;

    $Got_Eof_Module = undef;

    print "="x70,"\n";
    print "read $filename\n";
    my $opt = new Verilog::Getopt;
    # Used to do this so we can read pre-vpassert'ed files,
    # but now we require a `include std_defines in all sources
    # even though a lint run may not indicate it's needed
    # (since lint runs pre-vpassert.)
    # $opt->define('__message_on',"1'b0");
    if ($filename =~ m!(.*)/!) {
	# Allow includes in same dir as the test
	my $fdir = $1;
	$opt->incdir($fdir);
	$opt->module_dir ($fdir);
    }

    my $pp = Verilog::Preproc->new(keep_comments=>0,
				   include_open_nonfatal=>0,
				   options=>$opt);

    my $parser = new MyParser();
    # Suck in std:: before enabling debug dumps
    $parser->std;

    $parser->debug($debug || $ENV{VERILOG_TEST_DEBUG});
    $pp->open($filename);
    if ($ENV{VERILOG_TEST_KEYWORDS}) {
	$parser->parse("`begin_keywords \"1364-2001\" ");
    }
    $parser->reset;
    # Similar to $parser->parse_preproc_file($pp);
    # but we want to stuff a module before the EOF
    while (defined(my $line = $pp->getline())) {
	$parser->parse ($line);
    }
    $parser->parse("module _GOT_EOF_MODULE; endmodule\n");
    $parser->eof;

    if (!$Any_Error && !$Got_Eof_Module) {
	warn "%Warning: $filename: Never parsed fake module at EOF\n";
	$parser->{_errored} = 1;
	$::Any_Error = 1;
    }

    print Dumper($parser->{symbol_table}) if $parser->debug;

    return $parser;
}
