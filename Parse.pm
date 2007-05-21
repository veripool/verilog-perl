# Verilog::Parse.pm -- Verilog preprocessing
# $Id$
# Author: Wilson Snyder <wsnyder@wsnyder.org>
######################################################################
#
# Copyright 2000-2007 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
######################################################################

=pod

=head1 NAME

Verilog::Parse - parse Verilog language files

=head1 WARNING

This module is no longer supported.  Use Verilog::Parser instead.

=head1 SYNOPSIS

  use Verilog::Parse;

  $parser = new Verilog::Parse;

  sub function {my ($parser, $what, $info) = @_; ...}
  $parser->callback ("xxx", \&function)

  $string = $parser->unreadback ();

  $parser->Verilog::Parse::parse ($FileHandle)

=head1 DESCRIPTION

This package implements parsing of the Verilog language.  A file is parsed
and callbacks are called for various entities in the file, as they occur.

=head1 WARNING

This module is no longer supported.  Use Verilog::Parser instead.

=over 4

=item $parser->new

Create a new parser.

=item $parser->callback ("token", \&function)

Request that when the parser hits the given token, function will be called.
The tokens that may be parsed are:

    "COMMENT"	Any text in // or /**/ comments.
    "STRING"	Any quoted string, including the quotes.
    "KEYWORD"	A Verilog keyword.  (See L<Verilog::Language>) 
    "SYMBOL"	A textual non-keyword
    "OPERATOR"	A non-alphanumeric operator.
    "NUMBER"	A number.

The callback will get three arguments.  The first is the parser (self).
The second is the exact type of token, one of those listed above.  Third
is a string with the symbol, number, etc.

=item $parser->parse ($FileHandle)

Read input from the filehandle, and perform callbacks as needed.

=item $parser->unreadback ()

Return any input string from the file that has not been sent to the
callback.  This will include whitespace and tokens which did not have a
callback.  (For example comments, if there is no comment callback.)  This
is useful for recording the entire contents of the input, for
preprocessors, pretty-printers, and such.

=back

=head1 EXAMPLE

Here's a simple example which will print every symbol in a verilog
file.  We also remember what line it occurred on, just for the heck of it.

    sub symbol_cb {
        # Callback from parser when a symbol occurs
        sub function (my ($parser, $what, $info) = @_; ...)
        $signals_and_symbols{$info} = $.;
    }
    
    sub verilog_read_symbols {
        my $filename = shift;
    
        local %signals_and_symbols = ();	# Signals already found in module
    
        my $fh = new FileHandle;
        my $parser = new Verilog::Parse;
        $parser->callback ("SYMBOL", \&symbol_cb);
        $fh->open("<$filename") or die "Can't read $filename.";
        $parser->Verilog::Parse::parse ($fh);
        $fh->close;
    
        foreach $sym (sort (keys %signals_and_symbols)) {
    	print "Symbol $sym\n";
        }
    }

=head1 BUGS

This is being distributed as a baseline for future contributions.  Don't
expect a lot, the parser is still naive, and there are many awkward cases
that aren't covered.

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.com/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.com/verilog-perl.html>.

Copyright 2000-2007 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License or the Perl Artistic License.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::ParseSig>, 
L<Verilog::Language>, 
L<IO::File>

=cut

######################################################################


package Verilog::Parse;
require 5.000;
require Exporter;

use strict;
use vars qw($VERSION);
use English;
use Carp;
use FileHandle;
use Verilog::Language;

######################################################################
#### Configuration Section

# Other configurable settings.
$Verilog::Parse::debug = 0;		# for debugging

$VERSION = '2.373';

#######################################################################

sub new {
    @_ <= 1 or croak 'usage: Verilog::Parse->new ({options})';
    my $self = shift;		# Class (Parser Element)
    $self ||= "Verilog::Parse";

    print "$self->new()\n" if $Verilog::Parse::debug;

    my $newself = {"unreadback" => "",		# Signals since last callback
		   };
    bless $newself, $self;
    $newself->callback ("COMMENT", \&null_cb);
    $newself->callback ("SYMBOL",  \&null_cb);
    $newself->callback ("KEYWORD", \&null_cb);
    $newself->callback ("NUMBER",  \&null_cb);
    $newself->callback ("OPERATOR",\&null_cb);
    $newself->callback ("STRING",  \&null_cb);
    return $newself;
}

######################################################################
####  Accessors

sub callback {
    @_==3 or croak 'usage: Verilog::Parse->new ({options})';
    my $self = shift;		# Class (Parser Element)
    my $what = shift;		# Token to add callback for
    my $func = shift;		# Function to callback

    print "$self->callback($what)\n" if $Verilog::Parse::debug;

    $self->{$what} = $func;
    return $self;
}

sub unreadback {
    # Return any un read text and clear it
    my $self = shift;	# Parser
    if (@_) {
	my $value = shift;	# Value/array/etc to set to
	$self->{unreadback} = $value;
    } else {
	my $info = $self->{unreadback};
	$self->{unreadback} = "";
	return $info;
    }
}

#######################################################################

sub null_cb {
    # Default Internal callback
    my $parser = shift;	# Parser invoked
    my $what = shift;	# What kinda token was gotten
    my $info = shift;	# Entity information
    $parser->{unreadback} .= $info;
}

#######################################################################

sub parse {
    # Parse a file handle
    @_ == 2 or croak 'usage: $parser->parse($fh)';
    my $self = shift;
    my $fh = shift;

    my $incomment = 0;
    my $quote = 0;
    my %modules_sigs = ();
    my $line;
    my $comment_string = "";
    $self->{unreadback} = "";
    my $string = "";
    while ($line = $fh->getline() ) {
	# Keep parsing whatever is on this line
	while ($line) {
	    #print "Lnc$incomment $line" if ($Verilog::Parse::debug);
	    if ($incomment) {
		if ($line =~ /\*\//) {
		    $comment_string .= $PREMATCH . $MATCH;
		    $line = $POSTMATCH;
		    my $info = $comment_string;
		    print "GotaCOMMENT $info\n"    if ($Verilog::Parse::debug);
		    &{$self->{COMMENT}} ($self, "COMMENT", $info);
		    $incomment = 0;
		}
		else {
		    $comment_string .= $line;
		    $line = "";
		}
	    }
	    elsif ($quote) {
		# Check for strings
		if ($line =~ /\"/) {
		    $string .= $PREMATCH . $MATCH;
		    $line = $POSTMATCH;
		    if ($PREMATCH !~ /\\$/) {
			my $info = $string;
			print "GotaSTRING $info\n"    if ($Verilog::Parse::debug);
			&{$self->{STRING}} ($self, "STRING", $info);
			$quote = 0;
		    }
		} else {
		    $string .= $line;
		}
	    }
	    else {
		# not in comment
		# Strip leading whitespace
		if ($line =~ s/^(\s+)//) {
		    $self->{unreadback} .= $MATCH;
		}
		next if ($line eq "");
		if ($line =~ /^\"/) {
		    $line = $POSTMATCH;
		    $string = $MATCH;
		    $quote = 1;
		}
		elsif (($line =~ /^[a-zA-Z_\`\$][a-zA-Z0-9_\`\$]*/)
                       || ($line =~ /^\\\S+\s+/)) { #cseddon - escaped identifiers
		    my $info = $MATCH;
		    $line = $POSTMATCH;
		    if (!$quote) {
			if (Verilog::Language::is_keyword($info)) {
			    print "GotaKEYWORD $info\n"    if ($Verilog::Parse::debug);
			    &{$self->{KEYWORD}} ($self, "KEYWORD", $info);
			} else {
			    print "GotaSYMBOL $info\n"    if ($Verilog::Parse::debug);
			    &{$self->{SYMBOL}} ($self, "SYMBOL", $info);
			}
		    }
		}
		elsif ($line =~ /^\/\*/) {
		    $comment_string = $MATCH;
		    $line = $POSTMATCH;
		    $incomment = 1;
		}
		elsif ($line =~ /^\/\//) {
		    my $info = $line;
		    print "GotaCOMMENT $info\n"    if ($Verilog::Parse::debug);
		    &{$self->{COMMENT}} ($self, "COMMENT", $info);
		    $line = "";
		}
		elsif (($line =~ /^(&& | \|\| | == | != | <= | >= | << | >> )/x)
		       || ($line =~ /^([][:;@\(\),.%!=<>?|&{}~^+---\/*#])/)) {  #]
		    my $info = $MATCH;
		    $line = $POSTMATCH;
		    print "GotaOPERATOR $info\n"    if ($Verilog::Parse::debug);
		    &{$self->{OPERATOR}} ($self, "OPERATOR", $info);
		}
		elsif (($line =~ /^([0-9]*'[BHODbhod]\ *[0-9A-FXZa-fxz_?]+)/)    #'
		    || ($line =~ /^([0-9]+[0-9a-fA-F_]*)/ )) {
		    my $info = $MATCH;
		    $line = $POSTMATCH;
		    print "GotaNUMBER $info\n"    if ($Verilog::Parse::debug);
		    &{$self->{NUMBER}} ($self, "NUMBER", $info);
		}
		elsif ($line =~ /\\\S+/) {
		    my $info = $MATCH;
		    $line = $POSTMATCH;
		    print "GotaSYMBOL $info\n"    if ($Verilog::Parse::debug);
		    &{$self->{SYMBOL}} ($self, "SYMBOL", $info);
		}
		else {
		    if ($line ne "") {
			$self->{unreadback} .= $line;
		        print STDERR "$.:Unknown symbol, ignoring to eol: $line\n";
	                $line = "";
                    }
		}
            }
        }
    }
    return $self;
}


######################################################################
### Package return
1;
