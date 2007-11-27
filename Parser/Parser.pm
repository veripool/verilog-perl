#$Id$
######################################################################
#
# Copyright 2001-2007 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
######################################################################

package Verilog::Parser;
use Carp;
use Verilog::Getopt;
use Verilog::Language;

require DynaLoader;
@ISA = qw(DynaLoader);

use strict;
use vars qw($VERSION $Debug);

$VERSION = '3.013';

#$Debug sets the default value for debug.  You're better off with the object method though.

######################################################################
#### Configuration Section

bootstrap Verilog::Parser;

#In Parser.xs:
# sub _new (class, sigparser)
# sub _open (class)
# sub _debug (class, level)
# sub parse (class)
# sub eof (class)
# sub filename (class, [setit])
# sub lineno (class, [setit])
# sub unreadback (class, [setit])
# sub unreadbackCat (class, add)

######################################################################
#### Constructors

sub new {
    my $class = shift;  $class = ref $class if ref $class;
    my $self = {_sigparser=>0,
		use_unreadback => 1,   # Backward compatibility
		@_};
    bless $self, $class;
    # Sets $self->{_cthis}
    $self->_new($self,
		# Options go here
		$self->{_sigparser},
		$self->{use_unreadback},
		);
    $self->debug($Debug) if $Debug;
    return $self;
}

######################################################################
####  Accessors

sub debug {
    my $self = shift;
    my $level = shift;
    $self->_debug($level) if defined $level;
}

sub fileline {
    my $self = shift;
    return ($self->filename||"").":".($self->lineno||"");
}

sub line { return lineno(@_); }  # Old, now undocumented

#######################################################################
#### Called by the parser

sub reset {
    my $self = shift;
}

sub parse_file {
    # Read a file and parse
    @_ == 2 or croak 'usage: $parser->parse_file($filename)';
    my $self = shift;
    my $filename = shift;

    my $fh = new IO::File;
    $fh->open($filename) or croak "%Error: $! $filename";
    $self->reset();
    $self->filename($filename);
    $self->lineno(1);
    while (defined(my $line = $fh->getline())) {
	$self->parse ($line);
    }
    $self->eof;
    $fh->close;
    return $self;
}

sub parse_preproc_file {
    # Read a preprocess file and parse
    @_ == 2 or croak 'usage: $parser->parse_file(Verilog::Preproc_object_ref)';
    my $self = shift;
    my $pp = shift;

    ref($pp) or croak "%Error: not passed a Verilog::Preproc object";
    $self->reset();
    while (defined(my $line = $pp->getline())) {
	$self->parse ($line);
    }
    $self->eof;
    return $self;
}

######################################################################
#### Called by the parser

sub error {
    my ($self,$text,$token)=@_;
    my $fileline = $self->filename.":".$self->lineno;
    croak ("%Error: $fileline: $text\n"
	   ."Stopped");
}

sub attribute {
    # Default Internal callback
    my $self = shift;	# Parser invoked
    my $token = shift;	# What token was parsed
    $self->unreadbackCat($token);
}

sub comment {
    # Default Internal callback
    my $self = shift;	# Parser invoked
    my $token = shift;	# What token was parsed
    $self->unreadbackCat($token);
}

sub string {
    # Default Internal callback
    my $self = shift;	# Parser invoked
    my $token = shift;	# What token was parsed
    $self->unreadbackCat($token);
}

sub keyword {
    # Default Internal callback
    my $self = shift;	# Parser invoked
    my $token = shift;	# What token was parsed
    $self->unreadbackCat($token);
}

sub symbol {
    # Default Internal callback
    my $self = shift;	# Parser invoked
    my $token = shift;	# What token was parsed
    $self->unreadbackCat($token);
}

sub operator {
    # Default Internal callback
    my $self = shift;	# Parser invoked
    my $token = shift;	# What token was parsed
    $self->unreadbackCat($token);
}

sub preproc {
    # Default Internal callback
    my $self = shift;	# Parser invoked
    my $token = shift;	# What token was parsed
    if (Verilog::Language::is_keyword($token)) {
	$self->keyword($token); # Do this for backward compatibility with Version 2.*
    } else {
	$self->symbol($token); # Do this for backward compatibility with Version 2.*
    }
}
sub number {
    # Default Internal callback
    my $self = shift;	# Parser invoked
    my $token = shift;	# What token was parsed
    $self->unreadbackCat($token);
}

sub sysfunc {
    # Default Internal callback - note the default action
    my $self = shift;	# Parser invoked
    my $token = shift;	# What token was parsed
    $self->symbol($token); # Do this for backward compatibility with Version 2.*
}

sub endparse {
    # Default Internal callback
    my $self = shift;	# Parser invoked
    my $token = shift;	# What token was parsed
    $self->unreadbackCat($token);
}

######################################################################
#### Package return
1;
__END__
=pod

=head1 NAME

Verilog::Parser - Parse Verilog language files

=head1 SYNOPSIS

  use Verilog::Parser;

  my $parser = new Verilog::Parser;
  $string = $parser->unreadback ();
  $line   = $parser->lineno ();
  $parser->parse ($text)
  $parser->parse_file ($filename)

=head1 DESCRIPTION

Verilog::Parser will tokenize a Verilog file when the parse() method is
called and invoke various callback methods.  This is useful for extracting
information and editing files while retaining all context.  For netlist
like extractions, see L<Verilog::Netlist>.

See the "Which Package" section of L<Verilog::Language> if you are unsure
which parsing package to use for a new application.

=head1 METHODS

=over 4

=item $parser = Verilog::Parser->new (args...)

Create a new Parser. Passing the named argument "use_unreadback => 0" will
disable later use of the unreadback method, which may improve performance.

=item $parser->eof ()

Indicate the end of the input stream.  All incomplete tokens will be parsed
and all remaining callbacks completed.

=item $parser->filename ($set)

Return (if $set is undefined) or set current filename.

=item $parser->lineno ($set)

Return (if $set is undefined) or set current line number.

=item $parser->parse ($string)

Parse the $string as verilog text.  Can be called multiple times.  Note not
all callbacks may be invoked until the eof method is called.

=item $parser->parse_file ($filename);

This method can be called to parse text from a file.  The argument can
be a filename or an already opened file handle. The return value from
parse_file() is a reference to the parser object.

=item $parser->parse_preproc_file ($preproc);

This method can be called to parse preprocessed text from a predeclared
Verilog::Preproc object.

=item $parser->unreadback ($string)

Return any input string from the file that has not been sent to the
callback.  This will include whitespace and tokens which did not have a
callback.  (For example comments, if there is no comment callback.)  This
is useful for recording the entire contents of the input, for
preprocessors, pretty-printers, and such.

With the optional argument, set the text to be returned with the next
unreadback call.  See also unreadbackCat, which is much faster.

To use this option, "use_unreadback => 1" must have been passed to the
constructor.

=item $parser->unreadbackCat ($text)

Add text to be returned with the next unreadback call.  This is much faster
than using "$parser->unreadback($parser->unreadback . $text)".

=back

=head1 CALLBACKS

In order to make the parser do anything interesting, you must make a
subclass where you override one or more of the following callback methods
as appropriate:

=over 4

=item $self->attribute ( $token )

This method is called when any text in (* *) are recognized.  The first
argument, $token, is the contents of the attribute including the delimiters.

=item $self->comment ( $token )

This method is called when any text in // or /**/ comments are recognized.
The first argument, $token, is the contents of the comment including the
comment delimiters.

=item $self->endparse ( $token )

This method is called when the file has been completely parsed, at the
End-Of-File of the parsed file.  It is useful for writing clean up
routines.

=item $self->keyword ( $token )

This method is called when any Verilog keyword is recognized.
The first argument, $token, is the keyword.

=item $self->number ( $token )

This method is called when any number is recognized.  The first argument,
$token, is the number.  The Verilog::Language::number_value function may be
useful for converting a Verilog value to a Perl integer.

=item $self->operator ( $token )

This method is called when any symbolic operator (+, -, etc) is recognized.
The first argument, $token, is the operator.

=item $self->preproc ( $token )

This method is called when any Verilog preprocessor `command is recognized.
Most of these are handled by the preprocessor, however any unrecognized
`defines are passed through.  For backward compatibility, if not defined
this function will call the symbol callback.

=item $self->string ( $token )

This method is called when any text in double quotes are recognized, or on
the text of protected regions.  The first argument, $token, is the contents
of the string including the quotes.

=item $self->symbol ( $token )

This method is called when any Verilog symbol is recognized.  A symbol is
considered a non-keyword bare-word.  The first argument, $token, is the
symbol.

=item $self->sysfunc ( $token )

This method is called when any Verilog $syscall is recognized.  The first
argument, $token, is the symbol.  For backward compatibility, if not
defined this function will call the symbol callback.

=back

=head1 EXAMPLE

Here's a simple example which will print every symbol in a verilog
file.

  package MyParser;
  use Verilog::Parser;
  @ISA = qw(Verilog::Parser);
  
  # parse, parse_file, etc are inherited from Verilog::Parser
  sub new {
      my $class = shift;
      #print "Class $class\n";
      my $self = $class->SUPER::new();
      bless $self, $class; 
      return $self;
  }
  
  sub symbol {
      my $self = shift;
      my $token = shift;
      
      $self->{symbols}{$token}++;
  }
  
  sub report {
      my $self = shift;
  
      foreach my $sym (sort keys %{$self->{symbols}}) {
  	 printf "Symbol %-30s occurs %4d times\n",
  	 $sym, $self->{symbols}{$sym};
      }
  }
  
  package main;
  
  my $parser = MyParser->new();
  $parser->parse_file (shift);
  $parser->report();

=head1 BUGS

This is being distributed as a baseline for future contributions.  Don't
expect a lot, the Parser is still naive, and there are many awkward cases
that aren't covered.

The parser currently assumes the string it is passed ends on a newline
boundary.  It should be changed to allow arbitrary chunks.

Cell instantiations without any arguments are not supported, an empty set
of parenthesis are required.  (Use "cell cell();", not "cell cell;".)

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
L<Verilog::Preproc>, 
L<Verilog::SigParser>, 
L<Verilog::Language>, 
L<Verilog::Netlist>, 
L<Verilog::Getopt>, 
L<vrename>,
L<vpm>
L<vppp>

=cut
