# See copyright, etc in below POD section.
######################################################################

package Verilog::Std;
use Config;
use IO::File;
use File::Path;
use Verilog::Language;
use Carp;
use strict;

use vars qw($VERSION);

######################################################################
#### Configuration Section

$VERSION = '3.468';

#######################################################################
# It's a PITRA to have pure datafiles get installed properly, so we have
# the std text here in this package.

our $_Std_Text = <<EOF;
`line 1 "Perl_Verilog::Std_module" 0
// Verilog-Perl Verilog::Std
// The basis for this package is described in IEEE 1800-2017 Annex G
package std;

class semaphore;
   extern function new(int keyCount = 0);
   extern function void put(int keyCount = 1);
   extern task get(int keyCount = 1);
   extern function int try_get(int keyCount = 1);
endclass

class mailbox #(type T = dynamic_singular_type) ;
   extern function new(int bound = 0);
   extern function int num();
   extern task put( T message);
   extern function int try_put( T message);
   extern task get( ref T message );
   extern function int try_get( ref T message );
   extern task peek( ref T message );
   extern function int try_peek( ref T message );
endclass

class process;
   typedef enum { FINISHED, RUNNING, WAITING, SUSPENDED, KILLED } state;
   extern static function process self();
   extern function state status();
   extern function void kill();
   extern task await();
   extern function void suspend();
   extern function void resume();
endclass

// randomize is here, however the parsing rules are special,
// For example there is "(null)", variable arguments, and "with {...}"
// randomize really should be a language keyword.
function int randomize();
endfunction

endpackage : std

import std::*;

EOF

#######################################################################
# ACCESSORS

sub std {
    my $std = shift || Verilog::Language::language_standard();
    if ($std =~ /^1800/) {
	return $_Std_Text;
    } else {
	return "";
    }
}

#######################################################################
1;

=pod

=head1 NAME

Verilog::Std - SystemVerilog Built-in std Package Definition

=head1 SYNOPSIS

Internally used by Verilog::SigParser, etc.

   use Verilog::Std;
   print Verilog::Std::std;

=head1 DESCRIPTION

Verilog::Std contains the built-in "std" package required by the
SystemVerilog standard.

=head1 FUNCTIONS

=over 4

=item std({I<standard>})

Return the definition of the std package.  Optionally pass the language
standard, defaulting to what Verilog::Language::language_standard returns if
unspecified.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2009-2019 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License
Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>

=cut

######################################################################
