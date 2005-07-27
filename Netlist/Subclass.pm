# Verilog - Verilog Perl Interface
# $Revision: 1.35 $$Date$$Author$
# Author: Wilson Snyder <wsnyder@wsnyder.org>
######################################################################
#
# Copyright 2000-2005 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
######################################################################

package Verilog::Netlist::Subclass;
use Class::Struct;
require Exporter;
$VERSION = '2.320';
@ISA = qw(Exporter);
@EXPORT = qw(structs);
use strict;

use vars qw($Warnings $Errors %_Error_Unlink_Files);
$Warnings = $Errors = 0;

# Maybe in the future
#struct ('Verilog::Netlist::Subclass'
#	 =>[name     	=> '$', #'	# Name of the element
#	    filename 	=> '$', #'	# Filename this came from
#	    lineno	=> '$', #'	# Linenumber this came from
#	    userdata	=> '%',		# User information
#	    ]);

######################################################################
#### Member functions

######################################################################
#### Error Handling
# Class::Struct is great, but it can't have a @ISA... Sigh.
# Thus you can't just call a $netlist_object->warn ("message...");

sub info {
    my $self = shift;
    $self = shift if ref $_[0];	# Optional reference to object
    CORE::warn "-Info: ".($self->filename||"").":".($self->lineno||"").": ".join('',@_);
}

sub warn {
    my $self = shift;
    $self = shift if ref $_[0];	# Optional reference to object
    CORE::warn "%Warning: ".($self->filename||"").":".($self->lineno||"").": ".join('',@_);
    $Warnings++;
}

sub error {
    my $self = shift;
    $self = shift if ref $_[0];	# Optional reference to object
    CORE::warn "%Error: ".($self->filename||"").":".($self->lineno||"").": ".join('',@_);
    $Errors++;
}

sub exit_if_error {
    my $self = shift;
    my %opts = @_;
    my $allow = $opts{allow} || "";
    exit(10) if ($Errors || ($Warnings && $allow !~ /warning/));
    return ($Errors + $Warnings);
}

sub unlink_if_error {
    $_Error_Unlink_Files{$_[0]} = 1;
}

END {
    $? = 10 if ($Errors || $Warnings);
    if ($?) {
	CORE::warn "Exiting due to errors\n";
	foreach my $file (keys %_Error_Unlink_Files) { unlink $file; }
    }
}

######################################################################
######################################################################
######################################################################
# DANGER WILL ROBINSON!
# Prior to perl 5.6, Class::Struct's new didn't bless the arguments,
# or allow parameter initialization!  We'll override it!

sub structs {
    my $func = shift;
    Class::Struct::struct (@_);
    my $baseclass = $_[0];
    (my $overclass = $baseclass) =~ s/::Struct$//;
    if ($] < 5.006) {
	# Now override what class::struct created
	eval "
            package $overclass;
            sub ${func} {
		my \$class = shift;
		my \$self = new $baseclass;
		bless \$self, \$class;
		while (\@_) {
		    my \$param = shift; my \$value = shift;
		    eval (\"\\\$self->\$param(\\\$value);\");  # Slow, sorry.
		}
		return \$self;
	    }";
    } else {
	#print \"NEW \",join(' ',\@_),\"\\n\";
	eval "
            package $overclass;
            sub ${func} {
		my \$class = shift;
		my \$self = new $baseclass (\@_);
		bless \$self, \$class;
	    }";
    }
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::Subclass - Common routines for all classes

=head1 SYNOPSIS

  use Verilog::Netlist::Subclass;
  package Verilog::Netlist::Something;
  @ISA = qw(Verilog::Netlist::Subclass);

  ...

  $self->info("We're here\n");
  $self->warn("Things look bad\n");
  $self->error("Things are even worse\n");
  $self->exit_if_error();

=head1 DESCRIPTION

Verilog::Netlist::Subclass is used as a base class for all structures.
It is mainly used so that $self->warn() and $self->error() will produce
consistent results.

=head1 MEMBER FUNCTIONS

=over 4

=item $self->error (I<Text...>)

Print an error in a standard format.  

=item $self->exit_if_error()

Exits the program if any errors were detected.

=item $self->filename()

The filename number the entity was created in.

=item $self->info (I<Text...>)

Print a informational in a standard format.  

=item $self->lineno()

The line number the entity was created on.

=item $self->unlink_if_error (I<filename>)

Requests the given file be deleted if any errors are detected.  Used for
temporary files.

=item $self->userdata (I<key>)
=item $self->userdata (I<key>, I<data>)

Sets (with two arguments) or retrieves the specified key from an opaque
hash.  This may be used to store application data on the specified node.

=item $self->warn (I<Text...>)

Print a warning in a standard format.  

=back

=head1 DISTRIBUTION

The latest version is available from CPAN and from
L<http://www.veripool.com/verilog-perl.html>.

Copyright 2000-2005 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License or the Perl Artistic License.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog::Netlist>

=cut
