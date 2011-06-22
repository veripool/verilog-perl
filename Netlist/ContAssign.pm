# Verilog - Verilog Perl Interface
# See copyright, etc in below POD section.
######################################################################

package Verilog::Netlist::ContAssign;

use Verilog::Netlist;
use Verilog::Netlist::Subclass;
use vars qw($VERSION @ISA);
use strict;
@ISA = qw(Verilog::Netlist::ContAssign::Struct
	Verilog::Netlist::Subclass);

$VERSION = '3.307';

structs('new',
	'Verilog::Netlist::ContAssign::Struct'
	=>[name    	=> '$', #'	# Unique ID
	   keyword    	=> '$', #'	# Keyword name
	   filename 	=> '$', #'	# Filename this came from
	   lineno	=> '$', #'	# Linenumber this came from
	   userdata	=> '%',		# User information
	   attributes	=> '%', #'	# Misc attributes for systemperl or other processors
	   #
	   lhs		=> '$', #'	# Left hand side of assignment
	   rhs		=> '$', #'	# Right hand side of assignment
	   module	=> '$', #'	# Module reference
	   ]);

sub delete {
    my $self = shift;
    my $h = $self->module->_statements;
    delete $h->{$self->name};
    return undef;
}

######################################################################
#### Methods

sub logger {
    my $self = shift;
    return $self->netlist->logger;
}
sub netlist {
    my $self = shift;
    return $self->module->netlist;
}

sub lint {}
sub link {}

sub verilog_text {
    my $self = shift;
    my @out = ($self->keyword," ",$self->lhs," = ",$self->rhs,";");
    return (wantarray ? @out : join('',@out));
}

sub dump {
    my $self = shift;
    my $indent = shift||0;
    print " "x$indent,"ContAssign:",$self->keyword,"  lhs:",$self->lhs,"  rhs:",$self->rhs;
    print "\n";
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::ContAssign - ContAssign assignment

=head1 SYNOPSIS

  use Verilog::Netlist;

  ...
  foreach my $cont ($module->statements)
    print $cont->name;

=head1 DESCRIPTION

A Verilog::Netlist::ContAssign object is created by Verilog::Netlist for
every continuous assignment statement in the current module.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->keyword

Keyword used to declare the assignment.  Currently "assign" is the only
supported value.

=item $self->lhs

Left hand side of the assignment.

=item $self->module

Pointer to the module the cell is in.

=item $self->netlist

Reference to the Verilog::Netlist the cell is under.

=item $self->rhs

Right hand side of the assignment.

=back

=head1 MEMBER FUNCTIONS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->dump

Prints debugging information for this cell.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2000-2011 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
