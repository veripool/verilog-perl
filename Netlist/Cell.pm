# Verilog - Verilog Perl Interface
# $Id$
# Author: Wilson Snyder <wsnyder@wsnyder.org>
######################################################################
#
# Copyright 2000-2006 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
######################################################################

package Verilog::Netlist::Cell;
use Class::Struct;

use Verilog::Netlist;
use Verilog::Netlist::Subclass;
@ISA = qw(Verilog::Netlist::Cell::Struct
	Verilog::Netlist::Subclass);
$VERSION = '2.360';
use strict;

structs('new',
	'Verilog::Netlist::Cell::Struct'
	=>[name     	=> '$', #'	# Instantiation name
	   filename 	=> '$', #'	# Filename this came from
	   lineno	=> '$', #'	# Linenumber this came from
	   userdata	=> '%',		# User information
	   attributes	=> '%', #'	# Misc attributes for systemperl or other processors
	   #
	   submodname	=> '$', #'	# Which module it instantiates
	   module	=> '$', #'	# Module reference
	   params	=> '$', #'	# Textual description of parameters
	   _pins	=> '%',		# List of Verilog::Netlist::Pins
	   byorder 	=> '$',		# True if Cell call uses order based pins
	   # after link():
	   submod	=> '$', #'	# Sub Module reference
	   # system perl
	   _autoinst	=> '$', #'	# Marked with AUTOINST tag
	   ]);

sub delete {
    my $self = shift;
    foreach my $pinref ($self->pins_sorted) {
	$pinref->delete;
    }
    my $h = $self->module->_cells;
    delete $h->{$self->name};
    return undef;
}

######################################################################
#### Methods

sub netlist {
    my $self = shift;
    return $self->module->netlist;
}

sub _link_guts {
    my $self = shift;
    if ($self->submodname()) {
	my $name = $self->submodname();
	my $sm = $self->netlist->find_module ($self->submodname());
	if (!$sm) {
	    $sm = $self->netlist->find_module ($self->netlist->remove_defines($self->submodname()));
	}
	$self->submod($sm);
	$sm->is_top(0) if $sm;
    }
    foreach my $pinref ($self->pins) {
	$pinref->_link();
    }
}
sub _link {
    my $self = shift;
    $self->_link_guts();
    if (!$self->submod()
	&& !$self->netlist->{_relink}
	&& !$self->module->is_libcell()
	&& $self->netlist->{link_read}) {
	print "  Link_Read ",$self->submodname,"\n" if $Verilog::Netlist::Debug;
	# Try 1: Direct filename
	$self->netlist->read_file(filename=>$self->submodname, error_self=>0);
	$self->_link_guts();
	# Try 2: Libraries
	if (!$self->submod()) {
	    $self->netlist->read_libraries();
	}
	$self->_link_guts();
	# Try 3: Bitch about missing file
	if (!$self->submod()) {
	    $self->netlist->read_file(filename=>$self->submodname,
				      error_self=>($self->netlist->{link_read_nonfatal} ? 0:$self));
	}
	# Got it; ask for another link
	if ($self->submod()) {
	    $self->netlist->{_relink} = 1;
	}
    }
}

sub lint {
    my $self = shift;
    if (!$self->submod() && !$self->netlist->{link_read_nonfatal}) {
        $self->error ($self,"Module reference not found: ",$self->submodname(),,"\n");
    }
    if (!$self->netlist->{skip_pin_interconnect}) {
	foreach my $pinref ($self->pins) {
	    $pinref->lint();
	}
    }
}

sub verilog_text {
    my $self = shift;
    my @out = $self->submodname." ".$self->name." (";
    my $comma="";
    foreach my $pinref ($self->pins_sorted) {
	push @out, $comma if $comma; $comma=", ";
	push @out, $pinref->verilog_text;
    }
    push @out, ");";
    return (wantarray ? @out : join('',@out));
}

sub dump {
    my $self = shift;
    my $indent = shift||0;
    my $norecurse = shift;
    print " "x$indent,"Cell:",$self->name(),"  is-a:",$self->submodname();
    print " ".$self->params if defined $self->params;
    print "\n";
    if ($self->submod()) {
	$self->submod->dump($indent+10, 'norecurse');
    }
    if (!$norecurse) {
	foreach my $pinref ($self->pins_sorted) {
	    $pinref->dump($indent+2);
	}
    }
}

######################################################################
#### Pins

sub new_pin {
    my $self = shift;
    # @_ params
    # Create a new pin under this cell
    my $pinref = new Verilog::Netlist::Pin (cell=>$self, @_);
    $self->portname($self->name) if !$self->name;	# Back Version 1.000 compatibility
    $self->_pins ($pinref->name(), $pinref);
    return $pinref;
}

sub find_pin {
    my $self = shift;
    my $name = shift;
    return $self->_pins($name);
}

sub pins {
    return (values %{$_[0]->_pins});
}

sub pins_sorted {
    return (sort {$a->name() cmp $b->name()} (values %{$_[0]->_pins}));
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::Cell - Instantiated cell within a Verilog Netlist

=head1 SYNOPSIS

  use Verilog::Netlist;

  ...
  my $cell = $module->find_cell ('cellname');
  print $cell->name;

=head1 DESCRIPTION

Verilog::Netlist creates a cell for every instantiation in the current
module.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->delete

Delete the cell from the module it's under.

=item $self->module

Pointer to the module the cell is in.

=item $self->name

The instantiation name of the cell.

=item $self->netlist

Reference to the Verilog::Netlist the cell is under.

=item $self->pins

List of Verilog::Netlist::Pin connections for the cell.

=item $self->pins_sorted

List of name sorted Verilog::Netlist::Pin connections for the cell.

=item $self->submod

Reference to the Verilog::Netlist::Module the cell instantiates.  Only
valid after the design is linked.

=item $self->submodname

The module name the cell instantiates (under the cell).

=back

=head1 MEMBER FUNCTIONS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->lint

Checks the cell for errors.  Normally called by Verilog::Netlist::lint.

=item $self->new_pin

Creates a new Verilog::Netlist::Pin connection for this cell.

=item $self->pins_sorted

Returns all Verilog::Netlist::Pin connections for this cell.

=item $self->dump

Prints debugging information for this cell.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.com/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.com/verilog-perl.html>.

Copyright 2000-2006 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License or the Perl Artistic License.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
