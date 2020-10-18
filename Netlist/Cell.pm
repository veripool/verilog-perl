# Verilog - Verilog Perl Interface
# See copyright, etc in below POD section.
######################################################################

package Verilog::Netlist::Cell;

use Verilog::Netlist;
use Verilog::Netlist::Subclass;
use vars qw($VERSION @ISA);
use strict;
@ISA = qw(Verilog::Netlist::Cell::Struct
	Verilog::Netlist::Subclass);

$VERSION = '3.472';

structs('new',
	'Verilog::Netlist::Cell::Struct'
	=>[name     	=> '$', #'	# Instantiation name
	   filename 	=> '$', #'	# Filename this came from
	   lineno	=> '$', #'	# Linenumber this came from
	   userdata	=> '%',		# User information
	   attributes	=> '%', #'	# Misc attributes for systemperl or other processors
	   #
	   comment	=> '$', #'	# Comment provided by user
	   submodname	=> '$', #'	# Which module it instantiates
	   module	=> '$', #'	# Module reference
	   params	=> '$', #'	# Textual description of parameters
	   range	=> '$', #'	# Range of ranged instance
	   _pins	=> '%',		# List of Verilog::Netlist::Pins
	   byorder 	=> '$',		# True if Cell call uses order based pins
	   # after link():
	   submod	=> '$', #'	# Sub Module reference
	   gateprim	=> '$', #'	# Primitive (and/buf/cmos etc), but not UDPs
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

sub logger {
    my $self = shift;
    return $self->netlist->logger;
}
sub netlist {
    my $self = shift;
    return $self->module->netlist;
}

sub _link_guts {
    my $self = shift;
    # This function is HOT, keep simple
    if (!$self->submod) {
	if (my $name = $self->submodname) {
	    my $netlist = $self->netlist;
	    my $sm = $netlist->find_module_or_interface_for_cell($name);
	    if (!$sm) {
		my $name2 = $netlist->remove_defines($name);
		$sm = $netlist->find_module_or_interface_for_cell($name2)
		    if $name ne $name2;
	    }
	    if ($sm) {
		$self->submod($sm);
		$sm->is_top(0);
	    }
	}
    }
}
sub _link {
    my $self = shift;
    # This function is HOT, keep simple
    $self->_link_guts();
    if (!$self->submod && Verilog::Language::is_gateprim($self->submodname)) {
	$self->gateprim(1);
    }
    if (!$self->submod()
	&& !$self->gateprim
	&& !$self->module->is_libcell()
	&& $self->netlist->{link_read}
	&& !$self->netlist->{_missing_submod}{$self->submodname}
	) {
	print "  Link_Read ",$self->submodname,"\n" if $Verilog::Netlist::Debug;
	# Try 1: Direct filename
	$self->netlist->read_file(filename=>$self->submodname, error_self=>0);
	$self->_link_guts();
	#
	# Try 2: Libraries
	if (!$self->submod()) {
	    $self->netlist->read_libraries();
	    $self->_link_guts();
	}
	# Try 3: Bitch about missing file
	if (!$self->submod()) {
	    $self->netlist->read_file(filename=>$self->submodname,
				      error_self=>($self->netlist->{link_read_nonfatal} ? 0:$self));
	}
	# Still missing
	if (!$self->submod()) {
	    # Don't link this file again - speeds up if many common gate-ish missing primitives
	    $self->netlist->{_missing_submod}{$self->submodname} = 1;
	}
	# Note if got it the new_module will add it to the _need_link list
    }
    # Link pins after module resolved, so don't do it multiple times if not found
    foreach my $pinref ($self->pins) {
	$pinref->_link();
    }
}

sub lint {
    my $self = shift;
    if (!$self->submod() && !$self->gateprim && !$self->netlist->{link_read_nonfatal}) {
        $self->error($self,"Module/Program/Interface reference not found: ",$self->submodname(),,"\n");
    }
    if ($self->netlist->{use_vars}) {
	foreach my $pinref ($self->pins) {
	    $pinref->lint();
	}
    }
}

sub verilog_text {
    my $self = shift;
    my @out = $self->submodname;
    if ($self->params) {
	push @out, " #(".$self->params.")";
    }
    push @out, " ".$self->name;
    if ($self->range) {
	push @out, " ".$self->range;
    }
    push @out, " (";
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
    print " ".$self->params if (($self->params||"") ne "");
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
    push @_, (cell=>$self);
    my $pinref = new Verilog::Netlist::Pin(@_);
    $self->_pins($pinref->name(), $pinref);
    return $pinref;
}

sub find_pin {
    my $self = shift;
    my $name = shift;
    return $self->_pins($name) || $self->_pins("\\".$name." ");
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
  my $cell = $module->find_cell('cellname');
  print $cell->name;

=head1 DESCRIPTION

A Verilog::Netlist::Cell object is created by Verilog::Netlist for every
instantiation in the current module.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->comment

Returns any comments following the definition.  keep_comments=>1 must be
passed to Verilog::Netlist::new for comments to be retained.

=item $self->delete

Delete the cell from the module it's under.

=item $self->gateprim

True if the cell is a gate primitive instantiation (buf/cmos/etc), but not
a UDP.

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

=item $self->range

The range for the cell (e.g. "[1:0]") or false (i.e. undef or "") if not
ranged.

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

Verilog-Perl is part of the L<https://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<https://www.veripool.org/verilog-perl>.

Copyright 2000-2020 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
