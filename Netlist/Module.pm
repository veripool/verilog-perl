# Verilog - Verilog Perl Interface
# See copyright, etc in below POD section.
######################################################################

package Verilog::Netlist::Module;

use Verilog::Netlist;
use Verilog::Netlist::ContAssign;
use Verilog::Netlist::Defparam;
use Verilog::Netlist::Port;
use Verilog::Netlist::Net;
use Verilog::Netlist::Cell;
use Verilog::Netlist::Pin;
use Verilog::Netlist::Subclass;
use vars qw($VERSION @ISA);
use strict;
@ISA = qw(Verilog::Netlist::Module::Struct
	Verilog::Netlist::Subclass);

$VERSION = '3.468';

structs('new',
	'Verilog::Netlist::Module::Struct'
	=>[name     	=> '$', #'	# Name of the module
	   filename 	=> '$', #'	# Filename this came from
	   lineno	=> '$', #'	# Linenumber this came from
	   netlist	=> '$', #'	# Netlist is a member of
	   keyword	=> '$', #'	# Type of module
	   userdata	=> '%',		# User information
	   attributes	=> '%', #'	# Misc attributes for systemperl or other processors
	   #
	   attrs	=> '@',		# list of "category name[ =](.*)" strings
	   comment	=> '$', #'	# Comment provided by user
	   _ports	=> '%',		# hash of Verilog::Netlist::Ports
	   _portsordered=> '@',		# list of Verilog::Netlist::Ports as ordered in list of ports
	   _nets	=> '%',		# hash of Verilog::Netlist::Nets
	   _cells	=> '%',		# hash of Verilog::Netlist::Cells
	   _celldecls	=> '%',		# hash of declared cells (for autocell only)
	   _cellarray	=> '%',		# hash of declared cell widths (for autocell only)
	   _cellnum	=> '$',		# Number of next unnamed cell
	   _level	=> '$',		# Depth in hierarchy (if calculated)
	   _statements	=> '%',		# hash of Verilog::Netlist::ContAssigns
	   _stmtnum	=> '$',		# Number of next unnamed statement
	   is_top	=> '$', #'	# Module is at top of hier (not a child)
	   is_libcell	=> '$', #'	# Module is a library cell
	   # SystemPerl:
	   _autocovers  => '%', #'	# Hash of covers found in code
	   _autosignal	=> '$', #'	# Module has /*AUTOSIGNAL*/ in it
	   _autosubcells=> '$', #'	# Module has /*AUTOSUBCELL_DECL*/ in it
	   _autotrace	=> '%', #'	# Module has /*AUTOTRACE*/ in it
	   _autoinoutmod=> '$', #'	# Module has /*AUTOINOUT_MODULE*/ in it
	   _pintemplates=> '@', #'	# Module SP_TEMPLATEs
	   _ctor	=> '$', #'	# Module has SC_CTOR in it
	   _code_symbols=> '$', #'	# Hash ref of symbols found in raw code
	   _covergroups => '%', #'	# Hash of covergroups found in code
	   lesswarn     => '$',	#'	# True if some warnings should be disabled
	   ]);

sub delete {
    my $self = shift;
    foreach my $oref ($self->nets) {
	$oref->delete;
    }
    foreach my $oref ($self->ports) {
	$oref->delete;
    }
    foreach my $oref ($self->cells) {
	$oref->delete;
    }
    foreach my $oref ($self->statements) {
	$oref->delete;
    }
    my $h = $self->netlist->{_modules};
    delete $h->{$self->name};
    return undef;
}

######################################################################

sub logger {
    return $_[0]->netlist->logger;
}

sub modulename_from_filename {
    my $filename = shift;
    (my $module = $filename) =~ s/.*\///;
    $module =~ s/\.[a-z]+$//;
    return $module;
}

sub find_port {
    my $self = shift;
    my $search = shift;
    return $self->_ports->{$search} || $self->_ports->{"\\".$search." "};
}
sub find_port_by_index {
    my $self = shift;
    my $myindex = shift;
    # @{$self->_portsordered}[$myindex-1] returns the name of
    # the port in the module at this index.  Then, this is
    # used to find the port reference via the port hash
    my $name = @{$self->_portsordered}[$myindex-1];
    return undef if !$name;
    return $self->_ports->{$name};
}
sub find_cell {
    my $self = shift;
    my $search = shift;
    return $self->_cells->{$search} || $self->_cells->{"\\".$search." "};
}
sub find_net {
    my $self = shift;
    my $search = shift;
    my $rtn = $self->_nets->{$search}||"";
    #print "FINDNET ",$self->name, " SS $search  $rtn\n";
    return $self->_nets->{$search} || $self->_nets->{"\\".$search." "};
}

sub attrs_sorted {
    return (sort {$a cmp $b} @{$_[0]->attrs});
}
sub nets {
    return (values %{$_[0]->_nets});
}
sub nets_sorted {
    return (sort {$a->name() cmp $b->name()} (values %{$_[0]->_nets}));
}
sub ports {
    return (values %{$_[0]->_ports});
}
sub ports_sorted {
    return (sort {$a->name() cmp $b->name()} (values %{$_[0]->_ports}));
}
sub ports_ordered {
    my $self = shift;
    return map {$self->_ports->{$_}} @{$self->_portsordered};
}
sub cells {
    return (values %{$_[0]->_cells});
}
sub cells_sorted {
    return (sort {$a->name() cmp $b->name()} (values %{$_[0]->_cells}));
}
sub statements {
    return (values %{$_[0]->_statements});
}
sub statements_sorted {
    return (sort {$a->name() cmp $b->name()} (values %{$_[0]->_statements}));
}

sub nets_and_ports_sorted {
    my $self = shift;
    my @list = ($self->nets, $self->ports,);
    my @outlist; my $last = "";
    # Eliminate duplicates
    foreach my $e (sort {$a->name() cmp $b->name()} (@list)) {
	next if $e eq $last;
	push @outlist, $e;
	$last = $e;
    }
    return (@outlist);
}

sub new_net {
    my $self = shift;
    my %params = @_;

    # Create a new net under this
    my $netref;
    if (defined($params{msb})) {
	my $data_type;
	$data_type = "[".($params{msb});
	$data_type .= ":".($params{lsb}) if defined $params{lsb};
	$data_type .= "]";
	$netref = new Verilog::Netlist::Net(decl_type=>'net',
					    net_type => 'wire',
					    data_type => $data_type,
					    %params,
					    module => $self);
    } else {
	$netref = new Verilog::Netlist::Net(decl_type => 'net',
					    net_type => 'wire',
					    %params,
					    module => $self);
    }
    $self->_nets($netref->name(), $netref);
    return $netref;
}

sub new_attr {
    my $self = shift;
    my $clean_text = shift;
    push @{$self->attrs}, $clean_text;
}

sub new_port {
    my $self = shift;
    # @_ params
    # Create a new port under this module
    my $portref = new Verilog::Netlist::Port(@_, module=>$self,);
    $self->_ports($portref->name(), $portref);
    return $portref;
}

sub new_cell {
    my $self = shift;
    my %params = @_; # name=>, filename=>, lineno=>, submodname=>, params=>
    # Create a new cell under this module
    if (!defined $params{name} || $params{name} eq '') {
	# Blank instance name; invent a new one; use the next instance number in this module t$
	$self->_cellnum(($self->_cellnum||0) + 1);
	$params{name} = '__unnamed_instance_' . $self->_cellnum;
    }
    if (my $preexist = $self->find_cell($params{name})) {
	$self->_cellnum(($self->_cellnum||0) + 1);
	$params{name} .= '__duplicate_' . $self->_cellnum;
    }
    # Create a new cell; pass the potentially modified options
    my $cellref = new Verilog::Netlist::Cell(%params, module=>$self,);
    # Add the new cell to the hash of cells in this module
    $self->_cells($params{name}, $cellref);
    return $cellref;
}

sub new_contassign {
    my $self = shift;
    my %params = @_; # name=>, filename=>, lineno=>, keyword=> etc
    # Create a new statement under this module
    if (!defined $params{name} || $params{name} eq '') {
	# Blank instance name; invent a new one; use the next instance number in this module t$
	$self->_stmtnum(($self->_stmtnum||0) + 1);
	$params{name} = '__unnamed_statement_' . $self->_stmtnum;
    }
    # Create a new object; pass the potentially modified options
    my $newref = new Verilog::Netlist::ContAssign(%params, module=>$self,);
    # Add the new object to the hash of statements in this module
    $self->_statements($params{name}, $newref);
    return $newref;
}

sub new_defparam {
    my $self = shift;
    my %params = @_; # name=>, filename=>, lineno=>, keyword=> etc
    # Create a new statement under this module
    if (!defined $params{name} || $params{name} eq '') {
	# Blank instance name; invent a new one; use the next instance number in this module t$
	$self->_stmtnum(($self->_stmtnum||0) + 1);
	$params{name} = '__unnamed_statement_' . $self->_stmtnum;
    }
    # Create a new object; pass the potentially modified options
    my $newref = new Verilog::Netlist::Defparam(%params, module=>$self,);
    # Add the new object to the hash of statements in this module
    $self->_statements($params{name}, $newref);
    return $newref;
}

sub level {
    my $self = shift;
    my $level = $self->_level;
    return $level if defined $level;
    $self->_level(1);  # Set before recurse in case there's circular module refs
    foreach my $cell ($self->cells) {
	if ($cell->submod) {
	    my $celllevel = $cell->submod->level;
	    $self->_level($celllevel+1) if $celllevel >= $self->_level;
	}
    }
    return $self->_level;
}

sub link {
    my $self = shift;
    # Ports create nets, so link ports before nets
    foreach my $portref ($self->ports) {
	$portref->_link();
    }
    foreach my $netref ($self->nets) {
	$netref->_link();
    }
    foreach my $cellref ($self->cells) {
	$cellref->_link();
    }
}

sub lint {
    my $self = shift;
    if ($self->netlist->{use_vars}) {
	foreach my $portref ($self->ports) {
	    $portref->lint();
	}
	foreach my $netref ($self->nets) {
	    $netref->lint();
	}
    }
    foreach my $cellref ($self->cells) {
	$cellref->lint();
    }
    foreach my $oref ($self->statements) {
	$oref->lint();
    }
}

sub verilog_text {
    my $self = shift;
    my @out = ($self->keyword||'module')." ".$self->name." (\n";
    my $indent = "   ";
    # Port list
    my $comma="";
    push @out, $indent;
    foreach my $portref ($self->ports_sorted) {
	push @out, $comma, $portref->verilog_text;
	$comma = ", ";
    }
    push @out, ");\n";

    # Signal list
    foreach my $netref ($self->nets_sorted) {
	push @out, $indent, $netref->verilog_text, "\n";
    }
    # Cell list
    foreach my $cellref ($self->cells_sorted) {
	push @out, $indent, $cellref->verilog_text, "\n";
    }
    foreach my $oref ($self->statements_sorted) {
	push @out, $indent, $oref->verilog_text, "\n";
    }

    push @out, "end".($self->keyword||'module')."\n";
    return (wantarray ? @out : join('',@out));
}

sub dump {
    my $self = shift;
    my $indent = shift||0;
    my $norecurse = shift;
    print " "x$indent,"Module:",$self->name(),"  Kwd:",($self->keyword||''),"  File:",$self->filename(),"\n";
    if (!$norecurse) {
	foreach my $portref ($self->ports_sorted) {
	    $portref->dump($indent+2);
	}
	foreach my $netref ($self->nets_sorted) {
	    $netref->dump($indent+2);
	}
	foreach my $cellref ($self->cells_sorted) {
	    $cellref->dump($indent+2);
	}
	foreach my $cellref ($self->statements_sorted) {
	    $cellref->dump($indent+2);
	}
    }
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::Module - Module within a Verilog Netlist

=head1 SYNOPSIS

  use Verilog::Netlist;

  ...
  my $module = $netlist->find_module('modname');
  my $cell = $self->find_cell('name')
  my $port =  $self->find_port('name')
  my $net =  $self->find_net('name')

=head1 DESCRIPTION

A Verilog::Netlist::Module object is created by Verilog::Netlist for every
module, macromodule, primitive or program in the design.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->cells

Returns list of references to Verilog::Netlist::Cell in the module.

=item $self->cells_sorted

Returns list of name sorted references to Verilog::Netlist::Cell in the module.

=item $self->comment

Returns any comments following the definition.  keep_comments=>1 must be
passed to Verilog::Netlist::new for comments to be retained.

=item $self->find_port_by_index

Returns the port name associated with the given index.  Indexes start at 1
(pin numbers are traditionally counted from pin 1..pin N, not starting at
zero.  This was probably an unfortunate choice, sorry.)

=item $self->is_top

Returns true if the module has no cells referencing it (is at the top of the hierarchy.)

=item $self->keyword

Returns the keyword used to declare the module ("module", "macromodule",
"primitive" or "program".)  It might at first not seem obvious that
programs are considered modules, but in most cases they contain the same
type of objects so can be handled identically.

=item $self->name

The name of the module.

=item $self->netlist

Reference to the Verilog::Netlist the module is under.

=item $self->nets

Returns list of references to Verilog::Netlist::Net in the module.

=item $self->nets_sorted

Returns list of name sorted references to Verilog::Netlist::Net in the module.

=item $self->nets_and_ports_sorted

Returns list of name sorted references to Verilog::Netlist::Net and
Verilog::Netlist::Port in the module.

=item $self->ports

Returns list of references to Verilog::Netlist::Port in the module.

=item $self->ports_ordered

Returns list of references to Verilog::Netlist::Port in the module sorted
by pin number.

=item $self->ports_sorted

Returns list of references to Verilog::Netlist::Port in the module sorted
by name.

=item $self->statements

Returns list of references to Verilog::Netlist::ContAssign in the module.
Other statement types (Always, etc) may also be added to this list in the
future.

=item $self->statements_sorted

Returns list of name sorted references to Verilog::Netlist::ContAssign in
the module.  Other statement types (Always, etc) may also be added to this
list in the future.

=back

=head1 MEMBER FUNCTIONS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->find_cell(I<name>)

Returns Verilog::Netlist::Cell matching given name.

=item $self->find_port(I<name>)

Returns Verilog::Netlist::Port matching given name.

=item $self->find_net(I<name>)

Returns Verilog::Netlist::Net matching given name.

=item $self->is_libcell

Returns if module declared inside a `celldefine.

=item $self->level

Returns the reverse depth of this module with respect to other modules.
Leaf modules (modules with no cells) will be level 1.  Modules which
instantiate cells of level 1 will be level 2 modules and so forth.  See
also Netlist's modules_sorted_level.

=item $self->lint

Checks the module for errors.

=item $self->link

Creates interconnections between this module and other modules.

=item $self->modulename_from_filename

Uses a rough algorithm (drop the extension) to convert a filename to the
module that is expected to be inside it.

=item $self->new_cell

Creates a new Verilog::Netlist::Cell.

=item $self->new_port

Creates a new Verilog::Netlist::Port.

=item $self->new_net

Creates a new Verilog::Netlist::Net.

=item $self->dump

Prints debugging information for this module.

=item $self->verilog_text

Returns verilog code which represents this module.  Returned as an array
that must be joined together to form the final text string.  The netlist
must be already ->link'ed for this to work correctly.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2000-2019 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
