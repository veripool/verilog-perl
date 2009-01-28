# Verilog - Verilog Perl Interface
# See copyright, etc in below POD section.
######################################################################

package Verilog::Netlist;
use Carp;
use IO::File;

use Verilog::Netlist::Module;
use Verilog::Netlist::File;
use Verilog::Netlist::Subclass;
use base qw(Verilog::Netlist::Subclass);
use strict;
use vars qw($Debug $Verbose $VERSION);

$VERSION = '3.110';

######################################################################
#### Error Handling

# Netlist file & line numbers don't apply
sub logger { return $_[0]->{logger}; }
sub filename { return 'Verilog::Netlist'; }
sub lineno { return ''; }

######################################################################
#### Creation

sub new {
    my $class = shift;
    my $self = {_modules => {},
		_files => {},
		options => undef,	# Usually pointer to Verilog::Getopt
		implicit_wires_ok => 1,
 		preproc => 'Verilog::Preproc',
		link_read => 1,
		logger => Verilog::Netlist::Logger->new,
		#include_open_nonfatal => 0,
		#keep_comments => 0,
		_libraries_done => {},
		@_};
    bless $self, $class;
    return $self;
}

######################################################################
#### Functions

sub link {
    my $self = shift;
    $self->{_relink} = 1;
    while ($self->{_relink}) {
	$self->{_relink} = 0;
	foreach my $modref ($self->modules) {
	    $modref->link();
	}
	foreach my $fileref ($self->files) {
	    $fileref->_link();
	}
    }
}
sub lint {
    my $self = shift;
    foreach my $modref ($self->modules_sorted) {
	next if $modref->is_libcell();
	$modref->lint();
    }
}

sub verilog_text {
    my $self = shift;
    my @out;
    foreach my $modref ($self->modules_sorted) {
	push @out, $modref->verilog_text, "\n";
    }
    return (wantarray ? @out : join('',@out));
}

sub dump {
    my $self = shift;
    foreach my $modref ($self->modules_sorted) {
	$modref->dump();
    }
}

######################################################################
#### Module access

sub new_module {
    my $self = shift;
    # @_ params
    # Can't have 'new Verilog::Netlist::Module' do this,
    # as not allowed to override Class::Struct's new()
    my $modref = new Verilog::Netlist::Module
	(netlist=>$self,
	 is_top=>1,
	 @_);
    $self->{_modules}{$modref->name} = $modref;
    return $modref;
}

sub defvalue_nowarn {
    my $self = shift;
    my $sym = shift;
    # Look up the value of a define, letting the user pick the accessor class
    if ($self->{options}) {
	return $self->{options}->defvalue_nowarn($sym);
    }
    return undef;
}

sub remove_defines {
    my $self = shift;
    my $sym = shift;
    my $val = "x";
    while (defined $val) {
	last if $sym eq $val;
	(my $xsym = $sym) =~ s/^\`//;
	$val = $self->defvalue_nowarn($xsym);  #Undef if not found
	$sym = $val if defined $val;
    }
    return $sym;
}

sub find_module {
    my $self = shift;
    my $search = shift;
    # Return module maching name
    my $mod = $self->{_modules}{$search};
    return $mod if $mod;
    # Allow FOO_CELL to be a #define to choose what instantiation is really used
    my $rsearch = $self->remove_defines($search);
    if ($rsearch ne $search) {
	return $self->find_module($rsearch);
    }
    return undef;
}

sub modules {
    my $self = shift;
    # Return all modules
    return (values %{$self->{_modules}});
}

sub modules_sorted {
    my $self = shift;
    # Return all modules
    return (sort {$a->name cmp $b->name} (values %{$self->{_modules}}));
}

sub modules_sorted_level {
    my $self = shift;
    # Return all modules
    return (sort {$a->level <=> $b->level || $a->name cmp $b->name}
	    (values %{$self->{_modules}}));
}

sub top_modules_sorted {
    my $self = shift;
    return grep ($_->is_top && !$_->is_libcell, $self->modules_sorted);
}

######################################################################
#### Files access

sub resolve_filename {
    my $self = shift;
    my $filename = shift;
    my $lookup_type = shift;
    if ($self->{options}) {
	$filename = $self->remove_defines($filename);
	$filename = $self->{options}->file_path($filename, $lookup_type);
    }
    if (!-r $filename || -d $filename) {
	return undef;
    }
    $self->dependency_in ($filename);
    return $filename;
}

sub new_file {
    my $self = shift;
    # @_ params
    # Can't have 'new Verilog::Netlist::File' do this,
    # as not allowed to override Class::Struct's new()
    my $fileref = new Verilog::Netlist::File
	(netlist=>$self,
	 @_);
    defined $fileref->name or carp "%Error: No name=> specified, stopped";
    $self->{_files}{$fileref->name} = $fileref;
    $fileref->basename (Verilog::Netlist::Module::modulename_from_filename($fileref->name));
    return $fileref;
}

sub find_file {
    my $self = shift;
    my $search = shift;
    # Return file maching name
    return $self->{_files}{$search};
}

sub files {
    my $self = shift; ref $self or die;
    # Return all files
    return (sort {$a->name() cmp $b->name()} (values %{$self->{_files}}));
}
sub files_sorted { return files(@_); }

sub read_file {
    my $self = shift;
    my $fileref = $self->read_verilog_file(@_);
    return $fileref;
}

sub read_verilog_file {
    my $self = shift;
    my $fileref = Verilog::Netlist::File::read
	(netlist=>$self,
	 @_);
    return $fileref;
}

sub read_libraries {
    my $self = shift;
    if ($self->{options}) {
	my @files = $self->{options}->library();
	foreach my $file (@files) {
	    if (!$self->{_libraries_done}{$file}) {
		$self->{_libraries_done}{$file} = 1;
		$self->read_file(filename=>$file, is_libcell=>1, );
		## $self->dump();
	    }
	}
    }
}

######################################################################
#### Dependencies

sub dependency_in {
    my $self = shift;
    my $filename = shift;
    $self->{_depend_in}{$filename} = 1;
}
sub dependency_out {
    my $self = shift;
    my $filename = shift;
    $self->{_depend_out}{$filename} = 1;
}

sub dependency_write {
    my $self = shift;
    my $filename = shift;

    my $fh = IO::File->new(">$filename") or die "%Error: $! writing $filename\n";
    print $fh "$filename";
    foreach my $dout (sort (keys %{$self->{_depend_out}})) {
	print $fh " $dout";
    }
    print $fh " :";
    foreach my $din (sort (keys %{$self->{_depend_in}})) {
	print $fh " $din";
    }
    print $fh "\n";
    $fh->close();
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist - Verilog Netlist

=head1 SYNOPSIS

    use Verilog::Netlist;

    # Setup options so files can be found
    use Verilog::Getopt;
    my $opt = new Verilog::Getopt;
    $opt->parameter( "+incdir+verilog",
		     "-y","verilog",
		     );

    # Prepare netlist
    my $nl = new Verilog::Netlist (options => $opt,);
    foreach my $file ('testnetlist.v') {
	$nl->read_file (filename=>$file);
    }
    # Read in any sub-modules
    $nl->link();
    $nl->lint();
    $nl->exit_if_error();

    foreach my $mod ($nl->top_modules_sorted) {
	show_hier ($mod, "  ", "", "");
    }

    sub show_hier {
	my $mod = shift;
	my $indent = shift;
	my $hier = shift;
	my $cellname = shift;
	if (!$cellname) {$hier = $mod->name;} #top modules get the design name
	else {$hier .= ".$cellname";} #append the cellname
	printf ("%-45s %s\n", $indent."Module ".$mod->name,$hier);
	foreach my $sig ($mod->ports_sorted) {
	    printf ($indent."	  %sput %s\n", $sig->direction, $sig->name);
	}
	foreach my $cell ($mod->cells_sorted) {
	    printf ($indent. "    Cell %s\n", $cell->name);
	    foreach my $pin ($cell->pins_sorted) {
		printf ($indent."     .%s(%s)\n", $pin->name, $pin->netname);
	    }
	    show_hier ($cell->submod, $indent."	 ", $hier, $cell->name) if $cell->submod;
	}
    }

=head1 DESCRIPTION

Verilog::Netlist reads and holds interconnect information about a whole
design database.

See the "Which Package" section of L<Verilog::Language> if you are unsure
which parsing package to use for a new application.

A Verilog::Netlist is composed of files, which contain the text read from
each file.

A file may contain modules, which are individual blocks that can be
instantiated (designs, in Synopsys terminology.)

Modules have ports, which are the interconnection between nets in that
module and the outside world.  Modules also have nets, (aka signals), which
interconnect the logic inside that module.

Modules can also instantiate other modules.  The instantiation of a module
is a Cell.  Cells have pins that interconnect the referenced module's pin
to a net in the module doing the instantiation.

Each of these types, files, modules, ports, nets, cells and pins have a
class.  For example Verilog::Netlist::Cell has the list of
Verilog::Netlist::Pin (s) that interconnect that cell.

=head1 FUNCTIONS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $netlist->lint

Error checks the entire netlist structure.

=item $netlist->link()

Resolves references between the different modules.

If link_read=>1 is passed when netlist->new is called (it is by default),
undefined modules will be searched for using the Verilog::Getopt package,
passed by a reference in the creation of the netlist.  To suppress errors
in any missing references, set link_read_nonfatal=>1 also.

If keep_comments=>1 is passed, comment fields will be entered on net
declarations into the Vtest::Netlist::Net structures.  Otherwise all
comments are stripped for speed.

=item $netlist->new

Creates a new netlist structure.  Pass optional parameters by name,
with the following parameters:

=over 8

=item options => $opt_object

An optional pointer to a Verilog::Getopt object, to be used for locating
files.

=item implicit_wires_ok => $true_or_false

Indicates whether to allow undeclared wires to be used.

=item logger => object

Specify a message handler object to be used for error handling, this class
should be a Verilog::Netlist::Logger object, or derived from one.  If
unspecified, a Verilog::Netlist::Logger local to this netlist will be
used.

=item preproc => $package_name

The name of the preprocessor class. Defaults to "Verilog::Preproc".

=item link_read => $true_or_false

Indicates whether or not the parser should automatically search for
undefined modules through the "options" object.

=item include_open_nonfatal => $true_or_false

Indicates that include files that do not exist should be ignored.

=item keep_comments => $true_or_false

Indicates that comments should be preserved in the structure (slower).

=back

=item $netlist->dump

Prints debugging information for the entire netlist structure.

=back

=head1 MODULE FUNCTIONS

=over 4

=item $netlist->find_module($name)

Returns Verilog::Netlist::Module matching given name.

=item $netlist->modules

Returns list of Verilog::Netlist::Module.

=item $netlist->modules_sorted

Returns name sorted list of Verilog::Netlist::Module.

=item $netlist->modules_sorted_level

Returns level sorted list of Verilog::Netlist::Module.  Leaf modules will
be first, the top most module will be last.

=item $netlist->new_module

Creates a new Verilog::Netlist::Module.

=item $netlist->top_modules_sorted

Returns name sorted list of Verilog::Netlist::Module, only for those
modules which have no children and are not unused library cells.

=back

=head1 FILE FUNCTIONS

=over 4

=item $netlist->dependency_write(I<filename>)

Writes a dependency file for make, listing all input and output files.

=item $netlist->defvalue_nowarn (I<define>)

Return the value of the specified define or undef.

=item $netlist->dependency_in(I<filename>)

Adds an additional input dependency for dependency_write.

=item $netlist->dependency_out(I<filename>)

Adds an additional output dependency for dependency_write.

=item $netlist->files

Returns list of Verilog::Netlist::File.

=item $netlist->files_sorted

Returns a name sorted list of Verilog::Netlist::File.

=item $netlist->find_file($name)

Returns Verilog::Netlist::File matching given name.

=item $netlist->read_file( filename=>$name)

Reads the given Verilog file, and returns a Verilog::Netlist::File
reference.

Generally called as $netlist->read_file.  Pass a hash of parameters.  Reads
the filename=> parameter, parsing all instantiations, ports, and signals,
and creating Verilog::Netlist::Module structures.

=item $netlist->read_libraries ()

Read any libraries specified in the options=> argument passed with the
netlist constructor.  Automatically invoked when netlist linking results in
a module that wasn't found, and thus might be inside the libraries.

=item $netlist->remove_defines (I<string>)

Expand any `defines in the string and return the results.  Undefined
defines will remain in the returned string.

=item $netlist->resolve_filename (I<string>, [I<lookup-type>])

Convert a module name to a filename.  Optional lookup-type is
'module','include', or 'all', to use only module_dirs, incdirs, or both for
the lookup.  Return undef if not found.

=item $self->verilog_text

Returns verilog code which represents the netlist.

=back

=head1 BUGS

Cell instantiations without any arguments are not supported, a empty set of
parenthesis are required.  (Use "cell cell();", not "cell cell;".)

Order based pin interconnect is not supported, use name based connections.

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2000-2009 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License or the Perl Artistic License.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist::Cell>,
L<Verilog::Netlist::File>,
L<Verilog::Netlist::Logger>,
L<Verilog::Netlist::Module>,
L<Verilog::Netlist::Net>,
L<Verilog::Netlist::Pin>,
L<Verilog::Netlist::Port>,
L<Verilog::Netlist::Subclass>

And the L<http://www.veripool.org/verilog-mode>Verilog-Mode package for Emacs.

=cut
