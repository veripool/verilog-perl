package mypackage;
   bit [7:0] pkg_addr;
   bit [7:0] pkg_data;
endpackage

module times ();
   time x;
   initial x = 33ns;	// Note no space
endmodule : times

interface itf #(parameter num_of_cli = 0);
   logic blabla;
   logic [7:0] addr, data;
   modport Master(input data, date_delayed, output addr);
endinterface : itf

module test (
   itf whole_int,
   itf.test modported_int,
   input logic clk, rst,
   input logic d_in,
   output logic d_out
   );

   import mypackage::*;

   logic 	d_int;
   logic [7:0] 	data_;
   assign      d_int = d_in + pkg_data;

   assign  modported_int.data = data_;

   always_ff @(posedge clk or negedge rst) begin
      if (~rst) d_out <= '0;
      else     d_out <= d_int;
   end

//   property p1;
//      @(posedge clk)
//	disable iff(!rst)
//	  $rose(d_int) |-> ##1 d_int;
//   endproperty
//
//   a1:     assert property(p1) else $warning("\nProperty violated\n");
//   c1:     cover  property(p1)  $display("\np1_cover\n");
endmodule : test

// Different ways of declaring pins/vars
module line49_diff_pins1 (
    input in_nw,		// Input, no type
    input [1:0] in_vec[2:0],	// Input, implicit
    input in_nvec,		// Isn't vectorized
    output logic out_logic,	// Output and var
    output out_also_logic	// "logic" sticks
 );
endmodule
module line49_diff_pins2 (in2_nw, in2_vec, out2reg);

   input       in2_nw;
   input [1:0] in2_vec [2:0];
   output reg  out2_reg;
   input signed in2_signed;

   var 		var1_imp;
   var [1:0]	var1_imp_vec [2:0];
   var reg	var1_imp_reg;
   var logic	var1_imp_logic;
endmodule

program automatic first_prog;
   int i;
endprogram

// Importing
package imp_test_pkg;
   typedef logic [7:0] byte_t;
   typedef logic [15:0] word_t;
   function afunc(integer w); afunc=0; endfunction
endpackage
module imp_test_mod;
   import imp_test_pkg::byte_t;
   byte_t some_byte;
endmodule
module imp_test_mod2;
   import imp_test_pkg::*;
   word_t some_word;
endmodule
module imp_test_mod3
  ( input imp_test_pkg::word_t wordin );
   localparam FROM_FUNC = imp_test_pkg::afunc(1);
endmodule

module var_unnamed_block;
   initial begin
      integer var_in_unnamed;
   end
endmodule

module cell_with_typeparam;
   addr #(.PARAMTYPE(integer)) acell ();
endmodule

module arrayed_wire;
   wire [3:0][7:0] n2;
endmodule

task empty_task;  // sv design book
endtask
task empty_task2;  // sv design book
   integer i;
endtask

task check_casts;
   typedef integer integer_t;
   sum = a + integer '(3);
   sum = a + integer_t '(3);
   sum = a + 10'(3);
endtask

module comma_assign;
   int n[1:2][1:3] = '{'{0,1,2}, '{3{4}}};
endmodule

task typed_pattern;
   typedef int triple [1:3];
   $mydisplay(triple'{0,1,2});
endtask

virtual class VclassWCopy;
   extern function new();
   virtual function VclassWCopy copy(input VclassWCopy src=null);
   endfunction
endclass : VclassWCopy
function VclassWCopy::new();
endfunction : new

typedef class FwdClass;
function bit [3:0] FwdClass::ffunc (bit [3:0] in);
   ffunc = in;
endfunction : ffunc

function VclassWCopy VclassWCopy::copy
  (input VclassWCopy to);
   dst = new();
endfunction : copy

task foreach_memref;
   bit [0:52] [7:0] mem;
   // It's *not* legal according to the grammar to have dotted/package ids here
   foreach (mem[i]) $write("i=%x ", mem[i]); $display;
endtask

typedef class PreTypedefedClass;
class PreTypedefedClass;
   extern function new();
endclass
typedef class PreTypedefedClass;

class NewInNew;
  function new;
     s_self = new;
  endfunction : new
endclass

// std package
class TryStd;
   semaphore s1;
   std::semaphore s2;
   mailbox #(integer) m1;
   std::mailbox m2;
   process p1;
   std::process p2;
endclass

module cg_test1;
   covergroup counter1 @ (posedge cyc);
      cyc_bined : coverpoint cyc {
	 bins zero    = {0};
	 bins low    = {1,5};
	 bins mid   = {[5:$]};
      }
      value_and_toggle:
	cross cyc_value, toggle;
   endgroup
endmodule

task randomize_dotted();
   int	    vbl;
   assert(vbl.randomize());
endtask

module prop_parens;
   LABEL: cover property (@(posedge clk) ((foo[3:0] == 4'h0) & bar));
endmodule

class this_dot_tests;
   task ass;
      this.super.foo = this.bar;
   endtask
endclass

module sized_out
  #( parameter SZ = 4 )
   ( output logic [SZ-1:0] o_sized );
endmodule

class solve_size;
   rand byte arrayed[];
   rand bit b;
   // The dot below doesn't seem legal according to grammar, but
   // the intent makes sense, and it appears in the VMM
   constraint solve_a_b { solve arrayed.size before b; }
endclass

class vmm_stuff;
   task examples;
      void'(this.a.funccall(x));
      this.a.taskcall();
      super.new(name2);
   endtask
   extern static local function bit foo1();
   extern virtual protected function void foo2();
   protected static string foo3;
   extern function bit foo4();
   static local bit foo5[string];
endclass

class vmm_cl_func_colon;
   typedef enum int unsigned {FIRM} restart_e;
   function void do_all(vmm_cl_func_colon::restart_e kind = vmm_cl_func_colon::FIRM);
   endfunction
endclass

class vmm_cl_subenv;
   extern protected virtual task do_reset(vmm_cl_func_colon::restart_e kind = vmm_cl_func_colon::FIRM);
endclass

task empty_comma;
   extracomma1(,);
   extracomma2("a",);
   extracomma3("a",,"c");
   extracomma4(,"b");
endtask
