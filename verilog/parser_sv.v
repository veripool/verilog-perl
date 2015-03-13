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
   logic [7:0] addr, data[9];
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
   logic [7:0] 	data_, bork[2];
   assign      d_int = d_in + pkg_data;

   assign  modported_int.data = data_;

   always_ff @(posedge clk or negedge rst) begin
      if (~rst) d_out <= '0;
      else     d_out <= d_int;
   end

   property p1;
      @(posedge clk)
	disable iff(!rst)
	  $rose(d_int) |-> ##1 d_int;
   endproperty

   //a1:   assert property(p1) else $warning("\nProperty violated\n");
   c1:     cover  property(p1)  $display("\np1_cover\n");
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
   extern function int uses_class_type();
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

task vmm_more;
   file_is_a_string(`__FILE__,`__LINE__);
   foreach(this.text[i]) begin $display("%s\n", this.text[i]); end
   // Not part of 1800-2005 grammar, but likely in 1800-2009
   queue = '{};
   -> this.item_taken;
endtask

// Extern Functions/tasks when defined must scope to the class they're in to get appropriate types
function int vmm_cl_func_colon::uses_class_type(restart_e note_uses_class_type);
   var restart_e also_uses_class_type;
endfunction

module hidden_checks;
   typedef int T;
   sub (.T(123));  // Different T
   task hidden;
      typedef bit T;  // Different T
   endtask
endmodule

typedef struct packed signed {
      rand int m_a;
      bit [7:0] m_b;
   } t_bug91;
t_bug91 v_bug91;

module bug98(interfacex x_if);
   h inst_h(.push(x_if.pop));
endmodule

module bugas;
   initial begin
      ASSERT_CHK: assert (0) else $error("%m -- not allowed %d", 0);
   end
endmodule

typedef enum [2:0] { ENUM_RANGED_VALUE } enum_ranged_t;

typedef struct packed { logic val; } t_bug202_struct;
typedef union packed { logic val; } t_bug202_union;

class ln288;
   extern virtual function string extvirtstr;
   extern virtual task extvirttask;
endclass

class cl_to_init;
  extern function new();
  extern static function cl_to_init init();
endclass
function cl_to_init cl_to_init::init();
endfunction
function cl_to_init::new();
endfunction
cl_to_init cl_inited = cl_to_init::init();

// pure virtual functions have no endfunction.
virtual class pure_virt_func_class;
   pure virtual function string pure_virt_func();
   pure virtual task pure_virt_task();
endclass

class extend_base;
   typedef enum { EN_A, EN_B } base_enum;
   virtual function extend_base create(); return null; endfunction
endclass
class extended extends extend_base;
   typedef base_enum be_t;  // type must come from base class
   virtual function int create ();  // Must override base's create
      be_t mye;
   endfunction
endclass

task rand_with_ln320();
   if (!randomize(v) with { v > 0 && v < maxval; }) begin end
   if (randomize(null)) begin end
endtask
task apply_request(data_req, input bit randomize = 1);
   if (randomize == 1) begin
      data_req.randomize();  // Generic method, not std::randomize
   end
endtask

task foreach_class_scope_ln330;
   foreach (extended::some_array[i,j]) begin end
endtask

module clkif_334;
   always @(posedge top.clk iff !top.clken_l) begin end
endmodule

module gen_ln338;
   generate
      case (P)
	32'b0:    initial begin end
	default:  initial begin end
      endcase
   endgenerate
endmodule

module par_packed;
   parameter logic [31:0] P1 [3:0] = '{ 1, 2, 3, 4 } ; // unpacked array
   wire struct packed { logic ecc; logic [7:0] data; } memsig;
endmodule

module not_a_bug315;
   typedef int supply_net_t;
   input int i;
   input imp_test_pkg::byte_t i;
   input supply_net_t bug316;
endmodule

module bins_bracket;
   parameter N = 2;
   covergroup cg_debitor @(posedge eclk);
      count: coverpoint count iff (erst_n) {
         // 'std' overrides std:: package, which confuses VP
	 //bins  std[] = { [0:N] };
      }
   endgroup
endmodule

virtual class ovm_void;
endclass
virtual class ovm_port_base #(type IF=ovm_void) extends ovm_void;
endclass
virtual class uvm_build_phase #(type BASE=ovm_void) extends BASE;
   static const string type_name = "uvm_build_phase";
endclass

class bug627sub;
endclass
class bug627 #(type TYPE=bug627sub);
  typedef TYPE types_t[$];
  static function types_t f();
      $display("%s", { TYPE::type_name });
      return types;
  endfunction
endclass

interface if_bug777;
    wire a;
    modport master (input a);
    modport slave (output a);
endinterface
module bug777 (clk, ifport);
   input clk;
   if_bug777 ifport ();
   if_bug777.mp ifportmp;
   //if_bug777.mp ifportmp ();  // Not legal
   // Currently unsupported, parens required so VP knows is instance
   //if_bug777 ifport;
endmodule
module bug778 ();
   virtual if_bug777.master bar;
endmodule
class cls778;
   virtual if_bug777.master bar;
endclass : cls778;

module bug810 #(
		/*parameter*/ int unsigned DW = 32);
endmodule
interface test_if (input clk);
endinterface

module bug815 (
	       test_if bad[2]);
endmodule

module bug868 (ifmp);
   if_bug777.master ifmp;
endmodule
