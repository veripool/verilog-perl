// Not legal:
// end : ADDRESS_TEST_BLOCK             // See 9.8.1
// `define at EOF with no newline

module bug26141 ();
   wire [0:3] b;
   wire a = b[2];
endmodule

module bug26940 ();
   (* attribute *)
   assign q = {1'b0,a} +{1'b0,b};

   adder u_add (.q(q),.a(d),.b(d));
   initial begin
      # 1;
      q=0;
      if (q!=0) $stop;
   end
endmodule

module bug26968 ();
   reg [4:0]  vect = 5'b10100;
   wire [4:0] tmp = { vect[0], vect[1], vect[2], vect[3], vect[4] };
   initial begin
      #1 $display("vect=%b, tmp=%b", vect, tmp);
   end
endmodule

module bug26969 (input [31:0] ad, output [15:0] regff, input [31:0] read);
   bufif0 ad_drv [31:0] (ad, {16'b0, regff}, read);
endmodule

module bug26970;
   parameter A = 2'b1, B = 3'b0;
   parameter x = {B,B,B,A,A,B};
endmodule

module bug26997;
   MUX_REG_8x8 PAGE_REG_B3 (
			    .CLK	(CLK),
			    /*
			     .IN	(DATA_RES[31:24]),
			     .OUT	(PAGE[31:24]),
			     .EN_IN	(EN_B3),
			     .EN_OUT	(PAGE_SEL),
			     */
			    .TC	(),
			    .TD	(),
			    .TQ	());
endmodule

module bug27013;
   submod u1(0);
   submod u2(1);
endmodule

module bug27036;
   reg [2:0]  a_fifo_cam_indices[3:0], lt_fifo_cam_indices[5:0];
   wire [2:0] db0_a_fifo_cam_indices = a_fifo_cam_indices[0];
endmodule

module bug27037;
   reg mem[12:2];
   reg [7:0] i;
endmodule

module bug27039;
   integer i;
endmodule

module bug27045(
    input clk, input reset,
    input [7:0] d,
    output reg [7:0] q );
   parameter 	     REG_DELAY = 0;
   always @(posedge clk or posedge reset)
     q <= #(REG_DELAY*2) d;
endmodule

module bug27062 (input D, output Q);
   p(Q, D);
endmodule

`timescale 1ns/1ns

module bug27066;
   integer i;
   time    t;
   realtime rt;
   function integer toint;
      input integer y;
      input [15:0] x;
      toint = x|y;
   endfunction
endmodule

module bug27067;
    initial $monitor( "%T %b %b %b", $time, clk1, clko1, clko2 );
    initial forever @( negedge clk1 ) dclk1ff <= #50 ~ dclk1ff;
endmodule

module bug27072(
    output reg sum,
    input wire ci);
endmodule

`resetall
module spec;
   specify
      specparam
	Tac = 0.1,
	Tcs = 0.2;
      if ( !B & !M )
	( posedge CLK => (  Q[0] : 1'bx )) = ( Tac, Tcs );
      $width (negedge CLK &&& EN, Tac, 0, notif_clk);
      ( in1 => q ) = (3, 4);
      ( in1 +=> q ) = Tac;
      ( a, b, c *> q1, q2) = 10;
      ( s +*> q ) = Tcs;
   endspecify
endmodule

module bugevent;
   event e;
   initial ->e;
   always @ (e && e) $write("Legal\n");
endmodule

module bugio (input [31:0] a, a2, output [15:0] o, o2, input ibit);
endmodule

module buglocal;
   always #(cyclehalf) begin
      clk <= ~clk;
   end
   always @(*) begin end
   initial force flag = 0;
   initial #(delta+0.5) CLRN <= 1;
   assign (weak0,weak1) VDD=1'b0;
   assign (weak0,weak1) VSS=1'b1;
   wire [71:0] #1 xxout = xxin;
   initial #1000_000 $finish;
   initial $display($time,,"Double commas are stupid");
   initial for (counter[3:0] = 4'h0; counter[3:0] < limit[3:0];
		counter[3:0] = counter[3:0] + 4'h1) $write();
   always @(posedge(clk && !xclk) or negedge(clk && xclk) or reset) $write();

   nmos   # (PullTime, PullTime, 0) (PT,PU,1'b1);
   pulldown (strong0) pullinst (r);

   defparam x.y.z.PAR = 1;

   cdrv #5.0 clk(clk);

   initial PI = 3.1415926535_8979323846;

   always val = @ eventid 1'h1;

   always dly = # (2:3:4) 5'h6 ;

   wire     \33escapeneeded = 1'b1;
   wire     \33escapenewlineend
	    = 1'b1;
   wire     \noescapenewlineend
	    = 1'b1;
   wire     \noescapespaceend = 1'b1;

endmodule

module v2kparam
  #(parameter WIDTH = 1,
    parameter LENGTH = 1, LENGTH2 = 1)
   (output [WIDTH-1:0] myout,
    input  [LENGTH-1:0] myin, myinb
    );
   assign myout = myin ^ myinb ^ $callemptyparens();
endmodule

module foreqn (in);
   input [1:0] in;
   reg        a,b;
   reg [1:0]  c;
   always for ({a,c[0]} = in; a < 1'b1; {b,c[1]} = in) begin
   end
   always for ({a,c[in]} = 0; a < 1'b1; {b,c[in]} = 2'b10) begin
   end
endmodule

module colonslash;
   always @*
     case (cond&4'b1110)
       'h0://Error
	 t = 7;
       'h2:/*Another comment*/
	     t = 6;
       'h4: t = 5;
     endcase
endmodule

module enums;
   enum {red, yellow, green} light;
   enum integer {IDLE, XX='x, S1='b01, S2='b10} state, next;
   enum {bronze=3, silver, gold} medal;
   enum { add=10, sub[5], jmp[6:8] } E1;
   typedef enum {NOPE, YUP} boolean;
   enum  logic [1:0] {IDLE, DIR} STATE, NSTATE;
endmodule

module invec (
    output logic novec,
    output logic [7:0] range,
    output logic [1:0] [7:0] arrayAndRange,
    output logic [2:0] [1:0] [7:0] arrayAndArrayAndRange,
    output reg signed novec2
	      );
endmodule

module bug34575;
   wire a,b,c,d;
   assign #(0,0)         a = 1;
   assign #(0:1:2)       b = 1;
   assign #(0:1:2,0:1:2) c = 1;
   assign #(0:1:2,0)     d = 1;
endmodule

module bug34649 (name);
       output reg name = 0;
endmodule
module bug34649b (
       output reg name = 0
		 );
endmodule
module bug10;
   initial begin
      x += 1;
      x -= 1;
      x /= 1;
      x *= 1;
      x |= 1;
      x ^= 1;
      x <<= 1;
      x >>= 1;
      x <<<= 1;
      x >>>= 1;
      y = x++;  // Part of expression
      y = ++x;
      y = x--;
      y = --x;
      x++; // Statement
      ++x;
      x--;
      --x;
   end
endmodule

module bug33;
   integer i;
   initial begin
      unique case (i)
      endcase
      priority case (i)
      endcase
      if (i) begin end else begin end
   end
endmodule

module bug16;
   timeunit 0.1ns;
   timeprecision 1ns;
endmodule

parameter bug39 = 0;

`default_nettype none
`pragma foo = bar
`default_nettype wire

module bug64;
   parameter integer  a=1,b=2;
   parameter real     c=3.0;
   parameter realtime d=4.0;
   parameter time     e=5.0;
endmodule

module bug166;
   assign {{o1,o2},o3,o4,{o5,o6}} = {{i1,i2},i3,i4,{i5,i6}};
endmodule

module coverage20090318;
   task atask;
      begin end
   endtask
endmodule

module svsig;
   function int count (input logic [3:0] d);
      automatic int count = d[0]+d[1]+d[2]+d[3];
      for (int i=0; i<4; i++) begin
	 if (d[i]) count++;
      end
      return (count);
   endfunction
   task automatic autoconst;
      const int CONS = 8;
      $display("CONS=%x\n", CONS);
      $display("Another stmt\n");
   endtask
endmodule

module bug_empty_func_param;
   //function int intfunc(int a=0, b=1);
   //   return a+b;
   //endfunction
   always_comb begin
      foo = funccall();
      foo = intfunc(a, b);
      foo = intfunc(a, .b(b));
      foo = intfunc(.b(b), .a(a));
   end
endmodule

module dotted_funcs;
   initial ram.dotTask(addr[31:0],ramdata);  // Call task
   initial zz = ram.a.dotFunc(foo);  // Call function
endmodule

module var_only_in_block;
   initial begin : named
      integer only_a_var_in_blk;
   end
endmodule

module v2k_vec_no_vec
  ( input [2:0] VEC,
    VEC2,  		// No direction, no port, no data type; inherits
    input NOVEC,	// No direction, no data type; use `default_nettype
    input ARY [1:0],
    NOARY2,		// Array doesn't inherit
    logic STILL_IN,	// No direction, data type; inherits direction
    input logic TYPED	// Logic type
    );
   task t (input [2:0] FVEC, FVEC2,
	   input NOVEC);
      begin end
   endtask
endmodule

module bugfor;
   initial for (a=0;a;) begin end
endmodule

module bug85 #(parameter type T_DATA = byte)
   (data);
   input T_DATA data;
   sub #(.T_DATA( T_DATA ))
   sub (.data(data));
endmodule

module bugmodportcomma (,a,);
   input a;
endmodule

module bug168;
   initial $display("\nWarning!  This is a\
              string with a line\
              continuation\
              at time %0d PS", $time);
endmodule

module bug183
  #(parameter NUM = 9
    , WIDTH = 8
    ) (  input logic  [NUM-1:0][WIDTH-1:0] a
	 , output logic  [WIDTH-1:0]        sum
	 );
   localparam NLOG =
                    (NUM <=     2) ?  1
                    : (NUM <=  1024) ? 10
                    : 0;
   typedef logic [WIDTH-1:0] val_t;
   val_t [NLOG:0][NUM-1:0] tree;
endmodule

module bug192;
   covergroup cg192 @(posedge cclk);
      count_tag_busy: coverpoint countones_tag_busy {
	 bins count[] = {[0:DEPTH]};
      }
   endgroup: cg192
   cg192 cover_ts = new();
endmodule

function bit func_implied_in (bit i); g_bit = ~i; endfunction

module sparam;
   specparam delay = 10;
endmodule

// bug221
sequence stable_before_s(sig, clks_before, clk, rst=1'b0);
    @(clk) !rst throughout(##1 $stable(sig)[*clks_before-1]);
endsequence : stable_before_s

property stable_window(sample, sig, clks_before, clks_after, clk=$default_clk ,rst=1'b0);
    @(clk) disable iff(rst)  ## clks_before  sample
            |-> stable_before_s(sig, clks_before, clk, rst).ended ##1
                    ($stable(sig)[*clks_after]);
endproperty : stable_window

property never(prop, clk=$default_clk , rst=1'b0);
    @(clk) disable iff(rst) not(prop);
endproperty : never

property recur_triggers(trig, n, cond, clk=$default_clk , rst=1'b0);
    @(clk) disable iff (rst)
     not ( !cond throughout (trig ##1 trig[->(n-1)]) );
endproperty : recur_triggers

property data_transfer(
         start_ev, start_data, end_ev, end_data, clk=$default_clk ,rst=1'b0);
     logic [$bits(start_data)-1:0] local_data;
     @(clk) disable iff (rst)
     (start_ev, local_data = start_data) ##0
       (end_ev or (!end_ev ##1 (!start_ev throughout end_ev[->1])))
              |-> (local_data == end_data);
endproperty : data_transfer
