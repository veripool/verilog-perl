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
   // Copyright (c) 2002 Stephen Williams (steve@icarus.com)
   // GNU Licensed
   parameter   SET  = 1'b1,
		 CLR  = 1'b0,
		 S1   = 2'd1,
		 HINC = 3'd4;
   parameter   
     x = {S1,CLR,CLR,CLR,CLR,SET,SET,CLR,CLR,HINC };
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

module bug27009();
   // Copyright (c) 2002 Stephen Williams (steve@icarus.com)
   // GNU Licensed
   reg pullval;
   wire (weak0, weak1) value = pullval;
   //Legal?: buf (highz0, strong1) drive0(value, en0);
   //Legal?: not (strong0, highz1) drive1(value, en1);
endmodule // main


module bug27010;
   // Copyright (c) 2000 Yasuhisa Kato <ykato@mac.com>
   // GNU Licensed
   initial begin clk = 0 ; forever #5 clk = ~clk ; end
   drvz N ( clk, b, ~c, s ) ; // line(A)
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
