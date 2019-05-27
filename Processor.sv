`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03/31/2019 07:02:31 PM
// Design Name: 
// Module Name: Processor
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

// Written by David_Harris@hmc.edu

// Top level system including MIPS and memories





module SimpleProcessor(input logic clk, bclk, breset,
                       output memwrite,
                       output logic[3:0] an,
                       output logic[6:0] C,
                       output logic dp,
                       output logic [7:0] pcO);

        logic clear, clk_pulse, theReset;
	    assign clear = 0;
	    
	    pulse_controller myclkCont(clk, bclk, clear, clk_pulse);
	    
        pulse_controller myresetCont(clk, breset, clear, theReset);
        
     
        logic[31:0] writedata, dataadr, instr , pc;
        assign pcO[0] = pc[0];
        assign pcO[1] = pc[1];  
        assign pcO[2] = pc[2];  
        assign pcO[3] = pc[3];  
        assign pcO[4] = pc[4];  
        assign pcO[5] = pc[5];  
        assign pcO[6] = pc[6];  
        assign pcO[7] = pc[7];           
        
        top  myPro(clk_pulse, theReset, writedata, dataadr, instr , pc, memwrite);
        
        
        logic [3:0] enables;
        assign enables[0] = 1;
        assign enables[1] = 1;
        assign enables[2] = 1;
        assign enables[3] = 1;
        logic [3:0] digit3, digit2, digit1, digit0;
        
        assign digit0 = dataadr[3:0];
        assign digit1 = dataadr[7:4];
        assign digit2 = writedata[3:0];
        assign digit3 = writedata[7:4];
        
        display_controller mydisp(clk, theReset, enables, digit3, digit2, digit1, digit0, an, C, dp);
            

endmodule


////////////////////////////////////////////////////////
//  
//  display_controller.sv
//
//  by Will Sawyer  31 March 2017
//
//  puts 4 hexadecimal values (from O to F) on the 4-digit 7-segment display unit
//     
//
//  the AN, Cx and DP outputs are active-low, for the BASYS3 board
//    AN3 is the left-most digit, AN2 is the second-left-most, etc
//    C[6] is CA for the a segment, c[5] is CB for the b segment, etc
//   
//  Uses the 100 MHz board clock for clk, and uses a clear signal for resetting
//  Takes 4 active-high enable signals, 1 per digit, to enable 
//     or disable display digits
//
//  For correct connections, carefully plan what should be in the .XDC file
//   
//  
////////////////////////////////////////////////////////


module display_controller (
		input logic clk, clear,
		input logic [3:0] enables, 
		input logic [3:0] in3, in2, in1, in0,
		output logic [3:0] AN,
		output logic [6:0] C,
		output logic       DP
		);

		//logic [3:0] current_digit, cur_dig_AN;
		//logic [6:0] segments;
		
      //assign AN = ~(enables & cur_dig_AN);// AN signals are active low on the BASYS3 board,
                                // and must be enabled in order to display the digit
     // assign C = ~segments;     // segments must be inverted, since the C values are active low
     // assign DP = 1;            // makes the dot point always off 
                                // (0 = on, since it is active low)


		
		// divide system clock (100Mhz for Basys3) by 2^N using a counter, which allows us to multiplex at lower speed
        localparam N = 18;
        logic [N-1:0] count = {N{1'b0}}; //initial value
        always@ (posedge clk)
            count <= count + 1;
        
         
        logic [3:0]digit_val; // multiplexer of digits
        logic [3:0]digit_en;  // decoder of enable bits
         
        always_comb
         begin
         digit_en = 4'b1111; 
         digit_val = in0; 
         
          case(count[N-1:N-2]) //using only the 2 MSB's of the counter 
            
           2'b00 :  //select first 7Seg.
            begin
             digit_val = in0;
             digit_en = 4'b1110;
            end
            
           2'b01:  //select second 7Seg.
            begin
             digit_val = in1;
             digit_en = 4'b1101;
            end
            
           2'b10:  //select third 7Seg.
            begin
             digit_val = in2;
             digit_en = 4'b1011;
            end
             
           2'b11:  //select forth 7Seg.
            begin
             digit_val = in3;
             digit_en = 4'b0111;
            end
          endcase
         end
         
        
        //Convert digit value to LED vector. LEDs are active low.
        logic [6:0] sseg_LEDs; 
        always_comb
         begin 
          sseg_LEDs = 7'b1111111; //default
          case(digit_val)
           4'd0 : sseg_LEDs = 7'b1000000; //to display 0
           4'd1 : sseg_LEDs = 7'b1111001; //to display 1
           4'd2 : sseg_LEDs = 7'b0100100; //to display 2
           4'd3 : sseg_LEDs = 7'b0110000; //to display 3
           4'd4 : sseg_LEDs = 7'b0011001; //to display 4
           4'd5 : sseg_LEDs = 7'b0010010; //to display 5
           4'd6 : sseg_LEDs = 7'b0000010; //to display 6
           4'd7 : sseg_LEDs = 7'b1111000; //to display 7
           4'd8 : sseg_LEDs = 7'b0000000; //to display 8
           4'd9 : sseg_LEDs = 7'b0010000; //to display 9
           4'd10: sseg_LEDs = 7'b0001000; //to display a
           4'd11: sseg_LEDs = 7'b0000011; //to display b
           4'd12: sseg_LEDs = 7'b1000110; //to display c
           4'd13: sseg_LEDs = 7'b0100001; //to display d
           4'd14: sseg_LEDs = 7'b0000110; //to display e
           4'd15: sseg_LEDs = 7'b0001110; //to display f   
           default : sseg_LEDs = 7'b0111111; //dash
          endcase
         end
         
        assign AN = digit_en; 
        assign C = sseg_LEDs; 
        assign DP = 1'b1; //turn dp off
         
endmodule



/////////////////////////////////////////////////////////////////////////////////
// 
//   This module takes a slide switch or pushbutton input and 
//   does the following:
//     --debounces it (ignoring any addtional changes for ~40 milliseconds)
//     --synchronizes it with the clock edges
//     --produces just one pulse, lasting for one clock period
//   
//   Note that the 40 millisecond debounce time = 2000000 cycles of 
//   50MHz clock (which has 20 nsec period)
//   
//   sw_input: the signal coming from the slide switch or pushbutton
//   CLK: the 50 MHz system clock on the BASYS2 board
//   clk_pulse: the synchronized debounced single-pulse output
//
//////////////////////////////////////////////////////////////////////////////////

module pulse_controller(
	input CLK, sw_input, clear,
	output reg clk_pulse );

	 reg [2:0] state, nextstate;
	 reg [27:0] CNT; 
	 wire cnt_zero; 

	always @ (posedge CLK, posedge clear)
	   if(clear)
	    	state <=3'b000;
	   else
	    	state <= nextstate;

	always @ (sw_input, state, cnt_zero)
          case (state)
             3'b000: begin if (sw_input) nextstate = 3'b001; 
                           else nextstate = 3'b000; clk_pulse = 0; end	     
             3'b001: begin nextstate = 3'b010; clk_pulse = 1; end
             3'b010: begin if (cnt_zero) nextstate = 3'b011; 
                           else nextstate = 3'b010; clk_pulse = 1; end
             3'b011: begin if (sw_input) nextstate = 3'b011; 
                           else nextstate = 3'b100; clk_pulse = 0; end
             3'b100: begin if (cnt_zero) nextstate = 3'b000; 
                           else nextstate = 3'b100; clk_pulse = 0; end
            default: begin nextstate = 3'b000; clk_pulse = 0; end
          endcase

	always @(posedge CLK)
	   case(state)
		3'b001: CNT <= 100000000;
		3'b010: CNT <= CNT-1;
		3'b011: CNT <= 100000000;
		3'b100: CNT <= CNT-1;
	   endcase

//  reduction operator |CNT gives the OR of all bits in the CNT register	
	assign cnt_zero = ~|CNT;

endmodule

module top  (input   logic 	 clk, reset,            
	     output  logic[31:0] writedata, dataadr, instr , pc,         
	     output  logic       memwrite);  

   logic [31:0]  readdata;    

   // instantiate processor and memories  
   mips mips (clk, reset, pc, instr, memwrite, dataadr, writedata, readdata);  
   imem imem (pc[7:2], instr);  
   dmem dmem (clk, memwrite, dataadr, writedata, readdata);

endmodule



// External data memory used by MIPS single-cycle processor

module dmem (input  logic        clk, we,
             input  logic[31:0]  a, wd,
             output logic[31:0]  rd);

   logic  [31:0] RAM[63:0];
  
   assign rd = RAM[a[31:2]];    // word-aligned  read (for lw)

   always_ff @(posedge clk)
     if (we)
       RAM[a[31:2]] <= wd;      // word-aligned write (for sw)

endmodule



// External instruction memory used by MIPS single-cycle
// processor. It models instruction memory as a stored-program 
// ROM, with address as input, and instruction as output


module imem ( input logic [5:0] addr, output logic [31:0] instr);

// imem is modeled as a lookup table, a stored-program byte-addressable ROM
	always_comb
	   case ({addr,2'b00})		   	// word-aligned fetch
//		address		instruction
//		-------		-----------
		8'h00: instr = 32'h20020005;  	// disassemble, by hand 
		8'h04: instr = 32'h2003000c;  	// or with a program,
		8'h08: instr = 32'h2067fff7;  	// to find out what
		8'h0c: instr = 32'h00e22025;  	// this program does!
		8'h10: instr = 32'h00642824;
		8'h14: instr = 32'h00a42820;
		8'h18: instr = 32'h10a7000a;
		8'h1c: instr = 32'h0064202a;
		8'h20: instr = 32'h10800001;
		8'h24: instr = 32'h20050000;
		8'h28: instr = 32'h00e2202a;
		8'h2c: instr = 32'h00853820;
		8'h30: instr = 32'h00e23822;
		8'h34: instr = 32'hac670044;
		8'h38: instr = 32'h8c020050;
		8'h3c: instr = 32'hbc000000; //nop
        8'h40: instr = 32'hb8420001; // subi $2, $2, 1
		8'h44: instr = 32'hac020054;
		8'h48: instr = 32'h08000012;	// j 48, so it will loop here
	     default:  instr = {32{1'bx}};	// unknown address
	   endcase
endmodule


// single-cycle MIPS processor, with controller and datapath

module mips (input  logic        clk, reset,
             output logic[31:0]  pc,
             input  logic[31:0]  instr,
             output logic        memwrite,
             output logic[31:0]  aluout, writedata,
             input  logic[31:0]  readdata);

  logic        memtoreg, pcsrc, zero, alusrc, regdst, regwrite, jump;
  logic [2:0]  alucontrol;

  controller c (instr[31:26], instr[5:0], zero, memtoreg, memwrite, pcsrc,
                        alusrc, regdst, regwrite, jump, alucontrol);

  datapath dp (clk, reset, memtoreg, pcsrc, alusrc, regdst, regwrite, jump,
                          alucontrol, zero, pc, instr, aluout, writedata, readdata);

endmodule
module controller(input  logic[5:0] op, funct,
                  input  logic     zero,
                  output logic     memtoreg, memwrite,
                  output logic     pcsrc, alusrc,
                  output logic     regdst, regwrite,
                  output logic     jump,
                  output logic[2:0] alucontrol);

   logic [1:0] aluop;
   logic       branch;

   maindec md (op, memtoreg, memwrite, branch, alusrc, regdst, regwrite, 
		 jump, aluop);

   aludec  ad (funct, aluop, alucontrol);

   assign pcsrc = branch & zero;

endmodule

module maindec (input logic[5:0] op, 
	              output logic memtoreg, memwrite, branch,
	              output logic alusrc, regdst, regwrite, jump,
	              output logic[1:0] aluop );
   logic [8:0] controls;

   assign {regwrite, regdst, alusrc, branch, memwrite,
                memtoreg,  aluop, jump} = controls;

  always_comb
    case(op)
      6'b000000: controls <= 9'b110000100; // R-type
      6'b100011: controls <= 9'b101001000; // LW
      6'b101011: controls <= 9'b001010000; // SW
      6'b000100: controls <= 9'b000100010; // BEQ
      6'b001000: controls <= 9'b101000000; // ADDI
      6'b000010: controls <= 9'b000000001; // J
      6'b101111: controls <= 9'b000000000; // nop
      6'b101110: controls <= 9'b101000010; // subi
      default:   controls <= 9'bxxxxxxxxx; // illegal op
    endcase
endmodule

module aludec (input    logic[5:0] funct,
               input    logic[1:0] aluop,
               output   logic[2:0] alucontrol);
  always_comb
    case(aluop)
      2'b00: alucontrol  = 3'b010;  // add  (for lw/sw/addi)
      2'b01: alucontrol  = 3'b110;  // sub   (for beq)
      default: case(funct)          // R-TYPE instructions
          6'b100000: alucontrol  = 3'b010; // ADD
          6'b100010: alucontrol  = 3'b110; // SUB
          6'b100100: alucontrol  = 3'b000; // AND
          6'b100101: alucontrol  = 3'b001; // OR
          6'b101010: alucontrol  = 3'b111; // SLT
          default:   alucontrol  = 3'bxxx; // ???
        endcase
    endcase
endmodule

module datapath (input  logic clk, reset, memtoreg, pcsrc, alusrc, regdst,
                 input  logic regwrite, jump, 
		 input  logic[2:0]  alucontrol, 
                 output logic zero, 
		 output logic[31:0] pc, 
	         input  logic[31:0] instr,
                 output logic[31:0] aluout, writedata, 
	         input  logic[31:0] readdata);

  logic [4:0]  writereg;
  logic [31:0] pcnext, pcnextbr, pcplus4, pcbranch;
  logic [31:0] signimm, signimmsh, srca, srcb, result;
 
  // next PC logic
  flopr #(32) pcreg(clk, reset, pcnext, pc);
  adder       pcadd1(pc, 32'b100, pcplus4);
  sl2         immsh(signimm, signimmsh);
  adder       pcadd2(pcplus4, signimmsh, pcbranch);
  mux2 #(32)  pcbrmux(pcplus4, pcbranch, pcsrc,
                      pcnextbr);
  mux2 #(32)  pcmux(pcnextbr, {pcplus4[31:28], 
                    instr[25:0], 2'b00}, jump, pcnext);

// register file logic
   regfile     rf (clk, regwrite, instr[25:21], instr[20:16], writereg,
                   result, srca, writedata);

   mux2 #(5)    wrmux (instr[20:16], instr[15:11], regdst, writereg);
   mux2 #(32)  resmux (aluout, readdata, memtoreg, result);
   signext         se (instr[15:0], signimm);

  // ALU logic
   mux2 #(32)  srcbmux (writedata, signimm, alusrc, srcb);
   alu         alu (srca, srcb, alucontrol, aluout, zero);

endmodule


module regfile (input    logic clk, we3, 
                input    logic[4:0]  ra1, ra2, wa3, 
                input    logic[31:0] wd3, 
                output   logic[31:0] rd1, rd2);

  logic [31:0] rf [31:0];

  // three ported register file: read two ports combinationally
  // write third port on rising edge of clock. Register0 hardwired to 0.

  always_ff @(posedge clk)
     if (we3) 
         rf [wa3] <= wd3;	

  assign rd1 = (ra1 != 0) ? rf [ra1] : 0;
  assign rd2 = (ra2 != 0) ? rf[ ra2] : 0;

endmodule


module alu(input  logic [31:0] a, b, 
           input  logic [2:0]  alucont, 
           output logic [31:0] result,
           output logic zero);
           
    logic [31:0] zExt, ou, addOut, andOut, orOut;
    
    mux2New myMux(b, ~b, alucont[2], ou);
    
    adderNew myAdd(a, ou, alucont[2], addOut);
    
    assign zExt = addOut[31] ? 32'b0000_0000_0000_0000_0000_0000_0000_0001 : 32'b0000_0000_0000_0000_0000_0000_0000_0000;
    
    assign andOut = ou & a;
    
    assign orOut = ou | a;
    
    mux4New my4Mux(andOut, orOut, addOut, zExt, alucont[1:0], result);
    
    assign zero = ~|addOut;

endmodule


module mux2New 
(input  logic[31:0] i0, i1,  
              input  logic oi, 
              output logic[31:0] ou);
  
   assign ou = oi ? i1 : i0; 
endmodule


module mux4New(input  logic[31:0] e0, e1, e2, e3,  
              input  logic[1:0] oo, 
              output logic[31:0] outt);
  
   assign outt = oo[1] ? (oo[0] ? e3 : e2) : (oo[0] ? e1 : e0); 
endmodule

module adderNew (input  logic[31:0] a1, b1,
                input logic f2,
              output logic[31:0] y1);
     
     assign y1 = a1 + b1 + f2;
endmodule

module adder (input  logic[31:0] a, b,
              output logic[31:0] y);
     
     assign y = a + b;
endmodule

module sl2 (input  logic[31:0] a,
            output logic[31:0] y);
     
     assign y = {a[29:0], 2'b00}; // shifts left by 2
endmodule

module signext (input  logic[15:0] a,
                output logic[31:0] y);
              
  assign y = {{16{a[15]}}, a};    // sign-extends 16-bit a
endmodule

// parameterized register
module flopr #(parameter WIDTH = 8)
              (input logic clk, reset, 
	       input logic[WIDTH-1:0] d, 
               output logic[WIDTH-1:0] q);

  always_ff@(posedge clk, posedge reset)
    if (reset) q <= 0; 
    else       q <= d;
endmodule


// paramaterized 2-to-1 MUX
module mux2 #(parameter WIDTH = 8)
             (input  logic[WIDTH-1:0] d0, d1,  
              input  logic s, 
              output logic[WIDTH-1:0] y);
  
   assign y = s ? d1 : d0; 
endmodule

