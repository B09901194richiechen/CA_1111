// Your code
module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I
    );
    //==== I/O Declaration ========================
    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;  // 0: read from data memory; 1: write
    output [31:0] mem_addr_D ;  // address of data/stack memory
    output [31:0] mem_wdata_D;  // Data written to data/stack memory
    input  [31:0] mem_rdata_D;  // Data read from data/stack memory
    // For mem_I
    output [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;

    //==== Reg/Wire Declaration ===================
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    wire   [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    wire   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg
    wire [31:0] imme, imme_shifted;
    wire [ 6:0] opcode;
    wire [ 9:0] control;
    wire [ 1:0] ALUOp;
    wire [31:0] ALU_rs1, ALU_rs2;
    wire ALUSrc, MemtoReg, RegWrite, Branch, AUIPC;
    wire [ 3:0] ALU_ctrl;
    wire [31:0] ALU_result_single, ALU_result_multi, ALU_result;
    wire branch_ctrl;
    wire ready;
    wire multi;       // multi cycle = 1 when control is mul or div
    wire Jal, Jalr;

    //==== Submodule Connection ===================
    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//

    // Todo: other submodules
    InstructionDecoder U0 (.instruction(mem_rdata_I), .opcode(opcode), .R1(rs1), .R2(rs2), .RD(rd));
    Control            U1 (.opcode(opcode), .control(control));
    ImmediateGenerator U2 (.In(mem_rdata_I), .Out(imme));
    ALUControl         U3 (.ALUOp(ALUOp), .funct7({mem_rdata_I[30], mem_rdata_I[25]}), .funct3(mem_rdata_I[14:12]), .Control(ALU_ctrl));
    ALU_Single_Cycle   U4 (.a(ALU_rs1), .b(ALU_rs2), .ALU_ctrl(ALU_ctrl), .ALU_result(ALU_result_single), .branch_ctrl(branch_ctrl));  // for other
    ALU_Multi_Cycle    U5 (.clk(clk), .rst_n(rst_n), .valid(multi), .ready(ready), .mode(2'b0), .in_A(rs1_data), .in_B(rs2_data), .out(ALU_result_multi)); // for mulDiv

    //==== Combinational Part =====================
    assign mem_addr_I = PC;
    assign ALUSrc = control[9];
    assign MemtoReg = control[8];
    assign regWrite = (ready || control[7]);
    assign mem_wen_D = control[6];
    assign Branch = control[5];
    assign Jal = control[4];
    assign Jalr = control[3];
    assign AUIPC = control[2];
    assign ALUOp[1] = control[1];
    assign ALUOp[0] = control[0];
    assign ALU_rs1 = (Jal || Jalr || AUIPC) ? PC : rs1_data;
    assign ALU_rs2 = ALUSrc ? imme : ((Jal || Jalr) ? 32'd4 : rs2_data);
    assign multi = ((ALU_ctrl == 4'b0111) && (!ready));
    assign ALU_result = (ready)? ALU_result_multi : ALU_result_single;
    assign rd_data = MemtoReg ? mem_rdata_D : ALU_result;
    assign PC_nxt = (branch_ctrl || Jal) ? (PC + imme_shifted) : (Jalr ? (rs1_data + imme) : (multi ? PC : PC + 32'd4));

    assign imme_shifted = imme << 1;
    assign mem_addr_D = ALU_result;
    assign mem_wdata_D = rs2_data;



    //==== Sequential Part ========================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00400000; // Do not modify this value!!!
        end
        else begin
            PC <= PC_nxt; 
        end
    end
endmodule

module InstructionDecoder(
 input  [31:0] instruction,
 output [6:0]  opcode,
 output [4:0]  R1,
 output [4:0]  R2,
 output [4:0]  RD
);
 assign opcode = instruction[6:0];
 assign R1     = instruction[19:15];
 assign R2     = instruction[24:20];
 assign RD     = instruction[11:7];
endmodule

module Control(
    input [6:0] opcode,
    output reg [9:0] control
);
    //assign {ALUSrc, MemtoReg, RegWrite, mem_wen_D, Branch, Jal, Jalr, AUIPC, AluOp} = control;
    always @(*) begin
        case(opcode)
        7'b0110011 : control = 10'b0010000010; //add, sub, xor, mul, div
        7'b0010111 : control = 10'b1010000100; //auipc
        7'b0100011 : control = 10'b1001000000; //sw
        7'b0000011 : control = 10'b1110000000; //lw
        7'b1100011 : control = 10'b0000100001; //beq, bge
        7'b1100111 : control = 10'b0000001000; //jalr
        7'b1101111 : control = 10'b0010010000; //jal
        7'b0010011 : control = 10'b1010000011; //addi, slti, slli, srai
        default :    control = 10'b0000000000;
        endcase
    end
endmodule

module ImmediateGenerator(
    input [31:0] In,
    output reg [31:0] Out);
    always @(*) begin
        case(In[6:0])//opcode
            7'b0010111 : Out = {In[31:12], 12'b0};  // auipc
            7'b1101111 : Out = {{12{In[31]}} ,In[31], In[19:12], In[20], In[30:21]}; // jal
            7'b1100111 : Out = {{20{In[31]}},In[31:20]};//jalr
            7'b1100011 : Out = {{20{In[31]}},In[31], In[7], In[30:25], In[11:8]}; // beg, bge
            7'b0000011 : Out = {{20{In[31]}},In[31:20]};//lw
            7'b0100011 : Out = {{20{In[31]}},In[31:25],In[11:7]};//sw
            7'b0010011 : 
                begin
                case (In[12])
                    1'b0 : Out = {{20{In[31]}},In[31:20]};
                    1'b1 : Out = {27'b0, In[24:20]};
                    default : Out = 32'b0;
                endcase                  
                end
            default : Out = {32'b0};
        endcase
    end
endmodule

module ALUControl(
    input [1:0] ALUOp,
    input [1:0]funct7,
    input [2:0] funct3,//funct7: bit 30 and bit 25 func3: all (3bit)
    output reg [3:0] Control
    );
//ALUop
//00 auipc sw lw jal jalr
//01 beq bge
//10 add sub xor mul
//11 addi slti slli srai

//ALU
//0000 add (auipc sw lw add addi
//0001 slti
//0010 sub1 (sub beq
//0011 sub2 (bge
//0100 xor
//0101 srai
//0110 slli
//0111 mul
//1000 div
//1001 jal jalr
//1010
//1011
//1100
//1101
//1110
//1111
    always @(*) begin
        case (ALUOp)
            2'b00 : Control = 4'b0000; //auipc sw lw jal jalr
            2'b01 : begin
                case(funct3)
                    3'b000 : Control = 4'b0010;//beq
                    3'b101 : Control = 4'b0011;//bge
                    default : Control = 4'bxxxx;
                endcase
            end
            2'b10 : begin 
                case({funct7,funct3})
                    5'b00000 : Control = 4'b0000;//add
                    5'b10000 : Control = 4'b0010;//sub 
                    5'b00100 : Control = 4'b0100;//xor
                    5'b01000 : Control = 4'b0111;//mul
                    5'b01100 : Control = 4'b1000;//div
                    default : Control = 4'bxxxx;
                endcase
            end
            2'b11 : begin
                case(funct3)
                    3'b000 : Control = 4'b0000;//addi
                    3'b010 : Control = 4'b0001;//slti
                    3'b001 : Control = 4'b0110;//slli
                    3'b101 : Control = 4'b0101;//srai
                    default : Control = 4'bxxxx;
                endcase
            end
            default: Control = 4'bxxxx;
        endcase
    end
endmodule

module ALU_Single_Cycle(a, b, ALU_ctrl, ALU_result, branch_ctrl);
    // slti: comparison with blt with signed-number
    // add:    add, addi, lw, sw, auipc, jal, jalr
    // sub1:   sub, beq,
    // sub2:   bge
    // xor1:   xor,
    // shift1: srai
    // shift2: slli
    // slti1: 
    // mul div is in another module
    
    input  [31:0] a, b;
    input  [ 3:0] ALU_ctrl;
    output reg [31:0] ALU_result;
    output branch_ctrl;

    parameter add  = 4'b0000;
    parameter slti = 4'b0001;
    parameter sub1 = 4'b0010;
    parameter sub2 = 4'b0011;
    parameter xor1 = 4'b0100;
    parameter srai = 4'b0101;
    parameter slli = 4'b0110;
    parameter mul  = 4'b0111;
    parameter auipc = 4'b1000;

    always @(*) begin
        case (ALU_ctrl)
            add:  ALU_result = a + b;
            sub1: ALU_result = a - b;
            xor1: ALU_result = a ^ b;
            srai: ALU_result = a >>> b;
            slli: ALU_result = a << b;
            slti: ALU_result = (a < b) ? 32'b1 : 32'b0;             // if a < b, ALU_result =  1; o.w, ALU_result = 0    
            sub2: ALU_result = a - b;
            auipc: ALU_result = b + a;
            default: ALU_result = 32'b0;
        endcase
    end
    assign branch_ctrl = ((ALU_ctrl == sub1 && a == b) || (ALU_ctrl == sub2 && a >= b));
endmodule

module ALU_Multi_Cycle(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW2
    // Definition of ports
    input         clk, rst_n;
    input         valid;
    input  [1:0]  mode; // mode: 0: mulu, 1: divu,
    output        ready;
    input  [31:0] in_A, in_B;
    output [63:0] out;

    // Definition of states
    parameter IDLE = 3'd0;
    parameter MUL  = 3'd1;
    parameter DIV  = 3'd2;
    parameter SHIFT = 3'd3;
    parameter AVG = 3'd4;
    parameter OUT  = 3'd5;

    reg  [ 2:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;
    wire [63:0] out;

    assign out = shreg;
    assign ready = (state == OUT) ? 1 : 0;

    always @(*) begin
        case(state)
            IDLE: begin
                if      (valid == 0)              state_nxt = IDLE;
                else if (valid == 1 && mode == 0) state_nxt = MUL;
                else if (valid == 1 && mode == 1) state_nxt = DIV;
                else if (valid == 1 && mode == 2) state_nxt = SHIFT;
                else                              state_nxt = AVG;   // valid == 1 && mode == 3
            end
            MUL :
                if (counter == 31) state_nxt = OUT;
                else               state_nxt = MUL;
            DIV :
                if (counter == 31) state_nxt = OUT;
                else               state_nxt = DIV;
            SHIFT :
                state_nxt = OUT;
            AVG : 
                state_nxt = OUT;
            OUT : 
                state_nxt = IDLE;
            default :
                state_nxt = IDLE;
        endcase
    end
    // Todo 2: Counter
    always @(*) begin
        if (state == MUL || state == DIV) counter_nxt = counter + 1'b1;
        else                              counter_nxt = 0; 
        end
    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
    wire [32:0] MUL_tmp;
    assign MUL_tmp = (shreg[0] == 1) ? (shreg[63:32] + alu_in) : shreg[63:32];
    
    always @(*) begin
        if      (state == MUL)   alu_out = MUL_tmp;
        else if (state == DIV)   alu_out = shreg[62:31] - alu_in;
        else                     alu_out = alu_in;
    end
    
    // Todo 4: Shift register
    wire [32:0] AVG_tmp;
    wire [63:0] DIV_tmp;
    
    assign AVG_tmp = shreg[31:0] + alu_in;
    assign DIV_tmp = (alu_out[32] == 1) ? (shreg << 1) : {alu_out[31:0],shreg[30:0], 1'b1};
           // alu_out[32] == 1 means overflow, and shift onlt; otherwise, no overflow and update remainder and shift left with new bit 1

    always @(*) begin
        if      (state == IDLE && valid == 1) shreg_nxt = {32'b0, in_A};
        else if (state == MUL)                shreg_nxt = {alu_out, shreg[31:1]};
        else if (state == DIV)                shreg_nxt = DIV_tmp;
        else if (state == SHIFT)              shreg_nxt = {32'b0, shreg[31:0] >> alu_in[2:0]};
        else if (state == AVG)                shreg_nxt = {32'b0, AVG_tmp >> 1};
        else                                  shreg_nxt = 64'b0;
        
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state   <= IDLE;
            counter <= 0;
            alu_in  <= 0; 
            shreg   <= 0;
        end
        else begin
            state   <= state_nxt;
            counter <= counter_nxt;
            alu_in  <= alu_in_nxt;
            shreg   <= shreg_nxt;
        end
    end
endmodule

module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);

    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth

    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0; // zero: hard-wired zero
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'h7fffeffc; // sp: stack pointer
                    32'd3: mem[i] <= 32'h10008000; // gp: global pointer
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end
    end
endmodule