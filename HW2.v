module ALU(
    clk,
    rst_n,
    valid,
    ready,
    mode,
    in_A,
    in_B,
    out
);

    // Definition of ports
    input         clk, rst_n;
    input         valid;
    input  [1:0]  mode; // mode: 0: mulu, 1: divu, 2: shift, 3: avg
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

    // Todo: Wire and reg if needed
    reg  [ 2:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;

    // Todo: Instatiate any primitives if needed

    // Todo 5: Wire assignments
    wire [63:0] out;

    assign out = shreg;
    assign ready = (state == OUT) ? 1 : 0;

    // Combinational always block
    // Todo 1: Next-state logic of state machine
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

    // Todo: Sequential always block
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