def addw1 : instruction :=
  definst "addw" $ do
    pattern fun (v_2686 : imm int) ax => do
      v_5175 <- eval (handleImmediateWithSignExtend v_2686 16 16);
      v_5177 <- getRegister rax;
      v_5180 <- eval (add (concat (expression.bv_nat 1 0) v_5175) (concat (expression.bv_nat 1 0) (extract v_5177 48 64)));
      v_5182 <- eval (extract v_5180 1 2);
      v_5188 <- eval (extract v_5180 1 17);
      v_5193 <- eval (eq (extract v_5175 0 1) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_5177 0 48) v_5188);
      setRegister of (mux (bit_and (eq v_5193 (eq (extract v_5177 48 49) (expression.bv_nat 1 1))) (notBool_ (eq v_5193 (eq v_5182 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5180 9 17));
      setRegister zf (zeroFlag v_5188);
      setRegister af (bv_xor (bv_xor (extract v_5175 11 12) (extract v_5177 59 60)) (extract v_5180 12 13));
      setRegister sf v_5182;
      setRegister cf (extract v_5180 0 1);
      pure ()
    pat_end;
    pattern fun (v_2699 : imm int) (v_2698 : reg (bv 16)) => do
      v_5219 <- eval (handleImmediateWithSignExtend v_2699 16 16);
      v_5221 <- getRegister v_2698;
      v_5223 <- eval (add (concat (expression.bv_nat 1 0) v_5219) (concat (expression.bv_nat 1 0) v_5221));
      v_5225 <- eval (extract v_5223 1 2);
      v_5230 <- eval (extract v_5223 1 17);
      v_5235 <- eval (eq (extract v_5219 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2698) v_5230;
      setRegister of (mux (bit_and (eq v_5235 (eq (extract v_5221 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_5235 (eq v_5225 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5223 9 17));
      setRegister zf (zeroFlag v_5230);
      setRegister af (bv_xor (extract (bv_xor v_5219 v_5221) 11 12) (extract v_5223 12 13));
      setRegister sf v_5225;
      setRegister cf (extract v_5223 0 1);
      pure ()
    pat_end;
    pattern fun (v_2707 : reg (bv 16)) (v_2708 : reg (bv 16)) => do
      v_5255 <- getRegister v_2707;
      v_5257 <- getRegister v_2708;
      v_5259 <- eval (add (concat (expression.bv_nat 1 0) v_5255) (concat (expression.bv_nat 1 0) v_5257));
      v_5261 <- eval (extract v_5259 1 2);
      v_5266 <- eval (extract v_5259 1 17);
      v_5271 <- eval (eq (extract v_5255 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2708) v_5266;
      setRegister of (mux (bit_and (eq v_5271 (eq (extract v_5257 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_5271 (eq v_5261 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5259 9 17));
      setRegister zf (zeroFlag v_5266);
      setRegister af (bv_xor (extract (bv_xor v_5255 v_5257) 11 12) (extract v_5259 12 13));
      setRegister sf v_5261;
      setRegister cf (extract v_5259 0 1);
      pure ()
    pat_end;
    pattern fun (v_2702 : Mem) (v_2703 : reg (bv 16)) => do
      v_9564 <- evaluateAddress v_2702;
      v_9565 <- load v_9564 2;
      v_9567 <- getRegister v_2703;
      v_9569 <- eval (add (concat (expression.bv_nat 1 0) v_9565) (concat (expression.bv_nat 1 0) v_9567));
      v_9571 <- eval (extract v_9569 1 2);
      v_9572 <- eval (extract v_9569 1 17);
      v_9581 <- eval (eq (extract v_9565 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2703) v_9572;
      setRegister of (mux (bit_and (eq v_9581 (eq (extract v_9567 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_9581 (eq v_9571 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9569 9 17));
      setRegister af (bv_xor (extract (bv_xor v_9565 v_9567) 11 12) (extract v_9569 12 13));
      setRegister zf (zeroFlag v_9572);
      setRegister sf v_9571;
      setRegister cf (extract v_9569 0 1);
      pure ()
    pat_end;
    pattern fun (v_2690 : imm int) (v_2689 : Mem) => do
      v_11087 <- evaluateAddress v_2689;
      v_11088 <- eval (handleImmediateWithSignExtend v_2690 16 16);
      v_11090 <- load v_11087 2;
      v_11092 <- eval (add (concat (expression.bv_nat 1 0) v_11088) (concat (expression.bv_nat 1 0) v_11090));
      v_11093 <- eval (extract v_11092 1 17);
      store v_11087 v_11093 2;
      v_11096 <- eval (extract v_11092 1 2);
      v_11105 <- eval (eq (extract v_11088 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_11105 (eq (extract v_11090 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_11105 (eq v_11096 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_11092 9 17));
      setRegister af (bv_xor (extract (bv_xor v_11088 v_11090) 11 12) (extract v_11092 12 13));
      setRegister zf (zeroFlag v_11093);
      setRegister sf v_11096;
      setRegister cf (extract v_11092 0 1);
      pure ()
    pat_end;
    pattern fun (v_2694 : reg (bv 16)) (v_2693 : Mem) => do
      v_11120 <- evaluateAddress v_2693;
      v_11121 <- getRegister v_2694;
      v_11123 <- load v_11120 2;
      v_11125 <- eval (add (concat (expression.bv_nat 1 0) v_11121) (concat (expression.bv_nat 1 0) v_11123));
      v_11126 <- eval (extract v_11125 1 17);
      store v_11120 v_11126 2;
      v_11129 <- eval (extract v_11125 1 2);
      v_11138 <- eval (eq (extract v_11121 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_11138 (eq (extract v_11123 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_11138 (eq v_11129 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_11125 9 17));
      setRegister af (bv_xor (extract (bv_xor v_11121 v_11123) 11 12) (extract v_11125 12 13));
      setRegister zf (zeroFlag v_11126);
      setRegister sf v_11129;
      setRegister cf (extract v_11125 0 1);
      pure ()
    pat_end
