def shrq1 : instruction :=
  definst "shrq" $ do
    pattern fun (_ : clReg) (v_3035 : reg (bv 64)) => do
      v_5174 <- getRegister rcx;
      v_5176 <- eval (bv_and (extract v_5174 56 64) (expression.bv_nat 8 63));
      v_5177 <- eval (eq v_5176 (expression.bv_nat 8 0));
      v_5178 <- getRegister zf;
      v_5179 <- getRegister v_3035;
      v_5182 <- eval (lshr (concat v_5179 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_5176));
      v_5183 <- eval (extract v_5182 0 64);
      v_5186 <- getRegister sf;
      v_5189 <- getRegister pf;
      v_5195 <- getRegister of;
      v_5199 <- getRegister cf;
      v_5203 <- getRegister af;
      setRegister (lhs.of_reg v_3035) v_5183;
      setRegister af (mux v_5177 v_5203 undef);
      setRegister cf (mux (uge v_5176 (expression.bv_nat 8 64)) undef (mux v_5177 v_5199 (isBitSet v_5182 64)));
      setRegister of (mux (eq v_5176 (expression.bv_nat 8 1)) (isBitSet v_5179 0) (mux v_5177 v_5195 undef));
      setRegister pf (mux v_5177 v_5189 (parityFlag (extract v_5182 56 64)));
      setRegister sf (mux v_5177 v_5186 (isBitSet v_5182 0));
      setRegister zf (mux v_5177 v_5178 (eq v_5183 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3039 : imm int) (v_3040 : reg (bv 64)) => do
      v_5213 <- eval (bv_and (handleImmediateWithSignExtend v_3039 8 8) (expression.bv_nat 8 63));
      v_5214 <- eval (eq v_5213 (expression.bv_nat 8 0));
      v_5215 <- getRegister zf;
      v_5216 <- getRegister v_3040;
      v_5219 <- eval (lshr (concat v_5216 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_5213));
      v_5220 <- eval (extract v_5219 0 64);
      v_5223 <- getRegister sf;
      v_5226 <- getRegister pf;
      v_5232 <- getRegister of;
      v_5236 <- getRegister cf;
      v_5240 <- getRegister af;
      setRegister (lhs.of_reg v_3040) v_5220;
      setRegister af (mux v_5214 v_5240 undef);
      setRegister cf (mux (uge v_5213 (expression.bv_nat 8 64)) undef (mux v_5214 v_5236 (isBitSet v_5219 64)));
      setRegister of (mux (eq v_5213 (expression.bv_nat 8 1)) (isBitSet v_5216 0) (mux v_5214 v_5232 undef));
      setRegister pf (mux v_5214 v_5226 (parityFlag (extract v_5219 56 64)));
      setRegister sf (mux v_5214 v_5223 (isBitSet v_5219 0));
      setRegister zf (mux v_5214 v_5215 (eq v_5220 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3044 : reg (bv 64)) => do
      v_6580 <- getRegister v_3044;
      v_6582 <- eval (lshr (concat v_6580 (expression.bv_nat 1 0)) (expression.bv_nat 65 1));
      v_6583 <- eval (extract v_6582 0 64);
      setRegister (lhs.of_reg v_3044) v_6583;
      setRegister af undef;
      setRegister cf (isBitSet v_6582 64);
      setRegister of (isBitSet v_6580 0);
      setRegister pf (parityFlag (extract v_6582 56 64));
      setRegister sf (isBitSet v_6582 0);
      setRegister zf (zeroFlag v_6583);
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_3022 : Mem) => do
      v_9538 <- evaluateAddress v_3022;
      v_9539 <- load v_9538 8;
      v_9541 <- getRegister rcx;
      v_9543 <- eval (bv_and (extract v_9541 56 64) (expression.bv_nat 8 63));
      v_9545 <- eval (lshr (concat v_9539 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_9543));
      v_9546 <- eval (extract v_9545 0 64);
      store v_9538 v_9546 8;
      v_9548 <- eval (eq v_9543 (expression.bv_nat 8 0));
      v_9549 <- getRegister zf;
      v_9552 <- getRegister sf;
      v_9555 <- getRegister pf;
      v_9561 <- getRegister of;
      v_9565 <- getRegister cf;
      v_9569 <- getRegister af;
      setRegister af (mux v_9548 v_9569 undef);
      setRegister cf (mux (uge v_9543 (expression.bv_nat 8 64)) undef (mux v_9548 v_9565 (isBitSet v_9545 64)));
      setRegister of (mux (eq v_9543 (expression.bv_nat 8 1)) (isBitSet v_9539 0) (mux v_9548 v_9561 undef));
      setRegister pf (mux v_9548 v_9555 (parityFlag (extract v_9545 56 64)));
      setRegister sf (mux v_9548 v_9552 (isBitSet v_9545 0));
      setRegister zf (mux v_9548 v_9549 (eq v_9546 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3026 : imm int) (v_3025 : Mem) => do
      v_9577 <- evaluateAddress v_3025;
      v_9578 <- load v_9577 8;
      v_9581 <- eval (bv_and (handleImmediateWithSignExtend v_3026 8 8) (expression.bv_nat 8 63));
      v_9583 <- eval (lshr (concat v_9578 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_9581));
      v_9584 <- eval (extract v_9583 0 64);
      store v_9577 v_9584 8;
      v_9586 <- eval (eq v_9581 (expression.bv_nat 8 0));
      v_9587 <- getRegister zf;
      v_9590 <- getRegister sf;
      v_9593 <- getRegister pf;
      v_9599 <- getRegister of;
      v_9603 <- getRegister cf;
      v_9607 <- getRegister af;
      setRegister af (mux v_9586 v_9607 undef);
      setRegister cf (mux (uge v_9581 (expression.bv_nat 8 64)) undef (mux v_9586 v_9603 (isBitSet v_9583 64)));
      setRegister of (mux (eq v_9581 (expression.bv_nat 8 1)) (isBitSet v_9578 0) (mux v_9586 v_9599 undef));
      setRegister pf (mux v_9586 v_9593 (parityFlag (extract v_9583 56 64)));
      setRegister sf (mux v_9586 v_9590 (isBitSet v_9583 0));
      setRegister zf (mux v_9586 v_9587 (eq v_9584 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3029 : Mem) => do
      v_10123 <- evaluateAddress v_3029;
      v_10124 <- load v_10123 8;
      v_10126 <- eval (lshr (concat v_10124 (expression.bv_nat 1 0)) (expression.bv_nat 65 1));
      v_10127 <- eval (extract v_10126 0 64);
      store v_10123 v_10127 8;
      setRegister af undef;
      setRegister cf (isBitSet v_10126 64);
      setRegister of (isBitSet v_10124 0);
      setRegister pf (parityFlag (extract v_10126 56 64));
      setRegister sf (isBitSet v_10126 0);
      setRegister zf (zeroFlag v_10127);
      pure ()
    pat_end
