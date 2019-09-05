def adcw1 : instruction :=
  definst "adcw" $ do
    pattern fun (v_2563 : imm int) (v_2560 : reg (bv 16)) => do
      v_4344 <- getRegister cf;
      v_4346 <- eval (handleImmediateWithSignExtend v_2563 16 16);
      v_4347 <- eval (concat (expression.bv_nat 1 0) v_4346);
      v_4350 <- getRegister v_2560;
      v_4352 <- eval (add (mux (eq v_4344 (expression.bv_nat 1 1)) (add v_4347 (expression.bv_nat 17 1)) v_4347) (concat (expression.bv_nat 1 0) v_4350));
      v_4353 <- eval (extract v_4352 1 17);
      v_4355 <- eval (isBitSet v_4352 1);
      v_4358 <- eval (isBitSet v_4346 0);
      setRegister (lhs.of_reg v_2560) v_4353;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4346 v_4350) 11) (isBitSet v_4352 12)));
      setRegister cf (isBitSet v_4352 0);
      setRegister of (bit_and (eq v_4358 (isBitSet v_4350 0)) (notBool_ (eq v_4358 v_4355)));
      setRegister pf (parityFlag (extract v_4352 9 17));
      setRegister sf v_4355;
      setRegister zf (zeroFlag v_4353);
      pure ()
    pat_end;
    pattern fun (v_2569 : reg (bv 16)) (v_2570 : reg (bv 16)) => do
      v_4381 <- getRegister cf;
      v_4383 <- getRegister v_2569;
      v_4384 <- eval (concat (expression.bv_nat 1 0) v_4383);
      v_4387 <- getRegister v_2570;
      v_4389 <- eval (add (mux (eq v_4381 (expression.bv_nat 1 1)) (add v_4384 (expression.bv_nat 17 1)) v_4384) (concat (expression.bv_nat 1 0) v_4387));
      v_4390 <- eval (extract v_4389 1 17);
      v_4392 <- eval (isBitSet v_4389 1);
      v_4395 <- eval (isBitSet v_4383 0);
      setRegister (lhs.of_reg v_2570) v_4390;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4383 v_4387) 11) (isBitSet v_4389 12)));
      setRegister cf (isBitSet v_4389 0);
      setRegister of (bit_and (eq v_4395 (isBitSet v_4387 0)) (notBool_ (eq v_4395 v_4392)));
      setRegister pf (parityFlag (extract v_4389 9 17));
      setRegister sf v_4392;
      setRegister zf (zeroFlag v_4390);
      pure ()
    pat_end;
    pattern fun (v_2568 : Mem) (v_2565 : reg (bv 16)) => do
      v_8789 <- getRegister cf;
      v_8791 <- evaluateAddress v_2568;
      v_8792 <- load v_8791 2;
      v_8793 <- eval (concat (expression.bv_nat 1 0) v_8792);
      v_8796 <- getRegister v_2565;
      v_8798 <- eval (add (mux (eq v_8789 (expression.bv_nat 1 1)) (add v_8793 (expression.bv_nat 17 1)) v_8793) (concat (expression.bv_nat 1 0) v_8796));
      v_8799 <- eval (extract v_8798 1 17);
      v_8801 <- eval (isBitSet v_8798 1);
      v_8804 <- eval (isBitSet v_8792 0);
      setRegister (lhs.of_reg v_2565) v_8799;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8792 v_8796) 11) (isBitSet v_8798 12)));
      setRegister cf (isBitSet v_8798 0);
      setRegister of (bit_and (eq v_8804 (isBitSet v_8796 0)) (notBool_ (eq v_8804 v_8801)));
      setRegister pf (parityFlag (extract v_8798 9 17));
      setRegister sf v_8801;
      setRegister zf (zeroFlag v_8799);
      pure ()
    pat_end;
    pattern fun (v_2554 : imm int) (v_2555 : Mem) => do
      v_10222 <- evaluateAddress v_2555;
      v_10223 <- getRegister cf;
      v_10225 <- eval (handleImmediateWithSignExtend v_2554 16 16);
      v_10226 <- eval (concat (expression.bv_nat 1 0) v_10225);
      v_10229 <- load v_10222 2;
      v_10231 <- eval (add (mux (eq v_10223 (expression.bv_nat 1 1)) (add v_10226 (expression.bv_nat 17 1)) v_10226) (concat (expression.bv_nat 1 0) v_10229));
      v_10232 <- eval (extract v_10231 1 17);
      store v_10222 v_10232 2;
      v_10235 <- eval (isBitSet v_10231 1);
      v_10238 <- eval (isBitSet v_10225 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10225 v_10229) 11) (isBitSet v_10231 12)));
      setRegister cf (isBitSet v_10231 0);
      setRegister of (bit_and (eq v_10238 (isBitSet v_10229 0)) (notBool_ (eq v_10238 v_10235)));
      setRegister pf (parityFlag (extract v_10231 9 17));
      setRegister sf v_10235;
      setRegister zf (zeroFlag v_10232);
      pure ()
    pat_end;
    pattern fun (v_2556 : reg (bv 16)) (v_2559 : Mem) => do
      v_10256 <- evaluateAddress v_2559;
      v_10257 <- getRegister cf;
      v_10259 <- getRegister v_2556;
      v_10260 <- eval (concat (expression.bv_nat 1 0) v_10259);
      v_10263 <- load v_10256 2;
      v_10265 <- eval (add (mux (eq v_10257 (expression.bv_nat 1 1)) (add v_10260 (expression.bv_nat 17 1)) v_10260) (concat (expression.bv_nat 1 0) v_10263));
      v_10266 <- eval (extract v_10265 1 17);
      store v_10256 v_10266 2;
      v_10269 <- eval (isBitSet v_10265 1);
      v_10272 <- eval (isBitSet v_10259 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10259 v_10263) 11) (isBitSet v_10265 12)));
      setRegister cf (isBitSet v_10265 0);
      setRegister of (bit_and (eq v_10272 (isBitSet v_10263 0)) (notBool_ (eq v_10272 v_10269)));
      setRegister pf (parityFlag (extract v_10265 9 17));
      setRegister sf v_10269;
      setRegister zf (zeroFlag v_10266);
      pure ()
    pat_end
