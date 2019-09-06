def adcw1 : instruction :=
  definst "adcw" $ do
    pattern fun (v_2589 : imm int) (v_2590 : reg (bv 16)) => do
      v_4302 <- getRegister cf;
      v_4303 <- eval (handleImmediateWithSignExtend v_2589 16 16);
      v_4304 <- eval (concat (expression.bv_nat 1 0) v_4303);
      v_4307 <- getRegister v_2590;
      v_4309 <- eval (add (mux v_4302 (add v_4304 (expression.bv_nat 17 1)) v_4304) (concat (expression.bv_nat 1 0) v_4307));
      v_4310 <- eval (extract v_4309 1 17);
      setRegister (lhs.of_reg v_2590) v_4310;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4303 v_4307) 11) (isBitSet v_4309 12)));
      setRegister cf (isBitSet v_4309 0);
      setRegister of (overflowFlag v_4303 v_4307 v_4310);
      setRegister pf (parityFlag (extract v_4309 9 17));
      setRegister sf (isBitSet v_4309 1);
      setRegister zf (zeroFlag v_4310);
      pure ()
    pat_end;
    pattern fun (v_2598 : reg (bv 16)) (v_2599 : reg (bv 16)) => do
      v_4333 <- getRegister cf;
      v_4334 <- getRegister v_2598;
      v_4335 <- eval (concat (expression.bv_nat 1 0) v_4334);
      v_4338 <- getRegister v_2599;
      v_4340 <- eval (add (mux v_4333 (add v_4335 (expression.bv_nat 17 1)) v_4335) (concat (expression.bv_nat 1 0) v_4338));
      v_4341 <- eval (extract v_4340 1 17);
      setRegister (lhs.of_reg v_2599) v_4341;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4334 v_4338) 11) (isBitSet v_4340 12)));
      setRegister cf (isBitSet v_4340 0);
      setRegister of (overflowFlag v_4334 v_4338 v_4341);
      setRegister pf (parityFlag (extract v_4340 9 17));
      setRegister sf (isBitSet v_4340 1);
      setRegister zf (zeroFlag v_4341);
      pure ()
    pat_end;
    pattern fun (v_2594 : Mem) (v_2595 : reg (bv 16)) => do
      v_8644 <- getRegister cf;
      v_8645 <- evaluateAddress v_2594;
      v_8646 <- load v_8645 2;
      v_8647 <- eval (concat (expression.bv_nat 1 0) v_8646);
      v_8650 <- getRegister v_2595;
      v_8652 <- eval (add (mux v_8644 (add v_8647 (expression.bv_nat 17 1)) v_8647) (concat (expression.bv_nat 1 0) v_8650));
      v_8653 <- eval (extract v_8652 1 17);
      setRegister (lhs.of_reg v_2595) v_8653;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8646 v_8650) 11) (isBitSet v_8652 12)));
      setRegister cf (isBitSet v_8652 0);
      setRegister of (overflowFlag v_8646 v_8650 v_8653);
      setRegister pf (parityFlag (extract v_8652 9 17));
      setRegister sf (isBitSet v_8652 1);
      setRegister zf (zeroFlag v_8653);
      pure ()
    pat_end;
    pattern fun (v_2582 : imm int) (v_2581 : Mem) => do
      v_10003 <- evaluateAddress v_2581;
      v_10004 <- getRegister cf;
      v_10005 <- eval (handleImmediateWithSignExtend v_2582 16 16);
      v_10006 <- eval (concat (expression.bv_nat 1 0) v_10005);
      v_10009 <- load v_10003 2;
      v_10011 <- eval (add (mux v_10004 (add v_10006 (expression.bv_nat 17 1)) v_10006) (concat (expression.bv_nat 1 0) v_10009));
      v_10012 <- eval (extract v_10011 1 17);
      store v_10003 v_10012 2;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10005 v_10009) 11) (isBitSet v_10011 12)));
      setRegister cf (isBitSet v_10011 0);
      setRegister of (overflowFlag v_10005 v_10009 v_10012);
      setRegister pf (parityFlag (extract v_10011 9 17));
      setRegister sf (isBitSet v_10011 1);
      setRegister zf (zeroFlag v_10012);
      pure ()
    pat_end;
    pattern fun (v_2586 : reg (bv 16)) (v_2585 : Mem) => do
      v_10031 <- evaluateAddress v_2585;
      v_10032 <- getRegister cf;
      v_10033 <- getRegister v_2586;
      v_10034 <- eval (concat (expression.bv_nat 1 0) v_10033);
      v_10037 <- load v_10031 2;
      v_10039 <- eval (add (mux v_10032 (add v_10034 (expression.bv_nat 17 1)) v_10034) (concat (expression.bv_nat 1 0) v_10037));
      v_10040 <- eval (extract v_10039 1 17);
      store v_10031 v_10040 2;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10033 v_10037) 11) (isBitSet v_10039 12)));
      setRegister cf (isBitSet v_10039 0);
      setRegister of (overflowFlag v_10033 v_10037 v_10040);
      setRegister pf (parityFlag (extract v_10039 9 17));
      setRegister sf (isBitSet v_10039 1);
      setRegister zf (zeroFlag v_10040);
      pure ()
    pat_end
