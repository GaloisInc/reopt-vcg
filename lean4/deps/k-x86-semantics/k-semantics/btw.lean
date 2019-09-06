def btw1 : instruction :=
  definst "btw" $ do
    pattern fun (v_3307 : imm int) (v_3310 : reg (bv 16)) => do
      v_6234 <- getRegister v_3310;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6234 (sext (bv_and (handleImmediateWithSignExtend v_3307 8 8) (expression.bv_nat 8 15)) 16)) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3314 : reg (bv 16)) (v_3315 : reg (bv 16)) => do
      v_6245 <- getRegister v_3315;
      v_6246 <- getRegister v_3314;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6245 (bv_and v_6246 (expression.bv_nat 16 15))) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3299 : imm int) (v_3302 : Mem) => do
      v_9357 <- evaluateAddress v_3302;
      v_9358 <- eval (handleImmediateWithSignExtend v_3299 8 8);
      v_9363 <- load (add v_9357 (concat (expression.bv_nat 59 0) (bv_and (extract v_9358 0 5) (expression.bv_nat 5 1)))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_9363 (concat (expression.bv_nat 5 0) (bv_and (extract v_9358 5 8) (expression.bv_nat 3 7)))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3306 : reg (bv 16)) (v_3305 : Mem) => do
      v_9374 <- evaluateAddress v_3305;
      v_9375 <- getRegister v_3306;
      v_9380 <- load (add v_9374 (concat (expression.bv_nat 3 0) (extract (sext v_9375 64) 0 61))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_9380 (concat (expression.bv_nat 5 0) (extract v_9375 13 16))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
