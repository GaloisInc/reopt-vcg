def btq1 : instruction :=
  definst "btq" $ do
    pattern fun (v_3181 : imm int) (v_3184 : reg (bv 64)) => do
      v_5977 <- getRegister v_3184;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5977 (sext (bv_and (handleImmediateWithSignExtend v_3181 8 8) (expression.bv_nat 8 63)) 64)) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3188 : reg (bv 64)) (v_3189 : reg (bv 64)) => do
      v_5988 <- getRegister v_3189;
      v_5989 <- getRegister v_3188;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5988 (bv_and v_5989 (expression.bv_nat 64 63))) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3173 : imm int) (v_3176 : Mem) => do
      v_9313 <- evaluateAddress v_3176;
      v_9314 <- eval (handleImmediateWithSignExtend v_3173 8 8);
      v_9319 <- load (add v_9313 (concat (expression.bv_nat 59 0) (bv_and (extract v_9314 0 5) (expression.bv_nat 5 7)))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_9319 (concat (expression.bv_nat 5 0) (bv_and (extract v_9314 5 8) (expression.bv_nat 3 7)))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3180 : reg (bv 64)) (v_3179 : Mem) => do
      v_9330 <- evaluateAddress v_3179;
      v_9331 <- getRegister v_3180;
      v_9335 <- load (add v_9330 (concat (expression.bv_nat 3 0) (extract v_9331 0 61))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_9335 (concat (expression.bv_nat 5 0) (extract v_9331 61 64))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
