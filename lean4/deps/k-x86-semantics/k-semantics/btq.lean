def btq1 : instruction :=
  definst "btq" $ do
    pattern fun (v_3155 : imm int) (v_3158 : reg (bv 64)) => do
      v_6096 <- getRegister v_3158;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6096 (sext (bv_and (handleImmediateWithSignExtend v_3155 8 8) (expression.bv_nat 8 63)) 64)) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3162 : reg (bv 64)) (v_3163 : reg (bv 64)) => do
      v_6107 <- getRegister v_3163;
      v_6108 <- getRegister v_3162;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6107 (bv_and v_6108 (expression.bv_nat 64 63))) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3147 : imm int) (v_3149 : Mem) => do
      v_9489 <- evaluateAddress v_3149;
      v_9490 <- eval (handleImmediateWithSignExtend v_3147 8 8);
      v_9495 <- load (add v_9489 (concat (expression.bv_nat 59 0) (bv_and (extract v_9490 0 5) (expression.bv_nat 5 7)))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_9495 (concat (expression.bv_nat 5 0) (bv_and (extract v_9490 5 8) (expression.bv_nat 3 7)))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3153 : reg (bv 64)) (v_3152 : Mem) => do
      v_9506 <- evaluateAddress v_3152;
      v_9507 <- getRegister v_3153;
      v_9511 <- load (add v_9506 (concat (expression.bv_nat 3 0) (extract v_9507 0 61))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_9511 (concat (expression.bv_nat 5 0) (extract v_9507 61 64))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
