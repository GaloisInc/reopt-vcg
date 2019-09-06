def btl1 : instruction :=
  definst "btl" $ do
    pattern fun (v_3163 : imm int) (v_3167 : reg (bv 32)) => do
      v_5948 <- getRegister v_3167;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5948 (sext (bv_and (handleImmediateWithSignExtend v_3163 8 8) (expression.bv_nat 8 31)) 32)) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3171 : reg (bv 32)) (v_3172 : reg (bv 32)) => do
      v_5959 <- getRegister v_3172;
      v_5960 <- getRegister v_3171;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5959 (bv_and v_5960 (expression.bv_nat 32 31))) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3155 : imm int) (v_3158 : Mem) => do
      v_9280 <- evaluateAddress v_3158;
      v_9281 <- eval (handleImmediateWithSignExtend v_3155 8 8);
      v_9286 <- load (add v_9280 (concat (expression.bv_nat 59 0) (bv_and (extract v_9281 0 5) (expression.bv_nat 5 3)))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_9286 (concat (expression.bv_nat 5 0) (bv_and (extract v_9281 5 8) (expression.bv_nat 3 7)))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3162 : reg (bv 32)) (v_3161 : Mem) => do
      v_9297 <- evaluateAddress v_3161;
      v_9298 <- getRegister v_3162;
      v_9303 <- load (add v_9297 (concat (expression.bv_nat 3 0) (extract (sext v_9298 64) 0 61))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_9303 (concat (expression.bv_nat 5 0) (extract v_9298 29 32))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
