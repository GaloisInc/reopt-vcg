def btw1 : instruction :=
  definst "btw" $ do
    pattern fun (v_3282 : imm int) (v_3280 : reg (bv 16)) => do
      v_6353 <- getRegister v_3280;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6353 (sext (bv_and (handleImmediateWithSignExtend v_3282 8 8) (expression.bv_nat 8 15)) 16)) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3285 : reg (bv 16)) (v_3286 : reg (bv 16)) => do
      v_6364 <- getRegister v_3286;
      v_6365 <- getRegister v_3285;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6364 (bv_and v_6365 (expression.bv_nat 16 15))) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3273 : imm int) (v_3275 : Mem) => do
      v_9533 <- evaluateAddress v_3275;
      v_9534 <- eval (handleImmediateWithSignExtend v_3273 8 8);
      v_9539 <- load (add v_9533 (concat (expression.bv_nat 59 0) (bv_and (extract v_9534 0 5) (expression.bv_nat 5 1)))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_9539 (concat (expression.bv_nat 5 0) (bv_and (extract v_9534 5 8) (expression.bv_nat 3 7)))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3276 : reg (bv 16)) (v_3279 : Mem) => do
      v_9550 <- evaluateAddress v_3279;
      v_9551 <- getRegister v_3276;
      v_9556 <- load (add v_9550 (concat (expression.bv_nat 3 0) (extract (sext v_9551 64) 0 61))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_9556 (concat (expression.bv_nat 5 0) (extract v_9551 13 16))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
