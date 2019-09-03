def btrl1 : instruction :=
  definst "btrl" $ do
    pattern fun (v_3123 : imm int) (v_3125 : reg (bv 32)) => do
      v_6389 <- getRegister v_3125;
      v_6394 <- eval (uvalueMInt (mi 32 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3123 8 8) (expression.bv_nat 8 31)))));
      setRegister (lhs.of_reg v_3125) (bv_and v_6389 (bv_xor (extract (shl (expression.bv_nat 32 1) v_6394) 0 32) (expression.bv_nat 32 4294967295)));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6389 v_6394) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3129 : reg (bv 32)) (v_3130 : reg (bv 32)) => do
      v_6407 <- getRegister v_3130;
      v_6408 <- getRegister v_3129;
      v_6412 <- eval (uvalueMInt (mi 32 (svalueMInt (bv_and v_6408 (expression.bv_nat 32 31)))));
      setRegister (lhs.of_reg v_3130) (bv_and v_6407 (bv_xor (extract (shl (expression.bv_nat 32 1) v_6412) 0 32) (expression.bv_nat 32 4294967295)));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6407 v_6412) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3116 : imm int) (v_3115 : Mem) => do
      v_11461 <- evaluateAddress v_3115;
      v_11462 <- eval (handleImmediateWithSignExtend v_3116 8 8);
      v_11466 <- eval (add v_11461 (concat (expression.bv_nat 59 0) (bv_and (extract v_11462 0 5) (expression.bv_nat 5 3))));
      v_11467 <- load v_11466 1;
      v_11471 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11462 5 8) (expression.bv_nat 3 7))));
      store v_11466 (bv_and v_11467 (bv_xor (extract (shl (expression.bv_nat 8 1) v_11471) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11467 v_11471) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3120 : reg (bv 32)) (v_3119 : Mem) => do
      v_11484 <- evaluateAddress v_3119;
      v_11485 <- getRegister v_3120;
      v_11489 <- eval (add v_11484 (concat (expression.bv_nat 3 0) (extract (leanSignExtend v_11485 64) 0 61)));
      v_11490 <- load v_11489 1;
      v_11493 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11485 29 32)));
      store v_11489 (bv_and v_11490 (bv_xor (extract (shl (expression.bv_nat 8 1) v_11493) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11490 v_11493) 7 8);
      pure ()
    pat_end
